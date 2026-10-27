module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open scoped commutatorElement

theorem uexc_commutator_self {Ω : Type*} [Group Ω] {S : Subgroup Ω} (h : commutator ↥S = ⊤) :
    ⁅S, S⁆ = S := by
  rw [← Subgroup.map_subtype_commutator, h, Subgroup.map_top, S.range_subtype]

theorem uexc_pCore_two_le_center {G : Type*} [Group G] [Finite G]
    (hq : CFSG.Open.IsQuasisimple G) : CFSG.pCore 2 G ≤ Subgroup.center G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    (CFSG.pCore 2 G) with h | htop
  · exact h
  · exfalso
    have h2 : IsPGroup 2 G := by
      have := CFSG.pCore_isPGroup (p := 2) (G := G)
      rw [htop] at this
      exact this.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent G := h2.isNilpotent
    haveI : Nontrivial G := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial G
    rw [hq.1] at hlt
    exact lt_irrefl _ hlt

private theorem le_pCore_two {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (h : IsPGroup 2 N) : N ≤ CFSG.pCore 2 G := by
  rw [CFSG.pCore_eq_iSup]
  exact le_iSup_of_le N (le_iSup_of_le hN (le_iSup_of_le h le_rfl))

theorem uexc_odd_center_of_ker {G H : Type*} [Group G] [Finite G] [Group H]
    (hq : CFSG.Open.IsQuasisimple G) (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = CFSG.pCore 2 G) : Odd (Nat.card (Subgroup.center H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite H := Finite.of_surjective f hf
  haveI : Group.IsPerfect G := ⟨hq.1⟩
  rw [Nat.odd_iff]
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.center H) := by omega
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center H) 2 h2
  obtain ⟨g, hg⟩ := hf (c : H)
  have hcent : f.ker ≤ Subgroup.center G := by
    rw [hker]
    exact uexc_pCore_two_le_center hq
  have hgc : g ∈ Subgroup.center G := by
    rw [← CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel f hf hcent]
    show f g ∈ Subgroup.center H
    rw [hg]
    exact c.2
  have hc2 : c ^ 2 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  have hg2 : g ^ 2 ∈ CFSG.pCore 2 G := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hg]
    exact congrArg Subtype.val hc2
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := G) ⟨g ^ 2, hg2⟩
  have hgpow : g ^ (2 ^ (n + 1)) = 1 := by
    have := congrArg Subtype.val hn
    simpa [pow_succ', pow_mul] using this
  haveI hzn : (Subgroup.zpowers g).Normal := by
    refine ⟨fun m hm x => ?_⟩
    have hmc : m ∈ Subgroup.center G := Subgroup.zpowers_le.2 hgc hm
    have : x * m * x⁻¹ = m := by
      rw [Subgroup.mem_center_iff.1 hmc x, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hm
  have hzp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card_dvd_pow (n := n + 1)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hgpow)
  have hgker : g ∈ f.ker := by
    rw [hker]
    exact le_pCore_two hzn hzp (Subgroup.mem_zpowers g)
  have hc1 : (c : H) = 1 := by
    rw [← hg]
    exact hgker
  have : c = 1 := Subtype.ext hc1
  rw [this, orderOf_one] at hc
  omega

theorem uexc_twoCore_normal {Ω : Type*} [Group Ω] {S : Subgroup Ω} (hS : S.Normal) :
    ((CFSG.pCore 2 ↥S).map S.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hn
  have hg : g ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hS]
    exact Subgroup.mem_top g
  let α : MulAut ↥S := S.normalizerMonoidHom ⟨g, hg⟩
  have hcomp : S.subtype.comp α.toMonoidHom = (MulAut.conj g).toMonoidHom.comp S.subtype := by
    ext y
    simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  have hα : α x ∈ CFSG.pCore 2 ↥S := by
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore 2 ↥S).Characteristic) α
    rw [← hmap]
    exact Subgroup.mem_map_of_mem α.toMonoidHom hx
  refine ⟨α x, hα, ?_⟩
  have := congrArg (fun φ : ↥S →* Ω => φ x) hcomp
  simpa [MulAut.conj_apply] using this

theorem uexc_twoCore_isPGroup {Ω : Type*} [Group Ω] (S : Subgroup Ω) :
    IsPGroup 2 ((CFSG.pCore 2 ↥S).map S.subtype) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥S)).map S.subtype

theorem uexc_twoCore_le {Ω : Type*} [Group Ω] (S : Subgroup Ω) :
    (CFSG.pCore 2 ↥S).map S.subtype ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem uexc_twoCore_le_centralizer {Ω : Type*} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥S) :
    (CFSG.pCore 2 ↥S).map S.subtype ≤ Subgroup.centralizer (S : Set Ω) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.1 (uexc_pCore_two_le_center hq hx) ⟨g, hg⟩)

theorem uexc_isQuasisimple_map {Ω Ω' : Type*} [Group Ω] [Group Ω'] (π : Ω →* Ω')
    {S : Subgroup Ω} (hq : CFSG.Open.IsQuasisimple ↥S)
    (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) :
    CFSG.Open.IsQuasisimple ↥(S.map π) := by
  refine CFSG.LocalAnalysis.GLTheoremA.I142N.isQuasisimple_of_surjective (π.subgroupMap S)
    (π.subgroupMap_surjective S) (fun g hg => ?_) hq
  rw [Subgroup.mem_center_iff]
  intro s
  have h1 : (g : Ω) ∈ π.ker := congrArg Subtype.val hg
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hkc h1) s s.2)

theorem uexc_theta_bar {Ω Ω' : Type*} [Group Ω] [Group Ω'] (π : Ω →* Ω') {S : Subgroup Ω}
    (hperf : commutator ↥S = ⊤) (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω))
    {R : Type*} [Group R] (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) :
    ∃ θ' : ↥(S.map π) ⧸ Subgroup.center ↥(S.map π) ≃* R,
      ∀ s : ↥S, θ' (QuotientGroup.mk (π.subgroupMap S s)) = θ (QuotientGroup.mk s) := by
  haveI : Group.IsPerfect ↥S := ⟨hperf⟩
  have hfs : Function.Surjective (π.subgroupMap S) := π.subgroupMap_surjective S
  have hfker : (π.subgroupMap S).ker ≤ Subgroup.center ↥S := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 : (g : Ω) ∈ π.ker := congrArg Subtype.val hg
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hkc h1) s s.2)
  let g : ↥S →* ↥(S.map π) ⧸ Subgroup.center ↥(S.map π) :=
    (QuotientGroup.mk' (Subgroup.center ↥(S.map π))).comp (π.subgroupMap S)
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hfs
  have hgker : g.ker = Subgroup.center ↥S := by
    rw [← CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
      (π.subgroupMap S) hfs hfker]
    ext x
    simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  let e := QuotientGroup.quotientKerEquivOfSurjective g hgs
  refine ⟨(e.symm.trans (QuotientGroup.quotientMulEquivOfEq hgker)).trans θ, fun s => ?_⟩
  have h1 : e.symm (QuotientGroup.mk (π.subgroupMap S s)) = QuotientGroup.mk s :=
    e.symm_apply_eq.2 rfl
  simp only [MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]

theorem uexc_odd_center_map {Ω Ω' : Type} [Group Ω] [Finite Ω] [Group Ω'] (π : Ω →* Ω')
    {S : Subgroup Ω} (hq : CFSG.Open.IsQuasisimple ↥S)
    (hker : π.ker = (CFSG.pCore 2 ↥S).map S.subtype) :
    Odd (Nat.card (Subgroup.center ↥(S.map π))) := by
  refine uexc_odd_center_of_ker hq (π.subgroupMap S) (π.subgroupMap_surjective S) ?_
  ext x
  have h1 : (π.subgroupMap S) x = 1 ↔ (x : Ω) ∈ π.ker := by
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  rw [MonoidHom.mem_ker, h1, hker]
  exact Subgroup.mem_map_iff_mem S.subtype_injective

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
