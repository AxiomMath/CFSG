module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayerA
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

private lemma mulAut_conj_eq_one_iff_mem_center {G : Type*} [Group G] (j : G) :
    MulAut.conj j = 1 ↔ j ∈ Subgroup.center G := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : MulAut.conj j g = (1 : MulAut G) g := by rw [h]
    rw [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  · intro h
    apply MulEquiv.ext
    intro g
    rw [MulAut.conj_apply, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp h g).symm

private lemma mem_center_of_pow_mem_center_of_coprime {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hcop : Nat.Coprime p (Nat.card G)) {j : G} {n : ℕ}
    (hpow : j ^ p ^ n ∈ Subgroup.center G) : j ∈ Subgroup.center G := by
  let s : G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G) j
  have hs_pow : s ^ p ^ n = 1 := by
    show (QuotientGroup.mk' (Subgroup.center G) j) ^ p ^ n = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center G) _).mpr hpow
  have hdvd1 : orderOf s ∣ p ^ n := orderOf_dvd_of_pow_eq_one hs_pow
  have hdvd2 : orderOf s ∣ Nat.card G :=
    (orderOf_dvd_natCard s).trans (Subgroup.card_quotient_dvd_card (Subgroup.center G))
  have hcop' : Nat.Coprime (orderOf s) (Nat.card G) :=
    Nat.Coprime.coprime_dvd_left hdvd1 (hcop.pow_left n)
  have hone : orderOf s = 1 := hcop'.eq_one_of_dvd hdvd2
  exact (QuotientGroup.eq_one_iff (N := Subgroup.center G) j).mp (orderOf_eq_one_iff.mp hone)

private lemma not_isComponent_pPrimeCore {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) [Group.IsPerfect Y]
    (hgen : closure {y : Y | ∃ n : ℕ, orderOf y = p ^ n} = ⊤)
    (hK : CFSG.Open.IsKGroup Y)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (CFSG.pPrimeCore p Y) ≤ 3)
    (J : Subgroup ↥(CFSG.pPrimeCore p Y)) (hJ : CFSG.IsComponent J) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  let J' : Subgroup Y := J.map (CFSG.pPrimeCore p Y).subtype
  have hJ'normal : J'.Normal := normal_map_of_isComponent hrk hJ
  letI : J'.Normal := hJ'normal
  let e : ↥J ≃* ↥J' :=
    J.equivMapOfInjective (CFSG.pPrimeCore p Y).subtype
      (CFSG.pPrimeCore p Y).subtype_injective
  have hJ' : CFSG.IsQuasisimple ↥J' := CFSG.IsQuasisimple.of_mulEquiv e.symm hJ.1
  haveI : Group.IsPerfect ↥J' := hJ'.1
  haveI : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hJ'.2.1
  have hcatOpen : CFSG.Open.IsCatalogGroup (↥J' ⧸ Subgroup.center ↥J') :=
    hK.isCatalogGroup_of_surjective J' hJ'.2.2
      (QuotientGroup.mk' (Subgroup.center ↥J'))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J'))
  have hcat : CFSG.Assembly.InCatalog (↥J' ⧸ Subgroup.center ↥J') := hcatOpen
  haveI : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (↥J' ⧸ Subgroup.center ↥J')) := hS _ hJ'.2.2 hcat
  haveI : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J') :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient _
  let α : Y →* MulAut ↥J' := MulAut.conjNormal
  have hker : ∀ y : Y, (∃ n : ℕ, orderOf y = p ^ n) → α y = 1 := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    obtain ⟨j, hj⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner α y
    have hy_pow : y ^ p ^ n = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one y
    have hjpow : MulAut.conj (j ^ p ^ n) = 1 := by
      calc
        MulAut.conj (j ^ p ^ n) = (MulAut.conj j) ^ p ^ n :=
          map_pow (MulAut.conj) j (p ^ n)
        _ = (α y) ^ p ^ n := by rw [← hj]
        _ = α (y ^ p ^ n) := (map_pow α y (p ^ n)).symm
        _ = α 1 := by rw [hy_pow]
        _ = 1 := map_one α
    have hjcenter_pow : j ^ p ^ n ∈ Subgroup.center ↥J' :=
      (mulAut_conj_eq_one_iff_mem_center (j ^ p ^ n)).mp hjpow
    have hcopJ' : Nat.Coprime p (Nat.card ↥J') :=
      (CFSG.pPrimeCore_coprime_card (p := p) (G := Y)).coprime_dvd_right
        (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le J))
    have hjcenter : j ∈ Subgroup.center ↥J' :=
      mem_center_of_pow_mem_center_of_coprime hcopJ' hjcenter_pow
    exact hj.trans ((mulAut_conj_eq_one_iff_mem_center j).mpr hjcenter)
  have htop : α.ker = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le α.ker).mpr (fun y hy => hker y hy)
  have hcommJ' : ∀ a ∈ J', ∀ b ∈ J', a * b = b * a := by
    intro a _ b hb
    have ha1 : α a = 1 := by
      have : a ∈ α.ker := by rw [htop]; exact Subgroup.mem_top a
      exact MonoidHom.mem_ker.mp this
    have ha1' : MulAut.conjNormal (H := J') a = 1 := by
      change α a = 1
      exact ha1
    have hval : ((MulAut.conjNormal (H := J') a) ⟨b, hb⟩ : ↥J') = ⟨b, hb⟩ := by
      rw [ha1']
      rfl
    have hcoe : a * b * a⁻¹ = b := by
      have h := congrArg (Subtype.val) hval
      simpa [MulAut.conjNormal_apply] using h
    exact mul_inv_eq_iff_eq_mul.mp hcoe
  have hcommS : ∀ s t : ↥J' ⧸ Subgroup.center ↥J', s * t = t * s := by
    intro s t
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J') s
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J') t
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (Subgroup.center ↥J'))
      (Subtype.ext (hcommJ' a.val a.2 b.val b.2))
  obtain ⟨a, b, hab⟩ := hJ'.2.2
  exact hab (hcommS a b)

theorem layer_pPrimeCore_eq_bot {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    [Group.IsPerfect Y] (hgen : closure {y : Y | ∃ n : ℕ, orderOf y = p ^ n} = ⊤)
    (hK : CFSG.Open.IsKGroup Y)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (CFSG.pPrimeCore p Y) ≤ 3) :
    CFSG.layer ↥(CFSG.pPrimeCore p Y) = ⊥ := by
  rw [CFSG.layer.eq_sSup, sSup_eq_bot]
  intro J hJ
  exact (not_isComponent_pPrimeCore hp hgen hK hS hrk J hJ).elim

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
