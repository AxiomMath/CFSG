module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace S11

variable {G : Type} [Group G] [Finite G]

private theorem mem_zpowers_of_orderOf_eq {C : Subgroup G} [IsCyclic C] {y z : G} (hyC : y ∈ C)
    (hzC : z ∈ C) (hord : orderOf y = orderOf z) : z ∈ Subgroup.zpowers y := by
  have heq : Subgroup.zpowers (⟨y, hyC⟩ : C) = Subgroup.zpowers (⟨z, hzC⟩ : C) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk,
      Subgroup.orderOf_mk]
    exact hord
  have hz : (⟨z, hzC⟩ : C) ∈ Subgroup.zpowers (⟨y, hyC⟩ : C) := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩

open scoped Pointwise in
private theorem exists_conj_mem_sylow {q : ℕ} (hq : q.Prime) {Y : Subgroup G} (Q : Sylow q Y)
    {S : Subgroup G} (hSY : S ≤ Y) (hS : IsPGroup q S) :
    ∃ g : Y, ∀ s ∈ S, ∃ t ∈ (Q : Subgroup Y), (t : G) = (g : G) * s * (g : G)⁻¹ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hS' : IsPGroup q (S.subgroupOf Y) := hS.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hS'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q₀ Q
  have hconj : MulAut.conj g • (Q₀ : Subgroup Y) = (Q : Subgroup Y) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  refine ⟨g, fun s hs => ?_⟩
  have hsQ₀ : (⟨s, hSY hs⟩ : Y) ∈ Q₀ := hQ₀ (Subgroup.mem_subgroupOf.2 hs)
  have hmem := Subgroup.smul_mem_pointwise_smul (⟨s, hSY hs⟩ : Y) (MulAut.conj g) _ hsQ₀
  rw [hconj] at hmem
  exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩

private theorem isCyclic_of_isPGroup_of_cent_cyclic {q : ℕ} (hq : q.Prime) {Y : Subgroup G} {y : G}
    (hy : y ∈ Y) (hyq : orderOf y = q)
    (h : ∀ S : Subgroup G, S ≤ Y ⊓ Subgroup.centralizer ({y} : Set G) → IsPGroup q S →
      IsCyclic S) :
    ∀ S : Subgroup G, S ≤ Y → IsPGroup q S → IsCyclic S := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hzp : IsPGroup q (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyq, pow_one])
  obtain ⟨Q, hQ⟩ := (hzp.comap_subtype (K := Y)).exists_le_sylow
  have hQ'p : IsPGroup q ((Q : Subgroup Y).map Y.subtype) := Q.isPGroup'.map Y.subtype
  have hQ'Y : (Q : Subgroup Y).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
  have hyQ' : y ∈ (Q : Subgroup Y).map Y.subtype :=
    ⟨⟨y, hy⟩, hQ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers y)), rfl⟩
  have hQ'cyc : IsCyclic ((Q : Subgroup Y).map Y.subtype) := by
    set Q' : Subgroup G := (Q : Subgroup Y).map Y.subtype with hQ'
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hyq
      exact hq.one_lt.ne hyq
    haveI : Nontrivial Q' := ⟨⟨⟨y, hyQ'⟩, 1, fun h' => hy1 (congrArg Subtype.val h')⟩⟩
    haveI : Nontrivial (Subgroup.center Q') := hQ'p.center_nontrivial
    have hZp : IsPGroup q (Subgroup.center Q') := hQ'p.to_subgroup _
    have hdvd : q ∣ Nat.card (Subgroup.center Q') := by
      obtain ⟨n, hn0, hn⟩ := hZp.nontrivial_iff_card.1 inferInstance
      rw [hn]
      exact dvd_pow_self q hn0.ne'
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' q hdvd
    have hzQ' : ((ζ : Q') : G) ∈ Q' := (ζ : Q').2
    have hzord : orderOf ((ζ : Q') : G) = q := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hζ]
    have hzcomm : ∀ w ∈ Q', w * ((ζ : Q') : G) = ((ζ : Q') : G) * w := by
      intro w hw
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ζ.2 ⟨w, hw⟩)
    have hzcent : ((ζ : Q') : G) ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact hzcomm u hyQ'
    haveI hCcyc : IsCyclic ↥(Q' ⊓ Subgroup.centralizer ({y} : Set G)) :=
      h _ (inf_le_inf_right _ hQ'Y) (hQ'p.to_le inf_le_left)
    have hyC : y ∈ Q' ⊓ Subgroup.centralizer ({y} : Set G) :=
      ⟨hyQ', Subgroup.mem_centralizer_iff.2 fun u hu => by
        rw [Set.mem_singleton_iff] at hu
        rw [hu]⟩
    have hzC : ((ζ : Q') : G) ∈ Q' ⊓ Subgroup.centralizer ({y} : Set G) := ⟨hzQ', hzcent⟩
    have hy_mem : y ∈ Subgroup.zpowers ((ζ : Q') : G) :=
      mem_zpowers_of_orderOf_eq hzC hyC (hzord.trans hyq.symm)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy_mem
    have hQ'cent : Q' ≤ Subgroup.centralizer ({y} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      rw [← hn]
      exact (Commute.zpow_left (Commute.symm (hzcomm w hw)) n).eq
    exact h Q' (le_inf hQ'Y hQ'cent) hQ'p
  intro S hSY hSp
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow hq Q hSY hSp
  let φ : S →* ((Q : Subgroup Y).map Y.subtype) :=
    MonoidHom.codRestrict ((MulAut.conj (g : G)).toMonoidHom.comp S.subtype)
      ((Q : Subgroup Y).map Y.subtype) fun s => by
        obtain ⟨t, htQ, ht⟩ := hg s s.2
        exact ⟨t, htQ, by simpa [MulAut.conj_apply] using ht⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg (fun x : (Q : Subgroup Y).map Y.subtype => (x : G)) hab
    simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype] at this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  exact isCyclic_of_injective φ hφ

theorem cycModSylow_of_cent_cyclic {q : ℕ} (hq : q.Prime) {L : Subgroup G} {y : G}
    (hy : y ∈ centModSubgroup q L) (hyq : orderOf y = q)
    (h : ∀ S : Subgroup G, S ≤ centModSubgroup q L ⊓ Subgroup.centralizer ({y} : Set G) →
      IsPGroup q S → IsCyclic S) :
    CycModSylow q L := fun S hS hSp =>
  isCyclic_of_isPGroup_of_cent_cyclic hq hy hyq h S (fun g hg => centMod_iff.1 (hS g hg)) hSp

end S11

end CFSG.LocalAnalysis.GLTheoremA
