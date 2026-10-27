module

import CFSG.Sporadic.Recognition.McLASCert
import CFSG.Sporadic.Presentation.McLExact
import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Certificates


private theorem center_native_mcl :
    Subgroup.center CFSG.Blueprint.NativeSporadic.McL = ⊥ := by
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hnoncomm : ¬ IsMulCommutative CFSG.Blueprint.NativeSporadic.McL := by
    intro hcomm
    haveI := hcomm
    have hp : (Nat.card CFSG.Blueprint.NativeSporadic.McL).Prime :=
      (Group.is_simple_iff_prime_card).mp (CFSG.Sporadic.McL.isSimpleGroup_McL)
    rw [CFSG.Sporadic.McL.card_McL] at hp
    have h2dvd : 2 ∣ (898128000 : ℕ) := by norm_num
    have h := (Nat.dvd_prime (p := 898128000) (m := 2) hp).mp h2dvd
    omega
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnoncomm

private theorem exists_conj_of_pow_three_native {β : MulAut CFSG.Blueprint.NativeSporadic.McL}
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ∃ y : CFSG.Blueprint.NativeSporadic.McL, β = MulAut.conj y ∧ orderOf y = 3 ∧
      3 ^ 5 ∣ Nat.card (Subgroup.centralizer
        ({y} : Set CFSG.Blueprint.NativeSporadic.McL)) := by
  have hP : IsPGroup 2 (Outer CFSG.Blueprint.NativeSporadic.McL) :=
    IsPGroup.of_card (p := 2) (n := 1) (by
      rw [CFSG.Sporadic.Recognition.McLAS.card_outer_mcl]; norm_num)
  have hβinner : β ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner CFSG.Blueprint.NativeSporadic.McL :=
    CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hP (by norm_num) hβ3
  obtain ⟨y, hy⟩ := hβinner
  have hcenter : Subgroup.center CFSG.Blueprint.NativeSporadic.McL = ⊥ := center_native_mcl
  have hyne : y ≠ 1 := by
    rintro rfl
    exact hβ1 (by simpa using hy.symm)
  have hy3 : y ^ 3 = 1 := by
    have hconj : MulAut.conj (y ^ 3) = 1 := by
      rw [map_pow, hy, hβ3]
    have hmem : y ^ 3 ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.McL := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h := congrArg (fun (a : MulAut CFSG.Blueprint.NativeSporadic.McL) => a z) hconj
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      have h' : y ^ 3 * z = z * y ^ 3 := by
        have := congrArg (fun t => t * y ^ 3) h
        simpa [mul_assoc] using this
      exact h'.symm
    simpa [hcenter] using hmem
  have horder : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have hne : orderOf y ≠ 1 := fun h => hyne (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨x₁, x₂, -, -, hC1, hC2, -, hcls⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_three_of_certificate
  have hcard : Nat.card (Subgroup.centralizer
        ({y} : Set CFSG.Blueprint.NativeSporadic.McL)) = 29160 ∨
      Nat.card (Subgroup.centralizer
        ({y} : Set CFSG.Blueprint.NativeSporadic.McL)) = 972 := by
    rcases hcls y horder with h | h
    · exact Or.inl (by rw [Subgroup.card_centralizer_of_isConj h, hC1])
    · exact Or.inr (by rw [Subgroup.card_centralizer_of_isConj h, hC2])
  rcases hcard with h | h
  · exact ⟨y, hy.symm, horder, by rw [h]; norm_num⟩
  · exact ⟨y, hy.symm, horder, by rw [h]; norm_num⟩

theorem exists_conj_of_pow_three_mcl {L : Type} [Group L] [Finite L]
    (e : L ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) {β : MulAut L} (hβ3 : β ^ 3 = 1)
    (hβ1 : β ≠ 1) :
    ∃ x : L, β = MulAut.conj x ∧ orderOf x = 3 ∧
      3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set L)) := by
  obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let f : L ≃* CFSG.Blueprint.NativeSporadic.McL := e.trans φ.symm
  let β' : MulAut CFSG.Blueprint.NativeSporadic.McL := f.symm.trans (β.trans f)
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 : ∀ y : L, β (β (β y)) = y := by
      intro y
      have h := congrArg (fun (a : MulAut L) => a y) hβ3
      simpa [pow_three, MulAut.mul_apply] using h
    apply MulEquiv.ext
    intro n
    simp only [β', pow_three, MulAut.mul_apply, MulAut.one_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    change f (β (β (β (f.symm n)))) = n
    rw [h3 (f.symm n)]
    simp
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβ1
    apply MulEquiv.ext
    intro x
    have hx := congrArg (fun (a : MulAut CFSG.Blueprint.NativeSporadic.McL) => a (f x)) h
    simp only [β', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at hx
    simpa using f.injective hx
  obtain ⟨y, hy, horder, hdiv⟩ := exists_conj_of_pow_three_native hβ'3 hβ'1
  have hβconj : β = MulAut.conj (f.symm y) := by
    apply MulEquiv.ext
    intro x
    have h := congrArg (fun (a : MulAut CFSG.Blueprint.NativeSporadic.McL) => a (f x)) hy
    simp only [β', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
      MulAut.conj_apply] at h
    have h' := congrArg f.symm h
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h'
    exact h'
  have hcard : Nat.card (Subgroup.centralizer ({f.symm y} : Set L)) =
      Nat.card (Subgroup.centralizer
        ({y} : Set CFSG.Blueprint.NativeSporadic.McL)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro z
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      simpa using congrArg f h
    · intro h
      exact f.injective (by simpa using h)
  exact ⟨f.symm y, hβconj, by rw [MulEquiv.orderOf_eq, horder], by rwa [hcard]⟩

end Certificates

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
