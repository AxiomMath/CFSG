module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K3010

open Subgroup

theorem exists_conj_eq_inv {X : Type*} [Group X] [Finite X] [hX : Group.IsPerfect X]
    (h9 : ¬ 9 ∣ Nat.card X) {g : X} (hg : orderOf g = 3) : ∃ h : X, h * g * h⁻¹ = g⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard0 : Nat.card (zpowers g) = 3 := by rw [Nat.card_zpowers, hg]
  have hP0 : IsPGroup 3 (zpowers g) := IsPGroup.of_card (n := 1) (by rw [hcard0, pow_one])
  obtain ⟨P, hP⟩ := hP0.exists_le_sylow
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hdvd : Nat.card (P : Subgroup X) ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  have h3 : 3 ∣ Nat.card (P : Subgroup X) := by
    have h := Subgroup.card_dvd_of_le hP
    rwa [hcard0] at h
  have hn1 : n = 1 := by
    rw [hn] at hdvd h3
    rcases n with _ | _ | n
    · norm_num at h3
    · rfl
    · exact absurd ((pow_dvd_pow 3 (by omega : 2 ≤ n + 2)).trans hdvd) (by simpa using h9)
  have hPeq : zpowers g = (P : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hn, hn1, hcard0, pow_one])
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    norm_num at hg
  have hg3 : g ^ 3 = 1 := hg ▸ pow_orderOf_eq_one g
  by_contra hno
  push Not at hno
  have hN : normalizer (P : Subgroup X) ≤ centralizer ((P : Subgroup X) : Set X) := by
    intro m hm
    have hmg : m * g * m⁻¹ ∈ zpowers g := by
      rw [hPeq]
      exact (mem_normalizer_iff.1 hm g).1 (hPeq ▸ mem_zpowers g)
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hg] at hmg
    simp only [Finset.mem_image, Finset.mem_range] at hmg
    obtain ⟨i, hi, hgi⟩ := hmg
    have hcomm : g * m = m * g := by
      interval_cases i
      · rw [pow_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at hgi
        exact absurd hgi hg1
      · rw [pow_one, eq_mul_inv_iff_mul_eq] at hgi
        exact hgi
      · refine absurd ?_ (hno m)
        rw [← hgi, eq_inv_iff_mul_eq_one, ← pow_succ]
        exact hg3
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ zpowers g := by
      rw [hPeq]
      exact hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx'
    exact (Commute.zpow_left hcomm j).eq
  have hcomP : ∀ a b : (P : Subgroup X), a * b = b * a := fun a b =>
    Subtype.ext (hN (le_normalizer b.2) a a.2)
  have hker : ∀ x : X, MonoidHom.transferSylow P hN x = 1 := by
    have hle : commutator X ≤ (MonoidHom.transferSylow P hN).ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomP _ _
    intro x
    have hx : x ∈ commutator X := by
      rw [hX.commutator_eq_top]
      exact mem_top x
    exact MonoidHom.mem_ker.1 (hle hx)
  have hgP : g ∈ P := by
    have h := mem_zpowers g
    rw [hPeq] at h
    exact h
  have hpow := MonoidHom.transferSylow_eq_pow P hN g hgP
  rw [hker g] at hpow
  have h1 : g ^ (P : Subgroup X).index = 1 := by
    have := congrArg Subtype.val hpow
    simpa using this.symm
  have h3i := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h3i
  exact P.not_dvd_index h3i

theorem isPerfect_alternatingGroup_five : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem zmod_two_eq_one_of_isUnit {x : ZMod 2} (h : IsUnit x) : x = 1 := by
  fin_cases x
  · exact absurd h not_isUnit_zero
  · rfl

theorem toGL_surjective_three :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := ZMod 2)) := by
  intro g
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 :=
    zmod_two_eq_one_of_isUnit (Matrix.isUnits_det_units g)
  exact ⟨⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)), hdet⟩,
    Matrix.GeneralLinearGroup.ext fun _ _ => rfl⟩

theorem isPerfect_GL_three_two : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := by
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := ZMod 2) (n := 3) (by norm_num)
  exact Group.IsPerfect.ofSurjective toGL_surjective_three

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3, Fin.prod_univ_three, ZMod.card]
  norm_num

theorem alternatingGroup_five_exists_conj_eq_inv {g : alternatingGroup (Fin 5)}
    (hg : orderOf g = 3) : ∃ h, h * g * h⁻¹ = g⁻¹ := by
  haveI := isPerfect_alternatingGroup_five
  exact exists_conj_eq_inv (by rw [card_alternatingGroup_five]; decide) hg

theorem GL_three_two_exists_conj_eq_inv {g : GL (Fin 3) (ZMod 2)} (hg : orderOf g = 3) :
    ∃ h, h * g * h⁻¹ = g⁻¹ := by
  haveI := isPerfect_GL_three_two
  exact exists_conj_eq_inv (by rw [card_GL_three_two]; decide) hg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K3010
