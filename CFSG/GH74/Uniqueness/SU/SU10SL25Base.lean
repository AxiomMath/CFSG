module

public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup

theorem exists_equiv_of_isSL25 {Y : Type} [Group Y] (h : K.IsSL25 Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 5 ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hfin, hcard,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm⟩⟩

theorem card_of_isSL25 {Y : Type} [Group Y] (h : K.IsSL25 Y) : Nat.card Y = 120 := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := exists_equiv_of_isSL25 h
  calc Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := Nat.card_congr e.toEquiv
    _ = Nat.card F * (Nat.card F ^ 2 - 1) :=
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
    _ = 5 * (5 ^ 2 - 1) := by rw [hcard]
    _ = 120 := by norm_num

theorem exists_central_involution_of_isSL25 {Y : Type} [Group Y] (h : K.IsSL25 Y) :
    ∃ ζ : Y, orderOf ζ = 2 ∧ ζ ∈ center Y := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := exists_equiv_of_isSL25 h
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    decide
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hmem := CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F
  refine ⟨e.symm (CFSG.Semidihedral.OddFieldSL2.minusIdentity F), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F h2]
  · rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.symm.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hmem y']

theorem factorization_two_one_twenty : (120 : ℕ).factorization 2 = 3 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  rw [show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem sylow_isSL25_q8 {Y : Type} [Group Y] [Finite Y] (h : K.IsSL25 Y) (P : Sylow 2 Y) :
    Nonempty (↥(P : Subgroup Y) ≃* QuaternionGroup 2) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := exists_equiv_of_isSL25 h
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    decide
  have hP8 : Nat.card (P : Subgroup Y) = 8 := by
    have h8 : Nat.card (P : Subgroup Y) = 2 ^ (Nat.card Y).factorization 2 :=
      Sylow.card_eq_multiplicity P
    rw [h8, card_of_isSL25 h, factorization_two_one_twenty]
    norm_num
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (P : Subgroup Y).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  obtain ⟨n, hn3, ⟨φ⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd P'
  have ψ0 : ↥(P : Subgroup Y) ≃* ↥(P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    (Subgroup.equivMapOfInjective (P : Subgroup Y) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hP'.symm)
  obtain ⟨ψ⟩ : Nonempty (↥(P : Subgroup Y) ≃* QuaternionGroup (2 ^ (n - 2))) := ⟨ψ0.trans φ⟩
  have hnz : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hcardQ : Nat.card (QuaternionGroup (2 ^ (n - 2))) = 4 * 2 ^ (n - 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : 2 ^ (n - 2) = 2 := by
    have := Nat.card_congr ψ.toEquiv
    rw [hP8, hcardQ] at this
    omega
  rw [h2] at ψ
  exact ⟨ψ⟩

end CFSG.GH74.Uniqueness.SU.SU10
