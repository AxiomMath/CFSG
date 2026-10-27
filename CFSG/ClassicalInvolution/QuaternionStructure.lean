module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.ClassicalInvolution.QuaternionStructure.Structure
public import CFSG.ClassicalInvolution.QuaternionStructure.WitnessCore
public import CFSG.ClassicalInvolution.QuaternionStructure.Perfect
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.GorensteinWalter
open scoped MatrixGroups

universe u

theorem involution_mem_center_oddCore_quotient {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    {r : ℕ} (hr : 3 ≤ r) (hq : Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∀ t ∈ (S : Subgroup X), orderOf t = 2 →
      (QuotientGroup.mk t : X ⧸ oddCore X) ∈ Subgroup.center (X ⧸ oddCore X) :=
  fun t ht ho => CFSG.BrauerSuzuki.brauer_suzuki r hr S hq t ht ho

theorem exists_central_unique_involution_oddCore_quotient {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∃ z : X ⧸ oddCore X, orderOf z = 2 ∧ z ∈ Subgroup.center (X ⧸ oddCore X) ∧
      ∀ t : X ⧸ oddCore X, orderOf t = 2 → t = z := by
  obtain ⟨r, hr, hq⟩ := hS
  exact QuaternionStructure.exists_central_unique_involution S ⟨r, hr, hq⟩
    (involution_mem_center_oddCore_quotient S hr hq)

theorem quaternion_sylow_structure {X : Type u} [Group X] [Finite X] (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∃ z : X ⧸ oddCore X, orderOf z = 2 ∧ z ∈ Subgroup.center (X ⧸ oddCore X) ∧
      (∀ t : X ⧸ oddCore X, orderOf t = 2 → t = z) ∧
      (IsPGroup 2 (X ⧸ oddCore X) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧ Nonempty (L ≃* SL(2, F))) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧
            (∃ φ : L →* Matrix.ProjGenLinGroup (Fin 2) F, Function.Surjective φ ∧
              φ.ker.map L.subtype = Subgroup.zpowers z) ∧
            (∀ P : Sylow 2 L, ∃ k : ℕ, 1 ≤ k ∧
              Nonempty ((P : Subgroup L) ≃* QuaternionGroup (2 ^ k))) ∧
            ∃ M : Subgroup (X ⧸ oddCore X), M.Normal ∧ M ≤ L ∧ Nonempty (M ≃* SL(2, F))) ∨
        (CFSG.Open.IsQuasisimple (X ⧸ oddCore X) ∧
          Nat.card (Subgroup.center (X ⧸ oddCore X)) = 2 ∧
          Nonempty (((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ≃*
            alternatingGroup (Fin 7)))) := by
  obtain ⟨r, hr, hq⟩ := hS
  obtain ⟨z, hz2, hzc, hzu, hstr⟩ := QuaternionStructure.quaternion_structure_of_hyps
    CFSG.GorensteinWalter.gorensteinWalter S ⟨r, hr, hq⟩
    (involution_mem_center_oddCore_quotient S hr hq)
  refine ⟨z, hz2, hzc, hzu, ?_⟩
  rcases hstr with h1 | h2 | h3 | ⟨hcomm, hsimple, hcard, hiso⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨hcomm, hsimple⟩, hcard, hiso⟩))

theorem quaternion_sylow_structure_of_pow {X : Type u} [Group X] [Finite X] (S : Sylow 2 X)
    {k : ℕ} (hk : 1 ≤ k) (hS : Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ k))) :
    ∃ z : X ⧸ oddCore X, orderOf z = 2 ∧ z ∈ Subgroup.center (X ⧸ oddCore X) ∧
      (∀ t : X ⧸ oddCore X, orderOf t = 2 → t = z) ∧
      (IsPGroup 2 (X ⧸ oddCore X) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧ Nonempty (L ≃* SL(2, F))) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧
            (∃ φ : L →* Matrix.ProjGenLinGroup (Fin 2) F, Function.Surjective φ ∧
              φ.ker.map L.subtype = Subgroup.zpowers z) ∧
            (∀ P : Sylow 2 L, ∃ m : ℕ, 1 ≤ m ∧
              Nonempty ((P : Subgroup L) ≃* QuaternionGroup (2 ^ m))) ∧
            ∃ M : Subgroup (X ⧸ oddCore X), M.Normal ∧ M ≤ L ∧ Nonempty (M ≃* SL(2, F))) ∨
        (CFSG.Open.IsQuasisimple (X ⧸ oddCore X) ∧
          Nat.card (Subgroup.center (X ⧸ oddCore X)) = 2 ∧
          Nonempty (((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ≃*
            alternatingGroup (Fin 7)))) :=
  quaternion_sylow_structure S ⟨k + 2, by omega, by rw [Nat.add_sub_cancel]; exact hS⟩

theorem quaternion_sylow_structure_of_perfect {X : Type u} [Group X] [Finite X] (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hperf : commutator (X ⧸ oddCore X) = ⊤) :
    (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
        Nonempty ((X ⧸ oddCore X) ≃* SL(2, F))) ∨
      (CFSG.Open.IsQuasisimple (X ⧸ oddCore X) ∧
        Nat.card (Subgroup.center (X ⧸ oddCore X)) = 2 ∧
        Nonempty (((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ≃*
          alternatingGroup (Fin 7))) := by
  obtain ⟨r, hr, hq⟩ := hS
  rcases QuaternionStructure.quaternion_structure_of_perfect_of_hyps
      CFSG.GorensteinWalter.gorensteinWalter
      (fun Q _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h) S ⟨r, hr, hq⟩
      (involution_mem_center_oddCore_quotient S hr hq) hperf with h1 | ⟨hcomm, hsimple, hcard, hiso⟩
  · exact Or.inl h1
  · exact Or.inr ⟨⟨hcomm, hsimple⟩, hcard, hiso⟩

theorem exists_normal_twoComplement_of_isPGroup_oddCore_quotient {X : Type*} [Group X] [Finite X]
    (h : IsPGroup 2 (X ⧸ oddCore X)) :
    ∃ (N : Subgroup X) (_ : N.Normal), Odd (Nat.card N) ∧ IsPGroup 2 (X ⧸ N) :=
  ⟨oddCore X, inferInstance, QuaternionStructure.odd_natCard_oddCore X, h⟩

theorem specialLinearGroup_sylow_quaternion (F : Type*) [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (P : Sylow 2 SL(2, F)) :
    ∃ k : ℕ, 1 ≤ k ∧ Nonempty ((P : Subgroup SL(2, F)) ≃* QuaternionGroup (2 ^ k)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F
    (QuaternionStructure.odd_natCard_of_ringChar_ne_two F hF) P
  exact ⟨n - 2, by omega, ⟨e⟩⟩

theorem specialLinearGroup_unique_involution (F : Type*) [Field F] [Finite F]
    (hF : ringChar F ≠ 2) :
    (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) ∧ orderOf (-1 : SL(2, F)) = 2 ∧
      ∀ x : SL(2, F), orderOf x = 2 ↔ x = -1 := by
  obtain ⟨hc, ho, hu, -⟩ := CFSG.Semidihedral.OddFieldSL2.odd_field_involution_structure F
    (QuaternionStructure.odd_natCard_of_ringChar_ne_two F hF)
  exact ⟨hc, ho, hu⟩

end CFSG.ClassicalInvolution
