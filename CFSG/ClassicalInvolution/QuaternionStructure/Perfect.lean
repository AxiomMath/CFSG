module

public import CFSG.ClassicalInvolution.QuaternionStructure.Structure

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG CFSG.GorensteinWalter
open scoped MatrixGroups

universe u

theorem eq_top_of_normal_of_odd_index_of_perfect {Y : Type u} [Group Y] [Finite Y]
    (hFT : ∀ (Q : Type u) [Group Q] [Finite Q], Odd (Nat.card Q) → Group.IsSolvable Q)
    (hperf : Group.IsPerfect Y) (L : Subgroup Y) [L.Normal] (hL : Odd L.index) : L = ⊤ := by
  by_contra hne
  have hperfQ : Group.IsPerfect (Y ⧸ L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)
  have hsolv : Group.IsSolvable (Y ⧸ L) :=
    hFT _ (by rw [← Subgroup.index_eq_card]; exact hL)
  have hindex : 1 < L.index := by
    have h0 : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : L.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
    omega
  have hnt : Nontrivial (Y ⧸ L) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [← Subgroup.index_eq_card]; exact hindex)
  exact Group.IsPerfect.not_isSolvable (Y ⧸ L) hsolv

theorem not_isPerfect_of_isPGroup {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    (h : IsPGroup 2 Y) : ¬ Group.IsPerfect Y := by
  intro hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent Y := h.isNilpotent
  exact Group.IsPerfect.not_isSolvable Y (inferInstance : Group.IsSolvable Y)

theorem quaternion_structure_of_perfect_of_hyps (hGW : gorensteinWalterStatement.{u})
    (hFT : ∀ (Q : Type u) [Group Q] [Finite Q], Odd (Nat.card Q) → Group.IsSolvable Q)
    {X : Type u} [Group X] [Finite X] (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hBS : ∀ t ∈ (S : Subgroup X), orderOf t = 2 →
      (QuotientGroup.mk t : X ⧸ oddCore X) ∈ Subgroup.center (X ⧸ oddCore X))
    (hperf : commutator (X ⧸ oddCore X) = ⊤) :
    (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
        Nonempty ((X ⧸ oddCore X) ≃* SL(2, F))) ∨
      (commutator (X ⧸ oddCore X) = ⊤ ∧
        IsSimpleGroup ((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ∧
        Nat.card (Subgroup.center (X ⧸ oddCore X)) = 2 ∧
        Nonempty (((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ≃*
          alternatingGroup (Fin 7))) := by
  obtain ⟨z, hz2, -, -, hstr⟩ := quaternion_structure_of_hyps hGW S hS hBS
  have hperf' : Group.IsPerfect (X ⧸ oddCore X) := Group.isPerfect_def.mpr hperf
  have hnt : Nontrivial (X ⧸ oddCore X) :=
    ⟨⟨z, 1, fun h => by rw [h, orderOf_one] at hz2; omega⟩⟩
  rcases hstr with h2 | ⟨F, _, _, hF, L, hLn, hLi, ⟨e⟩⟩ |
      ⟨F, _, _, hF, L, hLn, hLi, ⟨φ, hφ, -⟩, -, -⟩ | h4
  · exact absurd hperf' (not_isPerfect_of_isPGroup h2)
  · have hL : L = ⊤ := eq_top_of_normal_of_odd_index_of_perfect hFT hperf' L hLi
    exact Or.inl ⟨F, inferInstance, inferInstance, hF,
      ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans e⟩⟩
  · exfalso
    have hL : L = ⊤ := eq_top_of_normal_of_odd_index_of_perfect hFT hperf' L hLi
    have hK : IsOddPrimePower (Nat.card F) := by
      have : Fintype F := Fintype.ofFinite F
      have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
      obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
      refine ⟨ringChar F, n, hp, hp.odd_of_ne_two hF, n.pos, ?_⟩
      rw [Nat.card_eq_fintype_card, hn]
    let ψ : X ⧸ oddCore X →* Matrix.ProjGenLinGroup (Fin 2) F :=
      φ.comp (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).toMonoidHom
    have hψ : Function.Surjective ψ :=
      hφ.comp (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).surjective
    have hperfP : Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := ψ) hψ
    exact (pgl2_commutator_ne_bot_ne_top F hK).2 (Group.isPerfect_def.mp hperfP)
  · obtain ⟨hcomm, hsimple, hcard, hiso⟩ := h4
    exact Or.inr ⟨hcomm, hsimple, hcard, hiso⟩

end CFSG.ClassicalInvolution.QuaternionStructure
