module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl264R
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Tags

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.O264

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux QuadraticMap

theorem exists_theta {K V S : Type} [Field K] [AddCommGroup V] [Module K V] [Group S]
    {Q : QuadraticForm K V} (E : S ≃* ProjOrthDerived Q) :
    ∃ θ : ↥(orthDerived Q) →* S, Function.Surjective θ ∧
      θ.ker = (scalars K V).subgroupOf (orthDerived Q) := by
  refine ⟨E.symm.toMonoidHom.comp (QuotientGroup.mk' _),
    E.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

theorem exists_orthModel {S : Type} [Group S] {t : StatedLieTag} {n : ℕ} (ht : OrthBad3 t n)
    (hS : LieModel S t n 3 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ) (Q : QuadraticForm K (Fin d → K))
      (θ : ↥(orthDerived Q) →* S), Nat.card K = 3 ∧ (polarBilin Q).Nondegenerate ∧ 7 ≤ d ∧
        Function.Surjective θ ∧ θ.ker = (scalars K (Fin d → K)).subgroupOf (orthDerived Q) := by
  have hn0 : n ≠ 0 := by rcases ht with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨-, -, hC⟩ : t ∈ classicalTags ∧ StatedClassicalModel S t n 3 1 := by
    rcases hS with h | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 hn0
  rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hC
    have hK3 : Nat.card K = 3 := by simpa using hK
    obtain ⟨θ, hθ, hker⟩ := exists_theta (e.trans (oddProjEquiv n (by omega)))
    exact ⟨K, inferInstance, inferInstance, _, _, θ, hK3,
      (regular_coordinateQuadOdd n K (two_ne_zero_of_card_eq_three hK3) hn).1, by omega, hθ, hker⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hC
    have hK3 : Nat.card K = 3 := by simpa using hK
    obtain ⟨θ, hθ, hker⟩ := exists_theta (e.trans (plusProjEquiv n (by omega)))
    exact ⟨K, inferInstance, inferInstance, _, _, θ, hK3,
      (regular_coordinateQuadPlus n K (by omega)).1, by omega, hθ, hker⟩
  · obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
    have hK3 : Nat.card K = 3 := by simpa using hK
    obtain ⟨θ, hθ, hker⟩ := exists_theta (e.trans (minusProjEquiv n (by omega) b c (by omega)))
    exact ⟨K, inferInstance, inferInstance, _, _, θ, hK3,
      (regular_coordinateQuadMinus n K b c hn hirr).1, by omega, hθ, hker⟩

end CFSG.ClassicalInvolution.Q3.TL4.O264
