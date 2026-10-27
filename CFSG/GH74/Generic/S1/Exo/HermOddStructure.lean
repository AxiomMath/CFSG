module

public import CFSG.GH74.Generic.S1.Exo.HermOddKernel
public import CFSG.GH74.Generic.S1.Exo.SoFormBasic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.Generic.S1.Exo.HermOddRho

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module QuadraticMap CFSG.Open
open scoped MatrixGroups

theorem soForm_minus_four_structure {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {V : Type} [AddCommGroup V] [Module K V] (hdim : finrank K V = 4) (Q : QuadraticForm K V)
    (hnd : LinearMap.Nondegenerate (polarBilin Q))
    (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card K ^ 2 ∧
      ∃ Ω : Subgroup (V ≃ₗ[K] V), Ω ≤ soForm Q ∧ IsSimpleGroup Ω ∧ Group.IsPerfect Ω ∧
        Nat.card Ω * 2 = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) ∧
        Nonempty (Ω ≃* StatedProj (StatedSL 2 E)) ∧
        LinearEquiv.neg K ∈ soForm Q ∧ LinearEquiv.neg K ∉ Ω ∧
        ∀ g ∈ soForm Q, g ∈ Ω ∨ LinearEquiv.neg K * g ∈ Ω := by
  classical
  have hfd : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hdim
  have hfinV : Finite V := Module.finite_of_finite K
  obtain ⟨E, hEF, hEA, ⟨D⟩⟩ := exists_oddNormPlane K h2
  have hfinE : Finite E := D.finite_E
  have hcardE : Nat.card E = Nat.card K ^ 2 := D.card_E
  have h4 : 4 ≤ Nat.card E := by
    rw [hcardE]
    have : 2 ≤ Nat.card K := Finite.one_lt_card
    nlinarith
  refine ⟨E, hEF, hfinE, hcardE, ?_⟩
  have hfdW : FiniteDimensional K (hermOddSpace D.σ) :=
    Module.finite_of_finrank_eq_succ (finrank_hermOddSpace D)
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff hnd
    (nondegenerate_hermOddForm D) (n := 2) (by omega) (by rw [finrank_hermOddSpace D])
    ⟨fun h => absurd h hnp, fun h => absurd h (not_isPlusType_hermOddForm D)⟩
  have hfinG : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  let Ω₄ := (hermOddRho D).range
  let Φ := linearEquivConj e.toLinearEquiv
  have hΩ4card : Nat.card Ω₄ * 2 = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    have := natCard_hermOddRho_range_mul_two D h2
    rw [hcardE, ← pow_mul] at this
    exact this
  have hΩcard : Nat.card (Ω₄.map Φ.toMonoidHom) = Nat.card Ω₄ :=
    (Nat.card_congr (MulEquiv.subgroupMap Φ Ω₄).toEquiv).symm
  have hle : Ω₄.map Φ.toMonoidHom ≤ soForm Q := by
    rintro _ ⟨x, ⟨g, rfl⟩, rfl⟩
    refine linearEquivConj_mem_soForm e ?_
    rw [mem_soForm_iff]
    exact ⟨(TauCeti.QuadraticMap.mem_orthogonalGroup_iff).1 (hermOddRho_mem D g),
      det_hermOddRho D h4 g⟩
  have hneg : (LinearEquiv.neg K : V ≃ₗ[K] V) ∉ Ω₄.map Φ.toMonoidHom := by
    rintro ⟨x, hx, hxn⟩
    apply neg_not_mem_range_hermOddRho D h2
    have : x = LinearEquiv.neg K := by
      apply Φ.injective
      rw [← linearEquivConj_neg e.toLinearEquiv] at hxn
      exact hxn
    rw [← this]
    exact hx
  obtain ⟨r, hrO, hrS⟩ := exists_reflection_not_mem_soForm h2 hdim Q hnd
  refine ⟨Ω₄.map Φ.toMonoidHom, hle, ?_, ?_, ?_, ?_, neg_mem_soForm_of_finrank_four hdim Q, hneg,
    ?_⟩
  · have := isSimpleGroup_hermOddRho_range D h4
    exact (MulEquiv.subgroupMap Φ Ω₄).symm.isSimpleGroup
  · have := isPerfect_hermOddRho_range D h4
    exact Group.IsPerfect.map Φ.toMonoidHom
  · rw [hΩcard]
    exact hΩ4card
  · exact ⟨((MulEquiv.subgroupMap Φ Ω₄).symm.trans (hermOddRangeEquiv D)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 E)⟩
  · exact mem_or_mul_mem_of_card (O := TauCeti.QuadraticMap.orthogonalGroup Q)
      (natCard_orthogonalGroup_minus_four hdim Q hnd hnp) (by rw [hΩcard]; exact hΩ4card) hle
      inf_le_left (neg_mem_soForm_of_finrank_four hdim Q) hneg hrO hrS

end CFSG.GH74.Generic.S1.Exo
