module

public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25I8
public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.Uniform.UThmStmtA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Dich

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)}


theorem mem_omegaNbr_of_commutes' {K J : Subgroup E} (hJ : J ∈ Φ) (hne : J ≠ K)
    (h : Commutes K J) : J ∈ omegaNbr Φ K := by
  refine ⟨hJ, hne, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  refine ⟨Subgroup.map J.subtype (P : Subgroup ↥J), ⟨J, hJ, P, rfl⟩, Subgroup.map_subtype_le _, ?_⟩
  rintro _ ⟨r, -, rfl⟩
  refine Subgroup.centralizer_le_normalizer (K : Set E) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact h k hk r r.2

theorem all_twin_of_dConnected (hΦ : HypOmegaGen Φ) (hconn : DConnected Φ) {A A' : Subgroup E}
    {z a₀ b₀ : E} (T : TwinSect0 Φ A A' z a₀ b₀) : ∀ L ∈ Φ, L = A ∨ L = A' := by
  have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup E => N ∈ Φ ∧ dAdj Φ M N) A N →
      N = A ∨ N = A' := by
    intro N hN
    induction hN with
    | refl => exact Or.inl rfl
    | tail hpre hstep ih =>
      rename_i M N'
      obtain ⟨hN'Φ, hadj⟩ := hstep
      have hMΦ : M ∈ Φ := by
        rcases ih with rfl | rfl
        · exact T.hA
        · exact T.hA'
      rcases ih with rfl | rfl
      · refine Or.inr (T.nbA N' hN'Φ ?_)
        rcases hadj with h | h
        · exact h
        · exact CFSG.ClassicalInvolution.Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hN'Φ hMΦ h
      · refine Or.inl (T.nbA' N' hN'Φ ?_)
        rcases hadj with h | h
        · exact h
        · exact CFSG.ClassicalInvolution.Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hN'Φ hMΦ h
  intro L hL
  exact hpath L (hconn _ T.hA L hL)

theorem dConnected_or_transitive3 {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hlt : Nat.card E < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore E = ⊥)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) :
    DConnected Φ ∨ ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : E, conjSub g K = L := by
  by_cases htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : E, conjSub g K = L
  · exact Or.inr htrans
  left
  push Not at htrans
  obtain ⟨K₀, hK₀, M₀, hM₀, hnc⟩ := htrans
  have hc0 : Commutes K₀ M₀ :=
    h4 (by norm_num) (by norm_num) E hlt Φ hΦ hO hA K₀ hK₀ M₀ hM₀ (fun ⟨g, hg⟩ => hnc g hg)
  have hne0 : K₀ ≠ M₀ := fun h => hnc 1 (by rw [conjSub_one, h])
  have hadj0 : dAdj Φ K₀ M₀ := dAdj_of_commutes hM₀ hne0 hc0
  have hjoin : ∀ M ∈ Φ,
      Relation.ReflTransGen (fun A B : Subgroup E => B ∈ Φ ∧ dAdj Φ A B) K₀ M ∧
        Relation.ReflTransGen (fun A B : Subgroup E => B ∈ Φ ∧ dAdj Φ A B) M K₀ := by
    intro M hM
    by_cases hMc : ∃ g : E, conjSub g K₀ = M
    · have hnotM : ¬ ∃ g : E, conjSub g M = M₀ := by
        rintro ⟨g, hg⟩
        obtain ⟨y, rfl⟩ := hMc
        exact hnc (g * y) (by rw [conjSub_mul]; exact hg)
      have hc : Commutes M M₀ :=
        h4 (by norm_num) (by norm_num) E hlt Φ hΦ hO hA M hM M₀ hM₀ hnotM
      have hne : M ≠ M₀ := fun h => hnotM ⟨1, by rw [conjSub_one, h]⟩
      have hadj : dAdj Φ M M₀ := dAdj_of_commutes hM₀ hne hc
      exact ⟨(Relation.ReflTransGen.single ⟨hM₀, hadj0⟩).tail ⟨hM, dAdj_symm hadj⟩,
        (Relation.ReflTransGen.single ⟨hM₀, hadj⟩).tail ⟨hK₀, dAdj_symm hadj0⟩⟩
    · push Not at hMc
      have hc : Commutes K₀ M :=
        h4 (by norm_num) (by norm_num) E hlt Φ hΦ hO hA K₀ hK₀ M hM (fun ⟨g, hg⟩ => hMc g hg)
      have hne : K₀ ≠ M := fun h => hMc 1 (by rw [conjSub_one, h])
      have hadj : dAdj Φ K₀ M := dAdj_of_commutes hM hne hc
      exact ⟨Relation.ReflTransGen.single ⟨hM, hadj⟩,
        Relation.ReflTransGen.single ⟨hK₀, dAdj_symm hadj⟩⟩
  intro K hK L hL
  exact (hjoin K hK).2.trans (hjoin L hL).1

end Dich

end CFSG.ClassicalInvolution.Asc77.C25J
