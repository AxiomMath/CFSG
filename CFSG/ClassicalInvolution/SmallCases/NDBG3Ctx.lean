module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Ctx
public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCNine

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem exists_ctxData_g2 (C : XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i₁ : Fin C.D.card}
    (hi₁ : C.D.tag i₁ = .G2) (h3 : 3 ≤ C.D.card) :
    ∃ i₀ i₂ : Fin C.D.card, i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₀ ≠ i₂ ∧
      (C.D.tag i₀ = .PSL ∧ C.D.rank i₀ = 2) ∧ (C.D.tag i₂ = .PSL ∧ C.D.rank i₂ = 2) ∧
      modOdd z (exactCore z C.K) = (C.psi i₀).range ∧
      oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi i₂).range ∧
      ∀ j, j ≠ i₁ → (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧
        oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range := by
  have hzC := XCtx.hzC z
  have hQ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2) := fun h => by
    rw [hi₁] at h
    exact absurd h.1 (by decide)
  have hrest : ∀ j, j ≠ i₁ → C.D.tag j = .PSL ∧ C.D.rank j = 2 := fun j hj => by
    by_contra h
    exact Cover.false_of_two_nonA1 C hnoF hj h hQ
  obtain ⟨i₀, hi₀, hK₀⟩ := C.exists_A1_of_K
  have h01 : i₀ ≠ i₁ := fun h => hQ (h ▸ hi₀)
  have hz₀ : oddQuotMk z ⟨z, hzC⟩ ∈ (C.psi i₀).range := by
    rw [← hK₀]
    exact oddQuotMk_mem_modOdd (C.involution_mem_exactCore C.K_tq C.K_cl) hzC
  have hothers : ∀ j, j ≠ i₁ → (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧
      oddQuotMk z ⟨z, hzC⟩ ∈ (C.psi j).range := by
    intro j hj
    refine ⟨hrest j hj, ?_⟩
    by_cases hj₀ : j = i₀
    · rw [hj₀]
      exact hz₀
    · obtain ⟨T, -, -, hTz, hTr⟩ := Cover.A1_member_twin C hnoF hQ hi₀ hK₀ (hrest j hj) hj₀
      rw [← hTr]
      exact oddQuotMk_mem_modOdd hTz.mem hzC
  obtain ⟨i₂, h20, h21⟩ := D4.exists_third_index h3 i₀ i₁
  exact ⟨i₀, i₂, h01, Ne.symm h21, Ne.symm h20, hi₀, hrest i₂ h21, hK₀, (hothers i₂ h21).2,
    hothers⟩

theorem localLeviComponent_g2_nine (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hqs : ∀ L ∈ Ω, CFSG.Open.IsQuasisimple L) (h9 : p ^ f = 9)
    (D : LocalLieSystemAt p f (exactFamily Ω z) z) (i : Fin D.card) (hG2 : D.tag i = .G2) :
    LocalLeviComponent p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_quasisimple hcls hqs)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      ∀ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ∀ i : Fin D.card,
        D.tag i = .G2 →
        ∃ D' : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
          (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ∃ i' : Fin D'.card,
          D'.tag i' = .G2 := by
    intro S₁ S₂ h D i hi
    subst h
    exact ⟨D, i, hi⟩
  obtain ⟨D', i', hi'⟩ := key _ _ h D i hG2
  exact ⟨D', i', Or.inr (Or.inr (Or.inr (Or.inr ⟨h9, Or.inl hi'⟩)))⟩

end CFSG.ClassicalInvolution.NDB.NDBG3
