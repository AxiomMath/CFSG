module

public import CFSG.ClassicalInvolution.SmallCases.NDBC8
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB.D4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer

theorem listedTwin_plus {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : t = .POmegaPlus) (hn : n = 4) : Asc77.ListedTwin t n := by
  subst ht hn
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

theorem exists_third_index {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) : ∃ j : Fin n, j ≠ a ∧ j ≠ b := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := fun j _ => by
    by_cases hja : j = a
    · simp [hja]
    · simp [h j hja]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have h2 := Finset.card_le_two (a := a) (b := b)
  omega

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem exists_ctxData (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i₁ : Fin C.D.card}
    (hi₁ : C.D.tag i₁ = .POmegaPlus ∧ C.D.rank i₁ = 4) (h3 : 3 ≤ C.D.card) :
    ∃ i₀ i₂ : Fin C.D.card, i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₀ ≠ i₂ ∧
      (C.D.tag i₀ = .PSL ∧ C.D.rank i₀ = 2) ∧ (C.D.tag i₂ = .PSL ∧ C.D.rank i₂ = 2) ∧
      Asc77.ListedTwin (C.D.tag i₁) (C.D.rank i₁) ∧
      modOdd z (exactCore z C.K) = (C.psi i₀).range ∧
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi i₂).range ∧
      ∀ j, j ≠ i₁ → (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧
        oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi j).range := by
  have hzC := Asc77.XCtx.hzC z
  have hQ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2) := fun h => by
    rw [hi₁.1] at h
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
  obtain ⟨i₂, h20, h21⟩ := exists_third_index h3 i₀ i₁
  exact ⟨i₀, i₂, h01, Ne.symm h21, Ne.symm h20, hi₀, hrest i₂ h21,
    listedTwin_plus hi₁.1 hi₁.2, hK₀, (hothers i₂ h21).2, hothers⟩

end CFSG.ClassicalInvolution.NDB.D4
