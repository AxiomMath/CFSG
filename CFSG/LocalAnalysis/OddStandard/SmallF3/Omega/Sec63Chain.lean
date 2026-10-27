module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L65
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63_step [Finite G] (hsh : Asc82Shapes) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {A B : Subgroup G} (h : WalterArrow A B) (hAF : InFStar A) :
    InFStar B ∧ (IsL29 A → IsL281 B ∨ IsOmega5 B ∨ IsOmega6Plus B ∨ IsOmega6Minus B) ∧
      (IsOmega5 A → IsOmega6Plus B ∨ IsOmega6Minus B) ∧
      (IsL281 A ∨ IsOmega6Plus A ∨ IsOmega6Minus A → False) := by
  have hBF : InFStar B := inFStar_of_walterArrow hS.a2 h hAF
  obtain ⟨hdvd, hne⟩ := ctrQ_dvd_of_walterArrow h
  obtain ⟨x, y, -, hy, -, hAc, hBc, -, -⟩ := h
  have hAq := hAc.isQuasisimple
  have hBq := hBc.isQuasisimple
  have hBsh := sec65_shape hsh hS ⟨y, hy, hBc⟩ hBF
  refine ⟨hBF, ?_, ?_, ?_⟩
  · intro hA
    rw [ctrQ_of_l29 hAq hA] at hdvd hne
    rcases hBsh with hB | hB | hB | hB | hB | hB
    · rw [ctrQ_of_l29 hBq hB] at hne
      exact absurd rfl hne
    · exact Or.inl hB
    · rcases hB with hB | hB
      · rw [ctrQ_of_l33 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_u33 hBq hB] at hdvd
        omega
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr (Or.inl hB))
    · exact Or.inr (Or.inr (Or.inr hB))
  · intro hA
    rw [ctrQ_of_psp4 hAq hA] at hdvd hne
    rcases hBsh with hB | hB | hB | hB | hB | hB
    · rw [ctrQ_of_l29 hBq hB] at hdvd
      omega
    · rw [ctrQ_of_l281 hBq hB] at hdvd
      omega
    · rcases hB with hB | hB
      · rw [ctrQ_of_l33 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_u33 hBq hB] at hdvd
        omega
    · rw [ctrQ_of_psp4 hBq hB] at hne
      exact absurd rfl hne
    · exact Or.inl hB
    · exact Or.inr hB
  · intro hA
    rcases hA with hA | hA | hA
    · rw [ctrQ_of_l281 hAq hA] at hdvd hne
      rcases hBsh with hB | hB | hB | hB | hB | hB
      · rw [ctrQ_of_l29 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_l281 hBq hB] at hne
        exact absurd rfl hne
      · rcases hB with hB | hB
        · rw [ctrQ_of_l33 hBq hB] at hdvd
          omega
        · rw [ctrQ_of_u33 hBq hB] at hdvd
          omega
      · rw [ctrQ_of_psp4 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_l43 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_u43 hBq hB] at hdvd
        omega
    · rw [ctrQ_of_l43 hAq hA] at hdvd hne
      rcases hBsh with hB | hB | hB | hB | hB | hB
      · rw [ctrQ_of_l29 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_l281 hBq hB] at hdvd
        omega
      · rcases hB with hB | hB
        · rw [ctrQ_of_l33 hBq hB] at hdvd
          omega
        · rw [ctrQ_of_u33 hBq hB] at hdvd
          omega
      · rw [ctrQ_of_psp4 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_l43 hBq hB] at hne
        exact absurd rfl hne
      · rw [ctrQ_of_u43 hBq hB] at hdvd
        omega
    · rw [ctrQ_of_u43 hAq hA] at hdvd hne
      rcases hBsh with hB | hB | hB | hB | hB | hB
      · rw [ctrQ_of_l29 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_l281 hBq hB] at hdvd
        omega
      · rcases hB with hB | hB
        · rw [ctrQ_of_l33 hBq hB] at hdvd
          omega
        · rw [ctrQ_of_u33 hBq hB] at hdvd
          omega
      · rw [ctrQ_of_psp4 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_l43 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_u43 hBq hB] at hne
        exact absurd rfl hne

theorem sec63_plain_chain [Finite G] (hsh : Asc82Shapes) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {V Y : Subgroup G} (hVF : InFStar V) (hV : IsL29 V ∨ IsL281 V)
    (hch : PlainChain V Y) :
    V = Y ∨
      (IsL29 V ∧ WalterArrow V Y ∧
        (IsL281 Y ∨ IsOmega5 Y ∨ IsOmega6Plus Y ∨ IsOmega6Minus Y)) ∨
      (IsL29 V ∧ ∃ Z : Subgroup G, WalterArrow V Z ∧ IsOmega5 Z ∧ WalterArrow Z Y ∧
        (IsOmega6Plus Y ∨ IsOmega6Minus Y)) := by
  have hch' : Relation.ReflTransGen WalterArrow V Y := hch
  rcases hch'.cases_head with hVY | ⟨Z₁, h1, hZ₁Y⟩
  · exact Or.inl hVY
  · right
    obtain ⟨hZ₁F, hs1, -, hs3⟩ := sec63_step hsh hS h1 hVF
    have hV29 : IsL29 V := by
      rcases hV with h | h
      · exact h
      · exact (hs3 (Or.inl h)).elim
    have hZ₁sh := hs1 hV29
    rcases hZ₁Y.cases_head with hZ₁eq | ⟨Z₂, h2, hZ₂Y⟩
    · left
      subst hZ₁eq
      exact ⟨hV29, h1, hZ₁sh⟩
    · right
      obtain ⟨hZ₂F, -, hs2', hs3'⟩ := sec63_step hsh hS h2 hZ₁F
      have hZ₁5 : IsOmega5 Z₁ := by
        rcases hZ₁sh with h | h | h | h
        · exact (hs3' (Or.inl h)).elim
        · exact h
        · exact (hs3' (Or.inr (Or.inl h))).elim
        · exact (hs3' (Or.inr (Or.inr h))).elim
      have hZ₂sh := hs2' hZ₁5
      rcases hZ₂Y.cases_head with hZ₂eq | ⟨Z₃, h3, -⟩
      · subst hZ₂eq
        exact ⟨hV29, Z₁, h1, hZ₁5, h2, hZ₂sh⟩
      · exfalso
        obtain ⟨-, -, -, hs3''⟩ := sec63_step hsh hS h3 hZ₂F
        rcases hZ₂sh with h | h
        · exact hs3'' (Or.inr (Or.inl h))
        · exact hs3'' (Or.inr (Or.inr h))

end CFSG.OddStandard.SmallF3.Omega
