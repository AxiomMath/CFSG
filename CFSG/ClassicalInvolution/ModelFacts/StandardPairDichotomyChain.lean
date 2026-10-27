module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyClassical
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

@[expose] def StandardPairChainSign (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₃ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ c₃ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ → c₃ ∈ R₃ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → orderOf c₃ = 2 →
      c₁ * c₂ = c₂ * c₁ → c₃ * c₂ = c₂ * c₃ → c₁ * c₃ = c₃ * c₁ →
      Commutes R₁ R₃ → R₁ ≠ R₂ → R₃ ≠ R₂ → ¬ Commutes R₁ R₂ → ¬ Commutes R₃ R₂ →
      ((∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∧
          ∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R₃) ∨
        ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂) ∧
          ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₂ R₃)

section Tags

variable {p : ℕ} [Fact p.Prime]

theorem standardPairChainSign_psl {n e : ℕ} (hadm : StatedLieAdmissible .PSL n p e) :
    StandardPairChainSign p .PSL n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ _ _ hne₁₂ hne₃₂ hnc₁₂
    hnc₃₂
  have hT := standardPairDichotomyTypes_psl hadm hp2 hq
  rcases hT R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h₁₂ with h | h | ⟨-, hl₁⟩ | ⟨hF, -⟩
  · exact absurd h hne₁₂
  · exact absurd h hnc₁₂
  · rcases hT R₂ h₂ R₃ h₃ c₂ c₃ hc₂ hc₃ ho₂ ho₃ h₃₂.symm with h' | h' | ⟨-, hl₃⟩ | ⟨hF, -⟩
    · exact absurd h'.symm hne₃₂
    · exact absurd h'.symm hnc₃₂
    · exact Or.inl ⟨hl₁, hl₃⟩
    · exact hF.elim
  · exact hF.elim

theorem standardPairChainSign_psu {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e) :
    StandardPairChainSign p .PSU n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ _ _ hne₁₂ hne₃₂ hnc₁₂
    hnc₃₂
  have hT := standardPairDichotomyTypes_psu hadm hp2 hq
  rcases hT R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h₁₂ with h | h | ⟨hF, -⟩ | ⟨-, hu₁⟩
  · exact absurd h hne₁₂
  · exact absurd h hnc₁₂
  · exact hF.elim
  · rcases hT R₂ h₂ R₃ h₃ c₂ c₃ hc₂ hc₃ ho₂ ho₃ h₃₂.symm with h' | h' | ⟨hF, -⟩ | ⟨-, hu₃⟩
    · exact absurd h'.symm hne₃₂
    · exact absurd h'.symm hnc₃₂
    · exact hF.elim
    · exact Or.inr ⟨hu₁, hu₃⟩

theorem standardPairChainSign_psp {n e : ℕ} (hadm : StatedLieAdmissible .PSp n p e) :
    StandardPairChainSign p .PSp n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ _ _ _ hne₁₂ _ hnc₁₂ _
  rcases standardPairDichotomyTypes_psp hadm hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h₁₂ with
    h | h | ⟨hF, -⟩ | ⟨hF, -⟩
  · exact absurd h hne₁₂
  · exact absurd h hnc₁₂
  · exact hF.elim
  · exact hF.elim

theorem standardPairChainSign_pOmegaPlus {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) : StandardPairChainSign p .POmegaPlus n e := by
  have hn : 4 ≤ n := hadm.2.2
  unfold StandardPairChainSign
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := e) (by omega : 3 ≤ n)]
  intro hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂
  exact (spinCtx_pOmegaPlus hn hp2 hq).sign h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃
    hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

theorem standardPairChainSign_pOmegaOdd {n e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    StandardPairChainSign p .POmegaOdd n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂
  exact (spinCtx_pOmegaOdd hadm.2.2.1 hp2 hq).sign h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃
    hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

theorem standardPairChainSign_pOmegaMinus {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    StandardPairChainSign p .POmegaMinus n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂
  exact (spinCtx_pOmegaMinus hadm hp2 hq).sign h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃
    hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

theorem standardPairChainSign_of_classical {t : StatedLieTag} {n e : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p e) : StandardPairChainSign p t n e := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [standardPairChainSign_psl hadm, standardPairChainSign_psu hadm,
    standardPairChainSign_psp hadm, standardPairChainSign_pOmegaOdd hadm,
    standardPairChainSign_pOmegaPlus hadm, standardPairChainSign_pOmegaMinus hadm]

end Tags

section Map

variable {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}

theorem StandardPairChainSign.map_of_commute (h : StandardPairChainSign p t n e)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) {X : Type} [Group X] (ψ : (Generic.modelUniv t n p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {R₁ R₂ R₃ : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    (h₃ : R₃ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c₁ c₂ c₃ : (Generic.modelUniv t n p e Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hc₃ : c₃ ∈ R₃) (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (ho₃ : orderOf c₃ = 2)
    (h₁₂ : c₁ * c₂ = c₂ * c₁) (h₃₂ : c₃ * c₂ = c₂ * c₃) (h₁₃ : c₁ * c₃ = c₃ * c₁)
    (hR₁₃ : Commutes (R₁.map ψ) (R₃.map ψ)) (hne₁₂ : R₁.map ψ ≠ R₂.map ψ)
    (hne₃₂ : R₃.map ψ ≠ R₂.map ψ) (hnc₁₂ : ¬ Commutes (R₁.map ψ) (R₂.map ψ))
    (hnc₃₂ : ¬ Commutes (R₃.map ψ) (R₂.map ψ)) :
    ((∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map ψ) (R₂.map ψ)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₂.map ψ) (R₃.map ψ)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map ψ) (R₂.map ψ)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₂.map ψ) (R₃.map ψ)) := by
  have hf : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hperf : ⁅R₁, R₁⁆ = R₁ :=
    le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl)
      (RouteD.Gaps.fundPerfect_modelUniv hp2 hfund hadm (by omega) R₁
        (longestFundamental_subset t _ h₁))
  have hmap : ∀ {A B : Subgroup (Generic.modelUniv t n p e Fact.out).K}, Commutes A B →
      Commutes (A.map ψ) (B.map ψ) := fun hAB => by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hAB x hx y hy]
  have hR₁₃' : Commutes R₁ R₃ := RouteD.Gaps.commutes_of_map_commutes hker hperf hR₁₃
  rcases h hp2 hq R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃'
      (fun hh => hne₁₂ (by rw [hh])) (fun hh => hne₃₂ (by rw [hh]))
      (fun hh => hnc₁₂ (hmap hh)) (fun hh => hnc₃₂ (hmap hh)) with
    ⟨⟨_, hl₁⟩, ⟨_, hl₃⟩⟩ | ⟨⟨_, hu₁⟩, ⟨_, hu₃⟩⟩
  · exact Or.inl ⟨⟨_, Balance.linearBlockStandardPair_map_of_ker_le_center hl₁ ψ hker⟩,
      ⟨_, Balance.linearBlockStandardPair_map_of_ker_le_center hl₃ ψ hker⟩⟩
  · have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e hf
    exact Or.inr
      ⟨⟨_, Balance.unitaryBlockStandardPair_map_of_ker_le_center hK hq hu₁ ψ hker⟩,
        ⟨_, Balance.unitaryBlockStandardPair_map_of_ker_le_center hK hq hu₃ ψ hker⟩⟩

end Map

section Propagation

variable {p e : ℕ} [Fact p.Prime] {X : Type} [Group X] {U V W : Subgroup X}

theorem linear_of_chain_sign (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hs : ((∃ W', LinearBlockStandardPair (GaloisField p e) W' U V) ∧
        ∃ W', LinearBlockStandardPair (GaloisField p e) W' V W) ∨
      ((∃ W', UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W' U V) ∧
        ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W' V W))
    (hlin : ∃ W', LinearBlockStandardPair (GaloisField p e) W' U V) :
    ∃ W', LinearBlockStandardPair (GaloisField p e) W' V W := by
  rcases hs with ⟨-, h⟩ | ⟨hu, -⟩
  · exact h
  · exact (false_of_linear_of_unitary hp2 hq hlin hu).elim

theorem unitary_of_chain_sign (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hs : ((∃ W', LinearBlockStandardPair (GaloisField p e) W' U V) ∧
        ∃ W', LinearBlockStandardPair (GaloisField p e) W' V W) ∨
      ((∃ W', UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W' U V) ∧
        ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W' V W))
    (huni : ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W' U V) :
    ∃ W', UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W' V W := by
  rcases hs with ⟨hl, -⟩ | ⟨-, h⟩
  · exact (false_of_linear_of_unitary hp2 hq hl huni).elim
  · exact h

end Propagation

end CFSG.ClassicalInvolution.ModelFacts
