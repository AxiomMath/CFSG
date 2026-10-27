module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

@[expose] def LinMarking (p : ℕ) {Ω : Type} [Group Ω] (S B : Subgroup Ω) (n d : ℕ) (F : Type)
    [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)) : Prop :=
  Nat.card F = 2 ^ n ∧ 1 ≤ n ∧ 2 ≤ d ∧ (d = 2 → 2 ≤ n) ∧ (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) ∧
    B ≤ Subgroup.normalizer (S : Set Ω) ∧
    ∀ b ∈ B, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ,
      LargeEvenInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ

@[expose] def UniMarking (p : ℕ) {Ω : Type} [Group Ω] (S B : Subgroup Ω) (n d : ℕ) (F : Type)
    [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) : Prop :=
  Nat.card F = (2 ^ n) ^ 2 ∧ 1 ≤ n ∧ 3 ≤ d ∧ (d = 3 → 2 ≤ n) ∧ p ∣ 2 ^ n + 1 ∧
    B ≤ Subgroup.normalizer (S : Set Ω) ∧
    ∀ b ∈ B, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
        (LargeEvenGUSet (Fin d) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ

@[expose] def LinModelData (p : ℕ) {Ω : Type} [Group Ω] (S B : Subgroup Ω) : Prop :=
  ∃ (n d : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)),
    LinMarking p S B n d F θ

@[expose] def UniModelData (p : ℕ) {Ω : Type} [Group Ω] (S B : Subgroup Ω) : Prop :=
  ∃ (n d : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))),
    UniMarking p S B n d F θ

@[expose] def T173AExtract : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassA) →
      LinModelData p S B ∨ UniModelData p S B

@[expose] def T173ALinBig : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω)
    (n d : ℕ) (F : Type) [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassA) →
      LinMarking p S B n d F θ → 2 ≤ n → ¬ p ∣ d → T173Concl p S B K N

@[expose] def T173ALinTwo : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω)
    (d : ℕ) (F : Type) [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassA) →
      LinMarking p S B 1 d F θ → T173Concl p S B K N

@[expose] def T173AUni : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω)
    (n d : ℕ) (F : Type) [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))),
    Cfg173 p S B N D K x → UniMarking p S B n d F θ → ¬ p ∣ d → T173Concl p S B K N

@[expose] def T173AMNonzeroLin : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω)
    (n d : ℕ) (F : Type) [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassA) →
      LinMarking p S B n d F θ → 2 ≤ n → p ∣ d → T173Concl p S B K N

@[expose] def T173AMNonzeroUni : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω)
    (n d : ℕ) (F : Type) [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassA) →
      UniMarking p S B n d F θ → p ∣ d → T173Concl p S B K N

@[expose] def T173AMNonzero : Prop :=
  T173AMNonzeroLin ∧ T173AMNonzeroUni

theorem i173FactA_of_cases (h0 : T173AExtract) (hLB : T173ALinBig) (hL2 : T173ALinTwo)
    (hU : T173AUni) (hM : T173AMNonzero) : I173FactA := by
  intro p Ω _ _ S B N D K x hcfg hcat
  rcases h0 p Ω S B N D K x hcfg hcat with ⟨n, d, F, _, _, θ, hlin⟩ | ⟨n, d, F, _, _, θ, huni⟩
  · by_cases hn : n = 1
    · subst hn
      exact hL2 p Ω S B N D K x d F θ hcfg hcat hlin
    · have hn2 : 2 ≤ n := by
        have := hlin.2.1
        omega
      by_cases hd : p ∣ d
      · exact hM.1 p Ω S B N D K x n d F θ hcfg hcat hlin hn2 hd
      · exact hLB p Ω S B N D K x n d F θ hcfg hcat hlin hn2 hd
  · by_cases hd : p ∣ d
    · exact hM.2 p Ω S B N D K x n d F θ hcfg hcat huni hd
    · exact hU p Ω S B N D K x n d F θ hcfg huni hd

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
