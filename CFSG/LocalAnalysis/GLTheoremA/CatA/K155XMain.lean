module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def L154NonInnDiag : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (X K J : Subgroup Γ) (x y : Γ),
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X K → IsChevSimple 2 (PSimple p K) → x ∈ X → x ^ p = 1 → y ^ p = 1 →
    x * y = y * x → y ∉ Subgroup.zpowers x →
    x ∈ Subgroup.normalizer (K : Set Γ) → y ∈ Subgroup.normalizer (K : Set Γ) → ¬ CentMod p K x →
    InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    y ∈ Subgroup.normalizer (J : Set Γ) → NonInnDiag p y J

@[expose] def L154NotTD4 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (X K J : Subgroup Γ) (x y : Γ),
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X K → IsChevSimple 2 (PSimple p K) → x ∈ X → x ^ p = 1 → y ^ p = 1 →
    x * y = y * x → y ∉ Subgroup.zpowers x →
    x ∈ Subgroup.normalizer (K : Set Γ) → y ∈ Subgroup.normalizer (K : Set Γ) → ¬ CentMod p K x →
    InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    y ∈ Subgroup.normalizer (J : Set Γ) → ¬ (p = 3 ∧ IsTD4 3 J)

theorem i155XAt_of_facts (hN : L154NonInnDiag) (hT : L154NotTD4) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I155X.I155XAt G p := by
  intro hp hp2 X K x y hXk hK hKc hxX hxp hyp hcomm hyx hyN hxN hcm hInn hField J hJ hyJ
  rw [I155X.closureIn_eq_self_of_mem_normalizer hxN] at hJ
  exact ⟨hN p hp hp2 G X K J x y hXk hK hKc hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ,
    hT p hp hp2 G X K J x y hXk hK hKc hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ⟩

section FieldCase


theorem field_case {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} {X J : Subgroup Γ} {y : Γ}
    (hJ : GLAPComponent p X J) (hF : FieldOn p y J) :
    NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J) := by
  refine ⟨MI.field_nonInnDiag_any hJ hF, ?_⟩
  rintro ⟨rfl, hT⟩
  exact MI.td4_not_field_holds hT hF

end FieldCase

end CFSG.LocalAnalysis.GLTheoremA.K155X
