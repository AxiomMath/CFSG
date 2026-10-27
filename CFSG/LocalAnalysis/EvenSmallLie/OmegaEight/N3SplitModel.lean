module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage2
open CFSG.EvenSmallLie.OmegaEight.CPrime

@[expose] def splitCGens (ε : Eps) : Array (ℕ × ℕ) :=
  #[(phiK, phiK)] ++ ((List.range 6).map fun i =>
    (kronK (genRows ε i), kronK (genInvRows ε i))).toArray ++
    #[(kronK (reflRows ε (n0 ε)), kronK (reflRows ε (n0 ε)))]

@[expose] def splitTGens (ε : Eps) : Array (ℕ × ℕ) :=
  #[(phiK, phiK)] ++ ((List.range 6).map fun k =>
    (kronK (urRows ε k), kronK (urRows ε k))).toArray ++
    #[(kronK (reflRows ε (n0 ε)), kronK (reflRows ε (n0 ε)))]

@[expose] def splitModel (ε : Eps) : Model := ⟨tbarG, grpOf (splitCGens ε), grpOf (splitTGens ε)⟩

variable {G : Type*} [Group G]

structure SplitExtra (t : G) (TH W : Subgroup G) (a : G) : Prop where
  center : ∀ z ∈ TH, (∀ x ∈ TH, z * x = x * z) → z = 1 ∨ z = a ∨ z = t ∨ z = t * a
  nsc : ∀ A : Subgroup G, A ≤ TH → (∀ x ∈ TH, ∀ y ∈ A, x * y * x⁻¹ ∈ A) →
    (∀ x ∈ A, x * x = 1) → Nat.card A = 64 → t ∉ A →
    Nat.card ↥(TH ⊓ centralizer (A : Set G)) = 128 →
    A ≤ (W ⊓ centralizer ({t} : Set G)) ⊔ zpowers t

@[expose] def zfixSet (S : Subgroup GL12) (s : GL12) : Set Vec12 :=
  {v | (s : Mat12) *ᵥ v = v ∧ ∀ c ∈ S, c * s = s * c → (c : Mat12) *ᵥ v = v}

@[expose] def kerSet (S : Subgroup GL12) (s : GL12) : Set GL12 :=
  {c | c ∈ S ∧ c * s = s * c ∧ ∀ v, (s : Mat12) *ᵥ v = v → (c : Mat12) *ᵥ v = v}

@[expose] def burnSet (S : Subgroup GL12) (s : GL12) : Set (GL12 × Vec12) :=
  {p | p.1 ∈ S ∧ p.1 * s = s * p.1 ∧ (s : Mat12) *ᵥ p.2 = p.2 ∧ (p.1 : Mat12) *ᵥ p.2 = p.2}

@[expose] def IsCand (S : Subgroup GL12) (s : GL12) : Prop :=
  s * s = 1 ∧ s ≠ 1 ∧ Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7 ∧
    2 ^ 14 ≤ Nat.card ↥(S ⊓ centralizer ({s} : Set GL12)) * Nat.card (fixM (s : Mat12)) ∧
    Nat.card (zfixSet S s) ≤ 2

end CFSG.EvenSmallLie.OmegaEight.N3Split
