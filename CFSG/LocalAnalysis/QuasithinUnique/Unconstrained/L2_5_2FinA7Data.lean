module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinA7DataInputs
public import Certificates.Certificate4152

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A7

open Equiv

structure Facts : Prop where
  evP : ∀ σ ∈ P0l, Perm.sign σ = 1
  evV : ∀ σ ∈ V0l, Perm.sign σ = 1
  evK : ∀ σ ∈ K1l, Perm.sign σ = 1
  evT : ∀ σ ∈ T0l, Perm.sign σ = 1
  evGens : Perm.sign aP = 1 ∧ Perm.sign bP = 1 ∧ Perm.sign c1P = 1 ∧ Perm.sign c2P = 1
  oneP : (1 : Perm (Fin 7)) ∈ P0l
  mulP : ∀ x ∈ P0l, ∀ y ∈ P0l, x * y ∈ P0l
  invP : ∀ x ∈ P0l, x⁻¹ ∈ P0l
  oneV : (1 : Perm (Fin 7)) ∈ V0l
  mulV : ∀ x ∈ V0l, ∀ y ∈ V0l, x * y ∈ V0l
  invV : ∀ x ∈ V0l, x⁻¹ ∈ V0l
  oneK : (1 : Perm (Fin 7)) ∈ K1l
  mulK : ∀ x ∈ K1l, ∀ y ∈ K1l, x * y ∈ K1l
  invK : ∀ x ∈ K1l, x⁻¹ ∈ K1l
  oneT : (1 : Perm (Fin 7)) ∈ T0l
  mulT : ∀ x ∈ T0l, ∀ y ∈ T0l, x * y ∈ T0l
  invT : ∀ x ∈ T0l, x⁻¹ ∈ T0l
  VP : ∀ σ ∈ V0l, σ ∈ P0l
  PK : ∀ σ ∈ P0l, σ ∈ K1l
  cardP : P0l.toFinset.card = 8
  cardV : V0l.toFinset.card = 4
  cardK : K1l.toFinset.card = 24
  cardT : T0l.toFinset.card = 3
  Vnorm : ∀ k ∈ K1l, ∀ v ∈ V0l, k * v * k⁻¹ ∈ V0l
  Vcent : ∀ k ∈ K1l, (∀ v ∈ V0l, k * v = v * k) → k ∈ V0l
  notnormP : ∃ k ∈ K1l, ∃ p ∈ P0l, k * p * k⁻¹ ∉ P0l
  tau : ∀ τ : Perm (Fin 7), τ ^ 2 = 1 → (Finset.univ.filter fun i => τ i = i).card = 1 → ∃ k ∈ K1l, k * τ ≠ τ * k
  T0char : ∀ x : Perm (Fin 7), Perm.sign x = 1 → x ^ 3 = 1 → (∀ v ∈ V0l, x * v = v * x) → x ∈ T0l
  klein : ∀ u₁ ∈ P0l, ∀ u₂ ∈ P0l, u₁ ≠ 1 → u₂ ≠ 1 → u₁ ≠ u₂ → u₁ * u₂ = u₂ * u₁ → u₁ * u₁ = 1 → u₂ * u₂ = 1 → (∃ x : Perm (Fin 7), Perm.sign x = 1 ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧ x * u₁ = u₁ * x ∧ x * u₂ = u₂ * x) → u₁ ∈ V0l ∧ u₂ ∈ V0l
  Tconj : ∀ y ∈ T0l, y ≠ 1 → ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = y
  c1conj : ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = c1P
  three : ∀ y : Perm (Fin 7), Perm.sign y = 1 → y ^ 3 = 1 → y ≠ 1 → (∀ v ∈ V0l, y * v * y⁻¹ ∈ V0l) → y ∉ T0l → (∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = y) → y ∈ K1l
  aNe : aP ≠ 1
  bNe : bP ≠ 1
  abNe : aP ≠ bP
  abComm : aP * bP = bP * aP
  aaEq : aP * aP = 1
  bbEq : bP * bP = 1
  c2Ne : c2P ≠ 1
  c2Cube : c2P ^ 3 = 1
  c1Ne : c1P ≠ 1
  c1Cube : c1P ^ 3 = 1
  c2aComm : c2P * aP = aP * c2P
  c2bComm : c2P * bP = bP * c2P
  c1K : c1P ∈ K1l
  c1T : c1P ∉ T0l
  c2T : c2P ∈ T0l
  aV : aP ∈ V0l
  bV : bP ∈ V0l

set_option synthInstance.maxSize 8192 in
theorem a7_facts_h :
    (∀ σ ∈ P0l, Perm.sign σ = 1) ∧
      (∀ σ ∈ V0l, Perm.sign σ = 1) ∧
      (∀ σ ∈ K1l, Perm.sign σ = 1) ∧
      (∀ σ ∈ T0l, Perm.sign σ = 1) ∧
      (Perm.sign aP = 1 ∧ Perm.sign bP = 1 ∧ Perm.sign c1P = 1 ∧ Perm.sign c2P = 1) ∧
      ((1 : Perm (Fin 7)) ∈ P0l) ∧
      (∀ x ∈ P0l, ∀ y ∈ P0l, x * y ∈ P0l) ∧
      (∀ x ∈ P0l, x⁻¹ ∈ P0l) ∧
      ((1 : Perm (Fin 7)) ∈ V0l) ∧
      (∀ x ∈ V0l, ∀ y ∈ V0l, x * y ∈ V0l) ∧
      (∀ x ∈ V0l, x⁻¹ ∈ V0l) ∧
      ((1 : Perm (Fin 7)) ∈ K1l) ∧
      (∀ x ∈ K1l, ∀ y ∈ K1l, x * y ∈ K1l) ∧
      (∀ x ∈ K1l, x⁻¹ ∈ K1l) ∧
      ((1 : Perm (Fin 7)) ∈ T0l) ∧
      (∀ x ∈ T0l, ∀ y ∈ T0l, x * y ∈ T0l) ∧
      (∀ x ∈ T0l, x⁻¹ ∈ T0l) ∧
      (∀ σ ∈ V0l, σ ∈ P0l) ∧
      (∀ σ ∈ P0l, σ ∈ K1l) ∧
      (P0l.toFinset.card = 8) ∧
      (V0l.toFinset.card = 4) ∧
      (K1l.toFinset.card = 24) ∧
      (T0l.toFinset.card = 3) ∧
      (∀ k ∈ K1l, ∀ v ∈ V0l, k * v * k⁻¹ ∈ V0l) ∧
      (∀ k ∈ K1l, (∀ v ∈ V0l, k * v = v * k) → k ∈ V0l) ∧
      (∃ k ∈ K1l, ∃ p ∈ P0l, k * p * k⁻¹ ∉ P0l) ∧
      (∀ τ : Perm (Fin 7), τ ^ 2 = 1 → (Finset.univ.filter fun i => τ i = i).card = 1 → ∃ k ∈ K1l, k * τ ≠ τ * k) ∧
      (∀ x : Perm (Fin 7), Perm.sign x = 1 → x ^ 3 = 1 → (∀ v ∈ V0l, x * v = v * x) → x ∈ T0l) ∧
      (∀ u₁ ∈ P0l, ∀ u₂ ∈ P0l, u₁ ≠ 1 → u₂ ≠ 1 → u₁ ≠ u₂ → u₁ * u₂ = u₂ * u₁ → u₁ * u₁ = 1 → u₂ * u₂ = 1 → (∃ x : Perm (Fin 7), Perm.sign x = 1 ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧ x * u₁ = u₁ * x ∧ x * u₂ = u₂ * x) → u₁ ∈ V0l ∧ u₂ ∈ V0l) ∧
      (∀ y ∈ T0l, y ≠ 1 → ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = y) ∧
      (∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = c1P) ∧
      (∀ y : Perm (Fin 7), Perm.sign y = 1 → y ^ 3 = 1 → y ≠ 1 → (∀ v ∈ V0l, y * v * y⁻¹ ∈ V0l) → y ∉ T0l → (∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * c2P * g⁻¹ = y) → y ∈ K1l) ∧
      (aP ≠ 1) ∧
      (bP ≠ 1) ∧
      (aP ≠ bP) ∧
      (aP * bP = bP * aP) ∧
      (aP * aP = 1) ∧
      (bP * bP = 1) ∧
      (c2P ≠ 1) ∧
      (c2P ^ 3 = 1) ∧
      (c1P ≠ 1) ∧
      (c1P ^ 3 = 1) ∧
      (c2P * aP = aP * c2P) ∧
      (c2P * bP = bP * c2P) ∧
      (c1P ∈ K1l) ∧
      (c1P ∉ T0l) ∧
      (c2P ∈ T0l) ∧
      (aP ∈ V0l) ∧
      (bP ∈ V0l) :=
  Certificates.certificate4152

set_option synthInstance.maxSize 8192 in
theorem a7_facts : Facts := by
  have h := a7_facts_h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end A7

end CFSG.QuasithinUnique.Unc25G2
