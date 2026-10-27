module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAmalgam

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e7PilotFieldNormalizeUniqueNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Words

@[expose] def applyWordE7 : List (Fin (Tag.rank .E7)) → (Fin (Tag.rank .E7) → ℤ) →
    Fin (Tag.rank .E7) → ℤ
  | [], v => v
  | i :: ω, v => reflect .E7 i (applyWordE7 ω v)

theorem wordProd_smul_eq_applyWordE7 (ω : List (Fin (Tag.rank .E7))) (v : Fin (Tag.rank .E7) → ℤ) :
    (coxeterSystem .E7).wordProd ω • v = applyWordE7 ω v := by
  induction ω with
  | nil => simp [applyWordE7]
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, applyWordE7]

@[expose] def d6WordTable : List ((Fin (Tag.rank .E7) → ℤ) × List (Fin (Tag.rank .E7))) :=
  [(![0, 0, 0, 1, 0, 0, 0], []),
    (![0, 0, 0, -1, 0, 0, 0], [3]),
    (![0, 0, 0, 1, 1, 0, 0], [4]),
    (![0, 0, 1, 1, 0, 0, 0], [2]),
    (![0, 1, 0, 1, 0, 0, 0], [1]),
    (![0, -1, 0, -1, 0, 0, 0], [1, 3]),
    (![0, 0, -1, -1, 0, 0, 0], [2, 3]),
    (![0, 0, 0, -1, -1, 0, 0], [4, 3]),
    (![0, 0, 0, 0, 1, 0, 0], [3, 4]),
    (![0, 0, 0, 1, 1, 1, 0], [5, 4]),
    (![0, 0, 1, 0, 0, 0, 0], [3, 2]),
    (![0, 0, 1, 1, 1, 0, 0], [4, 2]),
    (![0, 1, 0, 0, 0, 0, 0], [3, 1]),
    (![0, 1, 0, 1, 1, 0, 0], [4, 1]),
    (![0, 1, 1, 1, 0, 0, 0], [2, 1]),
    (![0, -1, -1, -1, 0, 0, 0], [2, 1, 3]),
    (![0, -1, 0, -1, -1, 0, 0], [4, 1, 3]),
    (![0, -1, 0, 0, 0, 0, 0], [1, 3, 1]),
    (![0, 0, -1, -1, -1, 0, 0], [4, 2, 3]),
    (![0, 0, -1, 0, 0, 0, 0], [2, 3, 2]),
    (![0, 0, 0, -1, -1, -1, 0], [5, 4, 3]),
    (![0, 0, 0, 0, -1, 0, 0], [3, 4, 3]),
    (![0, 0, 0, 0, 1, 1, 0], [5, 3, 4]),
    (![0, 0, 0, 1, 1, 1, 1], [6, 5, 4]),
    (![0, 0, 1, 1, 1, 1, 0], [5, 4, 2]),
    (![0, 1, 0, 1, 1, 1, 0], [5, 4, 1]),
    (![0, 1, 1, 1, 1, 0, 0], [4, 2, 1]),
    (![0, -1, -1, -1, -1, 0, 0], [4, 2, 1, 3]),
    (![0, -1, 0, -1, -1, -1, 0], [5, 4, 1, 3]),
    (![0, 0, -1, -1, -1, -1, 0], [5, 4, 2, 3]),
    (![0, 0, 0, -1, -1, -1, -1], [6, 5, 4, 3]),
    (![0, 0, 0, 0, -1, -1, 0], [5, 3, 4, 3]),
    (![0, 0, 0, 0, 0, 1, 0], [4, 5, 3, 4]),
    (![0, 0, 0, 0, 1, 1, 1], [6, 5, 3, 4]),
    (![0, 0, 1, 1, 1, 1, 1], [6, 5, 4, 2]),
    (![0, 1, 0, 1, 1, 1, 1], [6, 5, 4, 1]),
    (![0, 1, 1, 1, 1, 1, 0], [5, 4, 2, 1]),
    (![0, 1, 1, 2, 1, 0, 0], [3, 4, 2, 1]),
    (![0, -1, -1, -2, -1, 0, 0], [3, 4, 2, 1, 3]),
    (![0, -1, -1, -1, -1, -1, 0], [5, 4, 2, 1, 3]),
    (![0, -1, 0, -1, -1, -1, -1], [6, 5, 4, 1, 3]),
    (![0, 0, -1, -1, -1, -1, -1], [6, 5, 4, 2, 3]),
    (![0, 0, 0, 0, -1, -1, -1], [6, 5, 3, 4, 3]),
    (![0, 0, 0, 0, 0, -1, 0], [4, 5, 3, 4, 3]),
    (![0, 0, 0, 0, 0, 1, 1], [6, 4, 5, 3, 4]),
    (![0, 1, 1, 1, 1, 1, 1], [6, 5, 4, 2, 1]),
    (![0, 1, 1, 2, 1, 1, 0], [5, 3, 4, 2, 1]),
    (![0, -1, -1, -2, -1, -1, 0], [5, 3, 4, 2, 1, 3]),
    (![0, -1, -1, -1, -1, -1, -1], [6, 5, 4, 2, 1, 3]),
    (![0, 0, 0, 0, 0, -1, -1], [6, 4, 5, 3, 4, 3]),
    (![0, 0, 0, 0, 0, 0, 1], [5, 6, 4, 5, 3, 4]),
    (![0, 1, 1, 2, 1, 1, 1], [6, 5, 3, 4, 2, 1]),
    (![0, 1, 1, 2, 2, 1, 0], [4, 5, 3, 4, 2, 1]),
    (![0, -1, -1, -2, -2, -1, 0], [4, 5, 3, 4, 2, 1, 3]),
    (![0, -1, -1, -2, -1, -1, -1], [6, 5, 3, 4, 2, 1, 3]),
    (![0, 0, 0, 0, 0, 0, -1], [5, 6, 4, 5, 3, 4, 3]),
    (![0, 1, 1, 2, 2, 1, 1], [6, 4, 5, 3, 4, 2, 1]),
    (![0, -1, -1, -2, -2, -1, -1], [6, 4, 5, 3, 4, 2, 1, 3]),
    (![0, 1, 1, 2, 2, 2, 1], [5, 6, 4, 5, 3, 4, 2, 1]),
    (![0, -1, -1, -2, -2, -2, -1], [5, 6, 4, 5, 3, 4, 2, 1, 3])]

set_option maxRecDepth 100000 in
theorem d6WordTable_check :
    (∀ p ∈ d6WordTable, (∀ i ∈ p.2, i ∈ E7Neighbour.high.nodes) ∧
      applyWordE7 p.2 (Pi.single 3 1) = p.1) ∧
    ∀ k < Tag.E7.rootCertificate.roots.length,
      iform (highRoot .E7) (Tag.E7.rootCertificate.root k) = 0 →
        ∃ p ∈ d6WordTable, p.1 = Tag.E7.rootCertificate.root k := by
  decide +kernel

theorem exists_word_of_mem_orthRoots_high
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ orthRoots E7Neighbour.high.root) :
    ∃ ω : List (Fin (Tag.rank .E7)), (∀ i ∈ ω, i ∈ E7Neighbour.high.nodes) ∧
      (coxeterSystem .E7).wordProd ω • (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) = γ := by
  obtain ⟨hall, hcomp⟩ := d6WordTable_check
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E7.rootCertificate_check hγ.1
  obtain ⟨p, hp, hpk⟩ := hcomp k hk hγ.2
  refine ⟨p.2, (hall p hp).1, ?_⟩
  rw [wordProd_smul_eq_applyWordE7, (hall p hp).2, hpk]

theorem wordProd_smul_highRoot_of_mem_nodes {ω : List (Fin (Tag.rank .E7))}
    (hω : ∀ i ∈ ω, i ∈ E7Neighbour.high.nodes) :
    (coxeterSystem .E7).wordProd ω • highRoot .E7 = highRoot .E7 := by
  have hfix : ∀ i ∈ E7Neighbour.high.nodes,
      reflect .E7 i (highRoot .E7) = highRoot .E7 := by
    decide +kernel
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul,
      ih fun j hj => hω j (List.mem_cons_of_mem i hj), simple_smul]
    exact hfix i (hω i List.mem_cons_self)

theorem exists_weyl_smul_orthPair
    {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (hαβ : iform α β = 0) :
    ∃ w : WeylGroup .E7, w • highRoot .E7 = α ∧
      w • (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) = β := by
  obtain ⟨w₁, hw₁⟩ := EPilot.exists_smul_eq_highRoot (Or.inr (Or.inl rfl)) hα
  have hβ₁ : w₁ • β ∈ orthRoots E7Neighbour.high.root := by
    refine ⟨IsRoot.smul hβ w₁, ?_⟩
    change iform (highRoot .E7) (w₁ • β) = 0
    rw [← hw₁, iform_smul, hαβ]
  obtain ⟨ω, hω, hωβ⟩ := exists_word_of_mem_orthRoots_high hβ₁
  refine ⟨w₁⁻¹ * (coxeterSystem .E7).wordProd ω, ?_, ?_⟩
  · rw [mul_smul, wordProd_smul_highRoot_of_mem_nodes hω, ← hw₁, inv_smul_smul]
  · rw [mul_smul, hωβ, inv_smul_smul]

end Words

end CFSG.SeitzReduction.E7Pilot
