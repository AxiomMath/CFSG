module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Wreathed.CentralSL2

@[expose] noncomputable def scalarRep {K : Type*} [Group K] (χ : K →* ℂ) :
    Representation ℂ K ℂ where
  toFun g := χ g • (1 : Module.End ℂ ℂ)
  map_one' := by simp
  map_mul' x y := by
    ext
    simp [mul_comm]

theorem scalarRep_character {K : Type*} [Group K] (χ : K →* ℂ) :
    (scalarRep χ).character = χ := by
  funext g
  change LinearMap.trace ℂ ℂ (χ g • (1 : Module.End ℂ ℂ)) = χ g
  simp

theorem scalarRep_isIrreducible {K : Type*} [Group K] (χ : K →* ℂ) :
    (scalarRep χ).IsIrreducible := by
  change IsSimpleOrder (Subrepresentation (scalarRep χ))
  have hnontrivial : (⊥ : Subrepresentation (scalarRep χ)) ≠ ⊤ := by
    intro hequal
    have hmem : (1 : ℂ) ∈ (⊥ : Subrepresentation (scalarRep χ)) := by
      rw [hequal]
      trivial
    exact one_ne_zero hmem
  let : Nontrivial (Subrepresentation (scalarRep χ)) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro S
  obtain hbot | htop := eq_bot_or_eq_top S.toSubmodule
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

theorem monoidHom_mem_blocksIrr {K : Type*} [Group K] (χ : K →* ℂ) :
    (χ : K → ℂ) ∈ BlocksIrr K :=
  ⟨ℂ, inferInstance, inferInstance, inferInstance, scalarRep χ, scalarRep_isIrreducible χ,
    scalarRep_character χ⟩

theorem blocksIrr_degree_one_mul {K : Type*} [Group K] {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K)
    (h1 : θ 1 = 1) (x y : K) : θ (x * y) = θ x * θ y := by
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
  have hdim : Module.finrank ℂ V = 1 := by
    rw [Representation.char_one] at h1
    exact_mod_cast h1
  have hscalar : ∀ g, ρ g = ρ.character g • (1 : Module.End ℂ V) := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
    have htrace : ρ.character g = c := by
      change LinearMap.trace ℂ V (ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]
      simp
    rw [htrace]
    exact hc
  change LinearMap.trace ℂ V (ρ (x * y)) = ρ.character x * ρ.character y
  rw [map_mul, hscalar x, hscalar y, smul_mul_smul, mul_one, map_smul, LinearMap.trace_one, hdim]
  simp

@[expose] noncomputable def degreeOneHom {K : Type*} [Group K] {θ : K → ℂ}
    (hθ : θ ∈ BlocksIrr K) (h1 : θ 1 = 1) : K →* ℂ where
  toFun := θ
  map_one' := h1
  map_mul' := blocksIrr_degree_one_mul hθ h1

theorem degreeOneHom_apply {K : Type*} [Group K] {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K)
    (h1 : θ 1 = 1) (g : K) : degreeOneHom hθ h1 g = θ g := rfl

theorem blocksIrr_degree_one_commutator {K : Type*} [Group K] {θ : K → ℂ}
    (hθ : θ ∈ BlocksIrr K) (h1 : θ 1 = 1) {g : K} (hg : g ∈ commutator K) : θ g = 1 := by
  let χ := degreeOneHom hθ h1
  have hunit : ∀ x, χ x * χ x⁻¹ = 1 := fun x => by rw [← map_mul, mul_inv_cancel, map_one]
  have hle : commutator K ≤ χ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    calc χ x * χ y * χ x⁻¹ * χ y⁻¹ = (χ x * χ x⁻¹) * (χ y * χ y⁻¹) := by ring
      _ = 1 := by rw [hunit, hunit, one_mul]
  exact hle hg

end CFSG.Wreathed.CentralSL2
