module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6

public section

namespace CFSG.Semidihedral.Principal

open TwoRankLowerBound.Helpers
open scoped commutatorElement

namespace RationalOddCharacter

theorem trace_mul_of_finrank_eq_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (h : Module.finrank ℂ W = 1) (f g : Module.End ℂ W) :
    LinearMap.trace ℂ W (f * g) = LinearMap.trace ℂ W f * LinearMap.trace ℂ W g := by
  let b := Module.finBasisOfFinrankEq ℂ W h
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul]
  simp [Matrix.trace_fin_one, Matrix.mul_apply]

theorem character_commutator_of_finrank_eq_one {A W : Type*} [Group A] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (h : Module.finrank ℂ W = 1)
    (σ : Representation ℂ A W) (a b : A) : σ.character ⁅a, b⁆ = 1 := by
  have hmul : ∀ x y : A, σ.character (x * y) = σ.character x * σ.character y := by
    intro x y
    change LinearMap.trace ℂ W (σ (x * y)) = LinearMap.trace ℂ W (σ x) * LinearMap.trace ℂ W (σ y)
    rw [map_mul, trace_mul_of_finrank_eq_one h]
  have hinv : ∀ x : A, σ.character x * σ.character x⁻¹ = 1 := by
    intro x
    rw [← hmul, mul_inv_cancel, Representation.char_one, h, Nat.cast_one]
  rw [commutatorElement_def, hmul, hmul, hmul]
  calc σ.character a * σ.character b * σ.character a⁻¹ * σ.character b⁻¹ =
      (σ.character a * σ.character a⁻¹) * (σ.character b * σ.character b⁻¹) := by ring
    _ = 1 := by rw [hinv, hinv, one_mul]

end RationalOddCharacter

open RationalOddCharacter

theorem rational_odd_character_degree_le_five_linear {A V : Type} [Group A] [Fintype A]
    (hodd : Odd (Nat.card A)) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ A V) (hrat : ∀ a : A, ∃ q : ℚ, ρ.character a = q)
    (hdeg : Module.finrank ℂ V ≤ 5) :
    (∀ θ ∈ BlocksIrr A, BlocksInnerProduct ρ.character θ ≠ 0 → θ 1 = 1) ∧
      (Function.Injective ρ → ∀ a b : A, a * b = b * a) := by
  classical
  have hηV : ρ.character ∈ BlocksVChar A := by
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    exact character_mem_virtualCharacters
      ({ vector := V, representation := ρ } : FiniteComplexRepresentation A)
  obtain ⟨n, hn, -⟩ := blocksVChar_exists_unique_expansion hηV
  have hcoeff : ∀ θ : BlocksIrr A, BlocksInnerProduct ρ.character θ = n θ := fun θ => by
    rw [← hn]
    exact blocksInnerProduct_expansion_coefficient n θ
  choose d hdpos hdval using fun χ : BlocksIrr A => blocksIrr_degree_eq_natCast χ
  let : Invertible (Nat.card A : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have hnat : ∀ θ : BlocksIrr A, 0 ≤ n θ := by
    intro θ
    obtain ⟨W, _, _, _, σ, -, hσθ⟩ := θ.property
    have hpair : BlocksInnerProduct ρ.character θ =
        (Nat.card A : ℂ)⁻¹ * ∑ g, ρ.character g * σ.character g⁻¹ := by
      unfold BlocksInnerProduct
      congr 1
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← hσθ, CFSG.Theory.Representation.representation_character_inv_eq_star_character]
      rfl
    rw [hcoeff, Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ] at hpair
    have hcast : n θ = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℤ) := by exact_mod_cast hpair
    omega
  have hreal : ∀ x, starRingEnd ℂ (ρ.character x) = ρ.character x := by
    intro x
    obtain ⟨q, hq⟩ := hrat x
    rw [hq]
    exact map_ratCast _ q
  have hsum : (Module.finrank ℂ V : ℤ) = ∑ χ ∈ n.support, n χ * (d χ : ℤ) := by
    have h := congrArg (fun f : A → ℂ => f 1) hn
    simp only [blocksCharacterExpansion_apply, Representation.char_one] at h
    have h' : ((Module.finrank ℂ V : ℤ) : ℂ) = ((∑ χ ∈ n.support, n χ * (d χ : ℤ) : ℤ) : ℂ) := by
      rw [Int.cast_natCast, ← h]
      push_cast
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [hdval χ]
    exact_mod_cast h'
  have hlinear : ∀ θ : BlocksIrr A, n θ ≠ 0 → (θ : A → ℂ) 1 = 1 := by
    intro θ hθ
    obtain ⟨W, _, _, _, σ, hσ, hσθ⟩ := θ.property
    by_contra hne
    let : σ.IsIrreducible := hσ
    have hθ1 : (θ : A → ℂ) 1 = (Module.finrank ℂ W : ℂ) := by
      rw [← hσθ, Representation.char_one]
    have hdvd := CFSG.Theory.Character.irreducible_dimension_dvd_group_order σ
    have hWodd : Odd (Module.finrank ℂ W) := Odd.of_dvd_nat hodd hdvd
    have hW1 : Module.finrank ℂ W ≠ 1 := fun h => hne (by rw [hθ1, h, Nat.cast_one])
    have hW3 : 3 ≤ Module.finrank ℂ W := by
      obtain ⟨k, hk⟩ := hWodd
      omega
    let θbar : BlocksIrr A := ⟨σ.dual.character, Module.Dual ℂ W, inferInstance, inferInstance,
      inferInstance, σ.dual, CFSG.Section1.representation_dual_irreducible_of σ hσ, rfl⟩
    have hbarval : ∀ g, (θbar : A → ℂ) g = star ((θ : A → ℂ) g) := by
      intro g
      change σ.dual.character g = _
      rw [← CFSG.Section1.conjugateCharacter_representationCharacter_eq_dual, hσθ]
      rfl
    have hne_bar : θbar ≠ θ := by
      intro h
      have hfix : σ.character = CFSG.Section1.conjugateCharacter σ.character := by
        funext g
        have := congrArg (fun χ : BlocksIrr A => (χ : A → ℂ) g) h
        simp only [hbarval] at this
        rw [hσθ]
        exact this.symm
      refine CFSG.Section1.proposition_1_1 hodd σ hσ (fun hprin => hne ?_) hfix
      rw [← hσθ, hprin]
      rfl
    have hbarcoeff : n θbar = n θ := by
      have h : BlocksInnerProduct ρ.character θbar =
          starRingEnd ℂ (BlocksInnerProduct ρ.character θ) := by
        unfold BlocksInnerProduct
        rw [map_mul, map_inv₀, map_natCast, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, hreal g, hbarval g]
        simp only [starRingEnd_apply, star_star]
      rw [hcoeff, hcoeff, map_intCast] at h
      exact_mod_cast h
    have hdθ : (d θ : ℤ) = Module.finrank ℂ W := by
      have h := (hdval θ).symm.trans hθ1
      exact_mod_cast h
    have hdbar : (d θbar : ℤ) = Module.finrank ℂ W := by
      have h : (d θbar : ℂ) = Module.finrank ℂ W := by
        rw [← hdval θbar, hbarval, hθ1]
        simp
      exact_mod_cast h
    have hsub : ({θ, θbar} : Finset (BlocksIrr A)) ⊆ n.support := by
      intro χ hχ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
      rcases hχ with rfl | rfl
      · exact Finsupp.mem_support_iff.mpr hθ
      · exact Finsupp.mem_support_iff.mpr (by rw [hbarcoeff]; exact hθ)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun χ => n χ * (d χ : ℤ)) fun χ _ _ => mul_nonneg (hnat χ) (by positivity)
    rw [Finset.sum_pair (Ne.symm hne_bar), ← hsum, hbarcoeff, hdθ, hdbar] at hle
    have hθpos : 1 ≤ n θ := by
      have := hnat θ
      omega
    have hW3' : (3 : ℤ) ≤ Module.finrank ℂ W := by exact_mod_cast hW3
    have hdeg' : (Module.finrank ℂ V : ℤ) ≤ 5 := by exact_mod_cast hdeg
    nlinarith
  refine ⟨fun θ hθmem hθ => ?_, fun hinj a b => ?_⟩
  · exact hlinear ⟨θ, hθmem⟩ fun h0 => hθ (by rw [hcoeff ⟨θ, hθmem⟩, h0, Int.cast_zero])
  · have hc : ρ.character ⁅a, b⁆ = ρ.character 1 := by
      have h := congrArg (fun f : A → ℂ => f ⁅a, b⁆) hn
      have h1 := congrArg (fun f : A → ℂ => f 1) hn
      simp only [blocksCharacterExpansion_apply] at h h1
      rw [← h, ← h1]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have hχ1 := hlinear χ (Finsupp.mem_support_iff.mp hχ)
      obtain ⟨W, _, _, _, σ, -, hσχ⟩ := χ.property
      have hW : Module.finrank ℂ W = 1 := by
        have h' : (Module.finrank ℂ W : ℂ) = 1 := by
          rw [← Representation.char_one σ, hσχ]
          exact hχ1
        exact_mod_cast h'
      rw [hχ1, ← hσχ, character_commutator_of_finrank_eq_one hW]
    have hone : ρ ⁅a, b⁆ = 1 := by
      apply CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank (ρ ⁅a, b⁆)
        (orderOf_pos ⁅a, b⁆).ne'
      · rw [← map_pow, pow_orderOf_eq_one, map_one]
      · change ρ.character ⁅a, b⁆ = _
        rw [hc, Representation.char_one]
    have hab : ⁅a, b⁆ = 1 := hinj (by rw [hone, map_one])
    exact commutatorElement_eq_one_iff_mul_comm.mp hab

end CFSG.Semidihedral.Principal
