module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.E6 (e6RootVec isRoot_iff_exists_e6RootVec)

open CFSG.RankThree.PartOne.KE (conjDiag3Hom conjDiag3Hom_apply conjDiag3_transvection)

open scoped MatrixGroups commutatorElement

section Cocycle

theorem e6A2_chain_check : ∀ i a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c →
    e6A2Root i a b ≠ e6A2Root i b c ∧ e6A2Root i a b + e6A2Root i b c ≠ 0 ∧
      ∃ m : Fin 72, e6RootVec m = e6A2Root i a b + e6A2Root i b c := by
  decide +kernel

theorem e6A2Root_add (i a b c : Fin 3) :
    e6A2Root i a b + e6A2Root i b c = e6A2Root i a c := by
  simp only [e6A2Root]
  abel


@[expose] def e6A2N (i a b c : Fin 3) : ℤ :=
  commConst Tag.E6 (e6A2Root i a b) (e6A2Root i b c) (1, 1)

theorem e6A2N_sign (i : Fin 3) {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    e6A2N i a b c = 1 ∨ e6A2N i a b c = -1 := by
  obtain ⟨hne, hne', hr⟩ := e6A2_chain_check i a b c hab hbc hac
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl))
    (isRoot_e6A2Root i hab) (isRoot_e6A2Root i hbc) hne (fun h => hne' (by rw [h]; abel))
  exact (h1 (isRoot_iff_exists_e6RootVec.2 hr)).1

variable {K : Type} [Field K]

theorem e6A2_cocycle (i : Fin 3) {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {η₁ η₂ η₃ : K}
    (h₁ : ∀ t : K, e6A2Rho K i (Matrix.SpecialLinearGroup.transvection hab t) =
      pinnedX Tag.E6 K (e6A2Root i a b) (η₁ * t))
    (h₂ : ∀ t : K, e6A2Rho K i (Matrix.SpecialLinearGroup.transvection hbc t) =
      pinnedX Tag.E6 K (e6A2Root i b c) (η₂ * t))
    (h₃ : ∀ t : K, e6A2Rho K i (Matrix.SpecialLinearGroup.transvection hac t) =
      pinnedX Tag.E6 K (e6A2Root i a c) (η₃ * t)) :
    η₃ = (e6A2N i a b c : K) * η₁ * η₂ := by
  obtain ⟨hne, hne', hr⟩ := e6A2_chain_check i a b c hab hbc hac
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl))
    (isRoot_e6A2Root i hab) (isRoot_e6A2Root i hbc) hne (fun h => hne' (by rw [h]; abel))
  have key := congrArg (e6A2Rho K i)
    (Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : K) 1)
  rw [map_commutatorElement, h₁, h₂, h₃] at key
  rw [(h1 (isRoot_iff_exists_e6RootVec.2 hr)).2 K (η₁ * 1) (η₂ * 1), e6A2Root_add] at key
  have := pinnedX_injective Tag.E6 K _ key
  unfold e6A2N
  linear_combination -this

end Cocycle

section Coboundary

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false in
theorem sign_coboundary (u : Fin 3 → Fin 3 → K) (hsq : ∀ a b, a ≠ b → u a b * u a b = 1)
    (hc : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → u a c = u a b * u b c) :
    ∃ d : Fin 3 → Kˣ, ∀ a b, a ≠ b → u a b * (d a : K) * ((d b)⁻¹ : Kˣ) = 1 := by
  have s01 := hsq 0 1 (by decide)
  have s02 := hsq 0 2 (by decide)
  have s10 := hsq 1 0 (by decide)
  have s12 := hsq 1 2 (by decide)
  have s20 := hsq 2 0 (by decide)
  have s21 := hsq 2 1 (by decide)
  have c012 := hc 0 1 2 (by decide) (by decide) (by decide)
  have c120 := hc 1 2 0 (by decide) (by decide) (by decide)
  have c201 := hc 2 0 1 (by decide) (by decide) (by decide)
  have c021 := hc 0 2 1 (by decide) (by decide) (by decide)
  have c102 := hc 1 0 2 (by decide) (by decide) (by decide)
  have c210 := hc 2 1 0 (by decide) (by decide) (by decide)
  have h01 : u 0 1 ≠ 0 := fun h => by rw [h] at s01; simp at s01
  have e1 : u 1 2 * u 2 1 = 1 := by
    have : u 0 1 * (u 1 2 * u 2 1 - 1) = 0 := by
      linear_combination (-1 : K) * c021 - (u 2 1) * c012
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h01
    · linear_combination h
  have e21 : u 2 1 = u 1 2 := by linear_combination (u 1 2) * e1 - (u 2 1) * s12
  have e3 : u 0 1 = u 1 2 * u 2 0 := by
    linear_combination c021 + (u 2 1) * c012 + (u 0 1 * u 1 2) * c201 + (u 1 2 * u 2 0) * s01
  have e10 : u 1 0 = u 0 1 := by linear_combination c120 - e3
  have e20 : u 2 0 = u 0 2 := by
    linear_combination -(u 2 0) * s12 - (u 1 2) * e3 - c012
  have hx : (u 0 1) * u 0 1 = 1 := s01
  have hxy : (u 1 2 * u 0 1) * (u 1 2 * u 0 1) = 1 := by linear_combination (u 1 2 * u 1 2) * s01 + s12
  have hxi : (u 0 1)⁻¹ = u 0 1 := inv_eq_of_mul_eq_one_right s01
  have hyi : (u 1 2)⁻¹ = u 1 2 := inv_eq_of_mul_eq_one_right s12
  let d : Fin 3 → Kˣ := ![1, Units.mkOfMulEqOne _ _ hx, Units.mkOfMulEqOne _ _ hxy]
  refine ⟨d, ?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · simp [d, hxi, hyi]; linear_combination s01
  · simp [d, hxi, hyi]; linear_combination c012 * (u 1 2 * u 0 1) + (u 1 2 * u 1 2) * s01 + s12
  · simp [d, hxi, hyi]; linear_combination e10 * (u 0 1) + s01
  · exact absurd rfl hab
  · simp [d, hxi, hyi]; linear_combination s12 * (u 0 1 * u 0 1) + s01
  · simp [d, hxi, hyi]; linear_combination e20 * (u 1 2 * u 0 1) + c012 * (u 1 2 * u 0 1) + (u 1 2 * u 1 2) * s01 + s12
  · simp [d, hxi, hyi]; linear_combination e21 * (u 1 2 * u 0 1 * u 0 1) + s12 * (u 0 1 * u 0 1) + s01
  · exact absurd rfl hab

end Coboundary


section Signs


local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

theorem exists_e6A2_signs : ∃ s : Fin 3 → Fin 3 → Fin 3 → ℤ,
    (∀ i a b, a ≠ b → s i a b = 1 ∨ s i a b = -1) ∧
    ∀ i a b c, a ≠ b → b ≠ c → a ≠ c → s i a c = e6A2N i a b c * s i a b * s i b c := by
  have h : ∀ i a b : Fin 3, ∃ η : ℚ, ∀ hab : a ≠ b, (η = 1 ∨ η = -1) ∧ ∀ t : ℚ,
      e6A2Rho ℚ i (Matrix.SpecialLinearGroup.transvection hab t) =
        pinnedX Tag.E6 ℚ (e6A2Root i a b) (η * t) := by
    intro i a b
    by_cases hab : a ≠ b
    · obtain ⟨ε, h1, h2⟩ := e6A2Rho_transvection (K := ℚ) i hab
      exact ⟨ε, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hab⟩
  choose η hη using h
  have h2 : ∀ i a b : Fin 3, ∃ z : ℤ, a ≠ b → (z = 1 ∨ z = -1) ∧ (z : ℚ) = η i a b := by
    intro i a b
    by_cases hab : a ≠ b
    · rcases (hη i a b hab).1 with h | h
      · exact ⟨1, fun _ => ⟨Or.inl rfl, by rw [h]; simp⟩⟩
      · exact ⟨-1, fun _ => ⟨Or.inr rfl, by rw [h]; simp⟩⟩
    · exact ⟨1, fun h => absurd h hab⟩
  choose z hz using h2
  refine ⟨z, fun i a b hab => (hz i a b hab).1, fun i a b c hab hbc hac => ?_⟩
  have hc := e6A2_cocycle (K := ℚ) i hab hbc hac (hη i a b hab).2 (hη i b c hbc).2
    (hη i a c hac).2
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [(hz i a c hac).2, (hz i a b hab).2, (hz i b c hbc).2]
  exact hc

@[expose] def e6A2S : Fin 3 → Fin 3 → Fin 3 → ℤ := Classical.choose exists_e6A2_signs

theorem e6A2S_sign (i : Fin 3) {a b : Fin 3} (hab : a ≠ b) : e6A2S i a b = 1 ∨ e6A2S i a b = -1 :=
  (Classical.choose_spec exists_e6A2_signs).1 i a b hab

theorem e6A2S_cocycle (i : Fin 3) {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    e6A2S i a c = e6A2N i a b c * e6A2S i a b * e6A2S i b c :=
  (Classical.choose_spec exists_e6A2_signs).2 i a b c hab hbc hac

variable {K : Type} [Field K]

theorem exists_diag_E6 (i : Fin 3) : ∃ d : Fin 3 → Kˣ, ∀ (a b : Fin 3) (hab : a ≠ b) (t : K),
    e6A2Rho K i (conjDiag3Hom d (Matrix.SpecialLinearGroup.transvection hab t)) =
      pinnedX Tag.E6 K (e6A2Root i a b) ((e6A2S i a b : K) * t) := by
  have h : ∀ a b : Fin 3, ∃ η : K, ∀ hab : a ≠ b, (η = 1 ∨ η = -1) ∧ ∀ t : K,
      e6A2Rho K i (Matrix.SpecialLinearGroup.transvection hab t) =
        pinnedX Tag.E6 K (e6A2Root i a b) (η * t) := by
    intro a b
    by_cases hab : a ≠ b
    · obtain ⟨ε, h1, h2⟩ := e6A2Rho_transvection (K := K) i hab
      exact ⟨ε, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hab⟩
  choose η hη using h
  have hsK : ∀ a b : Fin 3, a ≠ b → (e6A2S i a b : K) * (e6A2S i a b : K) = 1 := by
    intro a b hab
    rcases e6A2S_sign i hab with h | h <;> rw [h] <;> simp
  have hηK : ∀ a b : Fin 3, a ≠ b → η a b * η a b = 1 := by
    intro a b hab
    rcases (hη a b hab).1 with h | h <;> rw [h] <;> simp
  have hNK : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c →
      (e6A2N i a b c : K) * (e6A2N i a b c : K) = 1 := by
    intro a b c hab hbc hac
    rcases e6A2N_sign i hab hbc hac with h | h <;> rw [h] <;> simp
  obtain ⟨d, hd⟩ := sign_coboundary (K := K) (fun a b => η a b * (e6A2S i a b : K))
    (fun a b hab => by
      show (η a b * (e6A2S i a b : K)) * (η a b * (e6A2S i a b : K)) = 1
      linear_combination ((e6A2S i a b : K) * (e6A2S i a b : K)) * (hηK a b hab) + hsK a b hab)
    (fun a b c hab hbc hac => by
      have hη' := e6A2_cocycle (K := K) i hab hbc hac (hη a b hab).2 (hη b c hbc).2
        (hη a c hac).2
      have hs' : (e6A2S i a c : K) = (e6A2N i a b c : K) * (e6A2S i a b : K) * (e6A2S i b c : K) := by
        rw [e6A2S_cocycle i hab hbc hac]
        push_cast
        ring
      show η a c * (e6A2S i a c : K) = (η a b * (e6A2S i a b : K)) * (η b c * (e6A2S i b c : K))
      rw [hη', hs']
      linear_combination (η a b * η b c * (e6A2S i a b : K) * (e6A2S i b c : K)) *
        (hNK a b c hab hbc hac))
  refine ⟨d, fun a b hab t => ?_⟩
  rw [conjDiag3Hom_apply, conjDiag3_transvection, (hη a b hab).2]
  congr 1
  have h1 := hd a b hab
  linear_combination ((e6A2S i a b : K) * t) * h1 -
    (η a b * (d a : K) * ((d b)⁻¹ : Kˣ) * t) * hsK a b hab

@[expose] def e6A2Pair (γ : Fin 2 → ℤ) : Fin 3 × Fin 3 :=
  if γ = ![1, 0] then (0, 1) else if γ = ![0, 1] then (1, 2) else if γ = ![1, 1] then (0, 2)
  else if γ = ![-1, 0] then (1, 0) else if γ = ![0, -1] then (2, 1) else (2, 0)

@[expose] def e6A2Sign (i : Fin 3) (γ : Fin 2 → ℤ) : ℤ :=
  if (e6A2Pair γ).1 ≠ (e6A2Pair γ).2 then e6A2S i (e6A2Pair γ).1 (e6A2Pair γ).2 else 1

theorem e6A2Sign_eq (i : Fin 3) (γ : Fin 2 → ℤ) : e6A2Sign i γ = 1 ∨ e6A2Sign i γ = -1 := by
  unfold e6A2Sign
  split_ifs with h
  · exact e6A2S_sign i h
  · exact Or.inl rfl

theorem e6A2Pair_spec (K : Type) [Field K] (i : Fin 3) {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) :
    ∃ (a b : Fin 3) (hab : a ≠ b), e6A2Pair γ = (a, b) ∧
      (∀ c : K, CFSG.LieType.Steinberg.SL.x 2 K γ c =
        Matrix.SpecialLinearGroup.transvection hab c) ∧
      e6A2Frame i γ = e6A2Root i a b := by
  rcases mem_rootsA2_E6 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, by decide, by decide +kernel,
      fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
  · exact ⟨1, 2, by decide, by decide +kernel,
      fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
  · exact ⟨0, 2, by decide, by decide +kernel,
      fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
  · exact ⟨1, 0, by decide, by decide +kernel,
      fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
  · exact ⟨2, 1, by decide, by decide +kernel,
      fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
  · exact ⟨2, 0, by decide, by decide +kernel,
      fun c => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) c,
      by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩

end Signs
local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

theorem exists_three_sl3_E6_signed (K : Type) [Field K] :
    ∃ ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K,
      (∀ i, Function.Injective (ψ i)) ∧
      (∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) ∧
      ∀ i, ∀ γ ∈ RA2, ∀ c : K,
        ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          pinnedX Tag.E6 K (e6A2Frame i γ) ((e6A2Sign i γ : K) * c) := by
  choose d hd using fun i => exists_diag_E6 (K := K) i
  refine ⟨fun i => ((e6A2Rho K i).comp (conjDiag3Hom (d i))).codRestrict (adjointGroup Tag.E6 K)
      (fun A => e6A2Rho_mem i _), fun i => ?_, fun i j hij A B => ?_, fun i γ hγ c => ?_⟩
  · intro A B h
    exact CFSG.RankThree.PartOne.KLCE.conjDiag3_injective (d i)
      (e6A2Rho_injective i (congrArg Subtype.val h))
  · exact Subtype.ext_iff.2 (e6A2Rho_commute hij _ _).eq
  · obtain ⟨a, b, hab, hp, hx, hf⟩ := e6A2Pair_spec K i hγ
    have hs : e6A2Sign i γ = e6A2S i a b := by
      unfold e6A2Sign
      rw [hp]
      simp [hab]
    rw [hf, hs]
    change e6A2Rho K i (conjDiag3Hom (d i) (CFSG.LieType.Steinberg.SL.x 2 K γ c)) = _
    rw [hx, hd i a b hab c]

end CFSG.HardMathSupport.Malle.SeitzCube
