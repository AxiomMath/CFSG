module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix
open scoped MatrixGroups

section SL2

variable {R : Type*} [Field R]

@[expose] def upperUnit (c : R) : SL(2, R) :=
  SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c

@[expose] def lowerUnit (c : R) : SL(2, R) :=
  SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c

@[expose] def diagUnit (α : Rˣ) : SL(2, R) :=
  ⟨!![(α : R), 0; 0, ((α⁻¹ : Rˣ) : R)], by simp [Matrix.det_fin_two]⟩

@[expose] def weylUnit : SL(2, R) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_upperUnit (c : R) : (upperUnit c : Matrix (Fin 2) (Fin 2) R) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnit, SpecialLinearGroup.transvection_coe]

theorem coe_lowerUnit (c : R) : (lowerUnit c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnit, SpecialLinearGroup.transvection_coe]

theorem coe_diagUnit (α : Rˣ) :
    (diagUnit α : Matrix (Fin 2) (Fin 2) R) = !![(α : R), 0; 0, ((α⁻¹ : Rˣ) : R)] :=
  rfl

theorem coe_weylUnit : (weylUnit (R := R) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] :=
  rfl

theorem upperUnit_add (c d : R) : upperUnit (c + d) = upperUnit c * upperUnit d :=
  SpecialLinearGroup.transvection_add _ c d

@[simp]
theorem upperUnit_zero : upperUnit (0 : R) = 1 :=
  SpecialLinearGroup.transvection_coeff_zero _

theorem upperUnit_inv (c : R) : (upperUnit c)⁻¹ = upperUnit (-c) :=
  SpecialLinearGroup.transvection_inv _ c

theorem upperUnit_mul_comm (c d : R) : upperUnit c * upperUnit d = upperUnit d * upperUnit c := by
  rw [← upperUnit_add, ← upperUnit_add, add_comm]

theorem lowerUnit_add (c d : R) : lowerUnit (c + d) = lowerUnit c * lowerUnit d :=
  SpecialLinearGroup.transvection_add _ c d

variable {S : Type*} [Field S]

@[simp]
theorem map_upperUnit (f : R →+* S) (c : R) :
    SpecialLinearGroup.map f (upperUnit c) = upperUnit (f c) :=
  SpecialLinearGroup.map_transvection f _ c

@[simp]
theorem map_lowerUnit (f : R →+* S) (c : R) :
    SpecialLinearGroup.map f (lowerUnit c) = lowerUnit (f c) :=
  SpecialLinearGroup.map_transvection f _ c

@[simp]
theorem map_diagUnit (f : R →+* S) (α : Rˣ) :
    SpecialLinearGroup.map f (diagUnit α) = diagUnit (Units.map f.toMonoidHom α) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, coe_diagUnit,
    coe_diagUnit]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem map_weylUnit (f : R →+* S) : SpecialLinearGroup.map f (weylUnit (R := R)) = weylUnit := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, coe_weylUnit,
    coe_weylUnit]
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnit_mul_upperUnit_mul_inv (α : Rˣ) (c : R) :
    diagUnit α * upperUnit c * (diagUnit α)⁻¹ = upperUnit ((α : R) * α * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  have hα : (α : R) ≠ 0 := α.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_upperUnit, coe_diagUnit, Matrix.mul_apply,
      Fin.sum_univ_two]
  field_simp

theorem weylUnit_mul_upperUnit_mul_inv (c : R) :
    weylUnit * upperUnit c * weylUnit⁻¹ = lowerUnit (-c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_upperUnit, coe_lowerUnit, coe_weylUnit,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem upperUnit_mul_diagUnit_commutator (c : R) (α : Rˣ) :
    upperUnit c * diagUnit α * (upperUnit c)⁻¹ * (diagUnit α)⁻¹ =
      upperUnit ((1 - (α : R) * α) * c) := by
  have h := diagUnit_mul_upperUnit_mul_inv α (-c)
  calc upperUnit c * diagUnit α * (upperUnit c)⁻¹ * (diagUnit α)⁻¹ =
        upperUnit c * (diagUnit α * upperUnit (-c) * (diagUnit α)⁻¹) := by
          rw [upperUnit_inv]
          group
    _ = upperUnit ((1 - (α : R) * α) * c) := by
          rw [h, ← upperUnit_add]
          congr 1
          ring

theorem eq_top_of_upperUnit_mem_of_lowerUnit_mem {H : Subgroup SL(2, R)}
    (hu : ∀ c, upperUnit c ∈ H) (hl : ∀ c, lowerUnit c ∈ H) : H = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hu c
  · exact hl c
  · exact absurd rfl hij

end SL2

section Quadratic

variable {K F : Type*} [Field K] [Field F] (ι : K →+* F)

theorem exists_eq_add_mul_of_notMem_range [Finite K] [Finite F]
    (hFK : Nat.card F = Nat.card K ^ 2) {ω : F} (hω : ω ∉ ι.range) (x : F) :
    ∃ k l : K, x = ι k + ι l * ω := by
  set φ : K × K → F := fun p => ι p.1 + ι p.2 * ω with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨k, l⟩ ⟨k', l'⟩ h
    simp only [hφ] at h
    by_cases hl : l = l'
    · subst hl
      rw [add_left_inj] at h
      rw [ι.injective h]
    · exfalso
      apply hω
      have hne : ι (l - l') ≠ 0 := by
        rw [map_sub]
        exact sub_ne_zero.2 (fun h' => hl (ι.injective h'))
      refine ⟨(k' - k) / (l - l'), ?_⟩
      rw [map_div₀, div_eq_iff hne, map_sub, map_sub]
      linear_combination -h
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hFK, sq])
  obtain ⟨⟨k, l⟩, hkl⟩ := hbij.2 x
  exact ⟨k, l, hkl.symm⟩

theorem exists_trace_one [Finite K] [Finite F] [CharP F 2] (σ : F →+* F)
    (hσι : ∀ k, σ (ι k) = ι k) (hfix : ∀ x, σ x = x → x ∈ ι.range)
    (hFK : Nat.card F = Nat.card K ^ 2) : ∃ ω : F, σ ω = ω + 1 := by
  obtain ⟨x, hx⟩ : ∃ x : F, x ∉ ι.range := by
    by_contra h
    push Not at h
    have hle := Nat.card_le_card_of_surjective ι h
    have hK : 1 < Nat.card K := Finite.one_lt_card
    rw [hFK] at hle
    nlinarith
  obtain ⟨k, l, hkl⟩ := exists_eq_add_mul_of_notMem_range ι hFK hx (x * x)
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hσx : σ x * σ x = ι k + ι l * σ x := by
    have := congrArg σ hkl
    rwa [map_mul, map_add, map_mul, hσι, hσι] at this
  have hne : x + σ x ≠ 0 := by
    intro h
    apply hx (hfix x _)
    linear_combination h - x * h2F
  have key : (x + σ x) * (x + σ x) = ι l * (x + σ x) := by
    linear_combination hkl + hσx + (x * σ x + ι k) * h2F
  have hsum : x + σ x = ι l := mul_right_cancel₀ hne key
  have hl0 : ι l ≠ 0 := hsum ▸ hne
  refine ⟨x * (ι l)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hσι]
  have hσx' : σ x = ι l + x := by linear_combination hsum - x * h2F
  rw [hσx']
  field_simp
  ring

theorem exists_trace_one_of_fixed [Finite K] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ : ∀ x : F, σ x = x ↔ x ∈ ι.range) (hFK : Nat.card F = Nat.card K ^ 2) :
    ∃ ω : F, σ ω = ω + 1 :=
  exists_trace_one ι σ.toRingHom (fun k => (hσ (ι k)).2 ⟨k, rfl⟩) (fun x hx => (hσ x).1 hx) hFK

theorem notMem_range_of_trace_one {σ : F →+* F} (hσι : ∀ k, σ (ι k) = ι k) {ω : F}
    (hω : σ ω = ω + 1) : ω ∉ ι.range := by
  rintro ⟨k, rfl⟩
  rw [hσι] at hω
  exact one_ne_zero (by linear_combination -hω : (1 : F) = 0)

end Quadratic

section Twisted

variable {K F : Type*} [Field K] [Field F] (ι : K →+* F)

@[expose] def subfieldSL : Subgroup SL(2, F) :=
  (SpecialLinearGroup.map ι).range

@[expose] def twistedSubfield (ω : F) : Subgroup SL(2, F) :=
  (subfieldSL ι).map (MulAut.conj (upperUnit ω)).toMonoidHom

theorem mem_subfieldSL {g : SL(2, F)} :
    g ∈ subfieldSL ι ↔ ∃ s : SL(2, K), SpecialLinearGroup.map ι s = g :=
  Iff.rfl

theorem mem_twistedSubfield {ω : F} {g : SL(2, F)} :
    g ∈ twistedSubfield ι ω ↔
      ∃ s : SL(2, K), upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ = g := by
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, ⟨s, rfl⟩, rfl⟩

theorem specialLinearGroup_map_injective :
    Function.Injective (SpecialLinearGroup.map (n := Fin 2) ι) := by
  intro s s' h
  ext i j
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) h
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact ι.injective this

theorem nonempty_mulEquiv_subfieldSL : Nonempty (SL(2, K) ≃* subfieldSL ι) :=
  ⟨MonoidHom.ofInjective (specialLinearGroup_map_injective ι)⟩

theorem nonempty_mulEquiv_twistedSubfield (ω : F) : Nonempty (SL(2, K) ≃* twistedSubfield ι ω) :=
  ⟨(MonoidHom.ofInjective (specialLinearGroup_map_injective ι)).trans
    ((subfieldSL ι).equivMapOfInjective _ (MulEquiv.injective _))⟩

theorem upperUnit_mem_subfieldSL (k : K) : upperUnit (ι k) ∈ subfieldSL ι :=
  ⟨upperUnit k, map_upperUnit ι k⟩

theorem diagUnit_mem_subfieldSL (β : Kˣ) :
    diagUnit (Units.map ι.toMonoidHom β) ∈ subfieldSL ι :=
  ⟨diagUnit β, map_diagUnit ι β⟩

theorem weylUnit_mem_subfieldSL : weylUnit ∈ subfieldSL ι :=
  ⟨weylUnit, map_weylUnit ι⟩

theorem map_map_of_forall_eq (σ : F →+* F) (hσι : ∀ k, σ (ι k) = ι k) (s : SL(2, K)) :
    SpecialLinearGroup.map σ (SpecialLinearGroup.map ι s) = SpecialLinearGroup.map ι s := by
  ext i j
  simp [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hσι]

theorem twistedSubfield_fixed [CharP F 2] (σ : F →+* F) (hσι : ∀ k, σ (ι k) = ι k) {ω : F}
    (hω : σ ω = ω + 1) {g : SL(2, F)} (hg : g ∈ twistedSubfield ι ω) :
    upperUnit 1 * SpecialLinearGroup.map σ g * upperUnit 1 = g := by
  obtain ⟨s, rfl⟩ := (mem_twistedSubfield ι).1 hg
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hmap : SpecialLinearGroup.map σ
      (upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹) =
      upperUnit (ω + 1) * SpecialLinearGroup.map ι s * (upperUnit (ω + 1))⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_upperUnit, hω, map_map_of_forall_eq ι σ hσι]
  have h1 : upperUnit (1 : F) * upperUnit (ω + 1) = upperUnit ω := by
    rw [← upperUnit_add]
    congr 1
    linear_combination h2F
  have h2 : (upperUnit (ω + 1))⁻¹ * upperUnit (1 : F) = (upperUnit ω)⁻¹ := by
    rw [upperUnit_inv, upperUnit_inv, ← upperUnit_add]
    congr 1
    ring
  rw [hmap]
  calc upperUnit 1 * (upperUnit (ω + 1) * SpecialLinearGroup.map ι s *
        (upperUnit (ω + 1))⁻¹) * upperUnit 1
      = (upperUnit 1 * upperUnit (ω + 1)) * SpecialLinearGroup.map ι s *
          ((upperUnit (ω + 1))⁻¹ * upperUnit 1) := by simp only [mul_assoc]
    _ = upperUnit ω * SpecialLinearGroup.map ι s * (upperUnit ω)⁻¹ := by rw [h1, h2]

theorem upperUnit_one_inv [CharP F 2] : (upperUnit (1 : F))⁻¹ = upperUnit 1 := by
  rw [upperUnit_inv, CharTwo.neg_eq]

theorem conj_upperUnit_one_map_eq [CharP F 2] (σ : F →+* F) (hσι : ∀ k, σ (ι k) = ι k)
    {ω : F} (hω : σ ω = ω + 1) {g : SL(2, F)} (hg : g ∈ twistedSubfield ι ω) :
    MulAut.conj (upperUnit 1) (SpecialLinearGroup.map σ g) = g := by
  rw [MulAut.conj_apply, upperUnit_one_inv]
  exact twistedSubfield_fixed ι σ hσι hω hg

theorem upperUnit_mem_twistedSubfield (ω : F) (k : K) : upperUnit (ι k) ∈ twistedSubfield ι ω :=
  (mem_twistedSubfield ι).2
    ⟨upperUnit k, by rw [map_upperUnit, upperUnit_mul_comm, mul_inv_cancel_right]⟩

theorem upperUnit_one_mem_twistedSubfield (ω : F) : upperUnit 1 ∈ twistedSubfield ι ω := by
  simpa using upperUnit_mem_twistedSubfield ι ω 1

end Twisted

section Generation

private theorem eq_one_of_mul_self_eq_one_of_charTwo {R : Type*} [Field R] [CharP R 2] {x : R}
    (h : x * x = 1) : x = 1 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  have h3 : (x - 1) * (x - 1) = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)

theorem exists_unit_mul_self_ne_one {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) : ∃ α : Kˣ, (α : K) * α ≠ 1 := by
  by_contra h
  push Not at h
  have hone : ∀ α : Kˣ, α = 1 := fun α =>
    Units.ext (by rw [Units.val_one]; exact eq_one_of_mul_self_eq_one_of_charTwo (h α))
  have hsub : Subsingleton Kˣ := ⟨fun α β => by rw [hone α, hone β]⟩
  have h1 : Nat.card Kˣ ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  rw [Nat.card_units] at h1
  omega

variable {K F : Type*} [Field K] [Field F] (ι : K →+* F)

theorem coe_units_map_ringHom (β : Kˣ) : ((Units.map ι.toMonoidHom β : Fˣ) : F) = ι β :=
  rfl

theorem sup_twistedSubfield_eq_top [Finite K] [Finite F] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hFK : Nat.card F = Nat.card K ^ 2) {ω : F} (hω : ω ∉ ι.range) :
    subfieldSL ι ⊔ twistedSubfield ι ω = ⊤ := by
  set H := subfieldSL ι ⊔ twistedSubfield ι ω with hH
  have hsub : subfieldSL ι ≤ H := le_sup_left
  have htw : twistedSubfield ι ω ≤ H := le_sup_right
  obtain ⟨α, hα⟩ := exists_unit_mul_self_ne_one hq
  have he : (1 : K) - α * α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hconj : ∀ (β : Kˣ) (c : F), upperUnit c ∈ H → upperUnit (ι β * ι β * c) ∈ H := by
    intro β c hc
    have hβ : diagUnit (Units.map ι.toMonoidHom β) ∈ H := hsub (diagUnit_mem_subfieldSL ι β)
    have := H.mul_mem (H.mul_mem hβ hc) (H.inv_mem hβ)
    rwa [diagUnit_mul_upperUnit_mul_inv, coe_units_map_ringHom] at this
  have h0 : upperUnit (ι (1 - α * α) * ω) ∈ H := by
    have hα' : diagUnit (Units.map ι.toMonoidHom α) ∈ H := hsub (diagUnit_mem_subfieldSL ι α)
    have h1 : upperUnit ω * diagUnit (Units.map ι.toMonoidHom α) * (upperUnit ω)⁻¹ ∈ H :=
      htw ((mem_twistedSubfield ι).2 ⟨diagUnit α, by rw [map_diagUnit]⟩)
    have := H.mul_mem h1 (H.inv_mem hα')
    rwa [upperUnit_mul_diagUnit_commutator, coe_units_map_ringHom, ← map_mul, ← map_one ι,
      ← map_sub] at this
  have hK : ∀ k : K, upperUnit (ι k * ω) ∈ H := by
    intro k
    by_cases hk : k = 0
    · rw [hk, map_zero, zero_mul, upperUnit_zero]
      exact H.one_mem
    · obtain ⟨β, hβ⟩ := isSquare_of_charTwo' (k / (1 - α * α))
      have hβ0 : β ≠ 0 := by
        rintro rfl
        rw [mul_zero, div_eq_zero_iff] at hβ
        exact hβ.elim hk he
      have h := hconj (Units.mk0 β hβ0) _ h0
      have heq : ι ((Units.mk0 β hβ0 : Kˣ) : K) * ι ((Units.mk0 β hβ0 : Kˣ) : K) *
          (ι (1 - α * α) * ω) = ι k * ω := by
        rw [Units.val_mk0, ← map_mul, ← mul_assoc, ← map_mul, ← hβ, div_mul_cancel₀ _ he]
      rwa [heq] at h
  have hu : ∀ c : F, upperUnit c ∈ H := by
    intro c
    obtain ⟨k, l, rfl⟩ := exists_eq_add_mul_of_notMem_range ι hFK hω c
    rw [upperUnit_add]
    exact H.mul_mem (hsub (upperUnit_mem_subfieldSL ι k)) (hK l)
  have hl : ∀ c : F, lowerUnit c ∈ H := by
    intro c
    have hw : weylUnit ∈ H := hsub (weylUnit_mem_subfieldSL ι)
    have := H.mul_mem (H.mul_mem hw (hu (-c))) (H.inv_mem hw)
    rwa [weylUnit_mul_upperUnit_mul_inv, neg_neg] at this
  exact eq_top_of_upperUnit_mem_of_lowerUnit_mem hu hl

theorem sup_twistedSubfield_eq_top_of_trace_one [Finite K] [Finite F] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (hFK : Nat.card F = Nat.card K ^ 2) {σ : F →+* F}
    (hσι : ∀ k, σ (ι k) = ι k) {ω : F} (hω : σ ω = ω + 1) :
    subfieldSL ι ⊔ twistedSubfield ι ω = ⊤ :=
  sup_twistedSubfield_eq_top ι hq hFK (notMem_range_of_trace_one ι hσι hω)

end Generation

section Swap

variable {K : Type*} [Field K]

variable (K) in
@[expose] def diagSL2 : Subgroup (SL(2, K) × SL(2, K)) :=
  ((MonoidHom.id SL(2, K)).prod (MonoidHom.id SL(2, K))).range

variable (K) in
@[expose] def twistedDiagSL2 : Subgroup (SL(2, K) × SL(2, K)) :=
  (diagSL2 K).map (MulAut.conj ((upperUnit 1, 1) : SL(2, K) × SL(2, K))).toMonoidHom

theorem mem_diagSL2 {p : SL(2, K) × SL(2, K)} : p ∈ diagSL2 K ↔ p.1 = p.2 := by
  constructor
  · rintro ⟨s, rfl⟩
    rfl
  · intro h
    exact ⟨p.2, Prod.ext h.symm rfl⟩

theorem mem_twistedDiagSL2 {p : SL(2, K) × SL(2, K)} :
    p ∈ twistedDiagSL2 K ↔ ∃ s : SL(2, K), (upperUnit 1 * s * (upperUnit 1)⁻¹, s) = p := by
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, by simp [MulAut.conj_apply]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s, s), ⟨s, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem pair_mem_diagSL2 (s : SL(2, K)) : (s, s) ∈ diagSL2 K :=
  mem_diagSL2.2 rfl

theorem pair_mem_twistedDiagSL2 (s : SL(2, K)) :
    (upperUnit 1 * s * (upperUnit 1)⁻¹, s) ∈ twistedDiagSL2 K :=
  mem_twistedDiagSL2.2 ⟨s, rfl⟩

theorem upperUnit_one_pair_mem_twistedDiagSL2 :
    ((upperUnit 1, upperUnit 1) : SL(2, K) × SL(2, K)) ∈ twistedDiagSL2 K := by
  have h := pair_mem_twistedDiagSL2 (K := K) (upperUnit 1)
  rwa [mul_inv_cancel_right] at h

theorem twistedDiagSL2_fixed [CharP K 2] {p : SL(2, K) × SL(2, K)} (hp : p ∈ twistedDiagSL2 K) :
    (((upperUnit 1, upperUnit 1) : SL(2, K) × SL(2, K)) * p *
      ((upperUnit 1, upperUnit 1) : SL(2, K) × SL(2, K))⁻¹).swap = p := by
  obtain ⟨s, rfl⟩ := mem_twistedDiagSL2.1 hp
  have hu : (upperUnit (1 : K))⁻¹ = upperUnit 1 := upperUnit_one_inv
  refine Prod.ext ?_ ?_
  · change upperUnit 1 * s * (upperUnit 1)⁻¹ = upperUnit 1 * s * (upperUnit 1)⁻¹
    rfl
  · change upperUnit 1 * (upperUnit 1 * s * (upperUnit 1)⁻¹) * (upperUnit 1)⁻¹ = s
    rw [hu]
    have h2 : upperUnit (1 : K) * upperUnit 1 = 1 := by
      calc upperUnit (1 : K) * upperUnit 1 = (upperUnit 1)⁻¹ * upperUnit 1 := by rw [hu]
        _ = 1 := inv_mul_cancel _
    calc upperUnit 1 * (upperUnit 1 * s * upperUnit 1) * upperUnit 1 =
          (upperUnit 1 * upperUnit 1) * s * (upperUnit 1 * upperUnit 1) := by
            simp only [mul_assoc]
      _ = s := by rw [h2, one_mul, mul_one]

theorem nonempty_mulEquiv_twistedDiagSL2 : Nonempty (SL(2, K) ≃* twistedDiagSL2 K) := by
  have hinj : Function.Injective ((MonoidHom.id SL(2, K)).prod (MonoidHom.id SL(2, K))) :=
    fun s s' h => congrArg Prod.fst h
  exact ⟨(MonoidHom.ofInjective hinj).trans
    ((diagSL2 K).equivMapOfInjective _ (MulEquiv.injective _))⟩

theorem diag_sup_twistedDiag_eq_top [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    diagSL2 K ⊔ twistedDiagSL2 K = ⊤ := by
  set H := diagSL2 K ⊔ twistedDiagSL2 K with hH
  have hΔ : ∀ s : SL(2, K), (s, s) ∈ H := fun s =>
    (le_sup_left : diagSL2 K ≤ H) (pair_mem_diagSL2 s)
  have hΔ' : ∀ s : SL(2, K), (upperUnit 1 * s * (upperUnit 1)⁻¹, s) ∈ H := fun s =>
    (le_sup_right : twistedDiagSL2 K ≤ H) (pair_mem_twistedDiagSL2 s)
  set H₁ : Subgroup SL(2, K) := H.comap (MonoidHom.inl SL(2, K) SL(2, K)) with hH₁
  have hmem₁ : ∀ x : SL(2, K), x ∈ H₁ ↔ (x, (1 : SL(2, K))) ∈ H := fun x => Iff.rfl
  have hnorm : ∀ (g x : SL(2, K)), x ∈ H₁ → g * x * g⁻¹ ∈ H₁ := by
    intro g x hx
    rw [hmem₁] at hx ⊢
    have := H.mul_mem (H.mul_mem (hΔ g) hx) (H.inv_mem (hΔ g))
    simpa using this
  obtain ⟨α, hα⟩ := exists_unit_mul_self_ne_one hq
  have he : (1 : K) - α * α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have h0 : upperUnit ((1 - (α : K) * α) * 1) ∈ H₁ := by
    rw [hmem₁, ← upperUnit_mul_diagUnit_commutator]
    have := H.mul_mem (hΔ' (diagUnit α)) (H.inv_mem (hΔ (diagUnit α)))
    simpa using this
  have hu : ∀ c : K, upperUnit c ∈ H₁ := by
    intro c
    by_cases hc : c = 0
    · rw [hc, upperUnit_zero]
      exact H₁.one_mem
    · obtain ⟨β, hβ⟩ := isSquare_of_charTwo' (c / (1 - α * α))
      have hβ0 : β ≠ 0 := by
        rintro rfl
        rw [mul_zero, div_eq_zero_iff] at hβ
        exact hβ.elim hc he
      have h := hnorm (diagUnit (Units.mk0 β hβ0)) _ h0
      rw [diagUnit_mul_upperUnit_mul_inv, Units.val_mk0, mul_one, ← hβ,
        div_mul_cancel₀ _ he] at h
      exact h
  have hl : ∀ c : K, lowerUnit c ∈ H₁ := by
    intro c
    have h := hnorm weylUnit _ (hu (-c))
    rwa [weylUnit_mul_upperUnit_mul_inv, neg_neg] at h
  have htop : H₁ = ⊤ := eq_top_of_upperUnit_mem_of_lowerUnit_mem hu hl
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have h1 : (x * y⁻¹, (1 : SL(2, K))) ∈ H := (hmem₁ _).1 (htop ▸ mem_top _)
  have := H.mul_mem h1 (hΔ y)
  simpa using this

end Swap

section Block

variable {n : ℕ}

theorem map_pairEmbed {R S : Type*} [Field R] [Field S] (f : R →+* S) {a b : Fin n}
    (hab : a ≠ b) (A : SL(2, R)) :
    SpecialLinearGroup.map f (pairEmbed hab A) = pairEmbed hab (SpecialLinearGroup.map f A) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    pairEmbed_apply, pairEmbed_apply]
  by_cases h : i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  · rw [ite_eq_right h, ite_eq_right h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem pairEmbed_upperUnit {R : Type*} [Field R] {a b : Fin n} (hab : a ≠ b) (c : R) :
    pairEmbed hab (upperUnit c) = SpecialLinearGroup.transvection hab c :=
  pairEmbed_transvection_zero_one hab c

variable {K F : Type*} [Field K] [Field F] (ι : K →+* F)

theorem map_blockSpecialLinear_pair_eq {a b : Fin n} (hab : a ≠ b) :
    (blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))).map (SpecialLinearGroup.map ι) =
      (subfieldSL ι).map (pairEmbed hab) := by
  rw [← range_pairEmbed hab, subfieldSL, MonoidHom.range_eq_map, MonoidHom.range_eq_map,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun A => map_pairEmbed ι hab A

@[expose] def blockTwistedSubfield {a b : Fin n} (hab : a ≠ b) (ω : F) :
    Subgroup (SpecialLinearGroup (Fin n) F) :=
  (twistedSubfield ι ω).map (pairEmbed hab)

theorem blockTwistedSubfield_eq {a b : Fin n} (hab : a ≠ b) (ω : F) :
    blockTwistedSubfield ι hab ω =
      ((blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))).map
        (SpecialLinearGroup.map ι)).map
        (MulAut.conj (SpecialLinearGroup.transvection hab ω)).toMonoidHom := by
  rw [map_blockSpecialLinear_pair_eq ι hab, blockTwistedSubfield, twistedSubfield,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun A => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    pairEmbed_upperUnit]

theorem nonempty_mulEquiv_blockTwistedSubfield {a b : Fin n} (hab : a ≠ b) (ω : F) :
    Nonempty (SL(2, K) ≃* blockTwistedSubfield ι hab ω) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_twistedSubfield ι ω
  exact ⟨e.trans ((twistedSubfield ι ω).equivMapOfInjective _ (pairEmbed_injective hab))⟩

theorem transvection_one_mem_blockTwistedSubfield {a b : Fin n} (hab : a ≠ b) (ω : F) :
    SpecialLinearGroup.transvection hab (1 : F) ∈ blockTwistedSubfield ι hab ω :=
  ⟨upperUnit 1, upperUnit_one_mem_twistedSubfield ι ω, pairEmbed_upperUnit hab 1⟩

theorem blockTwistedSubfield_fixed [CharP F 2] (σ : F →+* F) (hσι : ∀ k, σ (ι k) = ι k)
    {ω : F} (hω : σ ω = ω + 1) {a b : Fin n} (hab : a ≠ b) {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ blockTwistedSubfield ι hab ω) :
    SpecialLinearGroup.transvection hab 1 * SpecialLinearGroup.map σ g *
      SpecialLinearGroup.transvection hab 1 = g := by
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  rw [map_pairEmbed, ← pairEmbed_upperUnit hab, ← map_mul, ← map_mul,
    twistedSubfield_fixed ι σ hσι hω hg₀]

theorem map_blockSpecialLinear_sup_blockTwistedSubfield [Finite K] [Finite F] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (hFK : Nat.card F = Nat.card K ^ 2) {ω : F} (hω : ω ∉ ι.range)
    {a b : Fin n} (hab : a ≠ b) :
    (blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))).map (SpecialLinearGroup.map ι) ⊔
        blockTwistedSubfield ι hab ω = blockSpecialLinear (K := F) ({a, b} : Finset (Fin n)) := by
  rw [map_blockSpecialLinear_pair_eq ι hab, blockTwistedSubfield, ← Subgroup.map_sup,
    sup_twistedSubfield_eq_top ι hq hFK hω, ← MonoidHom.range_eq_map, range_pairEmbed]

variable {K : Type*} [Field K]

@[expose] def pairEmbedProd {a b : Fin n} (hab : a ≠ b) :
    SL(2, K) × SL(2, K) →* SpecialLinearGroup (Fin n) K × SpecialLinearGroup (Fin n) K :=
  (pairEmbed hab).prodMap (pairEmbed hab)

theorem pairEmbedProd_upperUnit_pair {a b : Fin n} (hab : a ≠ b) :
    pairEmbedProd hab ((upperUnit 1, upperUnit 1) : SL(2, K) × SL(2, K)) =
      (SpecialLinearGroup.transvection hab 1, SpecialLinearGroup.transvection hab 1) := by
  change (pairEmbed hab (upperUnit 1), pairEmbed hab (upperUnit 1)) = _
  rw [pairEmbed_upperUnit]

theorem map_diag_sup_twistedDiag_eq_prod [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {a b : Fin n} (hab : a ≠ b) :
    (diagSL2 K).map (pairEmbedProd hab) ⊔ (twistedDiagSL2 K).map (pairEmbedProd hab) =
      (blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))).prod
        (blockSpecialLinear (K := K) ({a, b} : Finset (Fin n))) := by
  rw [← Subgroup.map_sup, diag_sup_twistedDiag_eq_top hq, ← MonoidHom.range_eq_map,
    pairEmbedProd, MonoidHom.range_prodMap, range_pairEmbed]

theorem mem_map_diagSL2_pairEmbedProd {a b : Fin n} (hab : a ≠ b)
    {p : SpecialLinearGroup (Fin n) K × SpecialLinearGroup (Fin n) K} :
    p ∈ (diagSL2 K).map (pairEmbedProd hab) ↔
      p.1 ∈ blockSpecialLinear ({a, b} : Finset (Fin n)) ∧ p.1 = p.2 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    replace hq := mem_diagSL2.1 hq
    refine ⟨?_, ?_⟩
    · rw [← range_pairEmbed hab]
      exact ⟨q.1, rfl⟩
    · change pairEmbed hab q.1 = pairEmbed hab q.2
      rw [hq]
  · rintro ⟨h1, h2⟩
    rw [← range_pairEmbed hab] at h1
    obtain ⟨A, hA⟩ := h1
    refine ⟨(A, A), pair_mem_diagSL2 A, Prod.ext hA ?_⟩
    rw [← h2]
    exact hA

theorem twistedDiag_pairEmbedProd_fixed [CharP K 2] {a b : Fin n} (hab : a ≠ b)
    {p : SpecialLinearGroup (Fin n) K × SpecialLinearGroup (Fin n) K}
    (hp : p ∈ (twistedDiagSL2 K).map (pairEmbedProd hab)) :
    ((SpecialLinearGroup.transvection hab 1, SpecialLinearGroup.transvection hab 1) * p *
      (SpecialLinearGroup.transvection hab 1, SpecialLinearGroup.transvection hab 1)⁻¹).swap =
      p := by
  obtain ⟨q, hq, rfl⟩ := hp
  have hswap : ∀ x : SL(2, K) × SL(2, K),
      pairEmbedProd hab x.swap = (pairEmbedProd hab x).swap := fun _ => rfl
  rw [← pairEmbedProd_upperUnit_pair hab, ← map_mul, ← map_inv, ← map_mul, ← hswap,
    twistedDiagSL2_fixed hq]

theorem transvection_pair_mem_map_twistedDiagSL2 {a b : Fin n} (hab : a ≠ b) :
    (SpecialLinearGroup.transvection hab (1 : K), SpecialLinearGroup.transvection hab (1 : K)) ∈
      (twistedDiagSL2 K).map (pairEmbedProd hab) :=
  ⟨_, upperUnit_one_pair_mem_twistedDiagSL2, pairEmbedProd_upperUnit_pair hab⟩

end Block

end CFSG.SeitzReduction.LinearPilot
