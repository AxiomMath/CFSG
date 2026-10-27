module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Levi
public import Mathlib.Algebra.CharP.Algebra

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement Pointwise Matrix

section Mobius

variable {K : Type*} [Field K]

@[expose] def projVec : Option K → Fin 2 → K
  | none => ![1, 0]
  | some z => ![z, 1]

open Classical in
@[expose] def projPt (w : Fin 2 → K) : Option K :=
  if w 1 = 0 then none else some (w 0 / w 1)

theorem projPt_projVec (z : Option K) : projPt (projVec z) = z := by
  cases z <;> simp [projPt, projVec]

theorem projVec_ne_zero (z : Option K) : projVec z ≠ 0 := by
  intro h
  cases z
  · have := congrFun h 0
    simp [projVec] at this
  · have := congrFun h 1
    simp [projVec] at this

theorem projPt_smul {c : K} (hc : c ≠ 0) (w : Fin 2 → K) : projPt (c • w) = projPt w := by
  by_cases hw : w 1 = 0
  · simp [projPt, hw]
  · have hcw : c * w 1 ≠ 0 := mul_ne_zero hc hw
    simp only [projPt, Pi.smul_apply, smul_eq_mul, hcw, hw, ↓reduceIte]
    congr 1
    field_simp

theorem exists_smul_projVec {w : Fin 2 → K} (hw : w ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ w = c • projVec (projPt w) := by
  by_cases h1 : w 1 = 0
  · have h0 : w 0 ≠ 0 := fun h0 => hw (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨w 0, h0, funext fun i => ?_⟩
    fin_cases i <;> simp [projPt, projVec, h1]
  · refine ⟨w 1, h1, funext fun i => ?_⟩
    fin_cases i <;> simp [projPt, projVec, h1]
    field_simp

@[expose] def mob (A : Matrix (Fin 2) (Fin 2) K) (z : Option K) : Option K :=
  projPt (A *ᵥ projVec z)

theorem SL_mulVec_ne_zero (A : Matrix.SpecialLinearGroup (Fin 2) K) {w : Fin 2 → K}
    (hw : w ≠ 0) : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w ≠ 0 := by
  intro h
  apply hw
  have := congrArg (fun v =>
    ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
  rwa [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec] at this

theorem mob_mul (A B : Matrix.SpecialLinearGroup (Fin 2) K) (z : Option K) :
    mob ((A * B : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) z =
      mob (A : Matrix (Fin 2) (Fin 2) K) (mob (B : Matrix (Fin 2) (Fin 2) K) z) := by
  obtain ⟨c, hc, hcw⟩ := exists_smul_projVec (SL_mulVec_ne_zero B (projVec_ne_zero z))
  rw [mob, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hcw,
    Matrix.mulVec_smul, projPt_smul hc]
  rfl

theorem mob_one (z : Option K) : mob (1 : Matrix (Fin 2) (Fin 2) K) z = z := by
  rw [mob, Matrix.one_mulVec, projPt_projVec]

theorem projPt_eq_none_iff {w : Fin 2 → K} : projPt w = none ↔ w 1 = 0 := by
  unfold projPt
  split_ifs with h <;> simp [h]

theorem projPt_eq_some_iff {w : Fin 2 → K} {z : K} :
    projPt w = some z ↔ w 1 ≠ 0 ∧ w 0 / w 1 = z := by
  unfold projPt
  split_ifs with h <;> simp [h]

theorem mob_none (A : Matrix (Fin 2) (Fin 2) K) : mob A none = projPt ![A 0 0, A 1 0] := by
  unfold mob
  congr 1
  funext i
  fin_cases i <;> simp [projVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mob_some (A : Matrix (Fin 2) (Fin 2) K) (z : K) :
    mob A (some z) = projPt ![A 0 0 * z + A 0 1, A 1 0 * z + A 1 1] := by
  unfold mob
  congr 1
  funext i
  fin_cases i <;> simp [projVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eq_of_mob_eq [CharP K 2] {A B : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : ∀ z, mob (A : Matrix (Fin 2) (Fin 2) K) z = mob (B : Matrix (Fin 2) (Fin 2) K) z) :
    A = B := by
  set C := B⁻¹ * A with hC
  have hCz : ∀ z, mob (C : Matrix (Fin 2) (Fin 2) K) z = z := fun z => by
    rw [hC, mob_mul, h, ← mob_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mob_one]
  set c := (C : Matrix (Fin 2) (Fin 2) K) with hc
  have hinf := hCz none
  have h0 := hCz (some 0)
  have h1 := hCz (some 1)
  rw [mob_none, projPt_eq_none_iff] at hinf
  rw [mob_some, projPt_eq_some_iff] at h0 h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_add] at hinf h0 h1
  obtain ⟨e11, e01⟩ := h0
  have e01' : c 0 1 = 0 := (div_eq_zero_iff.1 e01).resolve_right e11
  rw [hinf, e01', add_zero, zero_add, div_eq_one_iff_eq e11] at h1
  have hdet := C.2
  rw [Matrix.det_fin_two, ← hc, hinf, mul_zero, sub_zero, h1.2] at hdet
  have e00 : c 1 1 = 1 := by
    have h2 : (c 1 1 + 1) * (c 1 1 + 1) = 0 := by
      rw [add_mul_self_eq, hdet, mul_one, CharTwo.two_eq_zero, zero_mul, add_zero, mul_one,
        CharTwo.add_self_eq_zero]
    have := mul_self_eq_zero.1 h2
    rwa [CharTwo.add_eq_zero] at this
  have hC1 : C = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hc, hinf, e01', e00, h1.2]
  rw [hC, inv_mul_eq_one] at hC1
  exact hC1.symm

end Mobius

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem commutatorElement_x₁_mem {T : Subgroup X} (hT : d.leviShort ≤ normalizer (T : Set X))
    {t : X} (ht : t ∈ T) (b : d.Γ) : ⁅t, d.x₁ b⁆ ∈ T := by
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine mul_mem ht ?_
  rw [← mul_assoc]
  exact (mem_normalizer_iff.1 (hT (d.x₁_mem_leviShort b)) _).1 (inv_mem ht)

theorem exists_mem_Y_of_mem_W {T : Subgroup X} (hT : d.leviShort ≤ normalizer (T : Set X))
    {t : X} (ht : t ∈ T) (htW : t ∈ d.W) (htV : t ∉ d.V) : ∃ y ∈ T, y ∈ d.Y ∧ y ∉ d.V := by
  by_cases htY : t ∈ d.Y
  · exact ⟨t, ht, htY, htV⟩
  by_contra h
  push Not at h
  refine htY (d.mem_Y_of_forall_commutatorElement_x₁_mem_V htW fun b => ?_)
  refine h _ (d.commutatorElement_x₁_mem hT ht b) ?_
  exact commutatorElement_mem_comm.1
    (d.commutator_S_W (commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ b)) htW))

theorem exists_mem_W_of_mem_F {T : Subgroup X} (hT : d.leviShort ≤ normalizer (T : Set X))
    {t : X} (ht : t ∈ T) (htF : t ∈ d.F) (htV : t ∉ d.V) : ∃ w ∈ T, w ∈ d.W ∧ w ∉ d.V := by
  by_cases htW : t ∈ d.W
  · exact ⟨t, ht, htW, htV⟩
  by_contra h
  push Not at h
  refine htW (d.mem_W_of_forall_commutatorElement_x₁_mem_Y htF fun b => ?_)
  have hc : ⁅t, d.x₁ b⁆ ∈ d.W := commutatorElement_mem_comm.1
    (d.commutator_S_F (commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ b)) htF))
  by_contra hY
  exact (fun hV => hY (d.V_le_Y hV)) (h _ (d.commutatorElement_x₁_mem hT ht b) hc)

theorem exists_mem_F_of_mem_D {T : Subgroup X} (hT : d.leviShort ≤ normalizer (T : Set X))
    {t : X} (ht : t ∈ T) (htD : t ∈ d.D) (htV : t ∉ d.V) : ∃ f ∈ T, f ∈ d.F ∧ f ∉ d.V := by
  by_cases htF : t ∈ d.F
  · exact ⟨t, ht, htF, htV⟩
  refine ⟨⁅t, d.x₁ 1⁆, d.commutatorElement_x₁_mem hT ht 1, commutatorElement_mem_comm.1
    (d.commutator_S_D (commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ 1)) htD)), ?_⟩
  intro hV
  exact htF (d.mem_F_of_commutatorElement_x₁_mem_W htD (d.Y_le_W (d.V_le_Y hV)))

theorem exists_J₆_conj_x₅ {c c' : d.Γ₀} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ t ∈ d.J₆, t * d.x₅ c * t⁻¹ = d.x₅ c' := by
  obtain ⟨β, hβ⟩ := d.nmUnits_surjective (Units.mk0 (c' / c) (div_ne_zero hc' hc))
  refine ⟨d.hBCD β, by rw [d.J₆_eq_range_hBCD]; exact ⟨β, rfl⟩, ?_⟩
  rw [hBCD_apply, d.torus_x₅]
  congr 1
  have h1 : d.nm (β : d.Γ) = c' / c := congrArg Units.val hβ
  have h2 : d.nm ((β ^ 2 : d.Γˣ) : d.Γ) = d.nm (β : d.Γ) * d.nm (β : d.Γ) := by
    rw [Units.val_pow_eq_pow_val, sq, d.nm_mul]
  simp only [Units.val_inv_eq_inv_val, coe_nmUnits, h2, h1]
  field_simp

theorem exists_σ_mul_σσ_div_eq (γ : d.Γˣ) :
    ∃ β : d.Γˣ, d.σUnits β * d.σUnits (d.σUnits β) * β⁻¹ = γ := by
  let f : d.Γˣ →* d.Γˣ := d.σUnits * d.σUnits.comp d.σUnits * invMonoidHom
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 fun β hβ => ?_
    have e1 : d.σ (β : d.Γ) * d.σ (d.σ (β : d.Γ)) = β := by
      have h := congrArg Units.val hβ
      simp only [f, MonoidHom.mul_apply, MonoidHom.comp_apply, invMonoidHom_apply,
        Units.val_mul, coe_σUnits, Units.val_inv_eq_inv_val, Units.val_one] at h
      have hb : (β : d.Γ) ≠ 0 := β.ne_zero
      field_simp at h
      exact h
    have e2 : d.σ (d.σ (β : d.Γ)) * β = d.σ β := by
      have h := congrArg d.σ e1
      rwa [map_mul, d.σ_cube] at h
    have hσσ : d.σ (d.σ (β : d.Γ)) * d.σ (d.σ (β : d.Γ)) = 1 := by
      have hb : (β : d.Γ) ≠ 0 := β.ne_zero
      apply mul_right_cancel₀ hb
      calc d.σ (d.σ (β : d.Γ)) * d.σ (d.σ (β : d.Γ)) * β
          = d.σ (d.σ (β : d.Γ)) * (d.σ (d.σ (β : d.Γ)) * β) := by ring
        _ = d.σ (d.σ (β : d.Γ)) * d.σ β := by rw [e2]
        _ = 1 * β := by rw [mul_comm, e1, one_mul]
    have h3 : d.σ (d.σ (β : d.Γ)) = 1 := d.sq_injective (by rw [sq, hσσ, one_pow])
    refine Units.ext ?_
    rw [Units.val_one, ← d.σ_cube (β : d.Γ), h3, map_one]
  exact Finite.injective_iff_surjective.1 hinj γ

theorem exists_J₆_conj_x₄ {c c' : d.Γ} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ t ∈ d.J₆, t * d.x₄ c * t⁻¹ = d.x₄ c' := by
  obtain ⟨β, hβ⟩ := d.exists_σ_mul_σσ_div_eq (Units.mk0 (c' / c) (div_ne_zero hc' hc))
  refine ⟨d.hBCD β, by rw [d.J₆_eq_range_hBCD]; exact ⟨β, rfl⟩, ?_⟩
  rw [hBCD_apply, d.torus_x₄]
  congr 1
  have h1 : d.σ (β : d.Γ) * d.σ (d.σ (β : d.Γ)) * (β : d.Γ)⁻¹ = c' / c := by
    have := congrArg Units.val hβ
    simpa [coe_σUnits] using this
  have hb : (β : d.Γ) ≠ 0 := β.ne_zero
  have hσb : d.σ (β : d.Γ) ≠ 0 := (map_ne_zero d.σ).2 hb
  have hσσb : d.σ (d.σ (β : d.Γ)) ≠ 0 := (map_ne_zero d.σ).2 hσb
  rw [eq_div_iff hc] at h1
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_pow]
  push_cast
  rw [coe_coe_nmUnits, ← h1]
  field_simp

theorem commutatorElement_mul_right_eq_D4 {G : Type*} [Group G] (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem leviShort_irreducible_D_mod_V {T : Subgroup X} (hVT : d.V ≤ T) (hTD : T ≤ d.D)
    (hT : d.leviShort ≤ normalizer (T : Set X)) : T = d.V ∨ T = d.D := by
  by_cases hTV : T ≤ d.V
  · exact Or.inl (le_antisymm hTV hVT)
  right
  obtain ⟨t, ht, htV⟩ := Set.not_subset.1 hTV
  obtain ⟨f, hf, hfF, hfV⟩ := d.exists_mem_F_of_mem_D hT ht (hTD ht) htV
  obtain ⟨w, hw, hwW, hwV⟩ := d.exists_mem_W_of_mem_F hT hf hfF hfV
  obtain ⟨y, hy, hyY, hyV⟩ := d.exists_mem_Y_of_mem_W hT hw hwW hwV
  obtain ⟨c, n, hn, rfl⟩ := d.mem_Y_iff.1 hyY
  have hc : c ≠ 0 := by
    rintro rfl
    rw [d.x₅_zero, one_mul] at hyV
    exact hyV hn
  have hx₅ : d.x₅ c ∈ T := by
    have := mul_mem hy (inv_mem (hVT hn))
    rwa [mul_inv_cancel_right] at this
  have hconj : ∀ g ∈ d.leviShort, ∀ z ∈ T, g * z * g⁻¹ ∈ T := fun g hg z hz =>
    (mem_normalizer_iff.1 (hT hg) z).1 hz
  have hU₅ : d.U₅ ≤ T := by
    rintro _ ⟨c', rfl⟩
    by_cases hc' : c' = 0
    · rw [hc', d.x₅_zero]
      exact one_mem _
    obtain ⟨s, hs, hsc⟩ := d.exists_J₆_conj_x₅ hc hc'
    rw [← hsc]
    exact hconj _ (d.J₆_le_leviShort hs) _ hx₅
  have hU₂ : d.U₂ ≤ T := by
    rintro _ ⟨a, rfl⟩
    rw [← d.u_conj_x₅ a]
    exact hconj _ d.u_mem_leviShort _ (hU₅ (d.x₅_mem_U₅ a))
  have hY : d.Y ≤ T := sup_le hU₅ hVT
  have h34 : d.x₃ 1 * d.x₄ 1 ∈ T := by
    have h := hconj _ (d.x₁_mem_leviShort 1) _ (hU₂ (d.x₂_mem_U₂ 1))
    have h' : ⁅d.x₁ 1, d.x₂ 1⁆ ∈ T := by
      rw [commutatorElement_def]
      exact mul_mem h (inv_mem (hU₂ (d.x₂_mem_U₂ 1)))
    rw [d.comm₁₂] at h'
    have h'' := mul_mem h' (inv_mem (hY (d.x₅_mem_Y (d.nm 1 * 1))))
    rw [mul_inv_cancel_right] at h''
    simpa using h''
  obtain ⟨γ, hγ⟩ := d.exists_σ_ne
  have hε : d.σ γ + d.σ (d.σ γ) ≠ 0 := fun h0 =>
    hγ (d.σ.injective (CharTwo.add_eq_zero.1 h0).symm)
  have hx₄ : d.x₄ (d.σ γ + d.σ (d.σ γ)) ∈ T := by
    have hz : ⁅d.x₁ γ, d.x₃ 1 * d.x₄ 1⁆ ∈ T := by
      rw [commutatorElement_def]
      exact mul_mem (hconj _ (d.x₁_mem_leviShort γ) _ h34) (inv_mem h34)
    have e3 : ∀ e, d.x₃ 1 * d.x₅ e * (d.x₃ 1)⁻¹ = d.x₅ e := fun e => by
      rw [(d.commute₃₅ 1 e).eq, mul_inv_cancel_right]
    rw [commutatorElement_mul_right_eq_D4, d.comm₁₃, d.comm₁₄, e3] at hz
    simp only [map_one, mul_one] at hz
    obtain ⟨a5, a6, a5', hz'⟩ : ∃ a5 a6 a5', d.x₄ (d.σ γ + d.σ (d.σ γ)) * d.x₅ a5 * d.x₆ a6 *
        d.x₅ a5' ∈ T := ⟨_, _, _, hz⟩
    have hrest : d.x₅ a5 * d.x₆ a6 * d.x₅ a5' ∈ T :=
      mul_mem (mul_mem (hY (d.x₅_mem_Y _)) (hVT (d.x₆_mem_V _))) (hY (d.x₅_mem_Y _))
    have := mul_mem hz' (inv_mem hrest)
    rwa [show d.x₄ (d.σ γ + d.σ (d.σ γ)) * d.x₅ a5 * d.x₆ a6 * d.x₅ a5' *
      (d.x₅ a5 * d.x₆ a6 * d.x₅ a5')⁻¹ = d.x₄ (d.σ γ + d.σ (d.σ γ)) by group] at this
  have hU₄ : d.U₄ ≤ T := by
    rintro _ ⟨c', rfl⟩
    by_cases hc' : c' = 0
    · rw [hc', d.x₄_zero]
      exact one_mem _
    obtain ⟨s, hs, hsc⟩ := d.exists_J₆_conj_x₄ hε hc'
    rw [← hsc]
    exact hconj _ (d.J₆_le_leviShort hs) _ hx₄
  have hU₃ : d.U₃ ≤ T := by
    rintro _ ⟨a, rfl⟩
    rw [← d.u_conj_x₄_eq_x₃ a]
    exact hconj _ d.u_mem_leviShort _ (hU₄ (d.x₄_mem_U₄ a))
  exact le_antisymm hTD (sup_le hU₂ (sup_le hU₃ (sup_le hU₄ hY)))

@[expose] def yv (w : Fin 2 → d.Γ₀) : X := d.x₅ (w 0) * d.x₆ (w 1)

theorem yv_add (w w' : Fin 2 → d.Γ₀) : d.yv (w + w') = d.yv w * d.yv w' := by
  simp only [yv, Pi.add_apply, d.x₅_add, d.x₆_add]
  calc d.x₅ (w 0) * d.x₅ (w' 0) * (d.x₆ (w 1) * d.x₆ (w' 1))
      = d.x₅ (w 0) * (d.x₅ (w' 0) * d.x₆ (w 1)) * d.x₆ (w' 1) := by group
    _ = d.x₅ (w 0) * (d.x₆ (w 1) * d.x₅ (w' 0)) * d.x₆ (w' 1) := by
        rw [(d.commute₅₆ (w' 0) (w 1)).eq]
    _ = d.x₅ (w 0) * d.x₆ (w 1) * (d.x₅ (w' 0) * d.x₆ (w' 1)) := by group

theorem yv_injective : Function.Injective d.yv := by
  intro w w' h
  have e : d.nf (0, 0, 0, 0, w 0, w 1) = d.nf (0, 0, 0, 0, w' 0, w' 1) := by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, one_mul]
    exact h
  have e' := d.nf_injective e
  simp only [Prod.mk.injEq, true_and] at e'
  funext i
  fin_cases i
  · exact e'.1
  · exact e'.2

theorem range_yv : Set.range d.yv = d.Y := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)
  · intro hg
    obtain ⟨a, _, ⟨b, rfl⟩, rfl⟩ := d.mem_Y_iff.1 hg
    exact ⟨![a, b], rfl⟩

theorem x₂_conj_x₅ (a c : d.Γ₀) : d.x₂ a * d.x₅ c * (d.x₂ a)⁻¹ = d.x₅ c * d.x₆ (a * c) := by
  rw [conj_eq_commutatorElement_mul, d.comm₂₅, (d.commute₅₆ c (a * c)).eq]

theorem neg_one_Γ₀ : (-1 : d.Γ₀) = 1 :=
  Subtype.ext (by simp [CharTwo.neg_eq])

@[expose] def slX₂ (a : d.Γ₀) : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slV : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, d.neg_one_Γ₀]⟩

theorem x₂_conj_yv (a : d.Γ₀) (w : Fin 2 → d.Γ₀) :
    d.x₂ a * d.yv w * (d.x₂ a)⁻¹ = d.yv ((d.slX₂ a : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) := by
  have h6 : d.x₂ a * d.x₆ (w 1) * (d.x₂ a)⁻¹ = d.x₆ (w 1) := by
    rw [(d.commute₂₆ a (w 1)).eq, mul_inv_cancel_right]
  calc d.x₂ a * d.yv w * (d.x₂ a)⁻¹
      = (d.x₂ a * d.x₅ (w 0) * (d.x₂ a)⁻¹) * (d.x₂ a * d.x₆ (w 1) * (d.x₂ a)⁻¹) := by
        simp only [yv]; group
    _ = d.x₅ (w 0) * d.x₆ (a * w 0) * d.x₆ (w 1) := by rw [d.x₂_conj_x₅, h6]
    _ = d.yv ((d.slX₂ a : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) := by
        simp [yv, slX₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_assoc, d.x₆_add]

theorem v_conj_yv (w : Fin 2 → d.Γ₀) :
    d.v * d.yv w * d.v⁻¹ = d.yv ((d.slV : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) := by
  calc d.v * d.yv w * d.v⁻¹ = (d.v * d.x₅ (w 0) * d.v⁻¹) * (d.v * d.x₆ (w 1) * d.v⁻¹) := by
        simp only [yv]; group
    _ = d.x₆ (w 0) * d.x₅ (w 1) := by rw [d.v_conj_x₅, d.v_conj_x₆]
    _ = d.yv ((d.slV : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) := by
        rw [← (d.commute₅₆ (w 1) (w 0)).eq]
        simp [yv, slV, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[expose] def slOnY : Subgroup X where
  carrier := {g | ∃ A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀,
    ∀ w, g * d.yv w * g⁻¹ = d.yv ((A : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)}
  mul_mem' := by
    rintro g g' ⟨A, hA⟩ ⟨A', hA'⟩
    refine ⟨A * A', fun w => ?_⟩
    rw [show g * g' * d.yv w * (g * g')⁻¹ = g * (g' * d.yv w * g'⁻¹) * g⁻¹ by group, hA', hA,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  one_mem' := ⟨1, fun w => by simp⟩
  inv_mem' := by
    rintro g ⟨A, hA⟩
    refine ⟨A⁻¹, fun w => ?_⟩
    have h := hA ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) *ᵥ w)
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
    rw [inv_inv, ← h]
    group

theorem leviLong_le_slOnY : d.leviLong ≤ d.slOnY := by
  rw [leviLong, closure_le]
  rintro g (⟨a, rfl⟩ | rfl)
  · exact ⟨d.slX₂ a, d.x₂_conj_yv a⟩
  · exact ⟨d.slV, d.v_conj_yv⟩

theorem sl_eq_of_yv {A B : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀}
    (h : ∀ w, d.yv ((A : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) =
      d.yv ((B : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)) : A = B := by
  ext i j
  have := congrFun (d.yv_injective (h (Pi.single j 1))) i
  simpa [Matrix.mulVec_single_one] using this

@[expose] def slOfLeviLong (g : d.leviLong) : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ :=
  Classical.choose (d.leviLong_le_slOnY g.2)

theorem slOfLeviLong_spec (g : d.leviLong) (w : Fin 2 → d.Γ₀) :
    (g : X) * d.yv w * (g : X)⁻¹ =
      d.yv ((d.slOfLeviLong g : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) :=
  Classical.choose_spec (d.leviLong_le_slOnY g.2) w

@[expose] def leviLongRep : d.leviLong →* Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ where
  toFun := d.slOfLeviLong
  map_one' := d.sl_eq_of_yv fun w => by
    rw [← d.slOfLeviLong_spec, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    simp
  map_mul' g g' := d.sl_eq_of_yv fun w => by
    rw [← d.slOfLeviLong_spec, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      ← d.slOfLeviLong_spec, ← d.slOfLeviLong_spec, Subgroup.coe_mul]
    group

theorem leviLongRep_spec (g : d.leviLong) (w : Fin 2 → d.Γ₀) :
    (g : X) * d.yv w * (g : X)⁻¹ =
      d.yv ((d.leviLongRep g : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) :=
  d.slOfLeviLong_spec g w

theorem hA_conj_x₅ (b : (d.Γ₀)ˣ) (c : d.Γ₀) :
    d.hA b * d.x₅ c * (d.hA b)⁻¹ = d.x₅ (((b⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) * c) := by
  rw [hA_apply, d.torus_x₅]
  congr 1
  have h : d.nm ((d.unitsIncl b⁻¹ : d.Γˣ) : d.Γ) = ((b⁻¹ ^ 3 : (d.Γ₀)ˣ) : d.Γ₀) :=
    congrArg Units.val (d.nmUnits_unitsIncl b⁻¹)
  change ((b ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) * d.nm ((d.unitsIncl b⁻¹ : d.Γˣ) : d.Γ) * c = _
  rw [h, ← Units.val_mul]
  congr 2
  group

theorem hA_conj_x₆ (b : (d.Γ₀)ˣ) (c : d.Γ₀) :
    d.hA b * d.x₆ c * (d.hA b)⁻¹ = d.x₆ ((b : d.Γ₀) * c) := by
  rw [hA_apply, d.torus_x₆]
  congr 1
  have h : d.nm ((d.unitsIncl b⁻¹ : d.Γˣ) : d.Γ) = ((b⁻¹ ^ 3 : (d.Γ₀)ˣ) : d.Γ₀) :=
    congrArg Units.val (d.nmUnits_unitsIncl b⁻¹)
  change ((b ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) * ((b ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) *
    d.nm ((d.unitsIncl b⁻¹ : d.Γˣ) : d.Γ) * c = _
  rw [h, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

theorem eq_one_of_mem_leviLong_of_conj_yv {g : X} (hg : g ∈ d.leviLong)
    (h : ∀ w, g * d.yv w * g⁻¹ = d.yv w) : g = 1 := by
  have hy6 : d.yv ![0, 1] = d.x₆ 1 := by simp [yv, d.x₅_zero]
  have hy5 : d.yv ![1, 0] = d.x₅ 1 := by simp [yv, d.x₆_zero]
  rcases d.mem_leviLong_iff.1 hg with ⟨x, ⟨a, rfl⟩, t, ht, rfl⟩ | ⟨x, ⟨a, rfl⟩, t, ht, y, ⟨b, rfl⟩,
    rfl⟩
  · rw [d.J₄_eq_range_hA] at ht
    obtain ⟨β, rfl⟩ := ht
    have e6 := h ![0, 1]
    rw [hy6, show d.x₂ a * d.hA β * d.x₆ 1 * (d.x₂ a * d.hA β)⁻¹ =
      d.x₂ a * (d.hA β * d.x₆ 1 * (d.hA β)⁻¹) * (d.x₂ a)⁻¹ by group, d.hA_conj_x₆,
      (d.commute₂₆ a _).eq, mul_inv_cancel_right] at e6
    have hβ : β = 1 := Units.ext (by simpa using d.x₆_injective e6)
    subst hβ
    rw [map_one, mul_one] at h ⊢
    have e5 := h ![1, 0]
    rw [hy5, d.x₂_conj_x₅, mul_one] at e5
    have ha : a = 0 := by
      have := mul_left_cancel (e5.trans (mul_one _).symm)
      exact d.x₆_eq_one_iff.1 this
    rw [ha, d.x₂_zero]
  · exfalso
    rw [d.J₄_eq_range_hA] at ht
    obtain ⟨β, rfl⟩ := ht
    have e6 := h ![0, 1]
    have hv6 : d.v * d.x₆ 1 * d.v⁻¹ = d.x₅ 1 := d.v_conj_x₆ 1
    rw [hy6, show d.x₂ a * d.hA β * d.v * d.x₂ b * d.x₆ 1 * (d.x₂ a * d.hA β * d.v * d.x₂ b)⁻¹ =
      d.x₂ a * (d.hA β * (d.v * (d.x₂ b * d.x₆ 1 * (d.x₂ b)⁻¹) * d.v⁻¹) * (d.hA β)⁻¹) *
        (d.x₂ a)⁻¹ by group, (d.commute₂₆ b _).eq, mul_inv_cancel_right, hv6, d.hA_conj_x₅,
      d.x₂_conj_x₅] at e6
    have e' : d.nf (0, 0, 0, 0, ((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) * 1,
        a * (((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) * 1)) = d.nf (0, 0, 0, 0, 0, 1) := by
      simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero, one_mul]
      exact e6
    have := congrArg (fun p => p.2.2.2.2.1) (d.nf_injective e')
    simp only [mul_one] at this
    exact (β⁻¹).ne_zero this

theorem card_SL_two_D4 (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have := Fintype.ofFinite K
  have hK : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card]
  have h1 : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (Fintype.card K ^ 2 - 1) * (Fintype.card K * (Fintype.card K - 1)) =
    (Fintype.card K * (Fintype.card K ^ 2 - 1)) * (Fintype.card K - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

theorem card_SL_Γ₀ : Nat.card (Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) = q * (q ^ 2 - 1) := by
  rw [card_SL_two_D4, d.card_Γ₀]

theorem leviLongRep_bijective : Function.Bijective d.leviLongRep := by
  have := d.finite
  have hinj : Function.Injective d.leviLongRep := by
    refine (injective_iff_map_eq_one _).2 fun g hg => Subtype.ext ?_
    refine d.eq_one_of_mem_leviLong_of_conj_yv g.2 fun w => ?_
    rw [d.leviLongRep_spec, hg, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  exact (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [d.card_leviLong, d.card_SL_Γ₀]⟩

@[expose] def leviLongEquiv : d.leviLong ≃* Matrix.SpecialLinearGroup (Fin 2) d.Γ₀ :=
  MulEquiv.ofBijective d.leviLongRep d.leviLongRep_bijective

theorem leviLongEquiv_apply (g : d.leviLong) : d.leviLongEquiv g = d.leviLongRep g :=
  rfl

theorem yamada_three_ten_Y : Nat.card d.Γ₀ = q ∧
    (∀ (g : d.leviLong) (w : Fin 2 → d.Γ₀), (g : X) * d.yv w * (g : X)⁻¹ =
      d.yv ((d.leviLongEquiv g : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)) ∧
    (∀ w w', d.yv (w + w') = d.yv w * d.yv w') ∧ Function.Injective d.yv ∧
    Set.range d.yv = d.Y :=
  ⟨d.card_Γ₀, fun g w => d.leviLongRep_spec g w, d.yv_add, d.yv_injective, d.range_yv⟩

@[expose] def mv (z : Fin 2 → d.Γ) : X := d.x₁ (z 0) * d.x₃ (z 1)

@[expose] def toΓ (A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) : Matrix (Fin 2) (Fin 2) d.Γ :=
  (A : Matrix (Fin 2) (Fin 2) d.Γ₀).map d.Γ₀.subtype

theorem toΓ_mul (A B : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) :
    d.toΓ (A * B) = d.toΓ A * d.toΓ B := by
  rw [toΓ, toΓ, toΓ, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

theorem toΓ_one : d.toΓ 1 = 1 := by
  rw [toΓ, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem x₃_mul_x₁_mem (s t : d.Γ) : (d.x₁ t * d.x₃ s)⁻¹ * (d.x₃ s * d.x₁ t) ∈ d.W := by
  have h := commutatorElement_mem_comm.1 (d.comm₁₃_mem_W t s)
  rw [commutatorElement_def, d.x₃_inv, d.x₁_inv] at h
  rw [mul_inv_rev, d.x₁_inv, d.x₃_inv]
  simpa [mul_assoc] using h

theorem x₂_conj_x₁ (a : d.Γ₀) (t : d.Γ) :
    d.x₂ a * d.x₁ t * (d.x₂ a)⁻¹ = d.x₁ t * ⁅d.x₁ t, d.x₂ a⁆ := by
  calc d.x₂ a * d.x₁ t * (d.x₂ a)⁻¹ = (d.x₁ t * d.x₁ t) * d.x₂ a * d.x₁ t * (d.x₂ a)⁻¹ := by
        rw [d.x₁_mul_self, one_mul]
    _ = d.x₁ t * (d.x₁ t * d.x₂ a * d.x₁ t * (d.x₂ a)⁻¹) := by group
    _ = d.x₁ t * ⁅d.x₁ t, d.x₂ a⁆ := by rw [commutatorElement_def, d.x₁_inv]

@[expose] def slOnYM : Subgroup X where
  carrier := {g | g ∈ normalizer (d.W : Set X) ∧ ∃ A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀,
    (∀ w, g * d.yv w * g⁻¹ = d.yv ((A : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)) ∧
    ∀ z, ∃ n ∈ d.W, g * d.mv z * g⁻¹ = d.mv (d.toΓ A *ᵥ z) * n}
  mul_mem' := by
    rintro g g' ⟨hgW, A, hA, hA'⟩ ⟨hg'W, B, hB, hB'⟩
    refine ⟨mul_mem hgW hg'W, A * B, fun w => ?_, fun z => ?_⟩
    · rw [show g * g' * d.yv w * (g * g')⁻¹ = g * (g' * d.yv w * g'⁻¹) * g⁻¹ by group, hB, hA,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
    · obtain ⟨n, hn, hz⟩ := hB' z
      obtain ⟨n', hn', hz'⟩ := hA' (d.toΓ B *ᵥ z)
      refine ⟨n' * (g * n * g⁻¹), mul_mem hn' ((mem_normalizer_iff.1 hgW n).1 hn), ?_⟩
      rw [show g * g' * d.mv z * (g * g')⁻¹ = g * (g' * d.mv z * g'⁻¹) * g⁻¹ by group, hz,
        show g * (d.mv (d.toΓ B *ᵥ z) * n) * g⁻¹ =
          g * d.mv (d.toΓ B *ᵥ z) * g⁻¹ * (g * n * g⁻¹) by group, hz', d.toΓ_mul,
        ← Matrix.mulVec_mulVec, mul_assoc]
  one_mem' := ⟨one_mem _, 1, fun w => by simp, fun z => ⟨1, one_mem _, by simp [d.toΓ_one]⟩⟩
  inv_mem' := by
    rintro g ⟨hgW, A, hA, hA'⟩
    refine ⟨inv_mem hgW, A⁻¹, fun w => ?_, fun z => ?_⟩
    · have h := hA ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) *ᵥ w)
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
      rw [inv_inv, ← h]
      group
    · obtain ⟨n, hn, h⟩ := hA' (d.toΓ A⁻¹ *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← d.toΓ_mul, mul_inv_cancel, d.toΓ_one, Matrix.one_mulVec] at h
      refine ⟨g⁻¹ * n⁻¹ * g, ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem hgW) n⁻¹).1 (inv_mem hn)
        rwa [inv_inv] at this
      · rw [inv_inv, show d.mv z = g * d.mv (d.toΓ A⁻¹ *ᵥ z) * g⁻¹ * n⁻¹ by rw [h]; group]
        group

theorem x₂_conj_mv (a : d.Γ₀) (z : Fin 2 → d.Γ) :
    ∃ n ∈ d.W, d.x₂ a * d.mv z * (d.x₂ a)⁻¹ = d.mv (d.toΓ (d.slX₂ a) *ᵥ z) * n := by
  have hWS := d.S_le_normalizer_W
  set n₀ := d.x₄ (d.σ (z 0) * d.σ (d.σ (z 0)) * (a : d.Γ)) * d.x₅ (d.nm (z 0) * a) with hn₀
  have hn₀W : n₀ ∈ d.W := mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)
  refine ⟨(d.x₃ (z 1))⁻¹ * n₀ * d.x₃ (z 1), ?_, ?_⟩
  · have := (mem_normalizer_iff.1 (hWS (inv_mem (d.U₃_le_S (d.x₃_mem_U₃ (z 1))))) _).1 hn₀W
    rwa [inv_inv] at this
  · have h3 : d.x₂ a * d.x₃ (z 1) * (d.x₂ a)⁻¹ = d.x₃ (z 1) := by
      rw [(d.commute₂₃ a (z 1)).eq, mul_inv_cancel_right]
    have e : d.mv (d.toΓ (d.slX₂ a) *ᵥ z) = d.x₁ (z 0) * (d.x₃ ((z 0) * a) * d.x₃ (z 1)) := by
      rw [← d.x₃_add]
      simp [mv, toΓ, slX₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    rw [e, show d.x₂ a * d.mv z * (d.x₂ a)⁻¹ =
      (d.x₂ a * d.x₁ (z 0) * (d.x₂ a)⁻¹) * (d.x₂ a * d.x₃ (z 1) * (d.x₂ a)⁻¹) by
      simp only [mv]; group, h3, d.x₂_conj_x₁, d.comm₁₂, hn₀]
    group

theorem v_conj_mv (z : Fin 2 → d.Γ) :
    ∃ n ∈ d.W, d.v * d.mv z * d.v⁻¹ = d.mv (d.toΓ d.slV *ᵥ z) * n := by
  refine ⟨_, d.x₃_mul_x₁_mem (z 0) (z 1), ?_⟩
  have e : d.mv (d.toΓ d.slV *ᵥ z) = d.x₁ (z 1) * d.x₃ (z 0) := by
    simp [mv, toΓ, slV, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e, show d.v * d.mv z * d.v⁻¹ = (d.v * d.x₁ (z 0) * d.v⁻¹) * (d.v * d.x₃ (z 1) * d.v⁻¹) by
    simp only [mv]; group, d.v_conj_x₁, d.v_conj_x₃, mul_inv_cancel_left]

theorem leviLong_le_slOnYM : d.leviLong ≤ d.slOnYM := by
  rw [leviLong, closure_le]
  rintro g (⟨a, rfl⟩ | rfl)
  · exact ⟨d.S_le_normalizer_W (d.U₂_le_S (d.x₂_mem_U₂ a)), d.slX₂ a, d.x₂_conj_yv a,
      d.x₂_conj_mv a⟩
  · exact ⟨d.v_mem_normalizer_W_of_Y, d.slV, d.v_conj_yv, d.v_conj_mv⟩

theorem leviLongRep_mv (g : d.leviLong) (z : Fin 2 → d.Γ) :
    ∃ n ∈ d.W, (g : X) * d.mv z * (g : X)⁻¹ = d.mv (d.toΓ (d.leviLongRep g) *ᵥ z) * n := by
  obtain ⟨-, A, hA, hA'⟩ := d.leviLong_le_slOnYM g.2
  have hAρ : A = d.leviLongRep g :=
    d.sl_eq_of_yv fun w => by rw [← hA, ← d.leviLongRep_spec]
  rw [← hAρ]
  exact hA' z

theorem exists_mv_of_mem_M {g : X} (hg : g ∈ d.M) : ∃ z, ∃ n ∈ d.W, d.mv z * n = g := by
  obtain ⟨a₁, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_M_coords hg
  refine ⟨![a₁, a₃], d.x₄ a₄ * d.x₅ a₅ * d.x₆ a₆,
    mul_mem (mul_mem (d.x₄_mem_W a₄) (d.x₅_mem_W a₅)) (d.x₆_mem_W a₆), ?_⟩
  simp only [mv, nf_apply, d.x₂_zero, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_assoc]

theorem eq_of_mv_mul_eq {z z' : Fin 2 → d.Γ} {n n' : X} (hn : n ∈ d.W) (hn' : n' ∈ d.W)
    (h : d.mv z * n = d.mv z' * n') : z = z' := by
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hn
  obtain ⟨b₄, b₅, b₆, rfl⟩ := d.mem_W_coords hn'
  have e : d.nf (z 0, 0, z 1, a₄, a₅, a₆) = d.nf (z' 0, 0, z' 1, b₄, b₅, b₆) := by
    simp only [mv, nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, mul_one, one_mul] at h ⊢
    simpa only [mul_assoc] using h
  have e' := d.nf_injective e
  simp only [Prod.mk.injEq] at e'
  funext i
  fin_cases i
  · exact e'.1
  · exact e'.2.2.1

theorem mv_add_mem (z z' : Fin 2 → d.Γ) : (d.mv z * d.mv z')⁻¹ * d.mv (z + z') ∈ d.W := by
  have e : (d.mv z * d.mv z')⁻¹ * d.mv (z + z') =
      (d.x₃ (z' 1))⁻¹ * ⁅(d.x₁ (z' 0))⁻¹, (d.x₃ (z 1))⁻¹⁆ * ((d.x₃ (z' 1))⁻¹)⁻¹ := by
    simp only [mv, Pi.add_apply, d.x₁_add, d.x₃_add, commutatorElement_def]
    group
  rw [e]
  simp only [d.x₁_inv, d.x₃_inv]
  have := (mem_normalizer_iff.1 (d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ (z' 1))))
    _).1 (d.comm₁₃_mem_W (z' 0) (z 1))
  rwa [d.x₃_inv] at this

theorem leviLong_J_irreducible_M_mod_W {T : Subgroup X} (hWT : d.W ≤ T) (hTM : T ≤ d.M)
    (hK : d.leviLong ≤ normalizer (T : Set X)) (hJ : d.J ≤ normalizer (T : Set X)) :
    T = d.W ∨ T = d.M := by
  by_cases hTW : T ≤ d.W
  · exact Or.inl (le_antisymm hTW hWT)
  right
  obtain ⟨t, ht, htW⟩ := Set.not_subset.1 hTW
  obtain ⟨z, n, hn, rfl⟩ := d.exists_mv_of_mem_M (hTM ht)
  have hconj : ∀ g ∈ normalizer (T : Set X), ∀ y ∈ T, g * y * g⁻¹ ∈ T := fun g hg y hy =>
    (mem_normalizer_iff.1 hg y).1 hy
  have hmv : d.mv z ∈ T := by
    have := mul_mem ht (inv_mem (hWT hn))
    rwa [mul_inv_cancel_right] at this
  have hx₃ : ∃ c ≠ 0, d.x₃ c ∈ T := by
    by_cases hz0 : z 0 = 0
    · refine ⟨z 1, fun hz1 => htW ?_, ?_⟩
      · rw [show d.mv z = 1 by simp [mv, hz0, hz1, d.x₁_zero, d.x₃_zero], one_mul]
        exact hn
      · simpa [mv, hz0, d.x₁_zero] using hmv
    · refine ⟨z 0, hz0, ?_⟩
      obtain ⟨n', hn', e⟩ := d.x₂_conj_mv 1 z
      have h1 := hconj _ (hK (d.x₂_mem_leviLong 1)) _ hmv
      rw [e] at h1
      have h2 : d.mv (d.toΓ (d.slX₂ 1) *ᵥ z) ∈ T := by
        have := mul_mem h1 (inv_mem (hWT hn'))
        rwa [mul_inv_cancel_right] at this
      have e2 : (d.mv z)⁻¹ * d.mv (d.toΓ (d.slX₂ 1) *ᵥ z) = d.x₃ (z 0) := by
        have hv : d.toΓ (d.slX₂ 1) *ᵥ z = ![z 0, z 0 + z 1] := by
          funext i
          fin_cases i <;> simp [toΓ, slX₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [hv]
        simp only [mv, Matrix.cons_val_zero, Matrix.cons_val_one, d.x₃_add, mul_inv_rev,
          d.x₁_inv, d.x₃_inv]
        rw [show d.x₃ (z 1) * d.x₁ (z 0) * (d.x₁ (z 0) * (d.x₃ (z 0) * d.x₃ (z 1))) =
          d.x₃ (z 1) * (d.x₁ (z 0) * d.x₁ (z 0)) * d.x₃ (z 0) * d.x₃ (z 1) by group,
          d.x₁_mul_self, mul_one, ← d.x₃_add, ← d.x₃_add]
        congr 1
        rw [add_comm (z 1) (z 0), add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [← e2]
      exact mul_mem (inv_mem hmv) h2
  obtain ⟨c, hc, hxc⟩ := hx₃
  have hU₃ : d.U₃ ≤ T := by
    rintro _ ⟨c', rfl⟩
    by_cases hc' : c' = 0
    · rw [hc', d.x₃_zero]
      exact one_mem _
    have h := hconj _ (hJ (d.torus_mem_J (1, Units.mk0 (c' / c) (div_ne_zero hc' hc)))) _ hxc
    rw [d.torus_x₃] at h
    simpa [div_mul_cancel₀ _ hc] using h
  have hU₁ : d.U₁ ≤ T := by
    rintro _ ⟨a, rfl⟩
    rw [← d.v_conj_x₃ a]
    exact hconj _ (hK d.v_mem_leviLong) _ (hU₃ (d.x₃_mem_U₃ a))
  exact le_antisymm hTM (sup_le hU₁ (sup_le hU₃ hWT))

theorem yamada_three_ten :
    (∀ T : Subgroup X, d.V ≤ T → T ≤ d.D → d.leviShort ≤ normalizer (T : Set X) →
      T = d.V ∨ T = d.D) ∧
    ((∀ (g : d.leviLong) (w : Fin 2 → d.Γ₀), (g : X) * d.yv w * (g : X)⁻¹ =
        d.yv ((d.leviLongEquiv g : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)) ∧
      (∀ w w', d.yv (w + w') = d.yv w * d.yv w') ∧ Function.Injective d.yv ∧
      Set.range d.yv = d.Y) ∧
    ((∀ (g : d.leviLong) (z : Fin 2 → d.Γ), ∃ n ∈ d.W,
        (g : X) * d.mv z * (g : X)⁻¹ = d.mv (d.toΓ (d.leviLongEquiv g) *ᵥ z) * n) ∧
      (∀ z z', (d.mv z * d.mv z')⁻¹ * d.mv (z + z') ∈ d.W) ∧
      (∀ g ∈ d.M, ∃ z, ∃ n ∈ d.W, d.mv z * n = g) ∧
      ∀ (z z' : Fin 2 → d.Γ) (n n' : X), n ∈ d.W → n' ∈ d.W → d.mv z * n = d.mv z' * n' →
        z = z') ∧
    (∀ T : Subgroup X, d.W ≤ T → T ≤ d.M → d.leviLong ≤ normalizer (T : Set X) →
      d.J ≤ normalizer (T : Set X) → T = d.W ∨ T = d.M) :=
  ⟨fun _ hV hD hT => d.leviShort_irreducible_D_mod_V hV hD hT,
    (d.yamada_three_ten_Y).2,
    ⟨fun g z => d.leviLongRep_mv g z, d.mv_add_mem, fun _ hg => d.exists_mv_of_mem_M hg,
      fun _ _ _ _ hn hn' h => d.eq_of_mv_mul_eq hn hn' h⟩,
    fun _ hW hM hK hJ => d.leviLong_J_irreducible_M_mod_W hW hM hK hJ⟩

abbrev LeviShortPoint : Type _ := ↥d.leviShort ⧸ d.B.subgroupOf d.leviShort

theorem x₁_mul_u_mem_leviShort (a : d.Γ) : d.x₁ a * d.u ∈ d.leviShort :=
  mul_mem (d.x₁_mem_leviShort a) d.u_mem_leviShort

@[expose] def leviShortCoset : Option d.Γ → d.LeviShortPoint
  | none => ((1 : d.leviShort) : d.LeviShortPoint)
  | some a => ((⟨d.x₁ a * d.u, d.x₁_mul_u_mem_leviShort a⟩ : d.leviShort) : d.LeviShortPoint)

theorem leviShortPoint_coe_eq_iff {g h : d.leviShort} :
    (g : d.LeviShortPoint) = (h : d.LeviShortPoint) ↔ (g : X)⁻¹ * h ∈ d.B := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem u_not_mem_B : d.u ∉ d.B := by
  intro h
  refine d.u_ne_one (d.bruhat_disjoint d.u d.u_mem_weyl 1 (one_mem _) d.u⁻¹ (inv_mem h) 1
    (one_mem _) ?_)
  rw [inv_mul_cancel, mul_one]

theorem S_le_B : d.S ≤ d.B := le_sup_left

theorem J_le_B : d.J ≤ d.B := le_sup_right

theorem x₁_mem_B (a : d.Γ) : d.x₁ a ∈ d.B := d.S_le_B (d.U₁_le_S (d.x₁_mem_U₁ a))

theorem leviShortCoset_bijective : Function.Bijective d.leviShortCoset := by
  constructor
  · rintro (_ | a) (_ | b) h
    · rfl
    · exfalso
      rw [leviShortCoset, leviShortCoset, leviShortPoint_coe_eq_iff] at h
      have h' : d.x₁ b * d.u ∈ d.B := by simpa using h
      apply d.u_not_mem_B
      have := mul_mem (inv_mem (d.x₁_mem_B b)) h'
      rwa [inv_mul_cancel_left] at this
    · exfalso
      rw [leviShortCoset, leviShortCoset, leviShortPoint_coe_eq_iff] at h
      have h' : d.x₁ a * d.u ∈ d.B := by simpa using inv_mem h
      apply d.u_not_mem_B
      have := mul_mem (inv_mem (d.x₁_mem_B a)) h'
      rwa [inv_mul_cancel_left] at this
    · rw [leviShortCoset, leviShortCoset, leviShortPoint_coe_eq_iff] at h
      have h' : (d.x₁ a * d.u)⁻¹ * (d.x₁ b * d.u) ∈ d.B := h
      have e : (d.x₁ a * d.u)⁻¹ * (d.x₁ b * d.u) = d.u * d.x₁ (a + b) * d.u := by
        rw [mul_inv_rev, d.u_inv, d.x₁_inv, d.x₁_add]
        group
      rw [e] at h'
      by_contra hab
      have hab' : a + b ≠ 0 := fun h0 => hab (by rw [CharTwo.add_eq_zero.1 h0])
      exact d.u_x₁_u_not_mem_B hab' h'
  · intro p
    induction p using QuotientGroup.induction_on with
    | H g =>
    rcases d.mem_leviShort_iff.1 g.2 with ⟨x, hx, h, hh, e⟩ | ⟨x, ⟨a, rfl⟩, h, hh, y, hy, e⟩
    · refine ⟨none, ?_⟩
      rw [leviShortCoset, leviShortPoint_coe_eq_iff, OneMemClass.coe_one, inv_one, one_mul, e]
      exact mul_mem (d.S_le_B (d.U₁_le_S hx)) (d.J_le_B hh.1)
    · refine ⟨some a, ?_⟩
      rw [leviShortCoset, leviShortPoint_coe_eq_iff]
      have hb : d.u * h * d.u * y ∈ d.B := by
        have := d.conj_mem_J d.u_mem_weyl hh.1
        rw [d.u_inv] at this
        exact mul_mem (d.J_le_B this) (d.S_le_B (d.U₁_le_S hy))
      have e' : (d.x₁ a * d.u)⁻¹ * (g : X) = d.u * h * d.u * y := by
        rw [e, mul_inv_rev, d.u_inv, d.x₁_inv]
        calc d.u * d.x₁ a * (d.x₁ a * h * d.u * y) = d.u * (d.x₁ a * d.x₁ a) * h * d.u * y := by
              group
          _ = d.u * h * d.u * y := by rw [d.x₁_mul_self, mul_one]
      exact e'.symm ▸ hb

@[expose] def leviShortCosetEquiv : Option d.Γ ≃ d.LeviShortPoint :=
  Equiv.ofBijective _ d.leviShortCoset_bijective

@[expose] def leviShortAct (g : d.leviShort) (z : Option d.Γ) : Option d.Γ :=
  d.leviShortCosetEquiv.symm (g • d.leviShortCosetEquiv z)

theorem leviShortAct_mul (g h : d.leviShort) (z : Option d.Γ) :
    d.leviShortAct (g * h) z = d.leviShortAct g (d.leviShortAct h z) := by
  simp [leviShortAct, mul_smul]

theorem leviShortAct_one (z : Option d.Γ) : d.leviShortAct 1 z = z := by
  simp [leviShortAct]

theorem leviShortAct_eq_iff {g : d.leviShort} {z w : Option d.Γ} :
    d.leviShortAct g z = w ↔ g • d.leviShortCoset z = d.leviShortCoset w := by
  rw [leviShortAct, Equiv.symm_apply_eq]
  rfl

@[expose] def slU₁ (b : d.Γ) : Matrix.SpecialLinearGroup (Fin 2) d.Γ :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem leviShortAct_x₁ (b : d.Γ) (z : Option d.Γ) :
    d.leviShortAct ⟨d.x₁ b, d.x₁_mem_leviShort b⟩ z =
      mob (d.slU₁ b : Matrix (Fin 2) (Fin 2) d.Γ) z := by
  rw [leviShortAct_eq_iff]
  cases z with
  | none =>
    rw [mob_none]
    simp only [slU₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [show projPt ![(1 : d.Γ), 0] = none from projPt_eq_none_iff.2 rfl]
    simp only [leviShortCoset, MulAction.Quotient.smul_coe]
    rw [leviShortPoint_coe_eq_iff]
    simpa using inv_mem (d.x₁_mem_B b)
  | some a =>
    rw [mob_some]
    simp only [slU₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [show projPt ![1 * a + b, 0 * a + 1] = some (a + b) from
      projPt_eq_some_iff.2 ⟨by simp, by simp⟩]
    simp only [leviShortCoset, MulAction.Quotient.smul_coe]
    rw [leviShortPoint_coe_eq_iff]
    change (d.x₁ b * (d.x₁ a * d.u))⁻¹ * (d.x₁ (a + b) * d.u) ∈ d.B
    rw [show d.x₁ (a + b) = d.x₁ b * d.x₁ a by rw [add_comm, d.x₁_add],
      show (d.x₁ b * (d.x₁ a * d.u))⁻¹ * (d.x₁ b * d.x₁ a * d.u) = 1 by group]
    exact one_mem _

theorem hBCD_conj_x₁ (b : d.Γˣ) (z : d.Γ) :
    d.hBCD b * d.x₁ z * (d.hBCD b)⁻¹ = d.x₁ (((b : d.Γ) ^ 2) * z) := by
  rw [hBCD_apply, d.torus_x₁]
  simp

theorem exists_u_x₁_u : ∃ a : d.Γ, a ≠ 0 ∧ ∀ c : d.Γ, c ≠ 0 →
    (d.x₁ (a / c) * d.u)⁻¹ * (d.u * d.x₁ c * d.u) ∈ d.B := by
  have hg : d.u * d.x₁ 1 * d.u ∈ d.leviShort :=
    mul_mem (mul_mem d.u_mem_leviShort (d.x₁_mem_leviShort 1)) d.u_mem_leviShort
  rcases d.mem_leviShort_iff.1 hg with ⟨x, hx, h, hh, e⟩ | ⟨x, ⟨a, rfl⟩, h, hh, y, hy, e⟩
  · exact absurd (e ▸ mul_mem (d.S_le_B (d.U₁_le_S hx)) (d.J_le_B hh.1))
      (d.u_x₁_u_not_mem_B one_ne_zero)
  have key : ∀ c : d.Γ, c ≠ 0 → (d.x₁ (a / c) * d.u)⁻¹ * (d.u * d.x₁ c * d.u) ∈ d.B := by
    intro c hc
    obtain ⟨β, hβ⟩ := d.sq_surjective_units (Units.mk0 c hc)
    have hβc : (β : d.Γ) ^ 2 = c := by
      rw [← Units.val_pow_eq_pow_val, hβ, Units.val_mk0]
    set s := d.hBCD β with hs_def
    have hs6 : s ∈ d.J₆ := by rw [d.J₆_eq_range_hBCD]; exact ⟨β, rfl⟩
    have hus : d.u * s * d.u = s⁻¹ := d.u_conj_eq_inv_of_mem_J₆ hs6
    have hus' : d.u * s⁻¹ * d.u = s := by
      have h' : (d.u * s * d.u)⁻¹ = d.u * s⁻¹ * d.u := by
        rw [mul_inv_rev, mul_inv_rev, d.u_inv, mul_assoc]
      rw [← h', hus, inv_inv]
    have hs1 : s * d.x₁ 1 * s⁻¹ = d.x₁ c := by rw [d.hBCD_conj_x₁, hβc, mul_one]
    have hs2 : s⁻¹ * d.x₁ a * s = d.x₁ (a / c) := by
      have h := d.hBCD_conj_x₁ β⁻¹ a
      rw [map_inv, inv_inv] at h
      rw [h, Units.val_inv_eq_inv_val, inv_pow, hβc, div_eq_inv_mul]
    have e1 : d.u * d.x₁ c * d.u = s⁻¹ * (d.u * d.x₁ 1 * d.u) * s := by
      calc d.u * d.x₁ c * d.u = d.u * (s * d.x₁ 1 * s⁻¹) * d.u := by rw [hs1]
        _ = d.u * s * (d.u * d.u) * d.x₁ 1 * (d.u * d.u) * s⁻¹ * d.u := by
            rw [d.u_mul_self]; group
        _ = (d.u * s * d.u) * (d.u * d.x₁ 1 * d.u) * (d.u * s⁻¹ * d.u) := by group
        _ = s⁻¹ * (d.u * d.x₁ 1 * d.u) * s := by rw [hus, hus']
    have e2 : (d.x₁ (a / c) * d.u)⁻¹ * (d.u * d.x₁ c * d.u) =
        d.u * (s⁻¹ * h) * d.u * (y * s) := by
      rw [e1, e, ← hs2, mul_inv_rev, d.u_inv]
      group
    rw [e2]
    have hJ : d.u * (s⁻¹ * h) * d.u ∈ d.J := by
      have := d.conj_mem_J d.u_mem_weyl (mul_mem (inv_mem hs6.1) hh.1)
      rwa [d.u_inv] at this
    exact mul_mem (d.J_le_B hJ) (mul_mem (d.S_le_B (d.U₁_le_S hy)) (d.J_le_B hs6.1))
  refine ⟨a, fun ha => ?_, key⟩
  have h1 := key 1 one_ne_zero
  rw [ha, zero_div, d.x₁_zero, one_mul, show d.u⁻¹ * (d.u * d.x₁ 1 * d.u) = d.x₁ 1 * d.u by
    group] at h1
  apply d.u_not_mem_B
  have := mul_mem (inv_mem (d.x₁_mem_B 1)) h1
  rwa [inv_mul_cancel_left] at this

@[expose] def slW (r : d.Γ) (hr : r ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) d.Γ :=
  ⟨!![0, r; r⁻¹, 0], by simp [Matrix.det_fin_two, hr, CharTwo.neg_eq]⟩

theorem leviShortCoset_zero :
    d.leviShortCoset (some 0) = ((⟨d.u, d.u_mem_leviShort⟩ : d.leviShort) : d.LeviShortPoint) := by
  rw [leviShortCoset, leviShortPoint_coe_eq_iff]
  simp [d.x₁_zero]

theorem exists_leviShortAct_u : ∃ (r : d.Γ) (hr : r ≠ 0), ∀ z,
    d.leviShortAct ⟨d.u, d.u_mem_leviShort⟩ z =
      mob (d.slW r hr : Matrix (Fin 2) (Fin 2) d.Γ) z := by
  obtain ⟨a, ha, hau⟩ := d.exists_u_x₁_u
  obtain ⟨r, hr⟩ := d.sq_surjective_units (Units.mk0 a ha)
  have hr2 : (r : d.Γ) ^ 2 = a := by rw [← Units.val_pow_eq_pow_val, hr, Units.val_mk0]
  refine ⟨r, r.ne_zero, fun z => ?_⟩
  rw [leviShortAct_eq_iff]
  cases z with
  | none =>
    rw [mob_none, show projPt ![(d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 0 0,
      (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 1 0] = some 0 from
      projPt_eq_some_iff.2 ⟨by simp [slW], by simp [slW]⟩, leviShortCoset_zero]
    simp only [leviShortCoset, MulAction.Quotient.smul_coe]
    rw [leviShortPoint_coe_eq_iff]
    simp
  | some c =>
    rw [mob_some]
    by_cases hc : c = 0
    · subst hc
      rw [show projPt ![(d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 0 0 * 0 +
        (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 0 1,
        (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 1 0 * 0 +
        (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 1 1] = none from
        projPt_eq_none_iff.2 (by simp [slW]), leviShortCoset_zero]
      simp only [leviShortCoset, MulAction.Quotient.smul_coe]
      rw [leviShortPoint_coe_eq_iff]
      change (d.u * d.u)⁻¹ * 1 ∈ d.B
      rw [d.u_mul_self, inv_one, one_mul]
      exact one_mem _
    · rw [show projPt ![(d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 0 0 * c +
        (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 0 1,
        (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 1 0 * c +
        (d.slW r r.ne_zero : Matrix (Fin 2) (Fin 2) d.Γ) 1 1] = some (a / c) from
        projPt_eq_some_iff.2 ⟨by simp [slW, hc, r.ne_zero], by
          simp only [slW, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, zero_add,
            add_zero]
          rw [← hr2]
          field_simp⟩]
      simp only [leviShortCoset, MulAction.Quotient.smul_coe]
      rw [leviShortPoint_coe_eq_iff]
      change (d.u * (d.x₁ c * d.u))⁻¹ * (d.x₁ (a / c) * d.u) ∈ d.B
      have h := inv_mem (hau c hc)
      rw [mul_inv_rev, inv_inv] at h
      convert h using 1
      group

theorem exists_leviShortAct_eq_mob (g : d.leviShort) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) d.Γ, ∀ z,
      d.leviShortAct g z = mob (A : Matrix (Fin 2) (Fin 2) d.Γ) z := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨r, hr, hu⟩ := d.exists_leviShortAct_u
  induction hg using closure_induction'' with
  | mem g hg =>
    rcases hg with ⟨b, rfl⟩ | rfl
    · exact ⟨d.slU₁ b, d.leviShortAct_x₁ b⟩
    · exact ⟨d.slW r hr, hu⟩
  | inv_mem g hg =>
    rcases hg with ⟨b, rfl⟩ | rfl
    · refine ⟨d.slU₁ b, fun z => ?_⟩
      rw [← d.leviShortAct_x₁ b]
      congr 1
      exact Subtype.ext (d.x₁_inv b)
    · refine ⟨d.slW r hr, fun z => ?_⟩
      rw [← hu z]
      congr 1
      exact Subtype.ext d.u_inv
  | one => exact ⟨1, fun z => by
      rw [Matrix.SpecialLinearGroup.coe_one, mob_one]
      exact d.leviShortAct_one z⟩
  | mul g g' hg hg' ih ih' =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨A', hA'⟩ := ih'
    refine ⟨A * A', fun z => ?_⟩
    rw [mob_mul, ← hA', ← hA, ← d.leviShortAct_mul]
    rfl

@[expose] def slOfLeviShort (g : d.leviShort) : Matrix.SpecialLinearGroup (Fin 2) d.Γ :=
  Classical.choose (d.exists_leviShortAct_eq_mob g)

theorem slOfLeviShort_spec (g : d.leviShort) (z : Option d.Γ) :
    d.leviShortAct g z = mob (d.slOfLeviShort g : Matrix (Fin 2) (Fin 2) d.Γ) z :=
  Classical.choose_spec (d.exists_leviShortAct_eq_mob g) z

@[expose] def leviShortRep : d.leviShort →* Matrix.SpecialLinearGroup (Fin 2) d.Γ where
  toFun := d.slOfLeviShort
  map_one' := eq_of_mob_eq fun z => by
    rw [← d.slOfLeviShort_spec, d.leviShortAct_one, Matrix.SpecialLinearGroup.coe_one, mob_one]
  map_mul' g g' := eq_of_mob_eq fun z => by
    rw [← d.slOfLeviShort_spec, mob_mul, ← d.slOfLeviShort_spec, ← d.slOfLeviShort_spec,
      d.leviShortAct_mul]

theorem leviShortRep_spec (g : d.leviShort) (z : Option d.Γ) :
    d.leviShortAct g z = mob (d.leviShortRep g : Matrix (Fin 2) (Fin 2) d.Γ) z :=
  d.slOfLeviShort_spec g z

theorem eq_zero_of_inv_mul_u_mem_B {t : X} (ht : t ∈ d.J) {a : d.Γ}
    (h : (d.x₁ a * t * d.u)⁻¹ * d.u ∈ d.B) : a = 0 := by
  by_contra ha
  apply d.u_x₁_u_not_mem_B ha
  have hut : d.u * t * d.u ∈ d.J := by
    have := d.conj_mem_J d.u_mem_weyl ht
    rwa [d.u_inv] at this
  have e : (d.x₁ a * t * d.u)⁻¹ * d.u = (d.u * t * d.u)⁻¹ * (d.u * d.x₁ a * d.u) := by
    rw [mul_inv_rev, mul_inv_rev, d.x₁_inv]
    group
  rw [e] at h
  have := mul_mem (d.J_le_B hut) h
  rwa [mul_inv_cancel_left] at this

theorem eq_one_of_leviShortAct_eq (g : d.leviShort) (h : ∀ z, d.leviShortAct g z = z) :
    g = 1 := by
  have hinf := (d.leviShortAct_eq_iff).1 (h none)
  simp only [leviShortCoset, MulAction.Quotient.smul_coe] at hinf
  rw [leviShortPoint_coe_eq_iff] at hinf
  have hgB : (g : X) ∈ d.B := by simpa using inv_mem hinf
  obtain ⟨x, ⟨α, rfl⟩, t, ht, hgt⟩ := d.exists_eq_mul_of_mem_leviShort_of_mem_B g.2 hgB
  have h0 := (d.leviShortAct_eq_iff).1 (h (some 0))
  rw [leviShortCoset_zero, MulAction.Quotient.smul_coe, leviShortPoint_coe_eq_iff] at h0
  change ((g : X) * d.u)⁻¹ * d.u ∈ d.B at h0
  rw [hgt] at h0
  obtain rfl := d.eq_zero_of_inv_mul_u_mem_B ht.1 h0
  rw [d.x₁_zero, one_mul] at hgt
  rw [d.J₆_eq_range_hBCD] at ht
  obtain ⟨β, rfl⟩ := ht
  have h1 := (d.leviShortAct_eq_iff).1 (h (some 1))
  simp only [leviShortCoset, MulAction.Quotient.smul_coe] at h1
  rw [leviShortPoint_coe_eq_iff] at h1
  change ((g : X) * (d.x₁ 1 * d.u))⁻¹ * (d.x₁ 1 * d.u) ∈ d.B at h1
  have e : (g : X) * (d.x₁ 1 * d.u) = d.x₁ ((β : d.Γ) ^ 2) * d.hBCD β * d.u := by
    rw [hgt, ← mul_one ((β : d.Γ) ^ 2), ← d.hBCD_conj_x₁]
    group
  have e' : ((g : X) * (d.x₁ 1 * d.u))⁻¹ * (d.x₁ 1 * d.u) =
      (d.x₁ ((β : d.Γ) ^ 2 + 1) * d.hBCD β * d.u)⁻¹ * d.u := by
    rw [e, d.x₁_add, (commute_of_add d.x₁_add ((β : d.Γ) ^ 2) 1).eq]
    simp only [mul_inv_rev, d.x₁_inv]
    group
  rw [e'] at h1
  have hβ := d.eq_zero_of_inv_mul_u_mem_B (⟨_, (d.hBCD_apply β).symm⟩ : d.hBCD β ∈ d.J) h1
  have hβ1 : β = 1 := d.units_eq_one_of_sq (Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact CharTwo.add_eq_zero.1 hβ))
  subst hβ1
  exact Subtype.ext (by rw [hgt, map_one]; rfl)

theorem leviShortRep_bijective : Function.Bijective d.leviShortRep := by
  have := d.finite
  have hinj : Function.Injective d.leviShortRep := by
    refine (injective_iff_map_eq_one _).2 fun g hg => d.eq_one_of_leviShortAct_eq g fun z => ?_
    rw [d.leviShortRep_spec, hg, Matrix.SpecialLinearGroup.coe_one, mob_one]
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
  rw [d.card_leviShort, card_SL_two_D4, d.card_Γ, ← pow_mul]

@[expose] def leviShortEquiv : d.leviShort ≃* Matrix.SpecialLinearGroup (Fin 2) d.Γ :=
  MulEquiv.ofBijective d.leviShortRep d.leviShortRep_bijective

theorem yamada_three_six_iso : Nat.card d.Γ = q ^ 3 ∧ Nat.card d.Γ₀ = q ∧
    Nonempty (d.leviShort ≃* Matrix.SpecialLinearGroup (Fin 2) d.Γ) ∧
    Nonempty (d.leviLong ≃* Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) :=
  ⟨d.card_Γ, d.card_Γ₀, ⟨d.leviShortEquiv⟩, ⟨d.leviLongEquiv⟩⟩

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
