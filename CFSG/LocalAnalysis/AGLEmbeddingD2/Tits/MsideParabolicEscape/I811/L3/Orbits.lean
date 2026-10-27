module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Mat2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Model
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F]

@[expose] def P2 : Subgroup (SL3 F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    rw [hg1, hg2, hh1, hh2]
    simp
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [hg1, hg2]

theorem mem_P2 {g : SL3 F} :
    g ∈ P2 ↔ (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 :=
  Iff.rfl

theorem lev_mulVec_zero (X : GL (Fin 2) F) (v : Fin 3 → F) :
    (((lev X : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 =
      ((X : Matrix (Fin 2) (Fin 2) F).det)⁻¹ * v 0 := by
  rw [coe_lev]
  simp [levMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem lev_mulVec_succ (X : GL (Fin 2) F) (v : Fin 3 → F) (i : Fin 2) :
    (((lev X : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i.succ =
      ((X : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun j => v j.succ)) i := by
  rw [coe_lev]
  fin_cases i <;> simp [levMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

theorem tail_ne_zero {v : Fin 3 → F} (hv : v ≠ 0) (h0 : v 0 = 0) :
    (fun j : Fin 2 => v j.succ) ≠ 0 := by
  intro h
  apply hv
  funext i
  fin_cases i
  · exact h0
  · exact congrFun h 0
  · exact congrFun h 1

theorem exists_lev_mulVec_eq_of_line (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) {v w : Fin 3 → F}
    (hv : v ≠ 0) (hw : w ≠ 0) (hv0 : v 0 = 0) (hw0 : w 0 = 0) :
    ∃ X : GL (Fin 2) F, (X : Matrix (Fin 2) (Fin 2) F) * cMat (F := F) = cMat * (X : Matrix (Fin 2) (Fin 2) F) ∧
      ((lev X : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w := by
  obtain ⟨X, hX, hXv⟩ := exists_comm_mulVec_eq hroot cMat_relation (tail_ne_zero hv hv0)
    (tail_ne_zero hw hw0)
  refine ⟨X, hX, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lev_mulVec_zero, hv0, hw0, mul_zero]
  · rw [lev_mulVec_succ, hXv]

theorem exists_lev_mulVec_eq_smul_of_generic (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) {v w : Fin 3 → F} (hv0 : v 0 ≠ 0) (hw0 : w 0 ≠ 0)
    (hv : (fun j : Fin 2 => v j.succ) ≠ 0) (hw : (fun j : Fin 2 => w j.succ) ≠ 0) :
    ∃ X : GL (Fin 2) F, (X : Matrix (Fin 2) (Fin 2) F) * cMat (F := F) = cMat * (X : Matrix (Fin 2) (Fin 2) F) ∧
      ∃ c : F, c ≠ 0 ∧ ((lev X : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • w := by
  have hw' : (v 0 / w 0) • (fun j : Fin 2 => w j.succ) ≠ 0 :=
    smul_ne_zero (div_ne_zero hv0 hw0) hw
  obtain ⟨X, hX, hXv⟩ := exists_comm_det_smul_mulVec_eq hroot hcube cMat_relation hv hw'
  have hdet : (X : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero]
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨X, hX, (X : Matrix (Fin 2) (Fin 2) F).det⁻¹ * (v 0 / w 0),
    mul_ne_zero (inv_ne_zero hdet) (div_ne_zero hv0 hw0), ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lev_mulVec_zero, Pi.smul_apply, smul_eq_mul]
    field_simp
  · rw [lev_mulVec_succ, Pi.smul_apply, smul_eq_mul]
    have h := congrFun hXv j
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, ← h]
    field_simp

@[expose] def InOrbit (W : Subgroup (SL3 F)) (v : Fin 3 → F) : Prop :=
  ∃ g ∈ W, ∃ c : F, c ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 = c • v

theorem inOrbit_e0 (W : Subgroup (SL3 F)) : InOrbit W (e0 (F := F)) :=
  ⟨1, W.one_mem, 1, one_ne_zero, by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, one_smul]⟩

theorem InOrbit.smul {W : Subgroup (SL3 F)} {v : Fin 3 → F} (h : InOrbit W v) {d : F}
    (hd : d ≠ 0) : InOrbit W (d • v) := by
  obtain ⟨g, hg, c, hc, hgc⟩ := h
  refine ⟨g, hg, c * d⁻¹, mul_ne_zero hc (inv_ne_zero hd), ?_⟩
  rw [hgc, smul_smul, mul_assoc, inv_mul_cancel₀ hd, mul_one]

theorem InOrbit.mulVec {W : Subgroup (SL3 F)} {v : Fin 3 → F} (h : InOrbit W v) {g : SL3 F}
    (hg : g ∈ W) : InOrbit W ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  obtain ⟨g', hg', c, hc, hgc⟩ := h
  refine ⟨g * g', W.mul_mem hg hg', c, hc, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hgc, Matrix.mulVec_smul]

theorem InOrbit.of_mulVec {W : Subgroup (SL3 F)} {v : Fin 3 → F} {g : SL3 F} (hg : g ∈ W)
    (h : InOrbit W ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) : InOrbit W v := by
  have := h.mulVec (W.inv_mem hg)
  rwa [sl_inv_mulVec_mulVec] at this

theorem inOrbit_of_line (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) {W : Subgroup (SL3 F)}
    (hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W)
    {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) (hv0 : v 0 = 0) (hw0 : w 0 = 0)
    (h : InOrbit W v) : InOrbit W w := by
  obtain ⟨X, hX, hXv⟩ := exists_lev_mulVec_eq_of_line hroot hv hw hv0 hw0
  have := h.mulVec (hlev X hX)
  rwa [hXv] at this

theorem inOrbit_of_generic (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) {W : Subgroup (SL3 F)}
    (hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W)
    {v w : Fin 3 → F} (hv0 : v 0 ≠ 0) (hw0 : w 0 ≠ 0)
    (hv : (fun j : Fin 2 => v j.succ) ≠ 0) (hw : (fun j : Fin 2 => w j.succ) ≠ 0)
    (h : InOrbit W v) : InOrbit W w := by
  obtain ⟨X, hX, c, hc, hXv⟩ := exists_lev_mulVec_eq_smul_of_generic hroot hcube hv0 hw0 hv hw
  have := h.mulVec (hlev X hX)
  rw [hXv] at this
  have h2 := this.smul (inv_ne_zero hc)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem vec_trichotomy (v : Fin 3 → F) :
    v = v 0 • e0 ∨ v 0 = 0 ∨ (v 0 ≠ 0 ∧ (fun j : Fin 2 => v j.succ) ≠ 0) := by
  by_cases h0 : v 0 = 0
  · exact Or.inr (Or.inl h0)
  by_cases ht : (fun j : Fin 2 => v j.succ) = 0
  · left
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have := congrFun ht j
      simp only [Pi.zero_apply] at this
      simp [this]
  · exact Or.inr (Or.inr ⟨h0, ht⟩)

theorem ne_zero_of_mulVec {g : SL3 F} {v : Fin 3 → F} (hv : v ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ≠ 0 :=
  fun h => hv ((sl_mulVec_eq_zero_iff g).mp h)

abbrev e1 : Fin 3 → F := Pi.single 1 1
abbrev e2 : Fin 3 → F := Pi.single 2 1

theorem exists_line_generic {g : SL3 F} (hg0 : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) 0 = 0) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ v 0 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 ≠ 0 ∧
        (fun j : Fin 2 => ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) j.succ) ≠ 0 := by
  set M := (g : Matrix (Fin 3) (Fin 3) F)
  have hdet : M.det = 1 := g.2
  rw [Matrix.det_fin_three] at hdet
  have hg00 : M 0 0 = 0 := by
    have := hg0
    rw [mulVec_e0] at this
    exact this
  have hcol : ∀ v : Fin 3 → F, v 0 = 0 → M *ᵥ v = fun i => M i 1 * v 1 + M i 2 * v 2 := by
    intro v hv
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv]
  have he1 : M *ᵥ e1 = fun i => M i 1 := by
    rw [hcol _ (by simp)]
    funext i
    simp
  have he2 : M *ᵥ e2 = fun i => M i 2 := by
    rw [hcol _ (by simp)]
    funext i
    simp
  have he12 : M *ᵥ (e1 + e2) = fun i => M i 1 + M i 2 := by
    rw [Matrix.mulVec_add, he1, he2]
    rfl
  have tail2 : ∀ a b : F, (fun j : Fin 2 => (![0, a, b] : Fin 3 → F) j.succ) ≠ 0 ↔
      (a ≠ 0 ∨ b ≠ 0) := by
    intro a b
    constructor
    · intro h
      by_contra hab
      push Not at hab
      apply h
      funext j
      fin_cases j <;> simp [hab.1, hab.2]
    · rintro hab h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      rcases hab with hab | hab
      · exact hab h0
      · exact hab h1
  have tailOf : ∀ w : Fin 3 → F, (fun j : Fin 2 => w j.succ) ≠ 0 ↔ (w 1 ≠ 0 ∨ w 2 ≠ 0) := by
    intro w
    constructor
    · intro h
      by_contra hab
      push Not at hab
      apply h
      funext j
      fin_cases j
      · exact hab.1
      · exact hab.2
    · rintro hab h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Pi.zero_apply] at h0 h1
      rcases hab with hab | hab
      · exact hab h0
      · exact hab h1
  have he1ne : (e1 : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  have he2ne : (e2 : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 2
    simp at this
  by_cases h1 : M 0 1 ≠ 0 ∧ (M 1 1 ≠ 0 ∨ M 2 1 ≠ 0)
  · refine ⟨e1, he1ne, by simp, ?_, ?_⟩
    · rw [he1]
      exact h1.1
    · rw [tailOf, he1]
      exact h1.2
  by_cases h2 : M 0 2 ≠ 0 ∧ (M 1 2 ≠ 0 ∨ M 2 2 ≠ 0)
  · refine ⟨e2, he2ne, by simp, ?_, ?_⟩
    · rw [he2]
      exact h2.1
    · rw [tailOf, he2]
      exact h2.2
  have hne : (e1 + e2 : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  refine ⟨e1 + e2, hne, by simp, ?_, ?_⟩
  · rw [he12]
    simp only
    by_cases ha : M 0 1 = 0
    · by_cases hb : M 0 2 = 0
      · exfalso
        rw [hg00, ha, hb] at hdet
        simp at hdet
      · rw [ha, zero_add]
        exact hb
    · by_cases hb : M 0 2 = 0
      · rw [hb, add_zero]
        exact ha
      · exfalso
        have h1' : M 1 1 = 0 ∧ M 2 1 = 0 := by
          by_contra hc
          apply h1
          refine ⟨ha, ?_⟩
          by_contra hd
          push Not at hd
          exact hc hd
        have h2' : M 1 2 = 0 ∧ M 2 2 = 0 := by
          by_contra hc
          apply h2
          refine ⟨hb, ?_⟩
          by_contra hd
          push Not at hd
          exact hc hd
        rw [h1'.1, h1'.2, h2'.1, h2'.2] at hdet
        simp at hdet
  · rw [tailOf, he12]
    simp only
    by_cases ha : M 0 1 = 0
    ·
      by_cases hb : M 0 2 = 0
      · exfalso
        rw [hg00, ha, hb] at hdet
        simp at hdet
      · have h2' : M 1 2 = 0 ∧ M 2 2 = 0 := by
          by_contra hc
          apply h2
          refine ⟨hb, ?_⟩
          by_contra hd
          push Not at hd
          exact hc hd
        rw [h2'.1, h2'.2, add_zero, add_zero]
        by_contra hd
        push Not at hd
        rw [hd.1, hd.2, ha] at hdet
        simp at hdet
    · have h1' : M 1 1 = 0 ∧ M 2 1 = 0 := by
        by_contra hc
        apply h1
        refine ⟨ha, ?_⟩
        by_contra hd
        push Not at hd
        exact hc hd
      rw [h1'.1, h1'.2, zero_add, zero_add]
      by_contra hd
      push Not at hd
      rw [h1'.1, h1'.2, hd.1, hd.2] at hdet
      simp at hdet

theorem e0_ne_zero : (e0 : Fin 3 → F) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem inOrbit_of_smul_e0 {W : Subgroup (SL3 F)} {w : Fin 3 → F} (hw : w ≠ 0)
    (h : w = w 0 • e0) : InOrbit W w := by
  have hw0 : w 0 ≠ 0 := by
    intro h0
    apply hw
    rw [h, h0, zero_smul]
  rw [h]
  exact (inOrbit_e0 W).smul hw0

theorem le_P1_or_le_P2_or_transitive (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) {W : Subgroup (SL3 F)}
    (hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W) :
    W ≤ P1 ∨ W ≤ P2 ∨ ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v := by
  by_cases h1 : W ≤ P1
  · exact Or.inl h1
  by_cases h2 : W ≤ P2
  · exact Or.inr (Or.inl h2)
  right; right
  obtain ⟨g, hgW, hgP⟩ := Set.not_subset.mp h1
  set u := (g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 with hu_def
  have hu : InOrbit W u := ⟨g, hgW, 1, one_ne_zero, (one_smul _ _).symm⟩
  have hu0 : u ≠ 0 := ne_zero_of_mulVec e0_ne_zero
  have hu_not : ¬ (u = u 0 • e0) := fun h => hgP (mem_P1_iff_exists.mpr ⟨u 0, h⟩)
  have hgen : ∃ v : Fin 3 → F, v 0 ≠ 0 ∧ (fun j : Fin 2 => v j.succ) ≠ 0 ∧ InOrbit W v := by
    rcases vec_trichotomy u with h | h | h
    · exact absurd h hu_not
    · obtain ⟨v, hv, hv0, hgv0, hgvt⟩ := exists_line_generic (g := g) h
      have hvO : InOrbit W v := inOrbit_of_line hroot hlev hu0 hv h hv0 hu
      exact ⟨_, hgv0, hgvt, hvO.mulVec hgW⟩
    · exact ⟨u, h.1, h.2, hu⟩
  obtain ⟨v₁, hv₁0, hv₁t, hv₁O⟩ := hgen
  have hallgen : ∀ w : Fin 3 → F, w 0 ≠ 0 → (fun j : Fin 2 => w j.succ) ≠ 0 → InOrbit W w :=
    fun w hw0 hwt => inOrbit_of_generic hroot hcube hlev hv₁0 hw0 hv₁t hwt hv₁O
  have hline : ∃ v : Fin 3 → F, v ≠ 0 ∧ v 0 = 0 ∧ InOrbit W v := by
    by_contra hno
    push Not at hno
    apply h2
    intro h hhW
    have key : ∀ v : Fin 3 → F, v ≠ 0 → v 0 = 0 →
        ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = 0 := by
      intro v hv hv0
      by_contra hne
      have hO : InOrbit W ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
        rcases vec_trichotomy ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) with h' | h' | h'
        · exact inOrbit_of_smul_e0 (ne_zero_of_mulVec hv) h'
        · exact absurd h' hne
        · exact hallgen _ h'.1 h'.2
      exact hno v hv hv0 (hO.of_mulVec hhW)
    have k1 := key e1 (by intro h; have := congrFun h 1; simp at this) (by simp)
    have k2 := key e2 (by intro h; have := congrFun h 2; simp at this) (by simp)
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at k1 k2
    exact ⟨k1, k2⟩
  obtain ⟨v₂, hv₂, hv₂0, hv₂O⟩ := hline
  intro w hw
  rcases vec_trichotomy w with h' | h' | h'
  · exact inOrbit_of_smul_e0 hw h'
  · exact inOrbit_of_line hroot hlev hv₂ hw hv₂0 h' hv₂O
  · exact hallgen w h'.1 h'.2

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
