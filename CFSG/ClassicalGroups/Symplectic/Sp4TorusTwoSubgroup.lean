module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp4

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin

variable {K : Type} [Field K]

@[expose] def diagSp4TorusHomFun (s : Fin 2 → Kˣ) : Fin 2 ⊕ Fin 2 → K :=
  Sum.elim (fun i => (s i : K)) fun i => ((s i)⁻¹ : K)

theorem mat_torusHom_eq_diagonal (s : Fin 2 → Kˣ) :
    mat (torusHom (r := 2) (k := K) s) = Matrix.diagonal (diagSp4TorusHomFun s) := by
  rw [mat, coe_torusHom]
  congr 1
  funext x
  simp [diagSp4TorusHomFun]

@[expose] def sp4TorusParam (i : Fin 2) (a : Kˣ) : Fin 2 → Kˣ :=
  if i = 0 then ![a, 1] else ![1, a]

theorem diagSp4TorusHomFun_sp4TorusParam_inl (i m : Fin 2) (a : Kˣ) :
    diagSp4TorusHomFun (sp4TorusParam i a) (Sum.inl m) =
      if m = i then (a : K) else 1 := by
  fin_cases i <;> fin_cases m <;> simp [sp4TorusParam, diagSp4TorusHomFun]

theorem diagSp4TorusHomFun_sp4TorusParam_inr (i m : Fin 2) (a : Kˣ) :
    diagSp4TorusHomFun (sp4TorusParam i a) (Sum.inr m) =
      if m = i then ((a⁻¹ : Kˣ) : K) else 1 := by
  fin_cases i <;> fin_cases m <;> simp [sp4TorusParam, diagSp4TorusHomFun]

theorem sp4_mulVec_mem_fixSub_of_mem_normalizer {R : Subgroup (StatedSp 2 K)}
    {g : StatedSp 2 K} (hg : g ∈ normalizer (R : Set (StatedSp 2 K)))
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ fixSub R) : mat g *ᵥ v ∈ fixSub R := by
  rw [mem_fixSub] at hv ⊢
  intro r hr
  have hconj : g⁻¹ * r * g ∈ R := (mem_set_normalizer_iff''.mp hg r).mp hr
  have h1 : r * g = g * (g⁻¹ * r * g) := by group
  have h2 : mat r * mat g = mat g * mat (g⁻¹ * r * g) := by
    rw [← mat_mul, h1, mat_mul]
  calc
    mat r *ᵥ (mat g *ᵥ v) = (mat r * mat g) *ᵥ v :=
      Matrix.mulVec_mulVec v (mat r) (mat g)
    _ = (mat g * mat (g⁻¹ * r * g)) *ᵥ v := by rw [h2]
    _ = mat g *ᵥ (mat (g⁻¹ * r * g) *ᵥ v) :=
      (Matrix.mulVec_mulVec v (mat g) (mat (g⁻¹ * r * g))).symm
    _ = mat g *ᵥ v := by rw [hv (g⁻¹ * r * g) hconj]

theorem smul_single_mem_of_diagonal_mulVec_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (f : ι → K) (p q : K) (c : ι)
    (hc : (f c - p) * (f c - q) ≠ 0)
    (hother : ∀ x, x ≠ c → (f x - p) * (f x - q) = 0)
    {W : Submodule K (ι → K)} (hW : ∀ w ∈ W, Matrix.diagonal f *ᵥ w ∈ W)
    {w : ι → K} (hw : w ∈ W) : w c • Pi.single c 1 ∈ W := by
  classical
  set u : ι → K := Matrix.diagonal f *ᵥ w - q • w with hu
  have huW : u ∈ W := W.sub_mem (hW w hw) (W.smul_mem q hw)
  set v : ι → K := Matrix.diagonal f *ᵥ u - p • u with hv
  have hvW : v ∈ W := W.sub_mem (hW u huW) (W.smul_mem p huW)
  have hcoord : v = fun x => (f x - p) * (f x - q) * w x := by
    funext x
    have hu' : u x = f x * w x - q * w x := by
      rw [hu, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
    calc
      v x = f x * u x - p * u x := by
        rw [hv, Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      _ = (f x - p) * (f x - q) * w x := by rw [hu']; ring
  have hv_single : v = ((f c - p) * (f c - q) * w c) • Pi.single c 1 := by
    rw [hcoord]
    funext x
    by_cases hx : x = c
    · subst hx; simp
    · have h0 : (f x - p) * (f x - q) = 0 := hother x hx
      simp [Pi.single_eq_of_ne hx, h0]
  have hmem : ((f c - p) * (f c - q) * w c) • Pi.single c 1 ∈ W := hv_single ▸ hvW
  have hres := W.smul_mem (((f c - p) * (f c - q))⁻¹) hmem
  have hcoef : ((f c - p) * (f c - q))⁻¹ * ((f c - p) * (f c - q) * w c) = w c := by
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rwa [smul_smul, hcoef] at hres

theorem eq_smul_single_of_diagonal_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (f : ι → K) (c : ι)
    (huniq : ∀ x, x ≠ c → f x ≠ f c)
    {v : ι → K} (hv : Matrix.diagonal f *ᵥ v = f c • v) :
    v = v c • Pi.single c 1 := by
  funext x
  by_cases hx : x = c
  · subst hx; simp
  · have hxval : v x = 0 := by
      have h1 : f x * v x = f c * v x := by
        have := congrFun hv x
        rwa [Matrix.mulVec_diagonal, Pi.smul_apply] at this
      have h2 : (f x - f c) * v x = 0 := by
        rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (huniq x hx))
    simp [hx, hxval]

theorem mul_eq_mul_inv_of_mem_torus (t : StatedSp 2 K)
    (hinv : ∀ d ∈ torus 2 K, t * d * t⁻¹ = d⁻¹) {d : StatedSp 2 K}
    (hd : d ∈ torus 2 K) : d * t = t * d⁻¹ := by
  have h2 : t * d⁻¹ * t⁻¹ = d := by
    have := hinv d⁻¹ ((torus 2 K).inv_mem hd)
    simpa using this
  calc
    d * t = (t * d⁻¹ * t⁻¹) * t := by rw [h2]
    _ = t * d⁻¹ := by group

theorem mulVec_inv_smul_of_mulVec_eq_smul {t d : StatedSp 2 K}
    (hdt : d * t = t * d⁻¹) {v : Fin 2 ⊕ Fin 2 → K} {mu : K} (hmu : mu ≠ 0)
    (hv : mat d *ᵥ v = mu • v) :
    mat d *ᵥ (mat t *ᵥ v) = mu⁻¹ • (mat t *ᵥ v) := by
  have hleft : mat d⁻¹ *ᵥ (mat d *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec v (mat d⁻¹) (mat d), ← mat_mul, inv_mul_cancel, mat_one,
      Matrix.one_mulVec]
  have h1 : mat d⁻¹ *ᵥ (mat d *ᵥ v) = mat d⁻¹ *ᵥ (mu • v) := by rw [hv]
  have hright : mat d⁻¹ *ᵥ (mu • v) = mu • (mat d⁻¹ *ᵥ v) := Matrix.mulVec_smul _ _ _
  have hv_eq : v = mu • (mat d⁻¹ *ᵥ v) := by
    calc
      v = mat d⁻¹ *ᵥ (mat d *ᵥ v) := hleft.symm
      _ = mat d⁻¹ *ᵥ (mu • v) := h1
      _ = mu • (mat d⁻¹ *ᵥ v) := hright
  have h5 : mat d⁻¹ *ᵥ v = mu⁻¹ • v := by
    have := congrArg (fun x => mu⁻¹ • x) hv_eq
    rw [smul_smul, inv_mul_cancel₀ hmu, one_smul] at this
    exact this.symm
  calc
    mat d *ᵥ (mat t *ᵥ v) = (mat d * mat t) *ᵥ v :=
      Matrix.mulVec_mulVec v (mat d) (mat t)
    _ = mat (d * t) *ᵥ v := by rw [mat_mul]
    _ = mat (t * d⁻¹) *ᵥ v := by rw [hdt]
    _ = (mat t * mat d⁻¹) *ᵥ v := by rw [← mat_mul]
    _ = mat t *ᵥ (mat d⁻¹ *ᵥ v) :=
      (Matrix.mulVec_mulVec v (mat t) (mat d⁻¹)).symm
    _ = mat t *ᵥ (mu⁻¹ • v) := by rw [h5]
    _ = mu⁻¹ • (mat t *ᵥ v) := Matrix.mulVec_smul _ _ _

theorem sp4_smul_single_mem_fixSub_of_torus_le_normalizer (a : Kˣ) (ha1 : a ≠ 1) (haa : a ≠ a⁻¹)
    {R : Subgroup (StatedSp 2 K)}
    (hDR : torus 2 K ≤ normalizer (R : Set (StatedSp 2 K)))
    {w : Fin 2 ⊕ Fin 2 → K} (hw : w ∈ fixSub R) (c : Fin 2 ⊕ Fin 2) :
    w c • Pi.single c 1 ∈ fixSub R := by
  have ha1K : (a : K) ≠ 1 := fun h => ha1 (Units.ext h)
  have haaK : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => haa (Units.ext h)
  have ha1K' : ((a⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h
    exact ha1 (inv_eq_one.mp (Units.ext h))
  have haaK' : ((a⁻¹ : Kˣ) : K) ≠ (a : K) := fun h => haa (Units.ext h).symm
  rcases c with i | i
  · have hdW : ∀ u ∈ fixSub R,
        Matrix.diagonal (diagSp4TorusHomFun (sp4TorusParam i a)) *ᵥ u ∈ fixSub R := by
      intro u hu
      rw [← mat_torusHom_eq_diagonal (sp4TorusParam i a)]
      exact sp4_mulVec_mem_fixSub_of_mem_normalizer
        (hDR (torusHom_mem_torus (sp4TorusParam i a))) hu
    have hc : (diagSp4TorusHomFun (sp4TorusParam i a) (Sum.inl i) - 1) *
        (diagSp4TorusHomFun (sp4TorusParam i a) (Sum.inl i) - ((a⁻¹ : Kˣ) : K)) ≠ 0 := by
      rw [diagSp4TorusHomFun_sp4TorusParam_inl]
      simp only [if_pos rfl]
      exact mul_ne_zero (sub_ne_zero.mpr ha1K) (sub_ne_zero.mpr haaK)
    have hother : ∀ x, x ≠ Sum.inl i →
        (diagSp4TorusHomFun (sp4TorusParam i a) x - 1) *
          (diagSp4TorusHomFun (sp4TorusParam i a) x - ((a⁻¹ : Kˣ) : K)) = 0 := by
      rintro (m | m) hx
      · rw [diagSp4TorusHomFun_sp4TorusParam_inl]
        by_cases hm : m = i
        · subst hm; exact absurd rfl hx
        · simp only [if_neg hm]; rw [sub_self, zero_mul]
      · rw [diagSp4TorusHomFun_sp4TorusParam_inr]
        by_cases hm : m = i
        · subst hm; simp
        · simp only [if_neg hm]; rw [sub_self, zero_mul]
    exact smul_single_mem_of_diagonal_mulVec_mem
      (diagSp4TorusHomFun (sp4TorusParam i a)) 1 ((a⁻¹ : Kˣ) : K) (Sum.inl i)
      hc hother hdW hw
  · have hdW : ∀ u ∈ fixSub R,
        Matrix.diagonal (diagSp4TorusHomFun (sp4TorusParam i a)) *ᵥ u ∈ fixSub R := by
      intro u hu
      rw [← mat_torusHom_eq_diagonal (sp4TorusParam i a)]
      exact sp4_mulVec_mem_fixSub_of_mem_normalizer
        (hDR (torusHom_mem_torus (sp4TorusParam i a))) hu
    have hc : (diagSp4TorusHomFun (sp4TorusParam i a) (Sum.inr i) - 1) *
        (diagSp4TorusHomFun (sp4TorusParam i a) (Sum.inr i) - (a : K)) ≠ 0 := by
      rw [diagSp4TorusHomFun_sp4TorusParam_inr]
      simp only [if_pos rfl]
      exact mul_ne_zero (sub_ne_zero.mpr ha1K') (sub_ne_zero.mpr haaK')
    have hother : ∀ x, x ≠ Sum.inr i →
        (diagSp4TorusHomFun (sp4TorusParam i a) x - 1) *
          (diagSp4TorusHomFun (sp4TorusParam i a) x - (a : K)) = 0 := by
      rintro (m | m) hx
      · rw [diagSp4TorusHomFun_sp4TorusParam_inl]
        by_cases hm : m = i
        · subst hm; simp
        · simp only [if_neg hm]; rw [sub_self, zero_mul]
      · rw [diagSp4TorusHomFun_sp4TorusParam_inr]
        by_cases hm : m = i
        · subst hm; exact absurd rfl hx
        · simp only [if_neg hm]; rw [sub_self, zero_mul]
    exact smul_single_mem_of_diagonal_mulVec_mem
      (diagSp4TorusHomFun (sp4TorusParam i a)) 1 (a : K) (Sum.inr i)
      hc hother hdW hw

theorem sp4_single_swap_mem_of_single_mem_of_inv_torus {t : StatedSp 2 K}
    (hinv : ∀ d ∈ torus 2 K, t * d * t⁻¹ = d⁻¹)
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (htW : ∀ v ∈ W, mat t *ᵥ v ∈ W) (a : Kˣ) (ha1 : a ≠ 1) (haa : a ≠ a⁻¹)
    {c : Fin 2 ⊕ Fin 2} (hcW : Pi.single c 1 ∈ W) :
    Pi.single (Sum.swap c) 1 ∈ W := by
  have ha1K : (a : K) ≠ 1 := fun h => ha1 (Units.ext h)
  have haaK : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => haa (Units.ext h)
  have ha1K' : ((a⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h
    exact ha1 (inv_eq_one.mp (Units.ext h))
  have haaK' : ((a⁻¹ : Kˣ) : K) ≠ (a : K) := fun h => haa (Units.ext h).symm
  have hinj : Function.Injective (fun v : Fin 2 ⊕ Fin 2 → K => mat t *ᵥ v) := by
    have h := Matrix.mulVec_injective_of_isUnit
      (Units.isUnit ((t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K))
    simpa [mat] using h
  rcases c with i | i
  · let s := sp4TorusParam i a
    have hdt : torusHom s * t = t * (torusHom s)⁻¹ :=
      mul_eq_mul_inv_of_mem_torus t hinv (torusHom_mem_torus s)
    have heig : mat (torusHom s) *ᵥ Pi.single (Sum.inl i) 1 =
        (a : K) • Pi.single (Sum.inl i) 1 := by
      rw [mat_torusHom_eq_diagonal, Matrix.diagonal_mulVec_single,
        diagSp4TorusHomFun_sp4TorusParam_inl]
      funext x
      by_cases hx : x = Sum.inl i
      · subst hx; simp
      · simp [Pi.single_eq_of_ne hx]
    have htwist := mulVec_inv_smul_of_mulVec_eq_smul hdt (Units.ne_zero a) heig
    have hpartner : diagSp4TorusHomFun s (Sum.inr i) = ((a⁻¹ : Kˣ) : K) := by
      rw [diagSp4TorusHomFun_sp4TorusParam_inr]; simp
    have htwist' : mat (torusHom s) *ᵥ (mat t *ᵥ Pi.single (Sum.inl i) 1) =
        ((a⁻¹ : Kˣ) : K) • (mat t *ᵥ Pi.single (Sum.inl i) 1) := by
      simpa using htwist
    have huniq : ∀ x, x ≠ Sum.inr i →
        diagSp4TorusHomFun s x ≠ diagSp4TorusHomFun s (Sum.inr i) := by
      rintro (m | m) hx
      · rw [diagSp4TorusHomFun_sp4TorusParam_inl, hpartner]
        by_cases hm : m = i
        · subst hm; simp only [if_pos rfl]; exact haaK
        · simp only [if_neg hm]; exact Ne.symm ha1K'
      · rw [diagSp4TorusHomFun_sp4TorusParam_inr, hpartner]
        by_cases hm : m = i
        · subst hm; exact absurd rfl hx
        · simp only [if_neg hm]; exact Ne.symm ha1K'
    have htwist'' : Matrix.diagonal (diagSp4TorusHomFun s) *ᵥ
        (mat t *ᵥ Pi.single (Sum.inl i) 1) =
        diagSp4TorusHomFun s (Sum.inr i) • (mat t *ᵥ Pi.single (Sum.inl i) 1) := by
      rw [← mat_torusHom_eq_diagonal s]
      simpa [hpartner] using htwist'
    have hclass := eq_smul_single_of_diagonal_mulVec_eq
      (diagSp4TorusHomFun s) (Sum.inr i) huniq htwist''
    have hmem : mat t *ᵥ Pi.single (Sum.inl i) 1 ∈ W := htW _ hcW
    have hbase : Pi.single (Sum.inl i) 1 ≠ (0 : Fin 2 ⊕ Fin 2 → K) := by
      intro h
      have := congrFun h (Sum.inl i)
      simpa using this
    have hcoeff : (mat t *ᵥ Pi.single (Sum.inl i) 1) (Sum.inr i) ≠ 0 := by
      intro h0
      have hzero : mat t *ᵥ Pi.single (Sum.inl i) 1 = 0 := by
        rw [hclass, h0, zero_smul]
      exact hbase (hinj (by simpa [Matrix.mulVec_zero] using hzero))
    have hres := W.smul_mem ((mat t *ᵥ Pi.single (Sum.inl i) 1) (Sum.inr i))⁻¹
      (hclass ▸ hmem)
    rwa [smul_smul, inv_mul_cancel₀ hcoeff, one_smul] at hres
  · let s := sp4TorusParam i a
    have hdt : torusHom s * t = t * (torusHom s)⁻¹ :=
      mul_eq_mul_inv_of_mem_torus t hinv (torusHom_mem_torus s)
    have heig : mat (torusHom s) *ᵥ Pi.single (Sum.inr i) 1 =
        ((a⁻¹ : Kˣ) : K) • Pi.single (Sum.inr i) 1 := by
      rw [mat_torusHom_eq_diagonal, Matrix.diagonal_mulVec_single,
        diagSp4TorusHomFun_sp4TorusParam_inr]
      funext x
      by_cases hx : x = Sum.inr i
      · subst hx; simp
      · simp [Pi.single_eq_of_ne hx]
    have htwist := mulVec_inv_smul_of_mulVec_eq_smul hdt (Units.ne_zero (a⁻¹)) heig
    have hinvval : (((a⁻¹ : Kˣ) : K))⁻¹ = (a : K) := by
      rw [← Units.val_inv_eq_inv_val, inv_inv]
    have hpartner : diagSp4TorusHomFun s (Sum.inl i) = (a : K) := by
      rw [diagSp4TorusHomFun_sp4TorusParam_inl]; simp
    have htwist' : mat (torusHom s) *ᵥ (mat t *ᵥ Pi.single (Sum.inr i) 1) =
        (a : K) • (mat t *ᵥ Pi.single (Sum.inr i) 1) := by
      simpa [hinvval] using htwist
    have huniq : ∀ x, x ≠ Sum.inl i →
        diagSp4TorusHomFun s x ≠ diagSp4TorusHomFun s (Sum.inl i) := by
      rintro (m | m) hx
      · rw [diagSp4TorusHomFun_sp4TorusParam_inl, hpartner]
        by_cases hm : m = i
        · subst hm; exact absurd rfl hx
        · simp only [if_neg hm]; exact Ne.symm ha1K
      · rw [diagSp4TorusHomFun_sp4TorusParam_inr, hpartner]
        by_cases hm : m = i
        · subst hm; simp only [if_pos rfl]; exact haaK'
        · simp only [if_neg hm]; exact Ne.symm ha1K
    have htwist'' : Matrix.diagonal (diagSp4TorusHomFun s) *ᵥ
        (mat t *ᵥ Pi.single (Sum.inr i) 1) =
        diagSp4TorusHomFun s (Sum.inl i) • (mat t *ᵥ Pi.single (Sum.inr i) 1) := by
      rw [← mat_torusHom_eq_diagonal s]
      simpa [hpartner] using htwist'
    have hclass := eq_smul_single_of_diagonal_mulVec_eq
      (diagSp4TorusHomFun s) (Sum.inl i) huniq htwist''
    have hmem : mat t *ᵥ Pi.single (Sum.inr i) 1 ∈ W := htW _ hcW
    have hbase : Pi.single (Sum.inr i) 1 ≠ (0 : Fin 2 ⊕ Fin 2 → K) := by
      intro h
      have := congrFun h (Sum.inr i)
      simpa using this
    have hcoeff : (mat t *ᵥ Pi.single (Sum.inr i) 1) (Sum.inl i) ≠ 0 := by
      intro h0
      have hzero : mat t *ᵥ Pi.single (Sum.inr i) 1 = 0 := by
        rw [hclass, h0, zero_smul]
      exact hbase (hinj (by simpa [Matrix.mulVec_zero] using hzero))
    have hres := W.smul_mem ((mat t *ᵥ Pi.single (Sum.inr i) 1) (Sum.inl i))⁻¹
      (hclass ▸ hmem)
    rwa [smul_smul, inv_mul_cancel₀ hcoeff, one_smul] at hres

theorem sp4_mem_of_onPlane_of_singles_mem {i : Fin 2} {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hei : Pi.single (Sum.inl i) 1 ∈ W) (hfi : Pi.single (Sum.inr i) 1 ∈ W)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : OnPlane i v) : v ∈ W := by
  have hdecomp : v = v (Sum.inl i) • Pi.single (Sum.inl i) 1 +
      v (Sum.inr i) • Pi.single (Sum.inr i) 1 := by
    funext k
    rcases k with m | m
    · by_cases hm : m = i
      · subst hm; simp
      · have h0 := hv (Sum.inl m) (by simp [hm]) (by simp)
        simp [hm, h0]
    · by_cases hm : m = i
      · subst hm; simp
      · have h0 := hv (Sum.inr m) (by simp) (by simp [hm])
        simp [hm, h0]
  rw [hdecomp]
  exact W.add_mem (W.smul_mem _ hei) (W.smul_mem _ hfi)

theorem eq_bot_of_torus_le_normalizer_of_inv [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {t : StatedSp 2 K} (hinv : ∀ d ∈ torus 2 K, t * d * t⁻¹ = d⁻¹)
    {R : Subgroup (StatedSp 2 K)} (hR : IsPGroup 2 R)
    (hDR : torus 2 K ≤ normalizer (R : Set (StatedSp 2 K)))
    (htR : t ∈ normalizer (R : Set (StatedSp 2 K))) : R = ⊥ := by
  classical
  have hKeven : Even (Nat.card K) := by
    rw [even_iff_two_dvd]
    haveI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff K 2 (Fintype.card K)).mp
      (FiniteField.cast_card_eq_zero K)
  haveI : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
    omega
  obtain ⟨a, ha1⟩ := exists_ne (1 : Kˣ)
  have haa : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : (a : K) * (a : K) = 1 := by
      have h' : a * a = 1 := (congrArg (fun x : Kˣ => a * x) h).trans (mul_inv_cancel a)
      exact congrArg (fun u : Kˣ => (u : K)) h'
    rcases (mul_self_eq_one_iff.mp h2) with h1 | h1
    · exact Units.ext h1
    · have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
      rw [hneg] at h1
      exact Units.ext h1
  have hcoord : ∀ w ∈ fixSub R, ∀ c : Fin 2 ⊕ Fin 2, w c • Pi.single c 1 ∈ fixSub R :=
    fun w hw c => sp4_smul_single_mem_fixSub_of_torus_le_normalizer a ha1 haa hDR hw c
  have htW : ∀ v ∈ fixSub R, mat t *ᵥ v ∈ fixSub R :=
    fun v hv => sp4_mulVec_mem_fixSub_of_mem_normalizer htR hv
  have hswap : ∀ c : Fin 2 ⊕ Fin 2,
      Pi.single c 1 ∈ fixSub R → Pi.single (Sum.swap c) 1 ∈ fixSub R :=
    fun c hc => sp4_single_swap_mem_of_single_mem_of_inv_torus hinv htW a ha1 haa hc
  have hEvenV : Even (Nat.card (Fin 2 ⊕ Fin 2 → K)) := by
    rw [natCard_vec]
    exact hKeven.pow_of_ne_zero (by norm_num)
  letI : MulAction R (Fin 2 ⊕ Fin 2 → K) := vecMulAction R
  obtain ⟨w, hwne, hwfix⟩ := exists_fixed_ne (G := R) hR hEvenV
    (0 : Fin 2 ⊕ Fin 2 → K) (by
      intro r
      show mat r.1 *ᵥ (0 : Fin 2 ⊕ Fin 2 → K) = 0
      exact Matrix.mulVec_zero _)
  have hwW : w ∈ fixSub R := by
    rw [mem_fixSub]
    intro r hr
    change mat r *ᵥ w = w
    exact hwfix ⟨r, hr⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin 2 ⊕ Fin 2, w c ≠ 0 := by
    by_contra h
    push Not at h
    exact hwne (funext fun c => by simpa using h c)
  have hcW : Pi.single c 1 ∈ fixSub R := by
    have hmem := hcoord w hwW c
    have hres := (fixSub R).smul_mem (w c)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hres
  have finish : ∀ (i : Fin 2), Pi.single (Sum.inl i) 1 ∈ fixSub R →
      Pi.single (Sum.inr i) 1 ∈ fixSub R → R = ⊥ := by
    intro i hei hfi
    let j : Fin 2 := if i = 0 then 1 else 0
    have hij : i ≠ j := by fin_cases i <;> simp [j]
    have hfixP : ∀ g ∈ R, ∀ v, OnPlane i v → mat g *ᵥ v = v := by
      intro g hg v hv
      exact (mem_fixSub.mp (sp4_mem_of_onPlane_of_singles_mem hei hfi hv)) g hg
    have hRplane : ∀ g ∈ R, ∀ v, OnPlane j v → OnPlane j (mat g *ᵥ v) := by
      intro g hg v hv
      exact onPlane_of_fixes hij (fun u hu => hfixP g hg u hu) hv
    letI : MulAction R {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v} :=
      planeMulAction R j hRplane
    have hEvenJ : Even (Nat.card {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v}) := by
      rw [natCard_onPlane]
      exact hKeven.pow_of_ne_zero (by norm_num)
    obtain ⟨u, hu_ne, hu_fix⟩ := exists_fixed_ne (G := R) hR hEvenJ
      (⟨0, onPlane_zero j⟩ : {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v}) (by
        intro r
        apply Subtype.ext
        change mat r.1 *ᵥ (0 : Fin 2 ⊕ Fin 2 → K) = 0
        exact Matrix.mulVec_zero _)
    have huW : u.1 ∈ fixSub R := by
      rw [mem_fixSub]
      intro r hr
      exact congrArg Subtype.val (hu_fix ⟨r, hr⟩)
    have hu0 : u.1 ≠ 0 := by
      intro h
      exact hu_ne (Subtype.ext h)
    have hcj : u.1 (Sum.inl j) ≠ 0 ∨ u.1 (Sum.inr j) ≠ 0 := by
      by_contra h
      push Not at h
      apply hu0
      funext k
      rcases k with m | m
      · by_cases hm : m = j
        · subst hm; exact h.1
        · exact u.2 _ (by simp [hm]) (by simp)
      · by_cases hm : m = j
        · subst hm; exact h.2
        · exact u.2 _ (by simp) (by simp [hm])
    have hbase : ∀ c : Fin 2 ⊕ Fin 2, u.1 c ≠ 0 → Pi.single c 1 ∈ fixSub R := by
      intro c hc
      have hmem := hcoord u.1 huW c
      have hres := (fixSub R).smul_mem (u.1 c)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hres
    have hej : Pi.single (Sum.inl j) 1 ∈ fixSub R := by
      rcases hcj with hc | hc
      · exact hbase _ hc
      · simpa using hswap (Sum.inr j) (hbase _ hc)
    have hfj : Pi.single (Sum.inr j) 1 ∈ fixSub R := by
      rcases hcj with hc | hc
      · simpa using hswap (Sum.inl j) (hbase _ hc)
      · exact hbase _ hc
    have hcover : ∀ m : Fin 2, m = i ∨ m = j := by
      intro m
      fin_cases i <;> fin_cases m <;> simp [j]
    have hbasis : ∀ c : Fin 2 ⊕ Fin 2, Pi.single c 1 ∈ fixSub R := by
      rintro (m | m)
      · rcases hcover m with hm | hm
        · subst hm; exact hei
        · subst hm; exact hej
      · rcases hcover m with hm | hm
        · subst hm; exact hfi
        · subst hm; exact hfj
    have htop : fixSub R = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have hsingle : ∀ c : Fin 2 ⊕ Fin 2, Pi.single c (v c) = v c • Pi.single c 1 := by
        intro c
        funext x
        by_cases hx : x = c
        · subst hx; simp
        · simp [Pi.single_eq_of_ne hx]
      have hsum : (∑ c : Fin 2 ⊕ Fin 2, Pi.single c (v c)) = v :=
        LinearMap.sum_single_apply (fun _ : Fin 2 ⊕ Fin 2 => K) v
      have hdecomp : v = ∑ c : Fin 2 ⊕ Fin 2, v c • Pi.single c 1 := by
        calc
          v = ∑ c : Fin 2 ⊕ Fin 2, Pi.single c (v c) := hsum.symm
          _ = ∑ c : Fin 2 ⊕ Fin 2, v c • Pi.single c 1 :=
            Finset.sum_congr rfl fun c _ => hsingle c
      rw [hdecomp]
      exact (fixSub R).sum_mem fun c _ => (fixSub R).smul_mem _ (hbasis c)
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    exact mat_eq_one_of_forall (g := r) (fun v => by
      have hvW : v ∈ fixSub R := by rw [htop]; exact Submodule.mem_top
      exact (mem_fixSub.mp hvW) r hr)
  rcases c with i | i
  · exact finish i hcW (by simpa using hswap (Sum.inl i) hcW)
  · exact finish i (by simpa using hswap (Sum.inr i) hcW) hcW

end CFSG.ClassicalGroups.Symplectic.Sp4

end
