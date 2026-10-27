module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3OddOrderEigen
import CFSG.ClassicalGroups.UnitaryFlag.HomologyEigen
import CFSG.ClassicalGroups.UnitaryFlag.SU3TorusFixVec

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped Pointwise Matrix

variable {n : ℕ} {K : Type} [Field K]

structure SU3TorusFrame (h : UnitaryFieldData 2 n K) (T : Subgroup (unitarySU 2 n K 3)) where
  v : Fin 3 → K
  e : Fin 3 → K
  f : Fin 3 → K
  χ : ↥T →* Kˣ
  stdHermForm_v_v : stdHermForm h 3 v v ≠ 0
  stdHermForm_e_e : stdHermForm h 3 e e = 0
  stdHermForm_f_f : stdHermForm h 3 f f = 0
  stdHermForm_e_f : stdHermForm h 3 e f = 1
  stdHermForm_e_v : stdHermForm h 3 e v = 0
  stdHermForm_f_v : stdHermForm h 3 f v = 0
  smul_v : ∀ t : T, (t : unitarySU 2 n K 3) • v = v
  smul_e : ∀ t : T, (t : unitarySU 2 n K 3) • e = (χ t : K) • e
  smul_f : ∀ t : T, (t : unitarySU 2 n K 3) • f = (χ t : K)⁻¹ • f
  χ_injective : Function.Injective χ
  χ_pow : ∀ t : T, (χ t : K) ^ (2 ^ n - 1) = 1

private theorem sup_span_eq_span_range {e v f : Fin 3 → K} :
    (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) = Submodule.span K (Set.range ![e, v, f]) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · rw [Submodule.span_le]
        rintro x rfl
        exact Submodule.subset_span ⟨0, by simp⟩
      · rw [Submodule.span_le]
        rintro x rfl
        exact Submodule.subset_span ⟨1, by simp⟩
    · rw [Submodule.span_le]
      rintro x rfl
      exact Submodule.subset_span ⟨2, by simp⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self e))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self f)

private theorem linearIndependent_of_herm (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    LinearIndependent K ![e, v, f] := by
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  have hve : stdHermForm h 3 v e = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hev
  have hvf : stdHermForm h 3 v f = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hfv
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • e + g 1 • v + g 2 • f = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have h0 : g 0 = 0 := by
    have h := congrArg (stdHermForm h 3 f) hg'
    simp only [map_add, map_smul, smul_eq_mul, hfe, hfv, hf, mul_one, mul_zero,
      add_zero, map_zero] at h
    exact h
  have h1 : g 1 = 0 := by
    have h := congrArg (stdHermForm h 3 v) hg'
    simp only [map_add, map_smul, smul_eq_mul, hve, hvf, mul_zero, add_zero,
      zero_add, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hv
  have h2 : g 2 = 0 := by
    have h := congrArg (stdHermForm h 3 e) hg'
    simp only [map_add, map_smul, smul_eq_mul, he, hev, hef, mul_one, mul_zero,
      add_zero, zero_add, map_zero] at h
    exact h
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem sup_eq_top_of_herm (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) = ⊤ := by
  have hspan : Submodule.span K (Set.range ![e, v, f]) = ⊤ :=
    (linearIndependent_of_herm h hv he hf hef hev hfv).span_eq_top_of_card_eq_finrank'
      (by simp)
  rw [sup_span_eq_span_range, hspan]

private theorem stdHermForm_e_add (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (he : stdHermForm h 3 e e = 0) (hev : stdHermForm h 3 e v = 0)
    (hef : stdHermForm h 3 e f = 1) {x y z : K} :
    stdHermForm h 3 e (x • e + y • v + z • f) = z := by
  simp only [map_add, map_smul, smul_eq_mul, he, hev, hef, mul_zero, mul_one,
    add_zero, zero_add]

private theorem stdHermForm_f_add (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hef : stdHermForm h 3 e f = 1) (hfv : stdHermForm h 3 f v = 0)
    (hf : stdHermForm h 3 f f = 0) {x y z : K} :
    stdHermForm h 3 f (x • e + y • v + z • f) = x := by
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  simp only [map_add, map_smul, smul_eq_mul, hfe, hfv, hf, mul_one, mul_zero,
    add_zero]

private theorem stdHermForm_v_add (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) {x y z : K} :
    stdHermForm h 3 v (x • e + y • v + z • f) = y * stdHermForm h 3 v v := by
  have hve : stdHermForm h 3 v e = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hev
  have hvf : stdHermForm h 3 v f = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hfv
  simp only [map_add, map_smul, smul_eq_mul, hve, hvf, mul_zero, add_zero, zero_add]

private theorem mem_span_e_of_herm_eq_zero (h : UnitaryFieldData 2 n K) {v e f w : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    (hspan : (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) = ⊤)
    (hew : stdHermForm h 3 e w = 0) (hvw : stdHermForm h 3 v w = 0) :
    w ∈ K ∙ e := by
  have hw : w ∈ (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) := by rw [hspan]; trivial
  obtain ⟨u, hu, zf, hzf, huz⟩ := Submodule.mem_sup.mp hw
  obtain ⟨xe, hxe, yv, hyv, hxy⟩ := Submodule.mem_sup.mp hu
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hxe
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp hyv
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hzf
  have hz : z = 0 := by
    have hh := hew
    rw [← huz, ← hxy, stdHermForm_e_add h he hev hef] at hh
    exact hh
  have hy : y = 0 := by
    have hh := hvw
    rw [← huz, ← hxy, stdHermForm_v_add h hev hfv] at hh
    exact (mul_eq_zero.mp hh).resolve_right hv
  rw [← huz, ← hxy, hy, hz]
  simp only [zero_smul, add_zero]
  exact Submodule.smul_mem (K ∙ e) x (Submodule.mem_span_singleton_self e)

private theorem mem_span_v_of_herm_eq_zero (h : UnitaryFieldData 2 n K) {v e f w : Fin 3 → K}
    (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    (hspan : (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) = ⊤)
    (hew : stdHermForm h 3 e w = 0) (hfw : stdHermForm h 3 f w = 0) :
    w ∈ K ∙ v := by
  have hw : w ∈ (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) := by rw [hspan]; trivial
  obtain ⟨u, hu, zf, hzf, huz⟩ := Submodule.mem_sup.mp hw
  obtain ⟨xe, hxe, yv, hyv, hxy⟩ := Submodule.mem_sup.mp hu
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hxe
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp hyv
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hzf
  have hz : z = 0 := by
    have hh := hew
    rw [← huz, ← hxy, stdHermForm_e_add h he hev hef] at hh
    exact hh
  have hx : x = 0 := by
    have hh := hfw
    rw [← huz, ← hxy, stdHermForm_f_add h hef hfv hf] at hh
    exact hh
  rw [← huz, ← hxy, hx, hz]
  simp only [zero_smul, add_zero, zero_add]
  exact Submodule.smul_mem (K ∙ v) y (Submodule.mem_span_singleton_self v)

private theorem mem_span_f_of_herm_eq_zero (h : UnitaryFieldData 2 n K) {v e f w : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    (hspan : (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) = ⊤)
    (hfw : stdHermForm h 3 f w = 0) (hvw : stdHermForm h 3 v w = 0) :
    w ∈ K ∙ f := by
  have hw : w ∈ (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) := by rw [hspan]; trivial
  obtain ⟨u, hu, zf, hzf, huz⟩ := Submodule.mem_sup.mp hw
  obtain ⟨xe, hxe, yv, hyv, hxy⟩ := Submodule.mem_sup.mp hu
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hxe
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp hyv
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hzf
  have hx : x = 0 := by
    have hh := hfw
    rw [← huz, ← hxy, stdHermForm_f_add h hef hfv hf] at hh
    exact hh
  have hy : y = 0 := by
    have hh := hvw
    rw [← huz, ← hxy, stdHermForm_v_add h hev hfv] at hh
    exact (mul_eq_zero.mp hh).resolve_right hv
  rw [← huz, ← hxy, hx, hy]
  simp only [zero_smul, add_zero, zero_add]
  exact Submodule.smul_mem (K ∙ f) z (Submodule.mem_span_singleton_self f)

private theorem ext_of_herm (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    {g g' : unitarySU 2 n K 3} (hge : g • e = g' • e) (hgv : g • v = g' • v)
    (hgf : g • f = g' • f) : g = g' := by
  have hspan : Submodule.span K (Set.range ![e, v, f]) = ⊤ := by
    rw [← sup_span_eq_span_range]
    exact sup_eq_top_of_herm h hv he hf hef hev hfv
  have hlin : Matrix.mulVecLin ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.mulVecLin ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    refine LinearMap.ext_on hspan ?_
    rintro x ⟨i, rfl⟩
    fin_cases i
    · rw [← unitarySU_smul_def h g, ← unitarySU_smul_def h g']
      exact hge
    · rw [← unitarySU_smul_def h g, ← unitarySU_smul_def h g']
      exact hgv
    · rw [← unitarySU_smul_def h g, ← unitarySU_smul_def h g']
      exact hgf
  have hmat : Matrix.toLin' ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.toLin' ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simpa only [Matrix.toLin'_apply'] using hlin
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLin'.injective hmat

private theorem smul_eq_mulVec (h : UnitaryFieldData 2 n K) (g : unitarySU 2 n K 3)
    (x : Fin 3 → K) :
    g • x = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
  rw [unitarySU_smul_def h, Matrix.mulVecLin_apply]

private theorem pow_eq_one_of_pow_smul_eq_one
    {g : unitarySU 2 n K 3} {x : Fin 3 → K} {c : K} (hx : x ≠ 0) (hsmul : g • x = c • x)
    {m : ℕ} (hg : g ^ m = 1) : c ^ m = 1 := by
  have h1 : c ^ m • x = (1 : K) • x := by
    rw [← pow_smul_eq_smul_pow hsmul m, hg, one_smul, one_smul]
  exact smul_left_injective K hx h1

private theorem stdHermForm_eq_zero_of_smul_eigen (h : UnitaryFieldData 2 n K)
    {g : unitarySU 2 n K 3} {x y : Fin 3 → K} {μ ν : K} (hμ : h.bar μ = μ)
    (hμν : μ * ν ≠ 1) (hx : g • x = μ • x) (hy : g • y = ν • y) :
    stdHermForm h 3 x y = 0 := by
  refine stdHermForm_eq_zero_of_eigen h (B := (g : GL (Fin 3) K)) g.2 hμ hμν ?_ ?_
  · rwa [unitarySU_smul_def h, Matrix.mulVecLin_apply] at hx
  · rwa [unitarySU_smul_def h, Matrix.mulVecLin_apply] at hy

private theorem smul_inv_of_smul {g : unitarySU 2 n K 3}
    {x : Fin 3 → K} {c : K} (hc : c ≠ 0) (hx : g • x = c • x) :
    g⁻¹ • x = c⁻¹ • x := by
  rw [inv_smul_eq_iff, smul_comm g c⁻¹ x, hx, inv_smul_smul₀ hc]

private theorem torus_smul_mem_isotropic (h : UnitaryFieldData 2 n K)
    {T : Subgroup (unitarySU 2 n K 3)} {a t : T} {v e f : Fin 3 → K} {s : K}
    (hvv : stdHermForm h 3 v v ≠ 0) (hee : stdHermForm h 3 e e = 0)
    (hff : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    (hs : s ≠ 1) (hs_pow : s ^ (2 ^ n - 1) = 1)
    (hae : (a : unitarySU 2 n K 3) • e = s • e)
    (hav : (a : unitarySU 2 n K 3) • v = v)
    (haf : (a : unitarySU 2 n K 3) • f = s⁻¹ • f)
    (hcomm : (t : unitarySU 2 n K 3) * (a : unitarySU 2 n K 3) =
      (a : unitarySU 2 n K 3) * (t : unitarySU 2 n K 3)) :
    (t : unitarySU 2 n K 3) • e ∈ K ∙ e ∧ (t : unitarySU 2 n K 3) • f ∈ K ∙ f := by
  have := h.charP
  have hspan : (K ∙ e) ⊔ (K ∙ v) ⊔ (K ∙ f) = ⊤ :=
    sup_eq_top_of_herm h hvv hee hff hef hev hfv
  have hbar_s : h.bar s = s := bar_eq_self_of_pow_two_pow_sub_one_eq_one h hs_pow
  have hs2 : s * s ≠ 1 := fun h2 => hs (mul_self_eq_one_iff_eq_one.mp h2)
  have hsi : h.bar s⁻¹ = s⁻¹ := by rw [map_inv₀, hbar_s]
  have hsi2 : s⁻¹ * s⁻¹ ≠ 1 :=
    fun h2 => hs (inv_eq_one.mp (mul_self_eq_one_iff_eq_one.mp h2))
  constructor
  · have hae_t : (a : unitarySU 2 n K 3) • ((t : unitarySU 2 n K 3) • e) =
        s • ((t : unitarySU 2 n K 3) • e) := by
      rw [← mul_smul, ← hcomm, mul_smul, hae, ← smul_comm]
    refine mem_span_e_of_herm_eq_zero h hvv hee hef hev hfv hspan ?_ ?_
    · exact stdHermForm_eq_zero_of_smul_eigen h hbar_s hs2 hae hae_t
    · exact stdHermForm_eq_zero_of_smul_eigen h (μ := 1) (ν := s) (by simp)
        (by simpa using hs) (by simpa using hav) hae_t
  · have haf_t : (a : unitarySU 2 n K 3) • ((t : unitarySU 2 n K 3) • f) =
        s⁻¹ • ((t : unitarySU 2 n K 3) • f) := by
      rw [← mul_smul, ← hcomm, mul_smul, haf, ← smul_comm]
    refine mem_span_f_of_herm_eq_zero h hvv hff hef hev hfv hspan ?_ ?_
    · exact stdHermForm_eq_zero_of_smul_eigen h hsi hsi2 haf haf_t
    · exact stdHermForm_eq_zero_of_smul_eigen h (μ := 1) (ν := s⁻¹) (by simp)
        (by simpa using inv_ne_one.mpr hs) (by simpa using hav) haf_t

private theorem exists_torus_character (h : UnitaryFieldData 2 n K)
    {T : Subgroup (unitarySU 2 n K 3)} {v e f : Fin 3 → K}
    (hvv : stdHermForm h 3 v v ≠ 0) (hee : stdHermForm h 3 e e = 0)
    (hff : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    (he0 : e ≠ 0)
    (htv : ∀ t : T, (t : unitarySU 2 n K 3) • v = v)
    (hte_mem : ∀ t : T, (t : unitarySU 2 n K 3) • e ∈ K ∙ e)
    (htf_mem : ∀ t : T, (t : unitarySU 2 n K 3) • f ∈ K ∙ f)
    (hpow_t : ∀ t : T, (t : unitarySU 2 n K 3) ^ (2 ^ n - 1) = 1) :
    ∃ chi : T →* Kˣ, (∀ t : T, (t : unitarySU 2 n K 3) • e = (chi t : K) • e) ∧
      (∀ t : T, (t : unitarySU 2 n K 3) • f = (chi t : K)⁻¹ • f) ∧
      Function.Injective chi ∧ ∀ t : T, (chi t : K) ^ (2 ^ n - 1) = 1 := by
  choose lam hlam using fun t : T => Submodule.mem_span_singleton.mp (hte_mem t)
  have hlam' : ∀ t : T, (t : unitarySU 2 n K 3) • e = lam t • e := fun t => (hlam t).symm
  have hlam0 : ∀ t : T, lam t ≠ 0 := fun t h0 =>
    (smul_ne_zero_iff_ne (t : unitarySU 2 n K 3)).2 he0 (by rw [hlam' t, h0, zero_smul])
  have hlam_pow : ∀ t : T, (lam t) ^ (2 ^ n - 1) = 1 :=
    fun t => pow_eq_one_of_pow_smul_eq_one he0 (hlam' t) (hpow_t t)
  have hlam_bar : ∀ t : T, h.bar (lam t) = lam t :=
    fun t => bar_eq_self_of_pow_two_pow_sub_one_eq_one h (hlam_pow t)
  have hf_eq : ∀ t : T, (t : unitarySU 2 n K 3) • f = (lam t)⁻¹ • f := by
    intro t
    obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp (htf_mem t)
    have hiso := stdHermForm_smul_smul h t e f
    rw [hlam' t, ← hmu] at hiso
    have hcalc : stdHermForm h 3 (lam t • e) (mu • f) =
        h.bar (lam t) * mu * stdHermForm h 3 e f := by
      rw [map_smulₛₗ (stdHermForm h 3) (lam t) e, LinearMap.smul_apply,
        map_smul, smul_smul, smul_eq_mul]
    have hprod : lam t * mu = 1 := by
      have h1 : h.bar (lam t) * mu * stdHermForm h 3 e f = stdHermForm h 3 e f :=
        hcalc.symm.trans hiso
      rw [hef, mul_one, hlam_bar t] at h1
      exact h1
    rw [← hmu, eq_inv_of_mul_eq_one_right hprod]
  let chi : ↥T →* Kˣ :=
    { toFun := fun t => Units.mk0 (lam t) (hlam0 t)
      map_one' := by
        apply Units.ext
        change lam 1 = 1
        exact smul_left_injective K he0 (by
          change lam 1 • e = (1 : K) • e
          rw [← hlam' 1]
          simp)
      map_mul' := fun s t => by
        apply Units.ext
        change lam (s * t) = lam s * lam t
        refine smul_left_injective K he0 ?_
        change lam (s * t) • e = (lam s * lam t) • e
        rw [← hlam' (s * t), Subgroup.coe_mul, mul_smul, hlam' t, ← smul_comm,
          hlam' s, smul_smul, mul_comm] }
  refine ⟨chi, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hlam' t
  · intro t
    exact hf_eq t
  · intro s t hst
    have hlam_eq : lam s = lam t := by
      have h := congrArg (fun u : Kˣ => (u : K)) hst
      change (chi s : K) = (chi t : K) at h
      exact h
    have hse : (s : unitarySU 2 n K 3) • e = (t : unitarySU 2 n K 3) • e := by
      rw [hlam' s, hlam' t, hlam_eq]
    have hsv : (s : unitarySU 2 n K 3) • v = (t : unitarySU 2 n K 3) • v := by
      rw [htv s, htv t]
    have hsf : (s : unitarySU 2 n K 3) • f = (t : unitarySU 2 n K 3) • f := by
      rw [hf_eq s, hf_eq t, hlam_eq]
    exact Subtype.ext (ext_of_herm h hvv hee hff hef hev hfv hse hsv hsf)
  · intro t
    exact hlam_pow t

theorem nonempty_su3TorusFrame (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    {T : Subgroup (unitarySU 2 n K 3)} (hTc : IsMulCommutative T)
    (hT : Nat.card T = 2 ^ n - 1) : Nonempty (SU3TorusFrame h T) := by
  classical
  have := h.finite
  have := h.charP
  have : IsMulCommutative T := hTc
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard_gt : 1 < Nat.card T := by rw [hT]; omega
  have : Finite T := inferInstance
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  obtain ⟨a, ha⟩ := exists_ne (1 : T)
  have ha_ne : (a : unitarySU 2 n K 3) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  have hpow_t : ∀ t : T, (t : unitarySU 2 n K 3) ^ (2 ^ n - 1) = 1 := by
    intro t
    have hdvd : orderOf (t : unitarySU 2 n K 3) ∣ Nat.card T := T.orderOf_dvd_natCard t.2
    rw [hT] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have ha_pow : (a : unitarySU 2 n K 3) ^ (2 ^ n - 1) = 1 := hpow_t a
  obtain ⟨v, e, f, s, hs, hav, hae, haf, hvv, hee, hff, hef, hev, hfv, hfix⟩ :=
    exists_hyperbolic_eigenbasis_of_pow_eq_one h ha_ne ha_pow
  have hav' : (a : unitarySU 2 n K 3) • v = v := by rw [smul_eq_mulVec h]; exact hav
  have hae' : (a : unitarySU 2 n K 3) • e = s • e := by rw [smul_eq_mulVec h]; exact hae
  have haf' : (a : unitarySU 2 n K 3) • f = s⁻¹ • f := by rw [smul_eq_mulVec h]; exact haf
  have he0 : e ≠ 0 := by rintro rfl; simp at hef
  have hs_pow : s ^ (2 ^ n - 1) = 1 := pow_eq_one_of_pow_smul_eq_one he0 hae' ha_pow
  have hcomm : ∀ t : T, (t : unitarySU 2 n K 3) * (a : unitarySU 2 n K 3) =
      (a : unitarySU 2 n K 3) * (t : unitarySU 2 n K 3) :=
    fun t => by
      simpa using congrArg (fun x : T => (x : unitarySU 2 n K 3)) (mul_comm' t a)
  have hlines : ∀ t : T, (t : unitarySU 2 n K 3) • e ∈ K ∙ e ∧
      (t : unitarySU 2 n K 3) • f ∈ K ∙ f :=
    fun t => torus_smul_mem_isotropic h hvv hee hff hef hev hfv hs hs_pow hae' hav' haf'
      (hcomm t)
  have htv : ∀ t : T, (t : unitarySU 2 n K 3) • v = v := fun t => by
    rw [smul_eq_mulVec h]
    exact torus_fixes_of_eigenvector h hTc hT a.2 hav hvv hfix t t.2
  obtain ⟨chi, hchi_e, hchi_f, hchi_inj, hchi_pow⟩ :=
    exists_torus_character h hvv hee hff hef hev hfv he0 htv
      (fun t => (hlines t).1) (fun t => (hlines t).2) hpow_t
  exact ⟨v, e, f, chi, hvv, hee, hff, hef, hev, hfv, htv, hchi_e, hchi_f, hchi_inj, hchi_pow⟩

namespace SU3TorusFrame

variable {h : UnitaryFieldData 2 n K} {T : Subgroup (unitarySU 2 n K 3)} (F : SU3TorusFrame h T)

theorem sup_eq_top : (K ∙ F.e) ⊔ (K ∙ F.v) ⊔ (K ∙ F.f) = ⊤ :=
  sup_eq_top_of_herm h F.stdHermForm_v_v F.stdHermForm_e_e F.stdHermForm_f_f
    F.stdHermForm_e_f F.stdHermForm_e_v F.stdHermForm_f_v

theorem ext {g g' : unitarySU 2 n K 3} (he : g • F.e = g' • F.e) (hv : g • F.v = g' • F.v)
    (hf : g • F.f = g' • F.f) : g = g' :=
  ext_of_herm h F.stdHermForm_v_v F.stdHermForm_e_e F.stdHermForm_f_f
    F.stdHermForm_e_f F.stdHermForm_e_v F.stdHermForm_f_v he hv hf

theorem e_ne_zero : F.e ≠ 0 := by
  intro h0
  have h := F.stdHermForm_e_f
  rw [h0, map_zero] at h
  exact one_ne_zero h.symm

theorem f_ne_zero : F.f ≠ 0 := by
  intro h0
  have h := F.stdHermForm_e_f
  rw [h0, map_zero] at h
  exact one_ne_zero h.symm

theorem v_ne_zero : F.v ≠ 0 := by
  intro h0
  exact F.stdHermForm_v_v (by rw [h0, map_zero])

theorem stdHermForm_f_e : stdHermForm h 3 F.f F.e = 1 := by
  have h' := (stdHermForm_isSymm h 3).eq F.e F.f
  rw [F.stdHermForm_e_f, map_one] at h'
  exact h'.symm

theorem e_notMem_span_f : F.e ∉ K ∙ F.f := by
  intro he
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp he
  have hzero : stdHermForm h 3 F.e F.f = 0 := by
    rw [← hc, LinearMap.map_smulₛₗ₂]
    simp [F.stdHermForm_f_f]
  rw [F.stdHermForm_e_f] at hzero
  exact one_ne_zero hzero

theorem mul_comm_of_mem (F : SU3TorusFrame h T) {a b : unitarySU 2 n K 3} (ha : a ∈ T)
    (hb : b ∈ T) : a * b = b * a := by
  have h : (⟨a, ha⟩ : T) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    apply F.χ_injective
    rw [map_mul, map_mul, mul_comm]
  simpa using congrArg Subtype.val h

private theorem bar_chi (t : T) : h.bar (F.χ t : K) = (F.χ t : K) :=
  bar_eq_self_of_pow_two_pow_sub_one_eq_one h (F.χ_pow t)

private theorem chi_ne_one {t : T} (ht : t ≠ 1) : (F.χ t : K) ≠ 1 := by
  intro h1
  refine ht (F.χ_injective ?_)
  rw [show F.χ t = 1 from Units.ext h1, map_one]

private theorem chi_sq_ne_one {t : T} (ht : t ≠ 1) :
    (F.χ t : K) * (F.χ t : K) ≠ 1 := by
  have := h.charP
  intro h2
  exact chi_ne_one F ht (mul_self_eq_one_iff_eq_one.mp h2)

private theorem mem_span_e_of_smul_eq_chi {t : T} (ht : t ≠ 1) {w : Fin 3 → K}
    (hw : (t : unitarySU 2 n K 3) • w = (F.χ t : K) • w) : w ∈ K ∙ F.e := by
  have := h.charP
  refine mem_span_e_of_herm_eq_zero h F.stdHermForm_v_v F.stdHermForm_e_e
    F.stdHermForm_e_f F.stdHermForm_e_v F.stdHermForm_f_v F.sup_eq_top ?_ ?_
  · exact stdHermForm_eq_zero_of_smul_eigen h (bar_chi F t) (chi_sq_ne_one F ht)
      (by simpa using F.smul_e t) hw
  · exact stdHermForm_eq_zero_of_smul_eigen h (μ := 1) (ν := F.χ t) (by simp)
      (by simpa using chi_ne_one F ht) (by simpa using F.smul_v t) hw

private theorem mem_span_v_of_smul_eq_one {t : T} (ht : t ≠ 1) {w : Fin 3 → K}
    (hw : (t : unitarySU 2 n K 3) • w = (1 : K) • w) : w ∈ K ∙ F.v := by
  have := h.charP
  have hbar : h.bar (F.χ t : K)⁻¹ = (F.χ t : K)⁻¹ := by rw [map_inv₀, bar_chi F t]
  refine mem_span_v_of_herm_eq_zero h F.stdHermForm_e_e
    F.stdHermForm_f_f F.stdHermForm_e_f F.stdHermForm_e_v F.stdHermForm_f_v
    F.sup_eq_top ?_ ?_
  · exact stdHermForm_eq_zero_of_smul_eigen h (bar_chi F t)
      (by simpa using chi_ne_one F ht) (by simpa using F.smul_e t) hw
  · exact stdHermForm_eq_zero_of_smul_eigen h hbar
      (by simpa using inv_ne_one.mpr (chi_ne_one F ht)) (by simpa using F.smul_f t) hw

private theorem mem_span_f_of_smul_eq_chi_inv {t : T} (ht : t ≠ 1) {w : Fin 3 → K}
    (hw : (t : unitarySU 2 n K 3) • w = (F.χ t : K)⁻¹ • w) : w ∈ K ∙ F.f := by
  have := h.charP
  have hbar : h.bar (F.χ t : K)⁻¹ = (F.χ t : K)⁻¹ := by rw [map_inv₀, bar_chi F t]
  have hne : (F.χ t : K)⁻¹ ≠ 1 := inv_ne_one.mpr (chi_ne_one F ht)
  refine mem_span_f_of_herm_eq_zero h F.stdHermForm_v_v
    F.stdHermForm_f_f F.stdHermForm_e_f F.stdHermForm_e_v F.stdHermForm_f_v
    F.sup_eq_top ?_ ?_
  · exact stdHermForm_eq_zero_of_smul_eigen h hbar
      (fun h2 => hne (mul_self_eq_one_iff_eq_one.mp h2)) (by simpa using F.smul_f t) hw
  · exact stdHermForm_eq_zero_of_smul_eigen h (μ := 1) (ν := (F.χ t : K)⁻¹) (by simp)
      (by simpa using hne) (by simpa using F.smul_v t) hw

private theorem mem_span_e_or_f_of_smul_eq_of_ne_one {t : T} (ht : t ≠ 1) {w : Fin 3 → K}
    {c : K} (hw : (t : unitarySU 2 n K 3) • w = c • w) (hc : c ≠ 1) :
    w ∈ K ∙ F.e ∨ w ∈ K ∙ F.f := by
  have := h.charP
  have hvw : stdHermForm h 3 F.v w = 0 :=
    stdHermForm_eq_zero_of_smul_eigen h (μ := 1) (ν := c) (by simp) (by rwa [one_mul])
      (by simpa using F.smul_v t) hw
  have hwtop : w ∈ (K ∙ F.e) ⊔ (K ∙ F.v) ⊔ (K ∙ F.f) := by rw [F.sup_eq_top]; trivial
  obtain ⟨u, hu, zf, hzf, huz⟩ := Submodule.mem_sup.mp hwtop
  obtain ⟨xe, hxe, yv, hyv, hxy⟩ := Submodule.mem_sup.mp hu
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hxe
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp hyv
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hzf
  have hy : y = 0 := by
    have hh := hvw
    rw [← huz, ← hxy, stdHermForm_v_add h F.stdHermForm_e_v F.stdHermForm_f_v] at hh
    exact (mul_eq_zero.mp hh).resolve_right F.stdHermForm_v_v
  by_cases hcχ : (F.χ t : K) * c = 1
  · right
    have hcinv : c = (F.χ t : K)⁻¹ := eq_inv_of_mul_eq_one_right hcχ
    have hcne : c ≠ 1 := by rw [hcinv]; exact inv_ne_one.mpr (chi_ne_one F ht)
    have hcc : c * c ≠ 1 := fun h2 => hcne (mul_self_eq_one_iff_eq_one.mp h2)
    have hbar : h.bar (F.χ t : K)⁻¹ = (F.χ t : K)⁻¹ := by rw [map_inv₀, bar_chi F t]
    have hprod : (F.χ t : K)⁻¹ * c ≠ 1 := by simpa [hcinv] using hcc
    have hfw : stdHermForm h 3 F.f w = 0 :=
      stdHermForm_eq_zero_of_smul_eigen h hbar hprod (by simpa using F.smul_f t) hw
    have hx : x = 0 := by
      have hh := hfw
      rw [← huz, ← hxy, stdHermForm_f_add h F.stdHermForm_e_f F.stdHermForm_f_v
        F.stdHermForm_f_f] at hh
      exact hh
    rw [← huz, ← hxy, hx, hy]
    simp only [zero_smul, add_zero, zero_add]
    exact Submodule.smul_mem (K ∙ F.f) z (Submodule.mem_span_singleton_self F.f)
  · left
    have hew : stdHermForm h 3 F.e w = 0 :=
      stdHermForm_eq_zero_of_smul_eigen h (bar_chi F t) hcχ (by simpa using F.smul_e t) hw
    have hz : z = 0 := by
      have hh := hew
      rw [← huz, ← hxy, stdHermForm_e_add h F.stdHermForm_e_e F.stdHermForm_e_v
        F.stdHermForm_e_f] at hh
      exact hh
    rw [← huz, ← hxy, hy, hz]
    simp only [zero_smul, add_zero]
    exact Submodule.smul_mem (K ∙ F.e) x (Submodule.mem_span_singleton_self F.e)

private theorem not_both_mem_span (x : Fin 3 → K) {g : unitarySU 2 n K 3}
    (he : g • F.e ∈ K ∙ x) (hf : g • F.f ∈ K ∙ x) : False := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hf
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact (smul_ne_zero_iff_ne g).2 (e_ne_zero F) ha.symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb
    exact (smul_ne_zero_iff_ne g).2 (f_ne_zero F) hb.symm
  have he' : F.e = a • (g⁻¹ • x) := by rw [← smul_comm g⁻¹ a x, ha, inv_smul_smul]
  have hf' : F.f = b • (g⁻¹ • x) := by rw [← smul_comm g⁻¹ b x, hb, inv_smul_smul]
  have hx' : g⁻¹ • x = a⁻¹ • F.e := by
    have h := congrArg (fun y => a⁻¹ • y) he'
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h
    exact h.symm
  have hfe : F.f = (b * a⁻¹) • F.e := by rw [hf', hx', smul_smul]
  have hzero : stdHermForm h 3 F.e F.f = 0 := by
    rw [hfe, map_smul, smul_eq_mul, F.stdHermForm_e_e, mul_zero]
  rw [F.stdHermForm_e_f] at hzero
  exact one_ne_zero hzero

theorem eq_one_of_pow_two_pow_eq_one {g : unitarySU 2 n K 3} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (he : g • F.e ∈ K ∙ F.e) (hv : g • F.v ∈ K ∙ F.v) (hf : g • F.f ∈ K ∙ F.f) : g = 1 := by
  have := h.charP
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  have ha1 : a = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 a).mp
      (by simpa using pow_eq_one_of_pow_smul_eq_one (e_ne_zero F) ha.symm hg)
  have hb1 : b = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 b).mp
      (by simpa using pow_eq_one_of_pow_smul_eq_one (v_ne_zero F) hb.symm hg)
  have hc1 : c = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 k 1 c).mp
      (by simpa using pow_eq_one_of_pow_smul_eq_one (f_ne_zero F) hc.symm hg)
  refine F.ext ?_ ?_ ?_
  · rw [← ha, ha1, one_smul, one_smul]
  · rw [← hb, hb1, one_smul, one_smul]
  · rw [← hc, hc1, one_smul, one_smul]

theorem smul_mem_of_commute {t : T} (ht : t ≠ 1) {g : unitarySU 2 n K 3}
    (hg : g * t = t * g) : g • F.e ∈ K ∙ F.e ∧ g • F.v ∈ K ∙ F.v ∧ g • F.f ∈ K ∙ F.f := by
  have hge : (t : unitarySU 2 n K 3) • (g • F.e) = (F.χ t : K) • (g • F.e) := by
    rw [← mul_smul, hg.symm, mul_smul, F.smul_e t, ← smul_comm]
  have hgv : (t : unitarySU 2 n K 3) • (g • F.v) = (1 : K) • (g • F.v) := by
    rw [← mul_smul, hg.symm, mul_smul, F.smul_v t, one_smul]
  have hgf : (t : unitarySU 2 n K 3) • (g • F.f) = (F.χ t : K)⁻¹ • (g • F.f) := by
    rw [← mul_smul, hg.symm, mul_smul, F.smul_f t, ← smul_comm]
  exact ⟨mem_span_e_of_smul_eq_chi F ht hge, mem_span_v_of_smul_eq_one F ht hgv,
    mem_span_f_of_smul_eq_chi_inv F ht hgf⟩

theorem smul_mem_of_conj_eq_inv {t : T} (ht : t ≠ 1) {g : unitarySU 2 n K 3}
    (hg : g * t * g⁻¹ = (t : unitarySU 2 n K 3)⁻¹) :
    g • F.e ∈ K ∙ F.f ∧ g • F.v ∈ K ∙ F.v ∧ g • F.f ∈ K ∙ F.e := by
  have hconj : (t : unitarySU 2 n K 3) = g⁻¹ * (t : unitarySU 2 n K 3)⁻¹ * g := by
    calc (t : unitarySU 2 n K 3) = g⁻¹ * (g * (t : unitarySU 2 n K 3) * g⁻¹) * g := by
          group
      _ = g⁻¹ * (t : unitarySU 2 n K 3)⁻¹ * g := by rw [hg]
  have hconj' : g⁻¹ * (t : unitarySU 2 n K 3) * g = (t : unitarySU 2 n K 3)⁻¹ := by
    calc g⁻¹ * (t : unitarySU 2 n K 3) * g =
          (g⁻¹ * (t : unitarySU 2 n K 3)⁻¹ * g)⁻¹ := by group
      _ = (t : unitarySU 2 n K 3)⁻¹ := by rw [← hconj]
  have htg : (t : unitarySU 2 n K 3) * g = g * (t : unitarySU 2 n K 3)⁻¹ := by
    calc (t : unitarySU 2 n K 3) * g = g * (g⁻¹ * (t : unitarySU 2 n K 3) * g) := by
          group
      _ = g * (t : unitarySU 2 n K 3)⁻¹ := by rw [hconj']
  have he_inv : (t : unitarySU 2 n K 3)⁻¹ • F.e = (F.χ t : K)⁻¹ • F.e :=
    smul_inv_of_smul (Units.ne_zero (F.χ t)) (F.smul_e t)
  have hv_inv : (t : unitarySU 2 n K 3)⁻¹ • F.v = (1 : K) • F.v := by
    have h := smul_inv_of_smul (g := (t : unitarySU 2 n K 3)) (x := F.v) (c := 1) one_ne_zero
      (by simpa using F.smul_v t)
    simpa using h
  have hf_inv : (t : unitarySU 2 n K 3)⁻¹ • F.f = (F.χ t : K) • F.f := by
    simpa using smul_inv_of_smul (inv_ne_zero (Units.ne_zero (F.χ t))) (F.smul_f t)
  have hge : (t : unitarySU 2 n K 3) • (g • F.e) = (F.χ t : K)⁻¹ • (g • F.e) := by
    rw [← mul_smul, htg, mul_smul, he_inv, ← smul_comm]
  have hgv : (t : unitarySU 2 n K 3) • (g • F.v) = (1 : K) • (g • F.v) := by
    rw [← mul_smul, htg, mul_smul, hv_inv, one_smul, one_smul]
  have hgf : (t : unitarySU 2 n K 3) • (g • F.f) = (F.χ t : K) • (g • F.f) := by
    rw [← mul_smul, htg, mul_smul, hf_inv, ← smul_comm]
  exact ⟨mem_span_f_of_smul_eq_chi_inv F ht hge, mem_span_v_of_smul_eq_one F ht hgv,
    mem_span_e_of_smul_eq_chi F ht hgf⟩

theorem smul_mem_of_mem_normalizer (hT1 : T ≠ ⊥) {g : unitarySU 2 n K 3}
    (hg : g ∈ Subgroup.normalizer (T : Set (unitarySU 2 n K 3))) :
    g • F.v ∈ K ∙ F.v ∧ ((g • F.e ∈ K ∙ F.e ∧ g • F.f ∈ K ∙ F.f) ∨
      (g • F.e ∈ K ∙ F.f ∧ g • F.f ∈ K ∙ F.e)) := by
  obtain ⟨t, htT, ht1⟩ := (Subgroup.bot_or_exists_ne_one T).resolve_left hT1
  let tT : T := ⟨t, htT⟩
  have htT1 : tT ≠ 1 := by
    intro h
    exact ht1 (congrArg Subtype.val h)
  let s : T := ⟨g * (tT : unitarySU 2 n K 3) * g⁻¹,
    (Subgroup.mem_normalizer_iff.mp hg (tT : unitarySU 2 n K 3)).mp htT⟩
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    have hval : (s : unitarySU 2 n K 3) = 1 := congrArg Subtype.val h
    have h2 : g * (tT : unitarySU 2 n K 3) * g⁻¹ = 1 := hval
    have : (tT : unitarySU 2 n K 3) = 1 := by
      calc (tT : unitarySU 2 n K 3) =
            g⁻¹ * (g * (tT : unitarySU 2 n K 3) * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h2]
        _ = 1 := by group
    exact this
  have hconj : ∀ w : Fin 3 → K, (s : unitarySU 2 n K 3) • (g • w) =
      g • ((tT : unitarySU 2 n K 3) • w) := by
    intro w
    rw [← mul_smul, ← mul_smul]
    congr 1
    change (g * (tT : unitarySU 2 n K 3) * g⁻¹) * g = g * (tT : unitarySU 2 n K 3)
    group
  have hgv : (s : unitarySU 2 n K 3) • (g • F.v) = (1 : K) • (g • F.v) := by
    rw [hconj, F.smul_v tT, one_smul]
  have hge : (s : unitarySU 2 n K 3) • (g • F.e) = (F.χ tT : K) • (g • F.e) := by
    rw [hconj, F.smul_e tT, ← smul_comm]
  have hgf : (s : unitarySU 2 n K 3) • (g • F.f) = (F.χ tT : K)⁻¹ • (g • F.f) := by
    rw [hconj, F.smul_f tT, ← smul_comm]
  have hge' : g • F.e ∈ K ∙ F.e ∨ g • F.e ∈ K ∙ F.f :=
    mem_span_e_or_f_of_smul_eq_of_ne_one F hs1 hge (chi_ne_one F htT1)
  have hgf' : g • F.f ∈ K ∙ F.e ∨ g • F.f ∈ K ∙ F.f :=
    mem_span_e_or_f_of_smul_eq_of_ne_one F hs1 hgf
      (by simpa using inv_ne_one.mpr (chi_ne_one F htT1))
  refine ⟨mem_span_v_of_smul_eq_one F hs1 hgv, ?_⟩
  rcases hge' with he | he <;> rcases hgf' with hf | hf
  · exfalso
    exact not_both_mem_span F F.e he hf
  · exact Or.inl ⟨he, hf⟩
  · exact Or.inr ⟨he, hf⟩
  · exfalso
    exact not_both_mem_span F F.f he hf

theorem eq_or_eq_of_smul_eq (hT1 : T ≠ ⊥) {Y : Submodule K (Fin 3 → K)}
    (hY : Y ∈ isotropicLines h 3) (hTY : ∀ t ∈ T, t • Y = Y) : Y = K ∙ F.e ∨ Y = K ∙ F.f := by
  have := h.charP
  obtain ⟨t, htT, ht1⟩ := (Subgroup.bot_or_exists_ne_one T).resolve_left hT1
  let tT : T := ⟨t, htT⟩
  have htT1 : tT ≠ 1 := by
    intro h
    exact ht1 (congrArg Subtype.val h)
  have hYfin : Module.finrank K Y = 1 := hY.1
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hYfin
    omega
  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hYne
  have hYeq : Y = K ∙ y := eq_span_singleton_of_mem_of_finrank_eq_one hYfin hyY hy0
  have hty : (tT : unitarySU 2 n K 3) • y ∈ K ∙ y := by
    have hmem : (tT : unitarySU 2 n K 3) • y ∈ (tT : unitarySU 2 n K 3) • Y :=
      Submodule.smul_mem_pointwise_smul y (tT : unitarySU 2 n K 3) Y hyY
    rwa [hTY (tT : unitarySU 2 n K 3) htT, hYeq] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hty
  by_cases hc1 : c = 1
  · have hw : (tT : unitarySU 2 n K 3) • y = (1 : K) • y := by rw [← hc, hc1]
    have hyv : y ∈ K ∙ F.v := mem_span_v_of_smul_eq_one F htT1 hw
    exfalso
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hyv
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact hy0 ha.symm
    have hvY : F.v ∈ Y := by
      rw [hYeq]
      have hva : a⁻¹ • y = F.v := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [← hva]
      exact Submodule.smul_mem (K ∙ y) a⁻¹ (Submodule.mem_span_singleton_self y)
    exact F.stdHermForm_v_v (hY.2 F.v hvY)
  · rcases mem_span_e_or_f_of_smul_eq_of_ne_one F htT1 (c := c) hc.symm hc1 with hy | hy
    · left
      rw [hYeq]
      exact (eq_span_singleton_of_mem_of_finrank_eq_one
        (finrank_span_singleton (e_ne_zero F)) hy hy0).symm
    · right
      rw [hYeq]
      exact (eq_span_singleton_of_mem_of_finrank_eq_one
        (finrank_span_singleton (f_ne_zero F)) hy hy0).symm

end SU3TorusFrame

end CFSG.ClassicalGroups.UnitaryFlag
