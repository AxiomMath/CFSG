module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Orbits
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Generation

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Action

@[expose] def miyamotoI2Scalar : Kˣ →* Kˣ :=
  powMonoidHom 2 * (powMonoidHom (2 ^ f - 1))⁻¹

theorem coe_miyamotoI2Scalar (a₀ : Kˣ) :
    ((miyamotoI2Scalar (f := f) a₀ : Kˣ) : K) = (a₀ : K) ^ 2 * ((a₀ : K) ^ (2 ^ f - 1))⁻¹ := by
  simp [miyamotoI2Scalar]

variable [CharP K 2]

include h in
theorem exists_miyamotoI2_scalar (γ : Kˣ) : ∃ a₀ : Kˣ, miyamotoI2Scalar (f := f) a₀ = γ := by
  have := h.finite
  have hinj : Function.Injective (miyamotoI2Scalar (f := f) (K := K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a₀ ha₀
    rw [MonoidHom.mem_ker, Units.ext_iff, coe_miyamotoI2Scalar, Units.val_one] at ha₀
    have ha0 : (a₀ : K) ≠ 0 := a₀.ne_zero
    have hp0 : (a₀ : K) ^ (2 ^ f - 1) ≠ 0 := pow_ne_zero _ ha0
    have e : (a₀ : K) ^ 2 = (a₀ : K) ^ (2 ^ f - 1) := by
      field_simp at ha₀
      exact ha₀
    have hN : ((a₀ : K) * h.bar a₀) ^ 2 = 1 := by
      rw [mul_pow, ← map_pow, e]
      exact pow_sub_one_mul_bar h ha0
    have hN1 : (a₀ : K) * h.bar a₀ = 1 := eq_one_of_sq_eq_one hN
    have h4 : ((a₀ : K) ^ 2) ^ 2 = 1 := by
      rw [← hN1, ← pow_sub_one_mul_sq h, ← e]
      ring
    have : (a₀ : K) = 1 := eq_one_of_sq_eq_one (eq_one_of_sq_eq_one h4)
    exact (mem_bot).2 (Units.ext this)
  exact (Finite.injective_iff_surjective.1 hinj) γ

omit [CharP K 2] in
theorem miyamotoI2Hom_conj_A2 (a₀ : Kˣ) (a c d : K) :
    (miyamotoI2Hom h a₀)⁻¹ * miyamotoXGL h a 0 c d * miyamotoI2Hom h a₀ =
      miyamotoXGL h ((miyamotoI2Scalar (f := f) a₀ : Kˣ) * a) 0
        ((miyamotoI2Scalar (f := f) a₀ : Kˣ) * c) ((a₀ : K) ^ 2 * h.bar ((a₀ : K) ^ 2) * d) := by
  rw [miyamotoI2Hom_conj, coe_miyamotoI2Scalar]

theorem rootB_conj_A2 {l : K} (hl : h.bar l = l) (a c d : K) :
    (miyamotoXGL h 0 l 0 0)⁻¹ * miyamotoXGL h a 0 c d * miyamotoXGL h 0 l 0 0 =
      miyamotoXGL h a 0 (c + a * l) d := by
  rw [miyamotoXGL_conj h hl (map_zero _), miyamotoXGL_inj]
  refine ⟨rfl, rfl, by ring, by simp⟩

omit [CharP K 2] in
theorem diagN2_conj_A2 {μ : Kˣ} (hμ : h.bar μ = μ) (a c d : K) :
    (miyamotoIHom h (1, μ))⁻¹ * miyamotoXGL h a 0 c d * miyamotoIHom h (1, μ) =
      miyamotoXGL h ((μ : K)⁻¹ * a) 0 (μ * c) d := by
  rw [miyamotoIHom_conj, miyamotoXGL_inj]
  refine ⟨by simp, by simp, by simp [hμ], by simp⟩

omit [CharP K 2] in
theorem miyamotoR2_conj_A2 (a c d : K) :
    (miyamotoR2 K)⁻¹ * miyamotoXGL h a 0 c d * miyamotoR2 K = miyamotoXGL h c 0 a d := by
  apply Units.ext
  rw [show (miyamotoR2 K)⁻¹ = miyamotoR2 K from inv_eq_of_mul_eq_one_right miyamotoR2_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP K 2] in
theorem miyamotoIHom_one_mem_N2 {μ : Kˣ} (hμ : h.bar μ = μ) :
    miyamotoIHom h (1, μ) ∈ miyamotoN2 h := by
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  refine (mem_miyamotoN2 h).2 ⟨!![(μ : K), 0; 0, (μ : K)⁻¹], by simp [Matrix.det_fin_two, hμ0],
    fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [map_inv₀, hμ]
  · rw [coe_miyamotoIHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoN2Mat, hμ]

end Action

section Orbits

variable [CharP K 2]

omit [CharP K 2] in
theorem miyamotoI2Hom_mem_I2_sup_N2 (a₀ : Kˣ) :
    miyamotoI2Hom h a₀ ∈ miyamotoI2 h ⊔ miyamotoN2 h :=
  mem_sup_left ⟨a₀, rfl⟩

omit [CharP K 2] in
theorem rootB_mem_I2_sup_N2 {l : K} (hl : h.bar l = l) :
    miyamotoXGL h 0 l 0 0 ∈ miyamotoI2 h ⊔ miyamotoN2 h :=
  mem_sup_right (miyamotoRootB_le_N2 h ⟨l, hl, rfl⟩)

theorem exists_I2_conj_scalar (γ : Kˣ) (a c d : K) :
    ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∃ d' : K,
      g⁻¹ * miyamotoXGL h a 0 c d * g = miyamotoXGL h (γ * a) 0 (γ * c) d' := by
  obtain ⟨a₀, ha₀⟩ := exists_miyamotoI2_scalar h γ
  refine ⟨_, miyamotoI2Hom_mem_I2_sup_N2 h a₀, (a₀ : K) ^ 2 * h.bar ((a₀ : K) ^ 2) * d, ?_⟩
  rw [miyamotoI2Hom_conj_A2, ha₀]

theorem conj_conj_eq {G : Type*} [Group G] {x y z g₁ g₂ : G} (e₁ : g₁⁻¹ * x * g₁ = y)
    (e₂ : g₂⁻¹ * y * g₂ = z) : (g₁ * g₂)⁻¹ * x * (g₁ * g₂) = z := by
  rw [← e₂, ← e₁]
  group

theorem exists_conj_normal_involution {a c d : K} (hac : a ≠ 0 ∨ c ≠ 0)
    (htr : h.bar a * c + a * h.bar c = 0) :
    ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∃ d' : K,
      g⁻¹ * miyamotoXGL h a 0 c d * g = miyamotoXGL h 1 0 0 d' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ {a c d : K}, a ≠ 0 → h.bar a * c + a * h.bar c = 0 →
      ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∃ d' : K,
        g⁻¹ * miyamotoXGL h a 0 c d * g = miyamotoXGL h 1 0 0 d' := by
    intro a c d ha htr
    have hba : h.bar a ≠ 0 := by simpa using ha
    have hl : h.bar (c / a) = c / a := by
      rw [map_div₀, div_eq_div_iff hba ha]
      linear_combination -htr + (a * h.bar c) * h2
    obtain ⟨g, hg, d', e⟩ := exists_I2_conj_scalar h (Units.mk0 a ha)⁻¹ a 0 d
    refine ⟨miyamotoXGL h 0 (c / a) 0 0 * g, mul_mem (rootB_mem_I2_sup_N2 h hl) hg, d',
      conj_conj_eq (rootB_conj_A2 h hl a c d) ?_⟩
    rw [show c + a * (c / a) = 0 by field_simp; linear_combination c * h2, e]
    simp [ha]
  rcases hac with ha | hc
  · exact key ha htr
  · obtain ⟨g, hg, d', e⟩ := key (a := c) (c := a) (d := d) hc (by linear_combination htr)
    exact ⟨miyamotoR2 K * g, mul_mem (mem_sup_right (miyamotoR2_mem_N2 h)) hg, d',
      conj_conj_eq (miyamotoR2_conj_A2 h a c d) e⟩

theorem exists_conj_normal_noninvolution {ω₀ : K} (hω₀ : ω₀ + h.bar ω₀ = 1) {a c d : K}
    (htr : h.bar a * c + a * h.bar c ≠ 0) :
    ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∃ d' : K,
      g⁻¹ * miyamotoXGL h a 0 c d * g = miyamotoXGL h 1 0 ω₀ d' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  have ha : a ≠ 0 := by
    rintro rfl
    exact htr (by simp)
  have hba : h.bar a ≠ 0 := by simpa using ha
  obtain ⟨g₁, hg₁, d₁, e₁⟩ := exists_I2_conj_scalar h (Units.mk0 a ha)⁻¹ a c d
  have hc₁ : (((Units.mk0 a ha)⁻¹ : Kˣ) : K) * c +
      h.bar ((((Units.mk0 a ha)⁻¹ : Kˣ) : K) * c) ≠ 0 := by
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀]
    intro e
    apply htr
    field_simp at e
    linear_combination e
  set c₁ := (((Units.mk0 a ha)⁻¹ : Kˣ) : K) * c with hc₁def
  have htrF : h.bar (c₁ + h.bar c₁) = c₁ + h.bar c₁ := by rw [map_add, hbb, add_comm]
  obtain ⟨μ, hμ2, hμF⟩ := exists_sq_eq_of_charTwo h (c₁ + h.bar c₁)⁻¹
  have hμ : h.bar μ = μ := hμF (by rw [map_inv₀, htrF])
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [sq, zero_mul] at hμ2
    exact inv_ne_zero hc₁ hμ2.symm
  obtain ⟨g₂, hg₂, d₂, e₂⟩ := exists_I2_conj_scalar h (Units.mk0 μ hμ0) (μ⁻¹ * 1) (μ * c₁) d₁
  have hl : h.bar (ω₀ + μ ^ 2 * c₁) = ω₀ + μ ^ 2 * c₁ := by
    rw [← add_bar_eq_zero_iff h, map_add, map_mul, map_pow, hμ]
    have : μ ^ 2 * (c₁ + h.bar c₁) = 1 := by rw [hμ2, inv_mul_cancel₀ hc₁]
    linear_combination hω₀ + this + h2
  have hμ' : h.bar ((Units.mk0 μ hμ0 : Kˣ) : K) = (Units.mk0 μ hμ0 : Kˣ) := hμ
  refine ⟨g₁ * miyamotoIHom h (1, Units.mk0 μ hμ0) * g₂ * miyamotoXGL h 0 (ω₀ + μ ^ 2 * c₁) 0 0,
    mul_mem (mul_mem (mul_mem hg₁ (mem_sup_right (miyamotoIHom_one_mem_N2 h hμ'))) hg₂)
      (rootB_mem_I2_sup_N2 h hl), d₂, ?_⟩
  have e₁' : g₁⁻¹ * miyamotoXGL h a 0 c d * g₁ = miyamotoXGL h 1 0 c₁ d₁ := by
    rw [e₁]
    congr 1
    simp [ha]
  refine conj_conj_eq (conj_conj_eq (conj_conj_eq e₁' (diagN2_conj_A2 h hμ' 1 c₁ d₁)) e₂) ?_
  rw [rootB_conj_A2 h hl, miyamotoXGL_inj]
  refine ⟨?_, rfl, ?_, rfl⟩ <;> simp only [Units.val_mk0]
  · field_simp
  · field_simp
    linear_combination (μ ^ 2 * c₁) * h2

theorem miyamotoXGL_A2_mul_self (a c d : K) :
    miyamotoXGL h a 0 c d * miyamotoXGL h a 0 c d =
      miyamotoXGL h 0 0 0 (h.bar a * c + a * h.bar c) := by
  rw [miyamotoXGL_mul_self h (map_zero _), miyamotoXGL_inj]
  exact ⟨rfl, rfl, by ring, by ring⟩

theorem miyamotoXGL_mem_Z_iff_of_mem_A2 {a c d : K} (hx : miyamotoXGL h a 0 c d ∈ miyamotoA2 h) :
    miyamotoXGL h a 0 c d ∈ miyamotoZ h ↔ a = 0 ∧ c = 0 := by
  rw [miyamotoXGL_mem_Z]
  refine ⟨fun e => ⟨e.1, e.2.2.1⟩, fun ⟨ha, hc⟩ => ⟨ha, rfl, hc, ?_⟩⟩
  obtain ⟨-, hd⟩ := (miyamotoXGL_mem_A2 h).1 hx
  subst ha hc
  exact (add_bar_eq_zero_iff h).1 (by simpa using hd)

theorem miyamotoI2_sup_N2_le_normalizer :
    miyamotoI2 h ⊔ miyamotoN2 h ≤ normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) ⊓
      normalizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
  have hle : miyamotoI2 h ⊔ miyamotoN2 h ≤ normalizer (miyamotoA2 h : Set (GL (Fin 4) K)) :=
    fun g hg => ((miyamotoA2_sup_levi_le h) (mem_sup_right hg)).2
  exact le_inf hle (hle.trans (normalizer_A2_le_normalizer_Z h))

theorem exists_I2_sup_N2_conj_mod_Z {x y : GL (Fin 4) K} (hx : x ∈ miyamotoA2 h)
    (hy : y ∈ miyamotoA2 h) (hxZ : x ∉ miyamotoZ h) (hyZ : y ∉ miyamotoZ h)
    (hinv : x * x = 1 ↔ y * y = 1) :
    ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, (g⁻¹ * x * g)⁻¹ * y ∈ miyamotoZ h := by
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : K, ω₀ + h.bar ω₀ = 1 := by
    obtain ⟨ω₀, hω⟩ := h.traceLin_surjective 1
    exact ⟨ω₀, congrArg Subtype.val hω⟩
  have hN := miyamotoI2_sup_N2_le_normalizer h
  have nf_inv : ∀ {x : GL (Fin 4) K}, x ∈ miyamotoA2 h → x ∉ miyamotoZ h → x * x = 1 →
      ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∃ d' : K, g⁻¹ * x * g = miyamotoXGL h 1 0 0 d' := by
    intro x hx hxZ hx2
    obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hx
    have hac : a ≠ 0 ∨ c ≠ 0 := by
      by_contra hne
      rw [not_or, not_not, not_not] at hne
      exact hxZ ((miyamotoXGL_mem_Z_iff_of_mem_A2 h hx).2 hne)
    rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj] at hx2
    exact exists_conj_normal_involution h hac hx2.2.2.2
  have nf_non : ∀ {x : GL (Fin 4) K}, x ∈ miyamotoA2 h → x * x ≠ 1 →
      ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∃ d' : K, g⁻¹ * x * g = miyamotoXGL h 1 0 ω₀ d' := by
    intro x hx hx2
    obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hx
    rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, Ne, miyamotoXGL_inj] at hx2
    exact exists_conj_normal_noninvolution h hω₀ fun e => hx2 ⟨rfl, rfl, rfl, e⟩
  have combine : ∀ {e d₁ d₂ : K} {g₁ g₂ : GL (Fin 4) K}, g₁ ∈ miyamotoI2 h ⊔ miyamotoN2 h →
      g₂ ∈ miyamotoI2 h ⊔ miyamotoN2 h → g₁⁻¹ * x * g₁ = miyamotoXGL h 1 0 e d₁ →
      g₂⁻¹ * y * g₂ = miyamotoXGL h 1 0 e d₂ →
      ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, (g⁻¹ * x * g)⁻¹ * y ∈ miyamotoZ h := by
    intro e d₁ d₂ g₁ g₂ hg₁ hg₂ e₁ e₂
    have hn₁ : miyamotoXGL h 1 0 e d₁ ∈ miyamotoA2 h := by
      rw [← e₁]
      exact (mem_normalizer_iff''.1 (hN hg₁).1 x).1 hx
    have hn₂ : miyamotoXGL h 1 0 e d₂ ∈ miyamotoA2 h := by
      rw [← e₂]
      exact (mem_normalizer_iff''.1 (hN hg₂).1 y).1 hy
    have hz : (miyamotoXGL h 1 0 e d₁)⁻¹ * miyamotoXGL h 1 0 e d₂ ∈ miyamotoZ h := by
      have hmem := mul_mem (inv_mem hn₁) hn₂
      rw [miyamotoXGL_inv h (map_zero _), miyamotoXGL_mul h (map_zero _)] at hmem ⊢
      rw [show (0 : K) + 0 = 0 by ring] at hmem ⊢
      refine (miyamotoXGL_mem_Z_iff_of_mem_A2 h hmem).2 ⟨CharTwo.add_self_eq_zero 1, ?_⟩
      simp only [zero_mul, add_zero]
      exact CharTwo.add_self_eq_zero e
    refine ⟨g₁ * g₂⁻¹, mul_mem hg₁ (inv_mem hg₂), ?_⟩
    have e' : (((g₁ * g₂⁻¹)⁻¹ * x * (g₁ * g₂⁻¹))⁻¹ * y) =
        g₂ * ((g₁⁻¹ * x * g₁)⁻¹ * (g₂⁻¹ * y * g₂)) * g₂⁻¹ := by group
    rw [e', e₁, e₂]
    exact (mem_normalizer_iff.1 (hN hg₂).2 _).1 hz
  by_cases hx2 : x * x = 1
  · obtain ⟨g₁, hg₁, d₁, e₁⟩ := nf_inv hx hxZ hx2
    obtain ⟨g₂, hg₂, d₂, e₂⟩ := nf_inv hy hyZ (hinv.1 hx2)
    exact combine hg₁ hg₂ e₁ e₂
  · obtain ⟨g₁, hg₁, d₁, e₁⟩ := nf_non hx hx2
    obtain ⟨g₂, hg₂, d₂, e₂⟩ := nf_non hy fun e => hx2 (hinv.2 e)
    exact combine hg₁ hg₂ e₁ e₂

theorem miyamotoI2N2_irreducible {B : Subgroup (GL (Fin 4) K)} (hZB : miyamotoZ h ≤ B)
    (hBA : B ≤ miyamotoA2 h) (hinv : ∀ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, ∀ x ∈ B, g⁻¹ * x * g ∈ B) :
    B = miyamotoZ h ∨ B = miyamotoA2 h := by
  have hbb := h.bar_bar
  by_cases hB : B ≤ miyamotoZ h
  · exact Or.inl (le_antisymm hB hZB)
  refine Or.inr (le_antisymm hBA ?_)
  obtain ⟨x, hxB, hxZ⟩ := Set.not_subset.1 hB
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : K, ω₀ + h.bar ω₀ = 1 := by
    obtain ⟨ω₀, hω⟩ := h.traceLin_surjective 1
    exact ⟨ω₀, congrArg Subtype.val hω⟩
  obtain ⟨w, hwB, hwZ, hw2⟩ : ∃ w ∈ B, w ∉ miyamotoZ h ∧ w * w = 1 := by
    by_cases hx2 : x * x = 1
    · exact ⟨x, hxB, hxZ, hx2⟩
    obtain ⟨a, c, d, -, rfl⟩ := (mem_A2 h).1 (hBA hxB)
    rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj] at hx2
    have htr : h.bar a * c + a * h.bar c ≠ 0 := fun e => hx2 ⟨rfl, rfl, rfl, e⟩
    obtain ⟨g, hg, d₁, e⟩ := exists_conj_normal_noninvolution h hω₀ (d := d) htr
    have hn : miyamotoXGL h 1 0 ω₀ d₁ ∈ B := e ▸ hinv g hg _ hxB
    have hn' : miyamotoXGL h 1 0 (ω₀ + 1 * 1) d₁ ∈ B :=
      rootB_conj_A2 h (map_one _) 1 ω₀ d₁ ▸ hinv _ (rootB_mem_I2_sup_N2 h (map_one _)) _ hn
    have hw : (miyamotoXGL h 1 0 ω₀ d₁)⁻¹ * miyamotoXGL h 1 0 (ω₀ + 1 * 1) d₁ =
        miyamotoXGL h 0 0 1 1 := by
      rw [miyamotoXGL_inv h (map_zero _), miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
      refine ⟨CharTwo.add_self_eq_zero 1, by ring, ?_, ?_⟩
      · linear_combination ω₀ * CharTwo.two_eq_zero (R := K)
      · simp only [map_one, one_mul, add_zero, mul_one]
        linear_combination (d₁ + h.bar ω₀ + ω₀) * CharTwo.two_eq_zero (R := K)
    have hwA : miyamotoXGL h 0 0 1 1 ∈ miyamotoA2 h :=
      (miyamotoXGL_mem_A2 h).2 ⟨rfl, by simp [CharTwo.add_self_eq_zero]⟩
    refine ⟨miyamotoXGL h 0 0 1 1, hw ▸ mul_mem (inv_mem hn) hn', ?_, ?_⟩
    · rw [miyamotoXGL_mem_Z_iff_of_mem_A2 h hwA]
      exact fun e => one_ne_zero e.2
    · rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj]
      simp
  have hinvol : ∀ v ∈ miyamotoA2 h, v * v = 1 → v ∈ B := by
    intro v hv hv2
    by_cases hvZ : v ∈ miyamotoZ h
    · exact hZB hvZ
    obtain ⟨g, hg, hz⟩ := exists_I2_sup_N2_conj_mod_Z h (hBA hwB) hv hwZ hvZ
      ⟨fun _ => hv2, fun _ => hw2⟩
    have : v = (g⁻¹ * w * g) * ((g⁻¹ * w * g)⁻¹ * v) := by group
    rw [this]
    exact mul_mem (hinv g hg w hwB) (hZB hz)
  intro v hv
  obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hv
  have hd' : (d + h.bar a * c) + h.bar (d + h.bar a * c) + 0 * h.bar c + h.bar 0 * c = 0 := by
    simp only [map_add, map_mul, hbb, zero_mul, map_zero, add_zero]
    linear_combination hd
  have e : miyamotoXGL h a 0 c d =
      miyamotoXGL h a 0 0 0 * miyamotoXGL h 0 0 c (d + h.bar a * c) := by
    rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
    refine ⟨by ring, by ring, by ring, ?_⟩
    simp only [map_zero, add_zero, mul_zero, zero_add]
    linear_combination (-(h.bar a * c)) * CharTwo.two_eq_zero (R := K)
  rw [e]
  refine mul_mem (hinvol _ ((miyamotoXGL_mem_A2 h).2 ⟨rfl, by simp⟩) ?_)
    (hinvol _ ((miyamotoXGL_mem_A2 h).2 ⟨rfl, hd'⟩) ?_)
  · rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj]
    simp
  · rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj]
    simp

end Orbits

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem miyamotoI2N2G_irreducible [CharP K 2] {B : Subgroup G}
    (hZB : miyamotoPull h L η (miyamotoZ h) ≤ B) (hBA : B ≤ miyamotoA2G h L η)
    (hinv : ∀ g ∈ miyamotoI2G h L η ⊔ miyamotoN2G h L η, ∀ x ∈ B, g⁻¹ * x * g ∈ B) :
    B = miyamotoPull h L η (miyamotoZ h) ∨ B = miyamotoA2G h L η := by
  have hle := sup_le (miyamotoI2_le_SU h) (miyamotoN2_le_gramSU h)
  rw [← miyamotoPull_sup h L η (miyamotoI2_le_SU h) (miyamotoN2_le_gramSU h)] at hinv
  obtain ⟨M, hM, rfl, hMinv⟩ := exists_invariant_of_miyamotoPull h L η
    (hBA.trans (miyamotoPull_le h L η _)) hle hinv
  have hMA : M ≤ miyamotoA2 h := (miyamotoPull_le_miyamotoPull_iff h L η hM).1 hBA
  have hZ : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  have hZM : miyamotoZ h ≤ M := (miyamotoPull_le_miyamotoPull_iff h L η hZ).1 hZB
  rcases miyamotoI2N2_irreducible h hZM hMA hMinv with e | e
  · exact Or.inl (by rw [e])
  · exact Or.inr (by rw [e])

end Pull

end CFSG.LocalAnalysis.EvenBN.U4
