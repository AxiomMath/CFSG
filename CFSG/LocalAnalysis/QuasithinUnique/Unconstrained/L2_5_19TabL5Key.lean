module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Aut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open Matrix
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.OuterAutomorphisms

theorem dl_mul_dl : dl * dl = 1 := by
  have := slGraphAut_sq 5 (ZMod 2)
  rwa [pow_two] at this

theorem dl_mul_conj (a : S) : dl * MulAut.conj a = MulAut.conj (dl a) * dl := by
  apply MulEquiv.ext
  intro g
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem eq_one_of_conj_eq_one (a : S) (h : MulAut.conj a = 1) : a = 1 := by
  have h1 : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut S => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * a = (a * g * a⁻¹) * a := by rw [this]
      _ = a * g := by group
  rw [center_S, Subgroup.mem_bot] at h1
  exact h1

theorem symm_of_sq (a : S) (h : (MulAut.conj a * dl) * (MulAut.conj a * dl) = 1) :
    (a : M5)ᵀ = a := by
  have h1 : MulAut.conj (a * dl a) = 1 := by
    calc MulAut.conj (a * dl a) = MulAut.conj a * MulAut.conj (dl a) := map_mul _ _ _
      _ = MulAut.conj a * MulAut.conj (dl a) * (dl * dl) := by rw [dl_mul_dl, mul_one]
      _ = MulAut.conj a * (MulAut.conj (dl a) * dl) * dl := by simp only [mul_assoc]
      _ = MulAut.conj a * (dl * MulAut.conj a) * dl := by rw [dl_mul_conj]
      _ = (MulAut.conj a * dl) * (MulAut.conj a * dl) := by simp only [mul_assoc]
      _ = 1 := h
  have h2 : a * dl a = 1 := eq_one_of_conj_eq_one _ h1
  have h3 : dl a = a⁻¹ := eq_inv_of_mul_eq_one_right h2
  have hB : (((a⁻¹ : S) : M5))ᵀ = ((a⁻¹ : S) : M5) := by
    have := congrArg (fun x : S => (x : M5)) h3
    simpa [dl_apply, Matrix.SpecialLinearGroup.coe_transpose] using this
  have hab : (a : M5) * ((a⁻¹ : S) : M5) = 1 := by
    have := congrArg (fun x : S => (x : M5)) (mul_inv_cancel a)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
    exact this
  have hab' : ((a⁻¹ : S) : M5) * (a : M5)ᵀ = 1 := by
    have := congrArg Matrix.transpose hab
    rw [Matrix.transpose_mul, hB, Matrix.transpose_one] at this
    exact this
  calc (a : M5)ᵀ = 1 * (a : M5)ᵀ := (one_mul _).symm
    _ = ((a : M5) * ((a⁻¹ : S) : M5)) * (a : M5)ᵀ := by rw [hab]
    _ = (a : M5) * (((a⁻¹ : S) : M5) * (a : M5)ᵀ) := by rw [Matrix.mul_assoc]
    _ = a := by rw [hab', Matrix.mul_one]

theorem dl_of_orth (g : S) (h : (g : M5) * (g : M5)ᵀ = 1) : dl g = g := by
  have hinv : g⁻¹ = g.transpose := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    simpa [Matrix.SpecialLinearGroup.coe_transpose] using h
  rw [dl_apply, hinv]
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose]

theorem dl_Ps : dl Ps = Ps := dl_of_orth Ps Pm_orth

theorem dl_bs : dl bs = bs := dl_of_orth bs bm_orth

theorem coe_mul_dl_inv (Q : S) : ((Q * dl (Q⁻¹) : S) : M5) = (Q : M5) * (Q : M5)ᵀ := by
  rw [dl_apply, inv_inv]
  simp [Matrix.SpecialLinearGroup.coe_transpose]

theorem key_involution (τ : MulAut S) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (z : S)
    (hz : orderOf z = 5) (hfix : τ z = z) :
    ∃ Q : S, ∀ g : S, τ g = Q * dl (Q⁻¹ * g * Q) * Q⁻¹ := by
  obtain ⟨a, ε, hε, hτa⟩ := aut_form τ
  obtain ⟨g, m, hgm⟩ := sylow_conj z hz
  interval_cases ε
  ·
    exfalso
    have hτa' : τ = MulAut.conj a := by rw [hτa]; simp
    have hsq : MulAut.conj (a * a) = 1 := by rw [map_mul, ← hτa']; exact hτ2
    have haa : a * a = 1 := eq_one_of_conj_eq_one _ hsq
    have hz' : a * z = z * a := by
      rw [hτa'] at hfix
      simp only [MulAut.conj_apply] at hfix
      calc a * z = (a * z * a⁻¹) * a := by group
        _ = z * a := by rw [hfix]
    have hcomm_w : Commute (g * a * g⁻¹) (g * z * g⁻¹) := by
      show g * a * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * a * g⁻¹)
      calc g * a * g⁻¹ * (g * z * g⁻¹) = g * (a * z) * g⁻¹ := by group
        _ = g * (z * a) * g⁻¹ := by rw [hz']
        _ = g * z * g⁻¹ * (g * a * g⁻¹) := by group
    have hcommPs : (g * a * g⁻¹) * Ps = Ps * (g * a * g⁻¹) := by
      rw [← hgm]
      exact (hcomm_w.zpow_right m).eq
    have ha'2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
      calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [haa]; group
    obtain ⟨x, hxdef⟩ : ∃ x : S, x = g * a * g⁻¹ := ⟨_, rfl⟩
    have hcommPs' : x * Ps = Ps * x := by rw [hxdef]; exact hcommPs
    have hx2 : x * x = 1 := by rw [hxdef]; exact ha'2
    have h1 : (x : M5) * Pm = Pm * (x : M5) := congrArg Subtype.val hcommPs'
    have h3 := circ_of_comm _ h1
    have h2 : (x : M5) * (x : M5) = 1 := by
      have := congrArg Subtype.val hx2
      rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
    rw [h3] at h2
    have h5 := circ_invol _ h2
    have h6 : x = 1 := Subtype.ext (by rw [h3, h5]; rfl)
    have ha1 : a = 1 := by
      have : a = g⁻¹ * x * g := by rw [hxdef]; group
      rw [this, h6]
      group
    apply hτ1
    rw [hτa', ha1, map_one]
  ·
    have hτa' : τ = MulAut.conj a * dl := by rw [hτa, pow_one]
    have hτpt : ∀ x, τ x = a * dl x * a⁻¹ := by
      intro x
      rw [hτa']
      simp [MulAut.mul_apply, MulAut.conj_apply]
    have hττ : ∀ y, τ (τ y) = y := fun y => by
      have := congrArg (fun φ : MulAut S => φ y) hτ2
      simpa using this
    obtain ⟨a', ha'def⟩ : ∃ a' : S, a' = g * a * dl (g⁻¹) := ⟨_, rfl⟩
    have hτ'pt : ∀ x : S, g * τ (g⁻¹ * x * g) * g⁻¹ = a' * dl x * a'⁻¹ := by
      intro x
      rw [hτpt, ha'def]
      simp only [map_mul, map_inv]
      group
    have hτ'τ' : ∀ x : S, a' * dl (a' * dl x * a'⁻¹) * a'⁻¹ = x := by
      intro x
      calc a' * dl (a' * dl x * a'⁻¹) * a'⁻¹
          = g * τ (g⁻¹ * (a' * dl x * a'⁻¹) * g) * g⁻¹ := (hτ'pt _).symm
        _ = g * τ (g⁻¹ * (g * τ (g⁻¹ * x * g) * g⁻¹) * g) * g⁻¹ := by rw [← hτ'pt x]
        _ = g * τ (τ (g⁻¹ * x * g)) * g⁻¹ := by
          congr 3
          group
        _ = x := by rw [hττ]; group
    have hτ'2 : (MulAut.conj a' * dl) * (MulAut.conj a' * dl) = 1 := by
      apply MulEquiv.ext
      intro x
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]
      exact hτ'τ' x
    have ha'sym : (a' : M5)ᵀ = a' := symm_of_sq a' hτ'2
    have hfixk : ∀ k : ℤ, g * τ (g⁻¹ * (g * z * g⁻¹) ^ k * g) * g⁻¹ = (g * z * g⁻¹) ^ k := by
      intro k
      have h1 : g⁻¹ * (g * z * g⁻¹) ^ k * g = z ^ k := by
        rw [conj_zpow]
        group
      rw [h1, map_zpow, hfix, conj_zpow]
    have hPsfix : a' * Ps * a'⁻¹ = Ps := by
      have h1 := hτ'pt Ps
      rw [← hgm, hfixk m] at h1
      rw [hgm] at h1
      rw [dl_Ps] at h1
      exact h1.symm
    have hcomm : a' * Ps = Ps * a' := by
      calc a' * Ps = (a' * Ps * a'⁻¹) * a' := by group
        _ = Ps * a' := by rw [hPsfix]
    obtain ⟨Q', hQ'⟩ := exists_Q a' ha'sym hcomm
    have ha'Q : a' = Q' * dl (Q'⁻¹) := Subtype.ext (hQ'.trans (coe_mul_dl_inv Q').symm)
    refine ⟨g⁻¹ * Q', fun x => ?_⟩
    have h1 := hτ'pt (g * x * g⁻¹)
    have h2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [h2] at h1
    calc τ x = g⁻¹ * (g * τ x * g⁻¹) * g := by group
      _ = g⁻¹ * (a' * dl (g * x * g⁻¹) * a'⁻¹) * g := by rw [h1]
      _ = g⁻¹ * ((Q' * dl (Q'⁻¹)) * dl (g * x * g⁻¹) * (Q' * dl (Q'⁻¹))⁻¹) * g := by rw [← ha'Q]
      _ = g⁻¹ * Q' * dl ((g⁻¹ * Q')⁻¹ * x * (g⁻¹ * Q')) * (g⁻¹ * Q')⁻¹ := by
        simp only [map_mul, map_inv]
        group

theorem card_outer_S : Nat.card (Outer S) ≤ 2 := by
  let f : Bool → Outer S := fun b => QuotientGroup.mk (if b then dl else 1)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ε, hε, hα⟩ := aut_form α
    have hinner : ∀ a : S, (MulAut.conj a : MulAut S) ∈ inner S := fun a => ⟨a, rfl⟩
    interval_cases ε
    · refine ⟨false, ?_⟩
      show (QuotientGroup.mk (1 : MulAut S) : Outer S) = QuotientGroup.mk α
      rw [QuotientGroup.eq, hα]
      simpa using hinner a
    · refine ⟨true, ?_⟩
      show (QuotientGroup.mk dl : Outer S) = QuotientGroup.mk α
      rw [QuotientGroup.eq, hα, pow_one]
      have := (inner_normal S).conj_mem _ (hinner a) dl⁻¹
      simpa [mul_assoc] using this
  calc Nat.card (Outer S) ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
    _ = 2 := by simp

theorem dl_inv (y : S) : (dl y)⁻¹ = y.transpose := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  have hy : (y : M5) * ((y⁻¹ : S) : M5) = 1 := by
    have := congrArg (fun x : S => (x : M5)) (mul_inv_cancel y)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
    exact this
  rw [Matrix.SpecialLinearGroup.coe_mul, dl_apply, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul, hy, Matrix.transpose_one]
  rfl

theorem twist_witness (Q : S) (τ : MulAut S) (hτ : ∀ g : S, τ g = Q * dl (Q⁻¹ * g * Q) * Q⁻¹) :
    ∃ x : S, (τ x)⁻¹ * x = Q * bs * Q⁻¹ := by
  refine ⟨Q * y0s * Q⁻¹, ?_⟩
  rw [hτ]
  have h1 : Q⁻¹ * (Q * y0s * Q⁻¹) * Q = y0s := by group
  rw [h1]
  have h2 : (dl y0s)⁻¹ * y0s = bs := by
    rw [dl_inv]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose]
    exact y0m_spec
  calc (Q * dl y0s * Q⁻¹)⁻¹ * (Q * y0s * Q⁻¹)
      = Q * ((dl y0s)⁻¹ * y0s) * Q⁻¹ := by group
    _ = Q * bs * Q⁻¹ := by rw [h2]

end CFSG.QuasithinUnique.Id2519.Tab.L5
