module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module
open LinearMap (BilinForm)

variable {r e : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem odd_unitary_conjugate_semilinear_involution_descent (h : UnitaryFieldData r e E)
    (hr : Odd r) [FiniteDimensional E V] (hn : 1 ≤ finrank E V)
    {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.SeparatingLeft)
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀H : ∀ v w, Hf (τ₀ v) (τ₀ w) = h.bar (Hf v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) :
    (μ = 1 ∨ μ = -1) ∧
    (∃ b : Eˣ, h.norm (b : E) = ((μ⁻¹ : Eˣ) : E)) ∧ (∃ t : Eˣ, h.bar (t : E) = -(t : E)) ∧
    ∀ b t : Eˣ, h.norm (b : E) = ((μ⁻¹ : Eˣ) : E) → h.bar (t : E) = -(t : E) →
      (∀ v, ((b : E) • τ₀) (((b : E) • τ₀) v) = v) ∧
      finrank h.fixedField (conjFixed h ((b : E) • τ₀)) = finrank E V ∧
      Function.Bijective (LinearMap.liftBaseChange E (conjFixed h ((b : E) • τ₀)).subtype) ∧
      (μ = 1 → ∃ B : BilinForm h.fixedField (conjFixed h ((b : E) • τ₀)),
        (∀ v w, (B v w : E) = Hf v w) ∧ B.IsSymm ∧ B.Nondegenerate ∧
        ∃ Φ : commutingUnitary Hf τ₀ ≃* TauCeti.BilinForm.isometryGroup B,
          ∀ g w, (((Φ g : conjFixed h ((b : E) • τ₀) ≃ₗ[h.fixedField]
            conjFixed h ((b : E) • τ₀)) w : conjFixed h ((b : E) • τ₀)) : V) =
              ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) w) ∧
      (μ = -1 → ∃ B : BilinForm h.fixedField (conjFixed h ((b : E) • τ₀)),
        (∀ v w, (B v w : E) = (t : E)⁻¹ * Hf v w) ∧ B.IsAlt ∧ B.Nondegenerate ∧
        Even (finrank E V) ∧
        ∃ Φ : commutingUnitary Hf τ₀ ≃* TauCeti.BilinForm.isometryGroup B,
          ∀ g w, (((Φ g : conjFixed h ((b : E) • τ₀) ≃ₗ[h.fixedField]
            conjFixed h ((b : E) • τ₀)) w : conjFixed h ((b : E) • τ₀)) : V) =
              ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) w) := by
  have : CharP E r := h.charP
  have h2 : (2 : E) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : E) = 0 := by exact_mod_cast h0
    have h4 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff E r 2).mp h3)
    obtain ⟨k, hk⟩ := hr
    have := h.prime.two_le
    omega
  obtain ⟨v₀, hv₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := E) (M := V)).mp (by omega)
  have hτv₀ : τ₀ v₀ ≠ 0 := fun h0 => hv₀ (hτ₀.1 (h0.trans (map_zero τ₀).symm))
  have hμbar : h.bar (μ : E) = μ := by
    have h3 : (h.bar (μ : E) - μ) • τ₀ v₀ = 0 := by
      rw [sub_smul, ← map_smulₛₗ, ← hμ, ← hμ (τ₀ v₀), sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hτv₀)
  have hμμ : (μ : E) * μ = 1 := by
    by_contra hne
    apply hv₀
    refine hnd v₀ fun w => ?_
    have h3 : Hf (τ₀ (τ₀ v₀)) (τ₀ (τ₀ w)) = Hf v₀ w := by
      rw [hτ₀H, hτ₀H, h.bar_bar]
    rw [hμ, hμ, Hf.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, hμbar,
      ← mul_assoc] at h3
    have h4 : ((μ : E) * μ - 1) * Hf v₀ w = 0 := by rw [sub_mul, one_mul, h3, sub_self]
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne)
  have hμ1 : μ = 1 ∨ μ = -1 := by
    rcases mul_self_eq_one_iff.mp hμμ with h3 | h3
    · exact Or.inl (Units.ext h3)
    · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
  have hμinvF : ((μ⁻¹ : Eˣ) : E) ∈ h.fixedField := by
    rw [h.mem_fixedField, Units.val_inv_eq_inv_val, map_inv₀, hμbar]
  have hne : (⟨_, hμinvF⟩ : h.fixedField) ≠ 0 := fun h0 =>
    (μ⁻¹).ne_zero (congrArg Subtype.val h0)
  obtain ⟨d, hd⟩ := (unitary_field_norm h).2.1 (Units.mk0 _ hne)
  have hdN : h.norm (d : E) = ((μ⁻¹ : Eˣ) : E) :=
    congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : E)) hd
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have ht0' : c₀ - h.bar c₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
  refine ⟨hμ1, ⟨d, hdN⟩, ⟨Units.mk0 _ ht0', by
    rw [Units.val_mk0, map_sub, h.bar_bar, neg_sub]⟩, fun b t hb ht => ?_⟩
  have hb0 : (b : E) ≠ 0 := b.ne_zero
  have ht0 : (t : E) ≠ 0 := t.ne_zero
  have hττ : ∀ v, ((b : E) • τ₀) (((b : E) • τ₀) v) = v := by
    intro v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smulₛₗ, hμ, smul_smul, smul_smul,
      show (b : E) * h.bar (b : E) = h.norm (b : E) from rfl, hb, Units.inv_mul, one_smul]
  have hspan := span_conjFixed hττ ht ht0 h2
  have hfinW := finite_conjFixed (h := h) (τ := (b : E) • τ₀)
  have hW : ∀ v w, v ∈ conjFixed h ((b : E) • τ₀) → w ∈ conjFixed h ((b : E) • τ₀) →
      Hf v w = ((μ⁻¹ : Eˣ) : E) * h.bar (Hf v w) := by
    intro v w hv hw
    have h3 : Hf (((b : E) • τ₀) v) (((b : E) • τ₀) w) = Hf v w := by
      rw [mem_conjFixed.mp hv, mem_conjFixed.mp hw]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, Hf.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, smul_eq_mul, hτ₀H, ← mul_assoc, mul_comm (h.bar (b : E)),
      show (b : E) * h.bar (b : E) = h.norm (b : E) from rfl, hb] at h3
    exact h3.symm
  refine ⟨hττ, finrank_conjFixed hττ ht ht0 h2, liftBaseChange_conjFixed_bijective hττ ht ht0 h2,
    fun hμ1' => ?_, fun hμ1' => ?_⟩
  ·
    have hc : ∀ v w, v ∈ conjFixed h ((b : E) • τ₀) → w ∈ conjFixed h ((b : E) • τ₀) →
        h.bar (1 * Hf v w) = 1 * Hf v w := by
      intro v w hv hw
      have h3 := hW v w hv hw
      rw [hμ1', inv_one, Units.val_one, one_mul] at h3
      rw [one_mul, ← h3]
    obtain ⟨Φ, hΦ⟩ := exists_restrict_equiv hττ hb0 ht ht0 h2 one_ne_zero hc
    refine ⟨conjDescentForm Hf ((b : E) • τ₀) 1 hc, fun v w => by
      rw [conjDescentForm_apply, one_mul], ⟨fun v w => Subtype.ext ?_⟩,
      conjDescentForm_nondegenerate hH hnd hspan one_ne_zero hc, Φ, hΦ⟩
    rw [conjDescentForm_apply, conjDescentForm_apply, one_mul, one_mul, ← hH.eq v w]
    have h3 := hW v w v.2 w.2
    rw [hμ1', inv_one, Units.val_one, one_mul] at h3
    exact h3
  ·
    have hbarH : ∀ v w, v ∈ conjFixed h ((b : E) • τ₀) → w ∈ conjFixed h ((b : E) • τ₀) →
        h.bar (Hf v w) = -Hf v w := by
      intro v w hv hw
      have h3 := hW v w hv hw
      rw [hμ1', inv_neg, inv_one, Units.val_neg, Units.val_one, neg_one_mul] at h3
      linear_combination h3
    have hc : ∀ v w, v ∈ conjFixed h ((b : E) • τ₀) → w ∈ conjFixed h ((b : E) • τ₀) →
        h.bar ((t : E)⁻¹ * Hf v w) = (t : E)⁻¹ * Hf v w := by
      intro v w hv hw
      rw [map_mul, map_inv₀, ht, hbarH v w hv hw, inv_neg, neg_mul_neg]
    have hBalt : (conjDescentForm Hf ((b : E) • τ₀) (t : E)⁻¹ hc).IsAlt := fun v => by
      refine Subtype.ext ?_
      rw [conjDescentForm_apply, ZeroMemClass.coe_zero]
      have h3 := hbarH v v v.2 v.2
      rw [hH.eq v v] at h3
      have h4 : (2 : E) * Hf v v = 0 := by linear_combination h3
      rw [(mul_eq_zero.mp h4).resolve_left h2, mul_zero]
    have hBnd := conjDescentForm_nondegenerate hH hnd hspan (inv_ne_zero ht0) hc
    obtain ⟨Φ, hΦ⟩ := exists_restrict_equiv hττ hb0 ht ht0 h2 (inv_ne_zero ht0) hc
    refine ⟨conjDescentForm Hf ((b : E) • τ₀) (t : E)⁻¹ hc, fun v w => conjDescentForm_apply _ _ _
      hc v w, hBalt, hBnd, ?_, Φ, hΦ⟩
    rw [← finrank_conjFixed hττ ht ht0 h2]
    exact CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank _ hBalt hBnd

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
