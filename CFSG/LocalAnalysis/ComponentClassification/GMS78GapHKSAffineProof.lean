module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSAffine

public section

namespace CFSG.ComponentClassification.GMS78

@[expose] def Affine.translationSubgroup (M : Type*) [AddCommGroup M] :
    Subgroup (Equiv.Perm M) where
  carrier := {x | ∃ v : M, ∀ m, x m = m + v}
  mul_mem' := by
    rintro x y ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨w + v, fun m => by rw [Equiv.Perm.mul_apply, hw, hv, add_assoc]⟩
  one_mem' := ⟨0, fun m => by simp⟩
  inv_mem' := by
    rintro x ⟨v, hv⟩
    refine ⟨-v, fun m => ?_⟩
    apply x.injective
    rw [show x (x⁻¹ m) = m from x.apply_symm_apply m, hv, neg_add_cancel_right]

theorem hksRegularNormalAffine : HKSRegularNormalAffine := by
  intro R _ _ M _ _ _ hR hd X haff h2 C hCX hC0 hcyc hnorm hreg
  classical
  have : Module.Finite R M := Module.Finite.of_finite
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (R := R) (by omega)
  have hlin : ∀ c ∈ C, ∃ φ : M ≃ₗ[R] M, ∀ m, c m = φ m := by
    intro c hc
    obtain ⟨φ, b, h⟩ := haff c (hCX hc)
    have hb : b = 0 := by
      have := h 0
      rw [hC0 c hc, map_zero, zero_add] at this
      exact this.symm
    exact ⟨φ, fun m => by rw [h, hb, add_zero]⟩
  have hcomm : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c := fun c hc d hd =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := C)).is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩)
  obtain ⟨l, hl0, hl1⟩ : ∃ l : R, l ≠ 0 ∧ l ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Fintype R := Fintype.ofFinite R
    have hsub : (Finset.univ : Finset R) ⊆ {0, 1} := fun r _ => by
      by_cases h0 : r = 0
      · simp [h0]
      · simp [hno r h0]
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h3
    have h4 : ({0, 1} : Finset R).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  obtain ⟨c, ⟨hcC, hcm⟩, -⟩ := hreg m₀ (l • m₀) hm₀ (smul_ne_zero hl0 hm₀)
  have hscal : ∀ v, c v = l • v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, hC0 c hcC, smul_zero]
    obtain ⟨d, ⟨hdC, hdm⟩, -⟩ := hreg m₀ v hm₀ hv
    obtain ⟨ψ, hψ⟩ := hlin d hdC
    have h1 : c (d m₀) = d (c m₀) := by
      have := congrArg (fun f : Equiv.Perm M => f m₀) (hcomm c hcC d hdC)
      simpa only [Equiv.Perm.mul_apply] using this
    rw [← hdm, h1, hcm, hψ, hψ, map_smul]
  have hcinv : ∀ v, c⁻¹ v = l⁻¹ • v := by
    intro v
    apply c.injective
    rw [show c (c⁻¹ v) = v from c.apply_symm_apply v, hscal, smul_smul, mul_inv_cancel₀ hl0,
      one_smul]
  obtain ⟨x, hxX, hx0, -⟩ := h2 0 m₀ m₀ 0 hm₀.symm hm₀
  obtain ⟨φ, b, hx⟩ := haff x hxX
  have hb : b = m₀ := by
    have := hx 0
    rw [hx0, map_zero, zero_add] at this
    exact this.symm
  have hxinv : ∀ w, φ (x⁻¹ w) = w - b := by
    intro w
    have h1 := hx (x⁻¹ w)
    rw [show x (x⁻¹ w) = w from x.apply_symm_apply w] at h1
    exact eq_sub_of_add_eq h1.symm
  have ht : ∀ w, c (x (c⁻¹ (x⁻¹ w))) = w + (l - 1) • b := by
    intro w
    rw [hcinv, hx, map_smul, hxinv, hscal, smul_add, smul_smul, mul_inv_cancel₀ hl0, one_smul,
      sub_smul, one_smul]
    abel
  have htX : c * x * c⁻¹ * x⁻¹ ∈ X :=
    mul_mem (mul_mem (mul_mem (hCX hcC) hxX) (inv_mem (hCX hcC))) (inv_mem hxX)
  have hβ : (l - 1) • b ≠ 0 := smul_ne_zero (sub_ne_zero.mpr hl1) (hb ▸ hm₀)
  refine ⟨Affine.translationSubgroup M, ?_, ?_, ?_⟩
  ·
    rintro y ⟨v, hv⟩
    by_cases hv0 : v = 0
    · have : y = 1 := Equiv.ext fun m => by rw [hv, hv0, add_zero]; rfl
      rw [this]
      exact one_mem _
    obtain ⟨d, ⟨hdC, hdβ⟩, -⟩ := hreg _ v hβ hv0
    obtain ⟨ψ, hψ⟩ := hlin d hdC
    have hy : y = d * (c * x * c⁻¹ * x⁻¹) * d⁻¹ := by
      ext m
      have h1 : d (d⁻¹ m) = m := d.apply_symm_apply m
      simp only [Equiv.Perm.mul_apply]
      rw [ht, hψ, map_add, ← hψ, ← hψ, h1, hdβ, hv]
    rw [hy]
    exact mul_mem (mul_mem (hCX hdC) htX) (inv_mem (hCX hdC))
  ·
    rintro y hyX r ⟨v, hv⟩
    obtain ⟨ψ, e, hy⟩ := haff y hyX
    refine ⟨ψ v, fun m => ?_⟩
    have hyinv : ψ (y⁻¹ m) + e = m := by
      rw [← hy]
      exact y.apply_symm_apply m
    simp only [Equiv.Perm.mul_apply]
    rw [hv, hy, map_add, add_right_comm, hyinv]
  ·
    intro β γ
    refine ⟨Equiv.addRight (γ - β), ⟨⟨γ - β, fun m => rfl⟩, by simp⟩, ?_⟩
    rintro r ⟨⟨v, hv⟩, hrβ⟩
    have hv' : v = γ - β := by
      rw [hv] at hrβ
      rw [← hrβ, add_sub_cancel_left]
    ext m
    rw [hv, hv']
    rfl

end CFSG.ComponentClassification.GMS78
