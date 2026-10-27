module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XElt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T : Subgroup G} {x1 x2 : G}

private lemma fzrAux_pow_three (h : FzStr t tau lam rho Z E W Q R T) {x : G} (hx : x ∈ E) :
    x ^ 3 = x⁻¹ := by
  have h4 : x ^ 4 = 1 := h.E_exp x hx
  have h3 : x ^ 3 * x = 1 := by rw [← pow_succ]; simpa using h4
  exact eq_inv_of_mul_eq_one_left h3

private lemma fzrAux_pq (h : FzStr t tau lam rho Z E W Q R T) (hx1 : x1 ∈ E) (hx2 : x2 ∈ E)
    (hx1Z : x1 ∉ Z) (hx2Z : x2 ∉ Z) (h12Z : x1⁻¹ * x2 ∉ Z) {p q : ℕ} (hp : p < 4) (hq : q < 4)
    (hrel : x1 ^ p * x2 ^ q = 1) : p = 0 ∧ q = 0 := by
  have hx1_3 : x1 ^ 3 = x1⁻¹ := fzrAux_pow_three h hx1
  have hx2_3 : x2 ^ 3 = x2⁻¹ := fzrAux_pow_three h hx2
  interval_cases p <;> interval_cases q <;>
    try simp only [pow_zero, pow_one, hx1_3, hx2_3, one_mul, mul_one] at hrel
  · exact ⟨rfl, rfl⟩
  · exact absurd (by rw [hrel]; exact Z.one_mem) hx2Z
  · exact absurd (h.E_invol x2 hx2 hrel) hx2Z
  · exact absurd (by rw [inv_eq_one.mp hrel]; exact Z.one_mem) hx2Z
  · exact absurd (by rw [hrel]; exact Z.one_mem) hx1Z
  · have hx2eq : x2 = x1⁻¹ := eq_inv_of_mul_eq_one_right hrel
    have hsq : x1⁻¹ * x1⁻¹ = (x1 ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
    exact absurd (by rw [hx2eq, hsq]; exact Z.inv_mem (h.E_sq x1 hx1)) h12Z
  · have hx1eq : x1 = (x2 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    exact absurd (by rw [hx1eq]; exact Z.inv_mem (h.E_sq x2 hx2)) hx1Z
  · have hx1eq : x1 = (x2⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    have hx1x2 : x1 = x2 := by rw [hx1eq, inv_inv]
    exact absurd (by rw [hx1x2, inv_mul_cancel]; exact Z.one_mem) h12Z
  · exact absurd (h.E_invol x1 hx1 hrel) hx1Z
  · have hx2eq : x2 = (x1 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hrel
    exact absurd (by rw [hx2eq]; exact Z.inv_mem (h.E_sq x1 hx1)) hx2Z
  · have hz2 : (x2 ^ 2)⁻¹ = x2 ^ 2 := by
      have h2 : x2 ^ 2 * (x2 ^ 2) = 1 := by
        rw [← pow_two]; exact h.Z_sq (x2 ^ 2) (h.E_sq x2 hx2)
      exact inv_eq_of_mul_eq_one_right h2
    have hx1sq : x1 ^ 2 = x2 ^ 2 := by
      have h' : x1 ^ 2 = (x2 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hrel
      rwa [hz2] at h'
    have hsq : (x1⁻¹ * x2) ^ 2 = 1 := by
      have hc : Commute x1⁻¹ x2 :=
        (show Commute x1 x2 from h.W_comm x1 (h.EW hx1) x2 (h.EW hx2)).inv_left
      rw [hc.mul_pow 2, inv_pow, hx1sq]
      rw [inv_mul_cancel]
    exact absurd (h.E_invol (x1⁻¹ * x2) (E.mul_mem (E.inv_mem hx1) hx2) hsq) h12Z
  · have hx1sq : x1 ^ 2 = (x2⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    have hx2eq : x2 = x1 ^ 2 := by rw [hx1sq, inv_inv]
    exact absurd (by rw [hx2eq]; exact h.E_sq x1 hx1) hx2Z
  · exact absurd (by rw [inv_eq_one.mp hrel]; exact Z.one_mem) hx1Z
  · exact absurd (by rw [hrel]; exact Z.one_mem) h12Z
  · have hx1inv : x1⁻¹ = (x2 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    have hx1eq : x1 = ((x2 ^ 2)⁻¹)⁻¹ := by rw [← inv_inv x1, hx1inv]
    exact absurd (by rw [hx1eq]; exact Z.inv_mem (Z.inv_mem (h.E_sq x2 hx2))) hx1Z
  · have hx1inv : x1⁻¹ = (x2⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hrel
    have hx1eq : x1 = x2⁻¹ := by rw [← inv_inv x1, hx1inv, inv_inv]
    exact absurd (by rw [hx1eq, inv_inv, ← pow_two]; exact h.E_sq x2 hx2) h12Z

theorem fzxElt_ker (h : FzStr t tau lam rho Z E W Q R T) (hx1 : x1 ∈ E) (hx2 : x2 ∈ E)
    (hx1Z : x1 ∉ Z) (hx2Z : x2 ∉ Z) (h12Z : x1⁻¹ * x2 ∉ Z) (v : FzXW)
    (hv : fzxElt t x1 x2 v = 1) : v = 0 := by
  have hv' : t ^ v.1.val * x1 ^ v.2.1.val * x2 ^ v.2.2.val = 1 := by
    simpa only [fzxElt] using hv
  have hv1lt : v.1.val < 2 := ZMod.val_lt v.1
  have hv21lt : v.2.1.val < 4 := ZMod.val_lt v.2.1
  have hv22lt : v.2.2.val < 4 := ZMod.val_lt v.2.2
  have hv1ne : v.1.val ≠ 1 := by
    intro he1
    have h1 : t = t ^ v.1.val := by rw [he1, pow_one]
    have hsplit : t * (x1 ^ v.2.1.val * x2 ^ v.2.2.val) = 1 := by
      rw [h1, ← mul_assoc]
      exact hv'
    have ht : t = (x1 ^ v.2.1.val * x2 ^ v.2.2.val)⁻¹ := eq_inv_of_mul_eq_one_left hsplit
    apply h.t_notin_E
    rw [ht]
    exact E.inv_mem (E.mul_mem (E.pow_mem hx1 v.2.1.val) (E.pow_mem hx2 v.2.2.val))
  have he0 : v.1.val = 0 := by
    interval_cases v.1.val
    · rfl
    · exact absurd rfl hv1ne
  have hrel : x1 ^ v.2.1.val * x2 ^ v.2.2.val = 1 := by
    have h' := hv'
    rw [he0, pow_zero, one_mul] at h'
    exact h'
  have hpq := fzrAux_pq h hx1 hx2 hx1Z hx2Z h12Z hv21lt hv22lt hrel
  exact Prod.ext ((ZMod.val_eq_zero v.1).mp he0)
    (Prod.ext ((ZMod.val_eq_zero v.2.1).mp hpq.1) ((ZMod.val_eq_zero v.2.2).mp hpq.2))

theorem fzxElt_inj (h : FzStr t tau lam rho Z E W Q R T) (hx1 : x1 ∈ E) (hx2 : x2 ∈ E)
    (hx1Z : x1 ∉ Z) (hx2Z : x2 ∉ Z) (h12Z : x1⁻¹ * x2 ∉ Z) :
    Function.Injective (fzxElt t x1 x2) := by
  intro v w hvw
  have htx1 : t * x1 = x1 * t := h.W_comm t h.t_mem x1 (h.EW hx1)
  have htx2 : t * x2 = x2 * t := h.W_comm t h.t_mem x2 (h.EW hx2)
  have h12 : x1 * x2 = x2 * x1 := h.W_comm x1 (h.EW hx1) x2 (h.EW hx2)
  have hadd := fzxElt_add h.t_sq (h.E_exp x1 hx1) (h.E_exp x2 hx2) htx1 htx2 h12
  have hker : fzxElt t x1 x2 (v - w) = 1 := by
    have h2 : fzxElt t x1 x2 v = fzxElt t x1 x2 (v - w) * fzxElt t x1 x2 w := by
      rw [← hadd (v - w) w, sub_add_cancel]
    rw [hvw] at h2
    have h3 := congrArg (fun z => z * (fzxElt t x1 x2 w)⁻¹) h2
    simpa [mul_assoc] using h3.symm
  have hzero : v - w = 0 := fzxElt_ker h hx1 hx2 hx1Z hx2Z h12Z (v - w) hker
  exact sub_eq_zero.mp hzero

end CFSG.OddStandard.SmallF3.FritzII
