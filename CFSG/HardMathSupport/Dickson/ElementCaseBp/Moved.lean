module

public import CFSG.HardMathSupport.Dickson.ElementCaseBp.Diagonal
public import CFSG.HardMathSupport.Timmesfeld.Balance.Moved

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open CFSG CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.HardMathSupport.Timmesfeld.Balance

theorem commute_of_moved_of_pow_mem_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {L : Subgroup Y} (hL : IsComponent L)
    (hLp : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) {f : Y} (hf : f ^ p ∈ Subgroup.center Y)
    (hmoved : conjSub f L ≠ L) {d : Y}
    (hd : d ∈ CFSG.Open.GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y)))
    (hdn : ∀ i : ℕ, d ∈ Subgroup.normalizer ((conjSub (f ^ i) L : Subgroup Y) : Set Y)) :
    ∀ x ∈ L, d * x = x * d := by
  have hp0 : 0 < p := hp.pos
  obtain ⟨Δ, hΔC, hΔcomp, hΔdvd, hΔmem⟩ :=
    exists_diagonal_component_of_pow_mem_center hp hL hf hmoved
  have hΔp : ¬ Nat.Coprime p (Nat.card Δ) := fun hc =>
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_refl p) (hLp.trans hΔdvd) hc
  have hdΔ := commute_of_mem_gLAPPrimeCoreOf_of_isComponent hp hΔC hΔcomp hΔp hd
  have hrel : ∀ x ∈ L, (List.ofFn fun i : Fin p =>
      d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹).prod =
      (List.ofFn fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹).prod := by
    intro x hx
    rw [← conj_ofFn_prod, hdΔ _ (hΔmem x hx)]
    group
  have hcommL : ∀ x ∈ L, ∀ w ∈ L, ∀ i : Fin p, (i : ℕ) ≠ 0 →
      Commute w (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) := by
    intro x hx w hw i hi
    exact commute_of_isComponent_of_ne hL (isComponent_conjSub' hL _)
      (conjSub_pow_ne_self_of_pow_mem_center hp hf hmoved (Nat.pos_of_ne_zero hi) i.2).symm w hw _
      (conj_mem_conjSub hx)
  have hdc : ∀ i : ℕ, conjSub d (conjSub (f ^ i) L) = conjSub (f ^ i) L := by
    intro i
    ext y
    have h1 : d⁻¹ * y * d ∈ conjSub (f ^ i) L ↔ y ∈ conjSub (f ^ i) L := by
      have h2 := Subgroup.mem_normalizer_iff.mp (hdn i) (d⁻¹ * y * d)
      have e : d * (d⁻¹ * y * d) * d⁻¹ = y := by group
      rw [e] at h2
      exact h2
    exact mem_conjSub_iff.trans h1
  have hiff : ∀ h, d * h * d⁻¹ ∈ L ↔ h ∈ L := by
    intro h
    have h0 := Subgroup.mem_normalizer_iff.mp (hdn 0) h
    rw [pow_zero, conjSub_one] at h0
    exact h0.symm
  refine commute_of_central_displacement hL.1 hiff ?_
  intro x hx w hw
  have hh : ∀ i : Fin p, (i : ℕ) ≠ 0 →
      Commute w (d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹) := by
    intro i hi
    have hmem : d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹ ∈ conjSub (f ^ (i : ℕ)) L := by
      rw [← hdc i]
      exact conj_mem_conjSub (conj_mem_conjSub hx)
    exact commute_of_isComponent_of_ne hL (isComponent_conjSub' hL _)
      (conjSub_pow_ne_self_of_pow_mem_center hp hf hmoved (Nat.pos_of_ne_zero hi) i.2).symm
      w hw _ hmem
  have := (commute_inv_mul_of_prod_eq hp0 w
    (fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹)
    (fun i : Fin p => d * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * d⁻¹)
    (hrel x hx).symm (fun i hi => hcommL x hx w hw i hi) hh).eq
  simpa using this

end CFSG.HardMathSupport.Dickson.ElementCaseBp
