module

public import CFSG.GH74.GLS.Stage4.T6X.T6RA

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6X

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem t6_pelt_K {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {r : G} (hrz : r * N.z = N.z * r)
    (hrodd : Odd (orderOf r)) {v : G} (hv : v ∈ N.S) (hvr : v * r * v⁻¹ = r⁻¹) :
    r ∈ N.K₁ ⊔ N.K₂ := by
  have hF := h.sec5.F5
  have hFz : ∀ f ∈ N.F, f * N.z = N.z * f := fun f hf => h.FS f hf _ h.sec5.loc.z_mem_S
  have hrC : r ∈ centralizer ({N.z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hrz
  have hFn := t2P53_F_normC₁ h.ctx hFz
  obtain ⟨c, hc, f, hf, hrcf⟩ := t2P53_split hFn (hF.C_le hrC)
  have hvC₁ : v ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := Subgroup.mem_sup_right hv
  have hfv : f * v = v * f := h.FS f hf v hv
  have hfv' : f * v⁻¹ = v⁻¹ * f := by
    calc f * v⁻¹ = v⁻¹ * (v * f) * v⁻¹ := by group
      _ = v⁻¹ * (f * v) * v⁻¹ := by rw [hfv]
      _ = v⁻¹ * f := by group
  have e1 : v * (c * f) * v⁻¹ = (v * c * v⁻¹) * f := by
    calc v * (c * f) * v⁻¹ = v * c * (f * v⁻¹) := by group
      _ = v * c * (v⁻¹ * f) := by rw [hfv']
      _ = (v * c * v⁻¹) * f := by group
  have e2 : (v * c * v⁻¹) * f = f⁻¹ * c⁻¹ := by
    rw [← e1, ← mul_inv_rev, ← hrcf]
    exact hvr
  have e3 : f⁻¹ = (v * c * v⁻¹) * f * c := by
    calc f⁻¹ = f⁻¹ * c⁻¹ * c := by group
      _ = (v * c * v⁻¹) * f * c := by rw [← e2]
  have hf2 : f * f ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
    have hcf : f * c * f⁻¹ ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := (Subgroup.mem_normalizer_iff.1 (hFn hf) c).1 hc
    have : f⁻¹ * f⁻¹ = (v * c * v⁻¹) * (f * c * f⁻¹) := by
      calc f⁻¹ * f⁻¹ = ((v * c * v⁻¹) * f * c) * f⁻¹ := by rw [← e3]
        _ = (v * c * v⁻¹) * (f * c * f⁻¹) := by group
    have hmem : f⁻¹ * f⁻¹ ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hvC₁ hc) (Subgroup.inv_mem _ hvC₁)) hcf
    have := Subgroup.inv_mem _ hmem
    simpa [mul_inv_rev] using this
  have hfodd : Odd (orderOf (f * f)) := by
    have : orderOf (f * f) ∣ orderOf f := by rw [← pow_two]; exact orderOf_pow_dvd 2
    exact Odd.of_dvd_nat (hF.F_odd f hf) this
  have hfK : f * f ∈ N.K₁ ⊔ N.K₂ := h.oddK _ hf2 hfodd
  have hbot : f * f ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨N.F.mul_mem hf hf, hfK⟩
  rw [hF.F_inter_K, Subgroup.mem_bot] at hbot
  have hf1 : f = 1 := t2P53_odd_sq (hF.F_odd f hf) hbot
  subst hf1
  rw [mul_one] at hrcf
  rw [hrcf] at hrodd ⊢
  exact h.oddK c hc hrodd

theorem a_conj_facts {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    N.a * u * N.a⁻¹ = N.z ∧ N.a * N.z * N.a⁻¹ = N.z * u := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hu : N.a⁻¹ * N.z * N.a = u := h.sec5.u_eq
  have hcyc : N.a⁻¹ * u * N.a = N.z * u := by
    have := h.sec5.weyl.a_cycle
    rwa [show N.u = u from h.sec5.u_eq] at this
  have h1 : N.a * u * N.a⁻¹ = N.z := by
    calc N.a * u * N.a⁻¹ = N.a * (N.a⁻¹ * N.z * N.a) * N.a⁻¹ := by rw [hu]
      _ = N.z := by group
  refine ⟨h1, ?_⟩
  have h2 : N.a * (N.z * u) * N.a⁻¹ = u := by
    rw [← hcyc]; group
  have h3 : (N.a * N.z * N.a⁻¹) * N.z = u := by
    calc (N.a * N.z * N.a⁻¹) * N.z = (N.a * N.z * N.a⁻¹) * (N.a * u * N.a⁻¹) := by rw [h1]
      _ = N.a * (N.z * u) * N.a⁻¹ := by group
      _ = u := h2
  have hz : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  calc N.a * N.z * N.a⁻¹ = ((N.a * N.z * N.a⁻¹) * N.z) * N.z⁻¹ := by group
    _ = u * N.z⁻¹ := by rw [h3]
    _ = u * N.z := by rw [hz]
    _ = N.z * u := hzu.symm

theorem RA_conj_K {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {r : G} (hr : r ∈ RA N p u) :
    N.a * r * N.a⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  have hru : r * u = u * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hpg := R₂_pGroup N h.prime
  have hrz := (RA_inv h).1 r hr
  have hodd : Odd (orderOf (N.a * r * N.a⁻¹)) := by
    have : orderOf (N.a * r * N.a⁻¹) = orderOf r := by
      have := MulEquiv.orderOf_eq (MulAut.conj N.a) r
      simpa [MulAut.conj_apply] using this
    rw [this]
    exact t6_odd_of_pGroup h.prime h.p_ne_two hpg hr.1
  refine t6_pelt_K h ?_ hodd (v := N.z * u)
    (N.S.mul_mem h.sec5.loc.z_mem_S h.sec5.loc.u_mem_S) ?_
  ·
    calc N.a * r * N.a⁻¹ * N.z = N.a * r * N.a⁻¹ * (N.a * u * N.a⁻¹) := by rw [ha1]
      _ = N.a * (r * u) * N.a⁻¹ := by group
      _ = N.a * (u * r) * N.a⁻¹ := by rw [hru]
      _ = (N.a * u * N.a⁻¹) * (N.a * r * N.a⁻¹) := by group
      _ = N.z * (N.a * r * N.a⁻¹) := by rw [ha1]
  ·
    rw [← ha2]
    calc N.a * N.z * N.a⁻¹ * (N.a * r * N.a⁻¹) * (N.a * N.z * N.a⁻¹)⁻¹
        = N.a * (N.z * r * N.z⁻¹) * N.a⁻¹ := by group
      _ = N.a * r⁻¹ * N.a⁻¹ := by rw [hrz]
      _ = (N.a * r * N.a⁻¹)⁻¹ := by group

end CFSG.GH74.GLS.Stage4.Rest.T6X
