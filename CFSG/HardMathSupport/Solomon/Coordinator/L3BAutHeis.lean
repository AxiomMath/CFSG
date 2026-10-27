module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exact ⟨0, by rw [Subgroup.orderOf_mk, h1]; rfl⟩
  · exact ⟨1, by rw [Subgroup.orderOf_mk, h1]; rfl⟩

theorem isPGroup_closure_heis {G : Type*} [Group G] {X P w : G} (hw : ∀ g : G, w * g = g * w)
    (hw3 : w ^ 3 = 1) (hX3 : X ^ 3 = 1) (hP3 : P ^ 3 = 1) (hXP : X * P = w * (P * X)) :
    IsPGroup 3 (Subgroup.closure {X, P} : Subgroup G) := by
  set A : Subgroup (G) := Subgroup.zpowers w with hAdef
  have hA : IsPGroup 3 A := isPGroup_zpowers_of_pow_three hw3
  have hAc : ∀ (g : G), ∀ y ∈ A, g * y * g⁻¹ = y := by
    intro g y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute (w ^ n) g := ((show Commute w g from hw g).zpow_left n)
    rw [mul_inv_eq_iff_eq_mul]
    exact hc.symm.eq
  have hAn : ∀ g : G, g ∈ Subgroup.normalizer (A : Set (G)) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hAc g y hy]
      exact hy
    · intro hy
      have h1 := hAc g⁻¹ (g * y * g⁻¹) hy
      rw [inv_inv] at h1
      have h2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [h2] at h1
      rw [h1]
      exact hy
  have hX3 : IsPGroup 3 (Subgroup.zpowers X) := isPGroup_zpowers_of_pow_three hX3
  have hP3 : IsPGroup 3 (Subgroup.zpowers P) := isPGroup_zpowers_of_pow_three hP3
  have hB : IsPGroup 3 (A ⊔ Subgroup.zpowers X : Subgroup (G)) :=
    hA.to_sup_of_normal_left' hX3 (fun g _ => hAn g)
  have hconj1 : P⁻¹ * X * P = w * X := by
    calc P⁻¹ * X * P = P⁻¹ * (X * P) := by group
      _ = P⁻¹ * (w * (P * X)) := by rw [hXP]
      _ = (P⁻¹ * w) * (P * X) := by group
      _ = (w * P⁻¹) * (P * X) := by rw [← hw P⁻¹]
      _ = w * X := by group
  have hconj2 : P * X * P⁻¹ = w⁻¹ * X := by
    have h : P * (P⁻¹ * X * P) * P⁻¹ = P * (w * X) * P⁻¹ :=
      congrArg (fun y => P * y * P⁻¹) hconj1
    have e1 : P * (P⁻¹ * X * P) * P⁻¹ = X := by group
    have e2 : P * (w * X) * P⁻¹ = w * (P * X * P⁻¹) := by
      calc P * (w * X) * P⁻¹ = (P * w) * X * P⁻¹ := by group
        _ = (w * P) * X * P⁻¹ := by rw [← hw P]
        _ = w * (P * X * P⁻¹) := by group
    rw [e1, e2] at h
    rw [eq_inv_mul_iff_mul_eq]
    exact h.symm
  have hwB : w ∈ (A ⊔ Subgroup.zpowers X : Subgroup (G)) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  have hXB : X ∈ (A ⊔ Subgroup.zpowers X : Subgroup (G)) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers X)
  have hB1 : ∀ y ∈ (A ⊔ Subgroup.zpowers X : Subgroup (G)), P * y * P⁻¹ ∈
      (A ⊔ Subgroup.zpowers X : Subgroup (G)) := by
    have : (A ⊔ Subgroup.zpowers X : Subgroup (G)) ≤
        (A ⊔ Subgroup.zpowers X : Subgroup (G)).comap (MulAut.conj P).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.2 ?_)
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hAc P y hy]
        exact Subgroup.mem_sup_left hy
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hconj2]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hwB) hXB
    exact fun y hy => this hy
  have hB2 : ∀ y ∈ (A ⊔ Subgroup.zpowers X : Subgroup (G)), P⁻¹ * y * P ∈
      (A ⊔ Subgroup.zpowers X : Subgroup (G)) := by
    have : (A ⊔ Subgroup.zpowers X : Subgroup (G)) ≤
        (A ⊔ Subgroup.zpowers X : Subgroup (G)).comap
          (MulAut.conj P⁻¹).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.2 ?_)
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have h3 := hAc P⁻¹ y hy
        rw [inv_inv] at h3
        rw [inv_inv, h3]
        exact Subgroup.mem_sup_left hy
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [inv_inv, hconj1]
        exact Subgroup.mul_mem _ hwB hXB
    intro y hy
    have h4 := this hy
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h4
    exact h4
  have hPn : P ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers X : Subgroup (G)) :
      Set (G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hB1 y
    · intro hy
      have := hB2 _ hy
      simpa [mul_assoc] using this
  have hC : IsPGroup 3 ((A ⊔ Subgroup.zpowers X) ⊔ Subgroup.zpowers P : Subgroup (G)) :=
    hB.to_sup_of_normal_left' hP3 (Subgroup.zpowers_le.2 hPn)
  refine hC.to_le ?_
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact Subgroup.mem_sup_left hXB
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)


end CFSG.HardMathSupport.Solomon.Coordinator
