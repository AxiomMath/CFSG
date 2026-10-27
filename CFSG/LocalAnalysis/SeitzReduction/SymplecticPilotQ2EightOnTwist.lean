module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowTwist

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Reflect

variable [CharP K 2]

omit [CharP K 2] in
theorem onNe_zero_of_map_eq_one {x : V} (hx : Q x = 1) : x ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

theorem onPolar_self (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, omegaInv_two_eq_zero, zero_mul]

omit [CharP K 2] in
theorem onReflect_commute {x y : V} (h : polar Q x y = 0) :
    reflect Q x * reflect Q y = reflect Q y * reflect Q x := by
  have e := reflect_conj (reflect_mem_orthogonalGroup Q x) y
  rw [reflect_apply_of_polar_eq_zero h, reflect_inv] at e
  calc reflect Q x * reflect Q y = reflect Q x * reflect Q y * reflect Q x * reflect Q x := by
        rw [mul_assoc _ (reflect Q x), reflect_mul_self, mul_one]
    _ = reflect Q y * reflect Q x := by rw [e]

omit [CharP K 2] in
theorem onReflect_mul_sq {x y : V} (h : polar Q x y = 0) :
    (reflect Q x * reflect Q y) ^ 2 = 1 := by
  rw [_root_.sq]
  calc reflect Q x * reflect Q y * (reflect Q x * reflect Q y) =
        reflect Q x * (reflect Q y * reflect Q x) * reflect Q y := by group
    _ = 1 := by
      rw [← onReflect_commute h, ← mul_assoc, reflect_mul_self, one_mul, reflect_mul_self]

theorem onReflect_injective (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate) {x y : V}
    (hx : Q x = 1) (hy : Q y = 1) (h : reflect Q x = reflect Q y) : x = y := by
  obtain ⟨z, hz⟩ := omegaInv_exists_polar_eq_one hQ (onNe_zero_of_map_eq_one hx)
  have e := congrArg (fun f : V ≃ₗ[K] V => f z) h
  simp only [reflect_apply_of_map_eq_one_two hx, reflect_apply_of_map_eq_one_two hy,
    polar_comm Q x z, hz, one_smul] at e
  rcases omegaTwo_eq_zero_or_eq_one hK (polar Q y z) with h0 | h1
  · rw [h0, zero_smul, add_zero] at e
    exact absurd (add_eq_left.1 e) (onNe_zero_of_map_eq_one hx)
  · rw [h1, one_smul] at e
    exact add_left_cancel e

theorem onEq_of_reflect_mul_eq_one (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {x y : V} (hx : Q x = 1) (hy : Q y = 1) (h : reflect Q x * reflect Q y = 1) : x = y := by
  refine onReflect_injective hK hQ hx hy ?_
  calc reflect Q x = reflect Q x * reflect Q y * reflect Q y := by
        rw [mul_assoc, reflect_mul_self, mul_one]
    _ = reflect Q y := by rw [h, one_mul]

theorem onReflect_ne_one (hQ : (polarBilin Q).Nondegenerate) {x : V} (hx : Q x = 1) :
    reflect Q x ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := omegaInv_exists_polar_eq_one hQ (onNe_zero_of_map_eq_one hx)
  have e := congrArg (fun f : V ≃ₗ[K] V => f z) h
  simp only [reflect_apply_of_map_eq_one_two hx, polar_comm Q x z, hz, one_smul] at e
  exact onNe_zero_of_map_eq_one hx (add_eq_left.1 (e.trans rfl))

end Reflect

section Dim

variable [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem onPolarBilin_isRefl : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rw [polar_comm, h]

theorem exists_nonsingular_perp_three (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1) (a x : V) :
    ∃ n, Q n = 1 ∧ polar Q a n = 0 ∧ polar Q v n = 0 ∧ polar Q x n = 0 := by
  classical
  set B := polarBilin Q with hBdef
  set S : Submodule K V := Submodule.span K ({a, v, x} : Set V) with hS
  set T := LinearMap.BilinForm.orthogonal B S with hT
  have hmemT : ∀ n, n ∈ T ↔ polar Q a n = 0 ∧ polar Q v n = 0 ∧ polar Q x n = 0 := by
    intro n
    rw [hT, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h a (Submodule.subset_span (by simp)), h v (Submodule.subset_span (by simp)),
        h x (Submodule.subset_span (by simp))⟩
    · rintro ⟨h1, h2, h3⟩ m hm
      refine Submodule.span_induction (p := fun m _ => B m n = 0) ?_ ?_ ?_ ?_ hm
      · rintro y (rfl | rfl | rfl)
        · exact h1
        · exact h2
        · exact h3
      · simp
      · intro y z _ _ hy hz
        rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
      · intro c y _ hy
        rw [map_smul, LinearMap.smul_apply, hy, smul_zero]
  by_contra hc
  push Not at hc
  have hsing : ∀ n ∈ T, Q n = 0 := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := (hmemT n).1 hn
    rcases omegaTwo_eq_zero_or_eq_one hK (Q n) with h0 | h0
    · exact h0
    · exact absurd h3 (hc n h0 h1 h2)
  have hTT : T ≤ LinearMap.BilinForm.orthogonal B T := by
    intro t ht
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro t' ht'
    rw [hBdef, polarBilin_apply_apply, polar, hsing _ (T.add_mem ht' ht), hsing _ ht',
      hsing _ ht, sub_zero, sub_zero]
  have hdS : finrank K S ≤ 3 := by
    have e : ({a, v, x} : Set V) = (({a, v, x} : Finset V) : Set V) := by simp
    rw [hS, e]
    refine (finrank_span_finset_le_card _).trans ?_
    exact (Finset.card_insert_le _ _).trans (by
      have := Finset.card_insert_le v ({x} : Finset V)
      rw [Finset.card_singleton] at this
      omega)
  have hdT := LinearMap.BilinForm.finrank_orthogonal hQ S
  have hdTT := LinearMap.BilinForm.finrank_orthogonal hQ T
  have hle := Submodule.finrank_mono hTT
  have hdS' : finrank K S ≤ finrank K V := Submodule.finrank_le S
  rw [← hT] at hdT
  have hTeq : T = LinearMap.BilinForm.orthogonal B T :=
    Submodule.eq_of_le_of_finrank_le hTT (by omega)
  have hvT : v ∈ T := by
    rw [hTeq, hT]
    exact LinearMap.BilinForm.le_orthogonal_orthogonal onPolarBilin_isRefl
      (Submodule.subset_span (by simp))
  rw [hsing v hvT] at hv
  exact zero_ne_one hv

end Dim

section Span

variable [CharP K 2] [FiniteDimensional K V]

omit [CharP K 2] in
theorem eq_of_forall_nonsingular (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1) {A C : V ≃ₗ[K] V}
    (h : ∀ x, Q x = 1 → A x = C x) : A = C := by
  refine LinearEquiv.ext fun y => ?_
  rcases omegaTwo_eq_zero_or_eq_one hK (Q y) with h0 | h1
  · obtain ⟨n, hn, hyn, -, -⟩ := exists_nonsingular_perp_three hK hQ hdim hv y y
    have hQyn : Q (y + n) = 1 := by
      rw [QuadraticMap.map_add Q, h0, hn, hyn, zero_add, add_zero]
    calc A y = A (y + n) - A n := by rw [map_add, add_sub_cancel_right]
      _ = C (y + n) - C n := by rw [h _ hQyn, h _ hn]
      _ = C y := by rw [map_add, add_sub_cancel_right]
  · exact h y h1

omit [CharP K 2] in
theorem apply_eq_self_of_nonsingular_perp (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1) (a : V)
    {A : V ≃ₗ[K] V} (h : ∀ u, Q u = 1 → polar Q a u = 0 → polar Q v u = 0 → A u = u) {y : V}
    (hya : polar Q a y = 0) (hyv : polar Q v y = 0) : A y = y := by
  rcases omegaTwo_eq_zero_or_eq_one hK (Q y) with h0 | h1
  · obtain ⟨n, hn, hna, hnv, hyn⟩ := exists_nonsingular_perp_three hK hQ hdim hv a y
    have hQyn : Q (y + n) = 1 := by
      rw [QuadraticMap.map_add Q, h0, hn, hyn, zero_add, add_zero]
    have h1' := h (y + n) hQyn (by rw [polar_add_right, hya, hna, add_zero])
      (by rw [polar_add_right, hyv, hnv, add_zero])
    calc A y = A (y + n) - A n := by rw [map_add, add_sub_cancel_right]
      _ = y := by rw [h1', h n hn hna hnv, add_sub_cancel_right]
  · exact h y h1 hya hyv

theorem on_commutator_le_self {X : Type*} [Group X] (H : Subgroup X) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem reflect_mul_reflect_mem_commutator (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ finrank K V) {x y : V} (hx : Q x = 1)
    (hy : Q y = 1) : reflect Q x * reflect Q y ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  by_cases hxy : x = y
  · rw [hxy, reflect_mul_self]
    exact Subgroup.one_mem _
  rcases omegaTwo_eq_zero_or_eq_one hK (polar Q x y) with hB0 | hB1
  swap
  · exact reflect_mul_reflect_mem_omega hx hy hB1
  have hx0 := onNe_zero_of_map_eq_one hx
  have hy0 := onNe_zero_of_map_eq_one hy
  have hyx : ∀ c : K, y ≠ c • x := by
    intro c h
    rcases omegaTwo_eq_zero_or_eq_one hK c with rfl | rfl
    · exact hy0 (by rw [h, zero_smul])
    · exact hxy (by rw [h, one_smul])
  have hxy' : ∀ c : K, x ≠ c • y := by
    intro c h
    rcases omegaTwo_eq_zero_or_eq_one hK c with rfl | rfl
    · exact hx0 (by rw [h, zero_smul])
    · exact hxy (by rw [h, one_smul])
  obtain ⟨z₁, hz₁x, hz₁y⟩ := omegaInv_exists_polar_eq_zero_polar_eq_one hQ hx0 hyx
  obtain ⟨z₂, hz₂y, hz₂x⟩ := omegaInv_exists_polar_eq_zero_polar_eq_one hQ hy0 hxy'
  obtain ⟨z, hz, hxz, hzy⟩ : ∃ z, Q z = 1 ∧ polar Q x z = 1 ∧ polar Q z y = 1 := by
    set z₀ := z₁ + z₂ with hz₀
    have hxz₀ : polar Q x z₀ = 1 := by
      rw [hz₀, polar_add_right, polar_comm Q x z₁, hz₁x, polar_comm Q x z₂, hz₂x, zero_add]
    have hz₀y : polar Q z₀ y = 1 := by
      rw [hz₀, polar_add_left, hz₁y, hz₂y, add_zero]
    rcases omegaTwo_eq_zero_or_eq_one hK (Q z₀) with h0 | h1
    · obtain ⟨n, hn, hny, hnx, hnz⟩ := exists_nonsingular_perp_three hK hQ hdim hx y z₀
      refine ⟨z₀ + n, ?_, ?_, ?_⟩
      · rw [QuadraticMap.map_add Q, h0, hn, hnz, zero_add, add_zero]
      · rw [polar_add_right, hxz₀, hnx, add_zero]
      · rw [polar_add_left, hz₀y, polar_comm Q n y, hny, add_zero]
    · exact ⟨z₀, h1, hxz₀, hz₀y⟩
  have e : reflect Q x * reflect Q y =
      (reflect Q x * reflect Q z) * (reflect Q z * reflect Q y) := by
    rw [mul_assoc, ← mul_assoc (reflect Q z), reflect_mul_self, one_mul]
  rw [e]
  exact Subgroup.mul_mem _ (reflect_mul_reflect_mem_omega hx hz hxz)
    (reflect_mul_reflect_mem_omega hz hy hzy)

end Span

section Plane

variable [CharP K 2]

theorem onPlane_decomp {a v : V} (hav : polar Q a v = 1) (y : V) :
    polar Q a (y + polar Q v y • a + polar Q a y • v) = 0 ∧
      polar Q v (y + polar Q v y • a + polar Q a y • v) = 0 ∧
      y = (y + polar Q v y • a + polar Q a y • v) + polar Q v y • a + polar Q a y • v := by
  have hva : polar Q v a = 1 := by rw [polar_comm, hav]
  refine ⟨?_, ?_, ?_⟩
  · rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, onPolar_self,
      hav, mul_zero, add_zero, mul_one, CharTwo.add_self_eq_zero]
  · rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, onPolar_self,
      hva, mul_zero, add_zero, mul_one, CharTwo.add_self_eq_zero]
  · have e1 := omegaInv_add_self K (polar Q v y • a)
    have e2 := omegaInv_add_self K (polar Q a y • v)
    calc y = y + (polar Q v y • a + polar Q v y • a) + (polar Q a y • v + polar Q a y • v) := by
          rw [e1, e2, add_zero, add_zero]
      _ = _ := by abel

theorem onApply_eq_of_fix {a v : V} (hav : polar Q a v = 1) {τ : V ≃ₗ[K] V}
    (hW : ∀ y, polar Q a y = 0 → polar Q v y = 0 → τ y = y) (y : V) :
    τ y = y + polar Q v y • (a + τ a) + polar Q a y • (v + τ v) := by
  obtain ⟨h1, h2, h3⟩ := onPlane_decomp hav y
  set w := y + polar Q v y • a + polar Q a y • v with hw
  have hτw : τ w = w := hW w h1 h2
  calc τ y = τ (w + polar Q v y • a + polar Q a y • v) := by rw [← h3]
    _ = w + polar Q v y • τ a + polar Q a y • τ v := by
      rw [map_add, map_add, map_smul, map_smul, hτw]
    _ = _ := by rw [hw, smul_add, smul_add]; abel

theorem onApply_mem_plane (hQ : (polarBilin Q).Nondegenerate) {a v : V} (hav : polar Q a v = 1)
    {τ : V ≃ₗ[K] V} (hτO : τ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hW : ∀ y, polar Q a y = 0 → polar Q v y = 0 → τ y = y) {x : V} (hx : x = a ∨ x = v) :
    τ x = polar Q v (τ x) • a + polar Q a (τ x) • v := by
  have hva : polar Q v a = 1 := by rw [polar_comm, hav]
  set x' := τ x with hx'
  have hperp : ∀ y, polar Q a y = 0 → polar Q v y = 0 → polar Q x' y = 0 := by
    intro y hya hyv
    rw [hx', ← hW y hya hyv, polar_map_of_mem hτO]
    rcases hx with rfl | rfl
    · exact hya
    · exact hyv
  set w := x' + polar Q v x' • a + polar Q a x' • v with hw
  have hwa : polar Q w a = 0 := by
    rw [polar_comm, (onPlane_decomp hav x').1]
  have hwv : polar Q w v = 0 := by
    rw [polar_comm, (onPlane_decomp hav x').2.1]
  have hw0 : w = 0 := by
    refine eq_zero_of_polar_eq_zero hQ fun z => ?_
    obtain ⟨hza, hzv, hz⟩ := onPlane_decomp hav z
    set zW := z + polar Q v z • a + polar Q a z • v with hzW
    have hwzW : polar Q w zW = 0 := by
      rw [hw, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        hperp zW hza hzv, hza, hzv, mul_zero, mul_zero, add_zero, add_zero]
    rw [hz, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hwzW, hwa,
      hwv, mul_zero, mul_zero, add_zero, add_zero]
  calc x' = x' + w := by rw [hw0, add_zero]
    _ = x' + x' + (polar Q v x' • a + polar Q a x' • v) := by rw [hw]; abel
    _ = _ := by rw [omegaInv_add_self K x', zero_add]

omit [CharP K 2] in
theorem onReflect_pow_three (v : V) : reflect Q v ^ 3 = reflect Q v := by
  rw [pow_succ, _root_.sq, reflect_mul_self, one_mul]

theorem eq_reflect_or_eq_reflect_of_fix (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {a v : V} (ha : Q a = 1) (hv : Q v = 1) (hav : polar Q a v = 1) {τ : V ≃ₗ[K] V}
    (hτO : τ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hτ2 : τ * τ = 1)
    (hτ3 : (τ * reflect Q v) ^ 3 = 1) (hτ1 : τ * reflect Q v ≠ 1)
    (hW : ∀ y, polar Q a y = 0 → polar Q v y = 0 → τ y = y) :
    τ = reflect Q a ∨ τ = reflect Q (a + v) := by
  have ha0 := onNe_zero_of_map_eq_one ha
  have hv0 := onNe_zero_of_map_eq_one hv
  have hav' : a ≠ v := by
    intro h
    rw [h, onPolar_self] at hav
    exact zero_ne_one hav
  have hfor := onApply_eq_of_fix hav hW
  have hτ2' : ∀ y, τ (τ y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, hτ2]
    rfl
  have hset : ∀ x, x ≠ 0 → τ x = polar Q v (τ x) • a + polar Q a (τ x) • v →
      τ x = a ∨ τ x = v ∨ τ x = a + v := by
    intro x hx0 hx
    rcases omegaTwo_eq_zero_or_eq_one hK (polar Q v (τ x)) with h1 | h1 <;>
      rcases omegaTwo_eq_zero_or_eq_one hK (polar Q a (τ x)) with h2 | h2 <;>
      rw [h1, h2] at hx <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hx
    · exact absurd (τ.injective (hx.trans (map_zero τ).symm)) hx0
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  have hQav : Q (a + v) = 1 := by
    rw [QuadraticMap.map_add Q, ha, hv, hav, CharTwo.add_self_eq_zero, zero_add]
  rcases hset a ha0 (onApply_mem_plane hQ hav hτO hW (Or.inl rfl)) with h₁ | h₁ | h₁ <;>
    rcases hset v hv0 (onApply_mem_plane hQ hav hτO hW (Or.inr rfl)) with h₂ | h₂ | h₂
  · exact absurd (τ.injective (h₁.trans h₂.symm)) hav'
  · exfalso
    have h1 : τ = 1 := LinearEquiv.ext fun y => by
      rw [hfor y, h₁, h₂, omegaInv_add_self K a, omegaInv_add_self K v, smul_zero, smul_zero,
        add_zero, add_zero]
      rfl
    rw [h1, one_mul, onReflect_pow_three] at hτ3
    exact onReflect_ne_one hQ hv hτ3
  · left
    refine LinearEquiv.ext fun y => ?_
    rw [hfor y, h₁, h₂, reflect_apply_of_map_eq_one_two ha, omegaInv_add_self K a, smul_zero,
      add_zero, add_left_comm, omegaInv_add_self K v, add_zero]
  · right
    refine LinearEquiv.ext fun y => ?_
    rw [hfor y, h₁, h₂, reflect_apply_of_map_eq_one_two hQav, polar_add_left, add_smul,
      add_comm v a]
    abel
  · exact absurd (τ.injective (h₁.trans h₂.symm)) hav'
  · exfalso
    have h := hτ2' a
    rw [h₁, h₂] at h
    exact hv0 (add_eq_left.1 h)
  · exfalso
    have h := hτ2' v
    rw [h₂, h₁] at h
    exact ha0 (add_eq_right.1 h)
  · exfalso
    have h1 : τ = reflect Q v := LinearEquiv.ext fun y => by
      rw [hfor y, h₁, h₂, reflect_apply_of_map_eq_one_two hv, ← add_assoc,
        omegaInv_add_self K a, zero_add, omegaInv_add_self K v, smul_zero, add_zero]
    exact hτ1 (by rw [h1, reflect_mul_self])
  · exact absurd (τ.injective (h₁.trans h₂.symm)) hav'

end Plane

section Twist

variable [CharP K 2] [FiniteDimensional K V] {Ω : Subgroup (V ≃ₗ[K] V)}

theorem exists_tau_of_commute_conj (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1)
    (hΩO : Ω ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hD : ∀ {x y : V}, Q x = 1 → Q y = 1 → reflect Q x * reflect Q y ∈ Ω)
    (hβ : ∀ g ∈ Ω, reflect Q v * g * reflect Q v ∈ Ω) (α : MulAut Ω)
    (hfix : ∀ g : Ω, (g : V ≃ₗ[K] V) v = v → α g = g)
    (hcomm : ∀ g h : Ω, (h : V ≃ₗ[K] V) = reflect Q v * g * reflect Q v →
      ((α h : Ω) : V ≃ₗ[K] V) = reflect Q v * α g * reflect Q v) :
    ∃ τ : V → V ≃ₗ[K] V,
      (∀ x (hx : Q x = 1), τ x = ((α ⟨_, hD hx hv⟩ : Ω) : V ≃ₗ[K] V) * reflect Q v) ∧
      (∀ (g : Ω) x, Q x = 1 →
        τ ((g : V ≃ₗ[K] V) x) = (α g : V ≃ₗ[K] V) * τ x * (α g : V ≃ₗ[K] V)⁻¹) ∧
      (∀ x, Q x = 1 → polar Q v x = 0 → τ x = reflect Q x) ∧
      (∀ x, Q x = 1 → polar Q v x = 1 → τ x = reflect Q x ∨ τ x = reflect Q (x + v)) := by
  classical
  have hsv := reflect_mem_orthogonalGroup Q v
  have hαβ : ∀ g : Ω, ((α ⟨_, hβ g g.2⟩ : Ω) : V ≃ₗ[K] V) =
      reflect Q v * α g * reflect Q v := fun g => hcomm g ⟨_, hβ g g.2⟩ rfl
  have hvv : reflect Q v v = v := reflect_apply_of_polar_eq_zero (onPolar_self v)
  refine ⟨fun x => if hx : Q x = 1 then ((α ⟨_, hD hx hv⟩ : Ω) : V ≃ₗ[K] V) *
    reflect Q v else 1, fun x hx => by simp only [hx, dite_true], ?_, ?_, ?_⟩
  · intro g x hx
    have hgO := hΩO g.2
    have hgx : Q ((g : V ≃ₗ[K] V) x) = 1 := by rw [map_of_mem hgO, hx]
    simp only [hx, hgx, dite_true]
    have e : (⟨_, hD hgx hv⟩ : Ω) = g * ⟨_, hD hx hv⟩ * ⟨_, hβ _ (g⁻¹).2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← reflect_conj hgO x]
      calc (g : V ≃ₗ[K] V) * reflect Q x * (g : V ≃ₗ[K] V)⁻¹ * reflect Q v =
          (g : V ≃ₗ[K] V) * reflect Q x * (reflect Q v * reflect Q v) *
            (g : V ≃ₗ[K] V)⁻¹ * reflect Q v := by rw [reflect_mul_self, mul_one]
        _ = _ := by group
    rw [e, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hαβ, map_inv, Subgroup.coe_inv]
    calc ((α g : Ω) : V ≃ₗ[K] V) * ((α ⟨_, hD hx hv⟩ : Ω) : V ≃ₗ[K] V) *
          (reflect Q v * ((α g : Ω) : V ≃ₗ[K] V)⁻¹ * reflect Q v) * reflect Q v =
        ((α g : Ω) : V ≃ₗ[K] V) * ((α ⟨_, hD hx hv⟩ : Ω) : V ≃ₗ[K] V) *
          reflect Q v * ((α g : Ω) : V ≃ₗ[K] V)⁻¹ * (reflect Q v * reflect Q v) := by
          group
      _ = _ := by rw [reflect_mul_self, mul_one]; group
  · intro x hx hvx
    simp only [hx, dite_true]
    have hxv : polar Q x v = 0 := by rw [polar_comm, hvx]
    have hfx : α ⟨_, hD hx hv⟩ = ⟨_, hD hx hv⟩ := by
      refine hfix _ ?_
      change (reflect Q x * reflect Q v) v = v
      rw [LinearEquiv.mul_apply, hvv, reflect_apply_of_polar_eq_zero hxv]
    rw [hfx]
    change reflect Q x * reflect Q v * reflect Q v = reflect Q x
    rw [mul_assoc, reflect_mul_self, mul_one]
  · intro x hx hvx
    simp only [hx, dite_true]
    have hxv : polar Q x v = 1 := by rw [polar_comm, hvx]
    set A : Ω := α ⟨_, hD hx hv⟩ with hA
    have hAO : (A : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hΩO A.2
    have hτO : (A : V ≃ₗ[K] V) * reflect Q v ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.mul_mem _ hAO hsv
    refine eq_reflect_or_eq_reflect_of_fix hK hQ hx hv hxv hτO ?_ ?_ ?_ ?_
    · have e : (⟨_, hD hx hv⟩ : Ω) * ⟨_, hβ _ (hD hx hv)⟩ = 1 := by
        apply Subtype.ext
        change reflect Q x * reflect Q v *
          (reflect Q v * (reflect Q x * reflect Q v) * reflect Q v) = 1
        calc reflect Q x * reflect Q v *
              (reflect Q v * (reflect Q x * reflect Q v) * reflect Q v) =
            reflect Q x * (reflect Q v * reflect Q v) * reflect Q x *
              (reflect Q v * reflect Q v) := by group
          _ = 1 := by simp only [reflect_mul_self, mul_one]
      have h1 := congrArg (fun g : Ω => ((α g : Ω) : V ≃ₗ[K] V)) e
      simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at h1
      rw [hcomm ⟨_, hD hx hv⟩ ⟨_, hβ _ (hD hx hv)⟩ rfl] at h1
      calc (A : V ≃ₗ[K] V) * reflect Q v * ((A : V ≃ₗ[K] V) * reflect Q v) =
          (A : V ≃ₗ[K] V) * (reflect Q v * (A : V ≃ₗ[K] V) * reflect Q v) := by group
        _ = 1 := h1
    · have e : (⟨_, hD hx hv⟩ : Ω) ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact reflect_mul_reflect_pow_three_two hx hv hxv)
      calc ((A : V ≃ₗ[K] V) * reflect Q v * reflect Q v) ^ 3 = ((A ^ 3 : Ω) : V ≃ₗ[K] V) := by
            rw [mul_assoc, reflect_mul_self, mul_one, Subgroup.coe_pow]
        _ = 1 := by rw [hA, ← map_pow, e, map_one, Subgroup.coe_one]
    · rw [mul_assoc, reflect_mul_self, mul_one]
      intro h
      have h1 : A = 1 := Subtype.ext h
      rw [hA, MulEquiv.map_eq_one_iff] at h1
      have h2 := congrArg Subtype.val h1
      have hxv' := onEq_of_reflect_mul_eq_one hK hQ hx hv h2
      rw [hxv', onPolar_self] at hvx
      exact zero_ne_one hvx
    · refine fun y hyx hyv => apply_eq_self_of_nonsingular_perp hK hQ hdim hv x
        (fun u hu hux huv => ?_) hyx hyv
      have huv' : polar Q u v = 0 := by rw [polar_comm, huv]
      have hsuv : reflect Q u v = v := reflect_apply_of_polar_eq_zero huv'
      set Ru : Ω := ⟨_, hD hv hu⟩ with hRu
      have hαRu : α Ru = Ru := hfix Ru (by
        change (reflect Q v * reflect Q u) v = v
        rw [LinearEquiv.mul_apply, hsuv, hvv])
      have e1 : (A : V ≃ₗ[K] V) * reflect Q v * reflect Q u =
          ((α (⟨_, hD hx hv⟩ * Ru) : Ω) : V ≃ₗ[K] V) := by
        rw [map_mul, hαRu, Subgroup.coe_mul, ← hA, mul_assoc]
      have e2 : reflect Q u * ((A : V ≃ₗ[K] V) * reflect Q v) =
          ((α ⟨_, hβ _ (Ru * ⟨_, hD hx hv⟩).2⟩ : Ω) : V ≃ₗ[K] V) := by
        rw [hαβ (Ru * ⟨_, hD hx hv⟩), map_mul, hαRu, Subgroup.coe_mul, ← hA]
        change _ = reflect Q v * (reflect Q v * reflect Q u * (A : V ≃ₗ[K] V)) * reflect Q v
        calc reflect Q u * ((A : V ≃ₗ[K] V) * reflect Q v) =
            (reflect Q v * reflect Q v) * reflect Q u * (A : V ≃ₗ[K] V) * reflect Q v := by
              rw [reflect_mul_self, one_mul, mul_assoc]
          _ = _ := by group
      have e3 : (⟨_, hD hx hv⟩ * Ru : Ω) = ⟨_, hβ _ (Ru * ⟨_, hD hx hv⟩).2⟩ := by
        apply Subtype.ext
        change reflect Q x * reflect Q v * (reflect Q v * reflect Q u) =
          reflect Q v * (reflect Q v * reflect Q u * (reflect Q x * reflect Q v)) * reflect Q v
        calc reflect Q x * reflect Q v * (reflect Q v * reflect Q u) =
            reflect Q x * (reflect Q v * reflect Q v) * reflect Q u := by group
          _ = reflect Q u * reflect Q x := by rw [reflect_mul_self, mul_one, onReflect_commute hux]
          _ = (reflect Q v * reflect Q v) * reflect Q u * reflect Q x *
                (reflect Q v * reflect Q v) := by rw [reflect_mul_self, one_mul, mul_one]
          _ = _ := by group
      have hc : (A : V ≃ₗ[K] V) * reflect Q v * reflect Q u =
          reflect Q u * ((A : V ≃ₗ[K] V) * reflect Q v) :=
        e1.trans ((congrArg (fun g : Ω => ((α g : Ω) : V ≃ₗ[K] V)) e3).trans e2.symm)
      have h1 : reflect Q (((A : V ≃ₗ[K] V) * reflect Q v) u) = reflect Q u := by
        rw [← reflect_conj hτO u, hc, mul_inv_cancel_right]
      exact onReflect_injective hK hQ (by rw [map_of_mem hτO, hu]) hu h1

theorem on_eq_one_of_pow_two_of_pow_three {X : Type*} [Group X] {x : X} (h2 : x ^ 2 = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, one_mul]

theorem eq_one_or_eq_conj_reflect_of_commute_conj (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1)
    (hΩO : Ω ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hD : ∀ {x y : V}, Q x = 1 → Q y = 1 → reflect Q x * reflect Q y ∈ Ω)
    (hβ : ∀ g ∈ Ω, reflect Q v * g * reflect Q v ∈ Ω) (α : MulAut Ω)
    (hfix : ∀ g : Ω, (g : V ≃ₗ[K] V) v = v → α g = g)
    (hcomm : ∀ g h : Ω, (h : V ≃ₗ[K] V) = reflect Q v * g * reflect Q v →
      ((α h : Ω) : V ≃ₗ[K] V) = reflect Q v * α g * reflect Q v) :
    α = 1 ∨ ∀ g : Ω, ((α g : Ω) : V ≃ₗ[K] V) = reflect Q v * g * reflect Q v := by
  obtain ⟨τ, hτ, hconj, hperp, hone⟩ :=
    exists_tau_of_commute_conj hK hQ hdim hv hΩO hD hβ α hfix hcomm
  have hv0 := onNe_zero_of_map_eq_one hv
  have hαR : ∀ x (hx : Q x = 1) (y : V), τ x = reflect Q y →
      ((α ⟨_, hD hx hv⟩ : Ω) : V ≃ₗ[K] V) = reflect Q y * reflect Q v := by
    intro x hx y hxy
    have e := hτ x hx
    rw [hxy] at e
    rw [e, mul_assoc, reflect_mul_self, mul_one]
  have hunif : (∀ x, Q x = 1 → polar Q v x = 1 → τ x = reflect Q x) ∨
      (∀ x, Q x = 1 → polar Q v x = 1 → τ x = reflect Q (x + v)) := by
    by_contra hc
    push Not at hc
    obtain ⟨⟨a, ha, hva, hτa⟩, ⟨b, hb, hvb, hτb⟩⟩ := hc
    have hτa' : τ a = reflect Q (a + v) := (hone a ha hva).resolve_left hτa
    have hτb' : τ b = reflect Q b := (hone b hb hvb).resolve_right hτb
    have hmem : reflect Q b * reflect Q a ∈ Ω := hD hb ha
    have key : ((α ⟨_, hmem⟩ : Ω) : V ≃ₗ[K] V) = reflect Q b * reflect Q (a + v) := by
      have e : (⟨_, hmem⟩ : Ω) = ⟨_, hD hb hv⟩ * (⟨_, hD ha hv⟩)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, reflect_inv]
        rw [mul_assoc, ← mul_assoc (reflect Q v), reflect_mul_self, one_mul]
      rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hαR b hb b hτb',
        hαR a ha (a + v) hτa', mul_inv_rev, reflect_inv, reflect_inv, mul_assoc,
        ← mul_assoc (reflect Q v), reflect_mul_self, one_mul]
    have hbv : polar Q b v = 1 := by rw [polar_comm, hvb]
    have hab : polar Q b (a + v) = polar Q b a + 1 := by rw [polar_add_right, hbv]
    have hQav : Q (a + v) = 1 := by
      rw [QuadraticMap.map_add Q, ha, hv, polar_comm, hva, CharTwo.add_self_eq_zero, zero_add]
    have hpow : ∀ n : ℕ, (⟨_, hmem⟩ : Ω) ^ n = 1 →
        (reflect Q b * reflect Q (a + v)) ^ n = 1 := by
      intro n hn
      rw [← key, ← Subgroup.coe_pow, ← map_pow, hn, map_one, Subgroup.coe_one]
    rcases omegaTwo_eq_zero_or_eq_one hK (polar Q b a) with h0 | h1
    · have h2 := hpow 2 (Subtype.ext (by rw [Subgroup.coe_pow]; exact onReflect_mul_sq h0))
      have h3 := reflect_mul_reflect_pow_three_two hb hQav (by rw [hab, h0, zero_add])
      have h5 := onEq_of_reflect_mul_eq_one hK hQ hb hQav (on_eq_one_of_pow_two_of_pow_three h2 h3)
      have h6 : polar Q b (a + v) = 0 := by rw [← h5]; exact onPolar_self b
      rw [hab, h0, zero_add] at h6
      exact one_ne_zero h6
    · have h2 := hpow 3 (Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact reflect_mul_reflect_pow_three_two hb ha h1))
      have h3 := onReflect_mul_sq (Q := Q) (x := b) (y := a + v)
        (by rw [hab, h1, CharTwo.add_self_eq_zero])
      have h4 := on_eq_one_of_pow_two_of_pow_three h3 h2
      have h5 := onEq_of_reflect_mul_eq_one hK hQ hb hQav h4
      have h6 : (⟨_, hmem⟩ : Ω) = 1 := by
        rw [← MulEquiv.map_eq_one_iff α]
        exact Subtype.ext (key.trans h4)
      have h7 := onEq_of_reflect_mul_eq_one hK hQ hb ha (congrArg Subtype.val h6)
      rw [h7] at h5
      exact hv0 (add_eq_left.1 h5.symm)
  rcases hunif with h | h
  · left
    have hall : ∀ x, Q x = 1 → τ x = reflect Q x := by
      intro x hx
      rcases omegaTwo_eq_zero_or_eq_one hK (polar Q v x) with h0 | h1
      · exact hperp x hx h0
      · exact h x hx h1
    refine MulEquiv.ext fun g => Subtype.ext ?_
    change ((α g : Ω) : V ≃ₗ[K] V) = g
    refine eq_of_forall_nonsingular hK hQ hdim hv fun x hx => ?_
    have hgO := hΩO g.2
    have hαgO := hΩO (α g).2
    have hgx : Q ((g : V ≃ₗ[K] V) x) = 1 := by rw [map_of_mem hgO, hx]
    have e := hconj g x hx
    rw [hall _ hgx, hall x hx, reflect_conj hαgO x] at e
    exact (onReflect_injective hK hQ hgx (by rw [map_of_mem hαgO, hx]) e).symm
  · right
    have hall : ∀ x, Q x = 1 → τ x = reflect Q (reflect Q v x) := by
      intro x hx
      rcases omegaTwo_eq_zero_or_eq_one hK (polar Q v x) with h0 | h1
      · rw [hperp x hx h0, reflect_apply_of_polar_eq_zero h0]
      · rw [h x hx h1, reflect_apply_of_map_eq_one_two hv, h1, one_smul]
    intro g
    have hgO := hΩO g.2
    have hαgO := hΩO (α g).2
    have hsvO := reflect_mem_orthogonalGroup Q v
    refine eq_of_forall_nonsingular hK hQ hdim hv fun y hy => ?_
    have hx : Q (reflect Q v y) = 1 := by rw [map_of_mem hsvO, hy]
    have hgx : Q ((g : V ≃ₗ[K] V) (reflect Q v y)) = 1 := by rw [map_of_mem hgO, hx]
    have hss : reflect Q v (reflect Q v y) = y := by
      rw [← LinearEquiv.mul_apply, reflect_mul_self]
      rfl
    have e := hconj g (reflect Q v y) hx
    rw [hall _ hgx, hall _ hx, reflect_conj hαgO, hss] at e
    have e' := onReflect_injective hK hQ (by rw [map_of_mem hsvO, hgx])
      (by rw [map_of_mem hαgO, hy]) e
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact e'.symm

end Twist

end CFSG.SeitzReduction.SymplecticPilot
