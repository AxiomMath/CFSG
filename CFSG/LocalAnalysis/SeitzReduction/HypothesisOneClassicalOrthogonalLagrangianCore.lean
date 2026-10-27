module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalLagrangianLevi

public section

namespace CFSG.SeitzReduction

namespace OrthogonalLagrangian

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem eq_of_eigen_pair {T : V ≃+ V} {y z : V}
    (hind : ∀ α β : K, α • y + β • z = 0 → α = 0 ∧ β = 0) {a b c : K} (hy : T y = a • y)
    (hz : T z = b • z) (hyz : T (y + z) = c • (y + z)) : a = b := by
  have h : (c - a) • y + (c - b) • z = 0 := by
    calc (c - a) • y + (c - b) • z = c • (y + z) - (a • y + b • z) := by module
      _ = 0 := by rw [← hyz, map_add, hy, hz, sub_self]
  obtain ⟨h1, h2⟩ := hind _ _ h
  rw [sub_eq_zero] at h1 h2
  rw [← h1, ← h2]

theorem semilinear_eq_smul_of_forall_eigen {φ : K ≃+* K} (T : V ≃+ V)
    (hTs : ∀ (a : K) x, T (a • x) = φ a • T x) {P : V → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (a : K) x, P x → P (a • x))
    (heig : ∀ x, P x → ∃ a : K, T x = a • x) {x₁ x₂ : V} (h₁ : P x₁) (h₂ : P x₂)
    (hind : ∀ a b : K, a • x₁ + b • x₂ = 0 → a = 0 ∧ b = 0) :
    (∀ a, φ a = a) ∧ ∃ c : K, ∀ x, P x → T x = c • x := by
  have hx₁ : x₁ ≠ 0 := by
    intro h
    have := (hind 1 0 (by rw [h, smul_zero, zero_smul, add_zero])).1
    exact one_ne_zero this
  obtain ⟨c, hc⟩ := heig x₁ h₁
  obtain ⟨c₂, hc₂⟩ := heig x₂ h₂
  obtain ⟨c₁₂, hc₁₂⟩ := heig (x₁ + x₂) (hadd _ _ h₁ h₂)
  have hcc₂ : c = c₂ := eq_of_eigen_pair hind hc hc₂ hc₁₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hx₁ (T.injective (hc.trans (map_zero T).symm))
  have hindep : ∀ x, P x → (∀ α β : K, α • x₁ + β • x = 0 → α = 0 ∧ β = 0) →
      T x = c • x := by
    intro x hx hxi
    obtain ⟨b, hb⟩ := heig x hx
    obtain ⟨e, he⟩ := heig (x₁ + x) (hadd _ _ h₁ hx)
    rw [hb, eq_of_eigen_pair hxi hc hb he]
  have hφ : ∀ a, φ a = a := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]
    have hind' : ∀ α β : K, α • (a • x₁) + β • x₂ = 0 → α = 0 ∧ β = 0 := by
      intro α β h
      rw [smul_smul] at h
      obtain ⟨h1, h2⟩ := hind _ _ h
      exact ⟨(mul_eq_zero.mp h1).resolve_right ha, h2⟩
    obtain ⟨b, hb⟩ := heig (a • x₁) (hsmul a _ h₁)
    obtain ⟨e, he⟩ := heig (a • x₁ + x₂) (hadd _ _ (hsmul a _ h₁) h₂)
    have hbc : b = c := (eq_of_eigen_pair hind' hb hc₂ he).trans hcc₂.symm
    have h1 : (φ a * c - c * a) • x₁ = 0 := by
      have e1 : T (a • x₁) = φ a • c • x₁ := by rw [hTs, hc]
      rw [hb, hbc] at e1
      calc (φ a * c - c * a) • x₁ = φ a • c • x₁ - c • a • x₁ := by module
        _ = 0 := by rw [← e1, sub_self]
    have h2 : φ a * c = c * a := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hx₁)
    exact mul_right_cancel₀ hc0 (h2.trans (mul_comm c a))
  refine ⟨hφ, c, fun x hx => ?_⟩
  by_cases hdep : ∃ a : K, x = a • x₁
  · obtain ⟨a, rfl⟩ := hdep
    rw [hTs, hc, hφ, smul_comm]
  · refine hindep x hx fun α β h => ?_
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hx₁, hβ⟩
    · refine absurd ⟨-(β⁻¹ * α), ?_⟩ hdep
      calc x = β⁻¹ • (α • x₁ + β • x) - (β⁻¹ * α) • x₁ := by
            rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hβ, one_smul]
            abel
        _ = -(β⁻¹ * α) • x₁ := by rw [h, smul_zero, zero_sub, neg_smul]

variable {Q : QuadraticForm K V} {N : V →ₗ[K] V}

section Semilinear

variable {φ : K ≃+* K} {T : V ≃+ V} (hTs : ∀ (a : K) x, T (a • x) = φ a • T x)
  (hTQ : ∀ x, Q (T x) = φ (Q x)) (hTN : ∀ x, T (N x) = N (T x))

include hTQ in
theorem polar_semilinear_apply (x y : V) : polar Q (T x) (T y) = φ (polar Q x y) := by
  rw [polar, polar, ← map_add, hTQ, hTQ, hTQ, map_sub, map_sub]

include hTs in
theorem semilinear_symm_smul (a : K) (x : V) : T.symm (a • x) = φ.symm a • T.symm x := by
  apply T.injective
  rw [hTs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

include hTQ in
theorem semilinear_map_symm (x : V) : Q (T.symm x) = φ.symm (Q x) := by
  apply φ.injective
  rw [← hTQ, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

include hTN in
theorem semilinear_symm_N (x : V) : T.symm (N x) = N (T.symm x) := by
  apply T.injective
  rw [hTN, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

variable [CharP K 2] (hL : IsLagrangianDisplacement Q N)

include hL hTN in
theorem apply_N_eq_of_commute {u v : V} (hu : Q (N u) = 0) (hv : Q (N v) = 0)
    (huv : polar Q u (N v) = 1) (hc : ∀ x, T (leviPair Q N u v x) = leviPair Q N u v (T x)) :
    T (N u) = polar Q (N (T v)) v • N v + (polar Q (N (T v)) u + polar Q (N (T v)) v) • N u := by
  have e := hc (N v)
  have h1 : polar Q (N v) v = 0 := by rw [hL.polar_N_self, hv]
  have h3 : polar Q (N v) u = 1 := by rw [polar_comm, huv]
  rw [hL.leviPair_apply_of_ker hu hv huv (hL.sq v), hTN v,
    hL.leviPair_apply_of_ker hu hv huv (hL.sq (T v)), h1, h3, zero_smul, add_zero, add_zero,
    one_smul, map_add, hTN v, add_assoc] at e
  exact add_left_cancel e

include hL hTN in
theorem exists_smul_of_commute_pair {u v z : V} (hu : Q (N u) = 0) (hv : Q (N v) = 0)
    (hz : Q (N z) = 0) (huv : polar Q u (N v) = 1) (huz : polar Q u (N z) = 0)
    (hzs : N z ∉ Submodule.span K {N u, N v})
    (hc : ∀ v', Q (N v') = 0 → polar Q u (N v') = 1 →
      ∀ x, T (leviPair Q N u v' x) = leviPair Q N u v' (T x)) :
    ∃ a : K, T (N u) = a • N u := by
  have hvz : Q (N (v + z)) = 0 := by
    rw [map_add, hL.map_add_of_ker (hL.sq v) (hL.sq z), hv, hz, add_zero]
  have huvz : polar Q u (N (v + z)) = 1 := by rw [map_add, polar_add_right, huv, huz, add_zero]
  have e1 := apply_N_eq_of_commute hTN hL hu hv huv (hc v hv huv)
  have e2 := apply_N_eq_of_commute hTN hL hu hvz huvz (hc (v + z) hvz huvz)
  set a₁ := polar Q (N (T v)) v
  set b₁ := polar Q (N (T v)) u + polar Q (N (T v)) v
  set a₂ := polar Q (N (T (v + z))) (v + z)
  set b₂ := polar Q (N (T (v + z))) u + polar Q (N (T (v + z))) (v + z)
  by_cases ha₂ : a₂ = 0
  · exact ⟨b₂, by rw [e2, ha₂, zero_smul, zero_add]⟩
  · refine absurd ?_ hzs
    have key : a₂ • N z = (a₁ - a₂) • N v + (b₁ - b₂) • N u := by
      rw [← sub_eq_zero]
      calc a₂ • N z - ((a₁ - a₂) • N v + (b₁ - b₂) • N u) =
            (a₂ • N (v + z) + b₂ • N u) - (a₁ • N v + b₁ • N u) := by rw [map_add]; module
        _ = 0 := by rw [← e1, ← e2, sub_self]
    rw [Submodule.mem_span_pair]
    refine ⟨a₂⁻¹ * (b₁ - b₂), a₂⁻¹ * (a₁ - a₂), ?_⟩
    rw [mul_smul, mul_smul, add_comm, ← smul_add, ← key, smul_smul, inv_mul_cancel₀ ha₂, one_smul]

end Semilinear

theorem eq_one_of_mul_self_eq_one_of_charTwo [CharP K 2] {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : (c - 1) * (c - 1) = 0 := by
    linear_combination h + (1 - c) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem semilinear_lagrangian_rigidity [CharP K 2] (hL : IsLagrangianDisplacement Q N)
    (hX1 : ∀ u v, Q (N u) = 0 → Q (N v) = 0 → polar Q u (N v) = 1 →
      ∃ z, Q (N z) = 0 ∧ polar Q u (N z) = 0 ∧ N z ∉ Submodule.span K {N u, N v})
    (hX2 : ∃ u v, Q (N u) = 0 ∧ Q (N v) = 0 ∧ polar Q u (N v) = 1)
    {φ : K ≃+* K} (T : V ≃+ V) (hTs : ∀ (a : K) x, T (a • x) = φ a • T x)
    (hTQ : ∀ x, Q (T x) = φ (Q x)) (hTN : ∀ x, T (N x) = N (T x))
    (hG1 : ∀ u v, Q (N u) = 0 → Q (N v) = 0 → polar Q u (N v) = 1 →
      ∀ x, T (leviPair Q N u v x) = leviPair Q N u v (T x))
    (hG2 : ∀ u v, Q (N u) = 0 → Q (N v) = 0 → polar Q u (N v) = 1 → ∀ w, N w = 0 →
      ∀ x, T ((eichler Q (N v) w * leviPair Q N u v * (eichler Q (N v) w)⁻¹) x) =
        (eichler Q (N v) w * leviPair Q N u v * (eichler Q (N v) w)⁻¹) (T x)) :
    (∀ a, φ a = a) ∧ ∀ x, T (T x) = x := by
  obtain ⟨u₀, v₀, hu₀, hv₀, huv₀⟩ := hX2
  have hNu₀v₀ : polar Q (N u₀) v₀ = 1 := by rw [hL.polar_left, huv₀]
  have h2a : ∀ u, Q (N u) = 0 → ∀ y, Q (N y) = 0 → polar Q u (N y) ≠ 0 →
      ∃ a : K, T (N u) = a • N u := by
    intro u hu y hy huy
    have hv : Q (N ((polar Q u (N y))⁻¹ • y)) = 0 := by
      rw [map_smul, QuadraticMap.map_smul, hy, smul_zero]
    have huv : polar Q u (N ((polar Q u (N y))⁻¹ • y)) = 1 := by
      rw [map_smul, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ huy]
    obtain ⟨z, hz, huz, hzs⟩ := hX1 u _ hu hv huv
    exact exists_smul_of_commute_pair hTN hL hu hv hz huv huz hzs
      fun v' hv' huv' => hG1 u v' hu hv' huv'
  have h2b : ∀ k, (∀ y, Q (N y) = 0 → polar Q k y = 0) → ∀ y, Q (N y) = 0 →
      polar Q (T k) y = 0 := by
    intro k hkr y hy
    have hy' : Q (N (T.symm y)) = 0 := by
      rw [← semilinear_symm_N hTN, semilinear_map_symm hTQ, hy, map_zero]
    rw [show y = T (T.symm y) from (T.apply_symm_apply y).symm, polar_semilinear_apply hTQ,
      hkr _ hy', map_zero]
  obtain ⟨l₀, hl₀⟩ := h2a u₀ hu₀ v₀ hv₀ (by rw [huv₀]; exact one_ne_zero)
  have h2c : ∀ k, N k = 0 → Q k = 0 → (∀ y, Q (N y) = 0 → polar Q k y = 0) →
      ∃ a : K, T k = a • k := by
    intro k hk hkQ hkr
    obtain ⟨y, rfl⟩ := hL.ker_le k hk
    have h1 : Q (N (u₀ + y)) = 0 := by
      rw [map_add, hL.map_add_of_ker (hL.sq u₀) hk, hu₀, hkQ, add_zero]
    have h2 : polar Q (u₀ + y) (N v₀) ≠ 0 := by
      rw [polar_add_left, huv₀, ← hL.polar_left, hkr v₀ hv₀, add_zero]
      exact one_ne_zero
    obtain ⟨l₁, hl₁⟩ := h2a (u₀ + y) h1 v₀ hv₀ h2
    rw [map_add, map_add, hl₀] at hl₁
    have hTk : T (N y) = (l₁ - l₀) • N u₀ + l₁ • N y := by
      rw [← sub_eq_zero]
      calc T (N y) - ((l₁ - l₀) • N u₀ + l₁ • N y) =
            (l₀ • N u₀ + T (N y)) - l₁ • (N u₀ + N y) := by module
        _ = 0 := by rw [hl₁, sub_self]
    have hp := h2b (N y) hkr v₀ hv₀
    rw [hTk, polar_add_left, polar_smul_left, polar_smul_left, hNu₀v₀, hkr v₀ hv₀, smul_eq_mul,
      smul_eq_mul, mul_zero, add_zero, mul_one, sub_eq_zero] at hp
    exact ⟨l₁, by rw [hTk, hp, sub_self, zero_smul, zero_add]⟩
  have h2d : ∀ x, N x = 0 ∧ Q x = 0 → ∃ a : K, T x = a • x := by
    rintro x ⟨hx, hxQ⟩
    by_cases hrad : ∀ y, Q (N y) = 0 → polar Q x y = 0
    · exact h2c x hx hxQ hrad
    · push Not at hrad
      obtain ⟨y, hy, hxy⟩ := hrad
      obtain ⟨u, rfl⟩ := hL.ker_le x hx
      exact h2a u hxQ y hy (by rwa [← hL.polar_left])
  have hind : ∀ a b : K, a • N u₀ + b • N v₀ = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have e1 := congrArg (fun x => polar Q x u₀) h
    have e2 := congrArg (fun x => polar Q x v₀) h
    simp only [polar_add_left, polar_smul_left, polar_zero_left, smul_eq_mul] at e1 e2
    rw [hL.polar_N_self, hu₀, polar_comm Q (N v₀) u₀, huv₀] at e1
    rw [hNu₀v₀, hL.polar_N_self, hv₀] at e2
    constructor
    · simpa using e2
    · simpa using e1
  obtain ⟨hφ, c, hcW⟩ := semilinear_eq_smul_of_forall_eigen T hTs
    (P := fun x => N x = 0 ∧ Q x = 0)
    (fun x y hx hy => ⟨by rw [map_add, hx.1, hy.1, add_zero],
      by rw [hL.map_add_of_ker hx.1 hy.1, hx.2, hy.2, add_zero]⟩)
    (fun a x hx => ⟨by rw [map_smul, hx.1, smul_zero],
      by rw [QuadraticMap.map_smul, hx.2, smul_zero]⟩)
    h2d ⟨hL.sq u₀, hu₀⟩ ⟨hL.sq v₀, hv₀⟩ hind
  have hTu : T (N u₀) = c • N u₀ := hcW _ ⟨hL.sq u₀, hu₀⟩
  have hTv : T (N v₀) = c • N v₀ := hcW _ ⟨hL.sq v₀, hv₀⟩
  have hc1 : c = 1 := by
    have e := polar_semilinear_apply hTQ u₀ (N v₀)
    rw [huv₀, map_one, hTv, polar_smul_right, ← hL.polar_left, ← hTN, hTu, polar_smul_left,
      hNu₀v₀, smul_eq_mul, smul_eq_mul, mul_one] at e
    exact eq_one_of_mul_self_eq_one_of_charTwo e
  have hW₀ : ∀ z, Q (N z) = 0 → T (N z) = N z := fun z hz => by
    rw [hcW _ ⟨hL.sq z, hz⟩, hc1, one_smul]
  have hW : ∀ y, T (N y) = N y := by
    intro y
    set k := T (N y) - N y with hkdef
    have hk : N k = 0 := by rw [hkdef, map_sub, ← hTN, hL.sq, map_zero, sub_self]
    have hTNy : N (T (N y)) = 0 := by rw [← hTN, hL.sq, map_zero]
    have hkQ : Q k = 0 := by
      rw [hkdef, vec_sub_eq_add K, hL.map_add_of_ker hTNy (hL.sq y), hTQ, hφ,
        CharTwo.add_self_eq_zero]
    have hkr : ∀ z, Q (N z) = 0 → polar Q k z = 0 := by
      intro z hz
      rw [hkdef, polar_sub_left, hTN, hL.polar_left, ← hW₀ z hz, polar_semilinear_apply hTQ, hφ,
        ← hL.polar_left, sub_self]
    let Tl : V ≃ₗ[K] V := T.toLinearEquiv fun a x => by rw [hTs, hφ]
    have hTl : ∀ x, Tl x = T x := fun x => rfl
    have hTlO : Tl ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => by rw [hTl, hTQ, hφ]
    set g := leviPair Q N u₀ v₀ with hgdef
    set r := eichler Q (N v₀) (N y) with hrdef
    set e := eichler Q (N v₀) k with hedef
    have hg : Tl * g = g * Tl := LinearEquiv.ext fun x => hG1 u₀ v₀ hu₀ hv₀ huv₀ x
    have hρ : Tl * (r * g * r⁻¹) = (r * g * r⁻¹) * Tl :=
      LinearEquiv.ext fun x => hG2 u₀ v₀ hu₀ hv₀ huv₀ (N y) (hL.sq y) x
    have hTr : Tl * r * Tl⁻¹ = r * e := by
      rw [hrdef, eichler_conj hTlO, hTl, hTl, hW₀ v₀ hv₀, show T (N y) = N y + k by
        rw [hkdef]; abel, hedef, eichler_mul (hL.polar_N_N v₀ y) (hL.polar_N_of_ker hk v₀)]
    have h1 : Tl * g * Tl⁻¹ = g := by rw [hg, mul_inv_cancel_right]
    have h2 : Tl * (r * g * r⁻¹) * Tl⁻¹ = r * g * r⁻¹ := by rw [hρ, mul_inv_cancel_right]
    have h3 : Tl * (r * g * r⁻¹) * Tl⁻¹ =
        (Tl * r * Tl⁻¹) * (Tl * g * Tl⁻¹) * (Tl * r * Tl⁻¹)⁻¹ := by group
    rw [h3, h1, hTr] at h2
    have h4 : e * g * e⁻¹ = g :=
      calc e * g * e⁻¹ = r⁻¹ * (r * e * g * (r * e)⁻¹) * r := by group
        _ = r⁻¹ * (r * g * r⁻¹) * r := by rw [h2]
        _ = g := by group
    have h5 : g * e * g⁻¹ = e :=
      calc g * e * g⁻¹ = (e * g * e⁻¹) * e * g⁻¹ := by rw [h4]
        _ = e := by group
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q (leviPair_mem_elementaryGroup u₀ v₀)
    have hgv : g (N v₀) = N v₀ + N u₀ := by
      rw [hgdef, hL.leviPair_apply_of_ker hu₀ hv₀ huv₀ (hL.sq v₀), hL.polar_N_self, hv₀,
        polar_comm Q (N v₀) u₀, huv₀, zero_smul, add_zero, add_zero, one_smul]
    have hgk : g k = k := by
      rw [hgdef, hL.leviPair_apply_of_ker hu₀ hv₀ huv₀ hk, hkr v₀ hv₀, hkr u₀ hu₀, zero_smul,
        add_zero, add_zero, zero_smul, add_zero]
    rw [hedef, eichler_conj hgO, hgv, hgk] at h5
    have h6 := LinearEquiv.congr_fun h5 v₀
    have hQ1 : Q (N v₀ + N u₀) = 0 := by
      rw [hL.map_add_of_ker (hL.sq v₀) (hL.sq u₀), hv₀, hu₀, add_zero]
    have hQ2 : polar Q (N v₀ + N u₀) k = 0 := by
      rw [polar_add_left, hL.polar_N_of_ker hk, hL.polar_N_of_ker hk, add_zero]
    rw [eichler_apply hQ1 hQ2, eichler_apply hv₀ (hL.polar_N_of_ker hk v₀)] at h6
    simp only [polar_add_right, hL.polar_self_N v₀, hv₀, hL.polar_swap u₀ v₀, huv₀,
      polar_comm Q v₀ k, hkr v₀ hv₀, hkQ, zero_add, zero_mul, mul_zero, add_zero, zero_smul,
      sub_zero, one_smul, add_eq_left] at h6
    rw [← sub_eq_zero]
    exact h6
  refine ⟨hφ, fun x => ?_⟩
  have hx : N (T x - x) = 0 := by rw [map_sub, ← hTN, hW, sub_self]
  obtain ⟨y, hy⟩ := hL.ker_le _ hx
  have h1 : T (T x - x) = T x - x := by rw [← hy, hW]
  rw [map_sub] at h1
  calc T (T x) = (T (T x) - T x) + T x := by abel
    _ = (T x - x) + T x := by rw [h1]
    _ = (T x + T x) - x := by abel
    _ = x := by
      rw [vec_add_self_eq_zero K, zero_sub, neg_eq_of_add_eq_zero_left (vec_add_self_eq_zero K x)]

end OrthogonalLagrangian

end CFSG.SeitzReduction
