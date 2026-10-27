module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Iwasawa
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaPrim

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped commutatorElement

variable {K V : Type*} [Field K] [IsF2 K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_apply_f2 {v : V} (hv : Q v = 1) (x : V) :
    reflect Q v x = x + polar Q x v • v := reflect_apply_of_map_eq_one' hv x

theorem reflect_eq_imp (hQ : (polarBilin Q).Nondegenerate) {a b : V} (ha : Q a = 1) (hb : Q b = 1)
    (h : reflect Q a = reflect Q b) : a = b := by
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at ha; exact zero_ne_one ha
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ ha0
  have hy1 : polar Q a y = 1 := IsF2.eq_one_of_ne_zero hy
  have h1 := congrArg (fun g : V ≃ₗ[K] V => g y) h
  simp only [reflect_apply_f2 ha, reflect_apply_f2 hb] at h1
  have h2 : polar Q y a • a = polar Q y b • b := add_left_cancel h1
  rw [polar_comm, hy1, one_smul] at h2
  rcases IsF2.eq_zero_or_one (polar Q y b) with h3 | h3
  · rw [h3, zero_smul] at h2
    exact absurd h2 ha0
  · rw [h3, one_smul] at h2
    exact h2

theorem commute_reflect_iff (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a : V} (ha : Q a = 1) :
    g * reflect Q a = reflect Q a * g ↔ g a = a := by
  have hc := reflect_conj hg a
  constructor
  · intro h
    have h1 : g * reflect Q a * g⁻¹ = reflect Q a := by rw [h]; group
    rw [h1] at hc
    exact reflect_eq_imp hQ (by rw [map_of_mem hg, ha]) ha hc.symm
  · intro h
    rw [h] at hc
    calc g * reflect Q a = g * reflect Q a * g⁻¹ * g := by group
      _ = reflect Q a * g := by rw [hc]

theorem exists_prescribed [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank K V) {p q : V} (hpq : LinearIndependent K ![p, q]) (ε₁ ε₂ : K) :
    ∃ a : V, polar Q p a = ε₁ ∧ polar Q q a = ε₂ ∧ Q a = 1 := by
  set f : V →ₗ[K] K × K := (polarBilin Q p).prod (polarBilin Q q) with hf
  have hfa : ∀ a, f a = (polar Q p a, polar Q q a) := fun a => by simp [hf]
  have hrange : LinearMap.range f = ⊤ := by
    by_contra hne
    obtain ⟨ψ, hψ0, hψ⟩ := Submodule.exists_le_ker_of_lt_top (LinearMap.range f)
      (lt_top_iff_ne_top.2 hne)
    have hψ' : ∀ x y : K, ψ (x, y) = x * ψ (1, 0) + y * ψ (0, 1) := fun x y => by
      have : ((x, y) : K × K) = x • ((1, 0) : K × K) + y • ((0, 1) : K × K) := by simp
      rw [this, map_add, map_smul, map_smul]; simp
    have hz : ∀ a, polar Q p a * ψ (1, 0) + polar Q q a * ψ (0, 1) = 0 := fun a => by
      have := hψ ⟨a, rfl⟩
      rw [LinearMap.mem_ker, hfa, hψ'] at this
      exact this
    have hz' : ψ (1, 0) • p + ψ (0, 1) • q = 0 := by
      refine eq_zero_of_polar_eq_zero hQ fun a => ?_
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
      linear_combination hz a
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hpq _ _ hz'
    apply hψ0
    refine LinearMap.ext fun xy => ?_
    obtain ⟨x, y⟩ := xy
    rw [hψ', h1, h2]
    simp
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
  obtain ⟨a₀, ha₀⟩ := hsurj (ε₁, ε₂)
  rw [hfa] at ha₀
  obtain ⟨ha₀1, ha₀2⟩ := Prod.mk.inj ha₀
  by_contra hcon
  push Not at hcon
  set U := LinearMap.ker f with hU
  have hUmem : ∀ z, z ∈ U ↔ polar Q p z = 0 ∧ polar Q q z = 0 := fun z => by
    rw [hU, LinearMap.mem_ker, hfa, Prod.mk_eq_zero]
  have hQ0 : ∀ z ∈ U, Q (a₀ + z) = 0 := fun z hz => by
    have hz' := (hUmem z).1 hz
    have := hcon (a₀ + z) (by rw [polar_add_right, ha₀1, hz'.1, add_zero])
      (by rw [polar_add_right, ha₀2, hz'.2, add_zero])
    exact (IsF2.eq_zero_or_one _).resolve_right this
  have hQa₀ : Q a₀ = 0 := by simpa using hQ0 0 (Submodule.zero_mem _)
  have hQz : ∀ z ∈ U, Q z = polar Q a₀ z := fun z hz => by
    have := hQ0 z hz
    rw [QuadraticMap.map_add Q, hQa₀, zero_add] at this
    rw [eq_neg_of_add_eq_zero_left this, IsF2.neg_eq_self]
  have hUU : U ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z' hz'
    show polar Q z' z = 0
    have e1 : polar Q z' z = Q (z' + z) - Q z' - Q z := rfl
    rw [e1, hQz _ (U.add_mem hz' hz), hQz _ hz', hQz _ hz, polar_add_right]
    ring
  have h1 := Submodule.finrank_mono hUU
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, ← hU] at h2
  have h3 : finrank K (K × K) = 2 := by simp [Module.finrank_prod]
  omega

section Prim

variable [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ finrank K V)
include hQ hd

theorem primitive {w : V} (hw : Q w = 1) {H : Subgroup (V ≃ₗ[K] V)}
    (hHE : H ≤ elementaryGroup Q) (hC : ∀ g ∈ elementaryGroup Q, g w = w → g ∈ H)
    (hne : ∃ g ∈ H, g w ≠ w) : H = elementaryGroup Q := by
  classical
  have hEO : ∀ g ∈ elementaryGroup Q, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    elementaryGroup_le_orthogonalGroup Q hg
  have hHO : ∀ g ∈ H, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg => hEO g (hHE hg)
  have hQ1 : ∀ a, Q a ≠ 0 → Q a = 1 := fun a ha => IsF2.eq_one_of_ne_zero ha
  set X : Set V := {b | ∃ h ∈ H, h w = b} with hXdef
  have hXQ : ∀ b ∈ X, Q b = 1 := by
    rintro b ⟨h, hh, rfl⟩
    rw [map_of_mem (hHO h hh), hw]
  have hwX : w ∈ X := ⟨1, H.one_mem, rfl⟩
  have hpair : ∀ u v, Q u = 1 → Q v = 1 → reflect Q u * reflect Q v ∈ elementaryGroup Q :=
    fun u v hu hv => reflect_mul_reflect_mem_elementaryGroup hQ (by omega) hu hv
  have hrefl_fix : ∀ v x, Q v = 1 → polar Q x v = 0 → reflect Q v x = x := fun v x hv hxv => by
    rw [reflect_apply_f2 hv, hxv, zero_smul, add_zero]
  set P : V → Prop := fun c => ∀ u v : V, Q u = 1 → Q v = 1 → polar Q u c = 0 → polar Q v c = 0 →
    reflect Q u * reflect Q v ∈ H with hP
  have hPw : P w := by
    intro u v hu hv huw hvw
    refine hC _ (hpair u v hu hv) ?_
    rw [LinearEquiv.mul_apply, hrefl_fix v w hv (by rw [polar_comm]; exact hvw),
      hrefl_fix u w hu (by rw [polar_comm]; exact huw)]
  have hPX : ∀ c ∈ X, P c := by
    rintro c ⟨h, hh, rfl⟩ u v hu hv huc hvc
    have hhO := hHO h hh
    have hhinvO : h⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hhO
    have hu' : Q (h⁻¹ u) = 1 := by rw [map_of_mem hhinvO, hu]
    have hv' : Q (h⁻¹ v) = 1 := by rw [map_of_mem hhinvO, hv]
    have hpol : ∀ y, polar Q y (h w) = 0 → polar Q (h⁻¹ y) w = 0 := fun y hy => by
      rw [← polar_map_of_mem hhO, LinearEquiv.apply_inv_apply']
      exact hy
    have hk := hPw (h⁻¹ u) (h⁻¹ v) hu' hv' (hpol u huc) (hpol v hvc)
    have e : reflect Q u * reflect Q v =
        h * (reflect Q (h⁻¹ u) * reflect Q (h⁻¹ v)) * h⁻¹ := by
      have h1 := reflect_conj hhO (h⁻¹ u)
      have h2 := reflect_conj hhO (h⁻¹ v)
      rw [LinearEquiv.apply_inv_apply'] at h1 h2
      calc reflect Q u * reflect Q v = (h * reflect Q (h⁻¹ u) * h⁻¹) * (h * reflect Q (h⁻¹ v) * h⁻¹) := by
            rw [h1, h2]
        _ = h * (reflect Q (h⁻¹ u) * reflect Q (h⁻¹ v)) * h⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh)
  have M1 : ∀ c ∈ X, ∀ w₁ ∈ X, ∀ b : V, Q b = 1 → polar Q w₁ b = 1 →
      polar Q c w₁ = polar Q c b → b ∈ X := by
    intro c hc w₁ hw₁ b hb hw1b hcw
    have hQw₁ := hXQ w₁ hw₁
    have hQd : Q (w₁ + b) = 1 := by
      rw [QuadraticMap.map_add Q, hQw₁, hb, hw1b, IsF2.one_add_one, zero_add]
    have hdc : polar Q (w₁ + b) c = 0 := by
      rw [polar_add_left, polar_comm Q w₁ c, polar_comm Q b c, ← hcw]
      exact IsF2.add_self_eq_zero _
    obtain ⟨u, hu1, hu2, hu3⟩ := exists_polar_eq_zero_map_ne_zero hQ (by omega) c w₁
    have hQu : Q u = 1 := hQ1 u hu3
    have hk : reflect Q (w₁ + b) * reflect Q u ∈ H :=
      hPX c hc (w₁ + b) u hQd hQu hdc (by rw [polar_comm]; exact hu1)
    have hcomp : (reflect Q (w₁ + b) * reflect Q u) w₁ = b := by
      rw [LinearEquiv.mul_apply, hrefl_fix u w₁ hQu hu2, reflect_apply_f2 hQd]
      have : polar Q w₁ (w₁ + b) = 1 := by rw [polar_add_right, polar_self_f2, zero_add, hw1b]
      rw [this, one_smul, ← add_assoc, add_self_eq_zero_f2 K, zero_add]
    obtain ⟨h₁, hh₁, rfl⟩ := hw₁
    exact ⟨_, H.mul_mem hk hh₁, by rw [LinearEquiv.mul_apply]; exact hcomp⟩
  have caseI : ∀ x ∈ X, polar Q w x = 1 → ∀ b : V, Q b = 1 → b ∈ X := by
    intro x hx hwx b hb
    have hxQ := hXQ x hx
    have hxw : polar Q x w = 1 := by rw [polar_comm]; exact hwx
    have hQwx : Q (w + x) = 1 := by
      rw [QuadraticMap.map_add Q, hw, hxQ, hwx, IsF2.one_add_one, zero_add]
    have hwxX : w + x ∈ X :=
      M1 x hx w hwX (w + x) hQwx (by rw [polar_add_right, polar_self_f2, hwx, zero_add])
        (by rw [polar_add_right, polar_self_f2, add_zero])
    have hN1 : ∀ b : V, Q b = 1 → polar Q w b = 1 → b ∈ X := by
      intro b hb hwb
      rcases IsF2.eq_zero_or_one (polar Q x b) with hxb | hxb
      · refine M1 (w + x) hwxX w hwX b hb hwb ?_
        rw [polar_add_left, polar_add_left, polar_self_f2, hxw, hwb, hxb, zero_add, add_zero]
      · refine M1 x hx w hwX b hb hwb ?_
        rw [hxw, hxb]
    by_cases hwb : polar Q w b = 1
    · exact hN1 b hb hwb
    have hwb0 : polar Q w b = 0 := (IsF2.eq_zero_or_one _).resolve_right hwb
    by_cases hbw : b = w
    · rw [hbw]; exact hwX
    have hwne : w ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hw; exact zero_ne_one hw
    have hbne : b ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hb; exact zero_ne_one hb
    obtain ⟨y, hy1, hy2, hyQ⟩ := exists_prescribed hQ (by omega)
      (linearIndependent_pair_of_ne hwne hbne (Ne.symm hbw)) 1 1
    have hyX : y ∈ X := hN1 y hyQ hy1
    have hyb0 : y + b ≠ 0 := fun h0 => by
      have hyb : y = b := add_right_cancel (h0.trans (add_self_eq_zero_f2 K b).symm)
      rw [hyb, hwb0] at hy1
      exact zero_ne_one hy1
    have hywb : y + b ≠ w := fun h => by
      have hy' : y = w + b := by
        calc y = y + (b + b) := by rw [add_self_eq_zero_f2 K, add_zero]
          _ = (y + b) + b := by rw [add_assoc]
          _ = w + b := by rw [h]
      rw [hy', polar_add_right, polar_self_f2, hwb0, add_zero] at hy1
      exact zero_ne_one hy1
    obtain ⟨c, hc1, hc2, hcQ⟩ := exists_prescribed hQ (by omega)
      (linearIndependent_pair_of_ne hyb0 hwne hywb) 0 1
    have hcX : c ∈ X := hN1 c hcQ hc2
    have hyb1 : polar Q y b = 1 := by rw [polar_comm]; exact hy2
    refine M1 c hcX y hyX b hb hyb1 ?_
    rw [polar_add_left] at hc1
    have h3 : polar Q y c = polar Q b c := by
      rw [eq_neg_of_add_eq_zero_left hc1, IsF2.neg_eq_self]
    rw [polar_comm Q c y, polar_comm Q c b, h3]
  have caseII : ∀ x ∈ X, x ≠ w → polar Q w x = 0 → ∃ y ∈ X, polar Q w y = 1 := by
    intro x hx hxw hwx
    have hxQ := hXQ x hx
    have hwne : w ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hw; exact zero_ne_one hw
    have hxne : x ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hxQ; exact zero_ne_one hxQ
    obtain ⟨v, hv1, hv2, hvQ⟩ := exists_prescribed hQ (by omega)
      (linearIndependent_pair_of_ne hxne hwne hxw) 0 1
    have hk : reflect Q x * reflect Q v ∈ H :=
      hPX x hx x v hxQ hvQ (polar_self_f2 x) (by rw [polar_comm]; exact hv1)
    have hxv : polar Q v x = 0 := by rw [polar_comm]; exact hv1
    have hwx' : polar Q w x = 0 := hwx
    refine ⟨w + v, ⟨reflect Q x * reflect Q v, hk, ?_⟩, ?_⟩
    · rw [LinearEquiv.mul_apply, reflect_apply_f2 hvQ, hv2, one_smul, reflect_apply_f2 hxQ,
        polar_add_left, hwx', hxv, add_zero, zero_smul, add_zero]
    · rw [polar_add_right, polar_self_f2, zero_add, hv2]
  have hT : ∀ b : V, Q b = 1 → b ∈ X := by
    obtain ⟨g₀, hg₀, hg₀w⟩ := hne
    have hxX : g₀ w ∈ X := ⟨g₀, hg₀, rfl⟩
    rcases IsF2.eq_zero_or_one (polar Q w (g₀ w)) with h0 | h1
    · obtain ⟨y, hyX, hy⟩ := caseII (g₀ w) hxX hg₀w h0
      exact caseI y hyX hy
    · exact caseI (g₀ w) hxX h1
  refine le_antisymm hHE fun g hg => ?_
  obtain ⟨h, hh, hhw⟩ := hT (g w) (by rw [map_of_mem (hEO g hg), hw])
  have hmem : h⁻¹ * g ∈ elementaryGroup Q :=
    (elementaryGroup Q).mul_mem ((elementaryGroup Q).inv_mem (hHE hh)) hg
  have hfix : (h⁻¹ * g) w = w := by
    rw [LinearEquiv.mul_apply, ← hhw, LinearEquiv.inv_apply_apply']
  have := H.mul_mem hh (hC _ hmem hfix)
  rwa [mul_inv_cancel_left] at this

theorem exists_order_three {v : V} (hv : Q v = 1) :
    ∃ v' : V, Q v' = 1 ∧ polar Q v v' = 1 ∧ (reflect Q v * reflect Q v') ^ 3 = 1 ∧
      reflect Q v * reflect Q v' ≠ 1 ∧
      reflect Q v * (reflect Q v * reflect Q v') * (reflect Q v)⁻¹ =
        (reflect Q v * reflect Q v')⁻¹ := by
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, QuadraticMap.map_zero] at hv; exact zero_ne_one hv
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hv0
  have hy1 : polar Q v y = 1 := IsF2.eq_one_of_ne_zero hy
  have hy0 : y ≠ 0 := fun h0 => by rw [h0, polar_zero_right] at hy1; exact zero_ne_one hy1
  have hvy : v ≠ y := fun h0 => by rw [← h0, polar_self_f2] at hy1; exact zero_ne_one hy1
  obtain ⟨v', hv'1, -, hv'Q⟩ := exists_prescribed hQ (by omega)
    (linearIndependent_pair_of_ne hv0 hy0 hvy) 1 0
  have hvO := reflect_mem_orthogonalGroup Q v
  have hv'O := reflect_mem_orthogonalGroup Q v'
  have hsq : ∀ a : V, reflect Q a * reflect Q a = 1 := fun a => reflect_mul_self Q a
  have hy1' : polar Q v v' = 1 := hv'1
  have hv'v : polar Q v' v = 1 := by rw [polar_comm]; exact hv'1
  have e1 : reflect Q v * reflect Q v' * reflect Q v = reflect Q (v + v') := by
    have := reflect_conj hvO v'
    rw [reflect_inv, reflect_apply_f2 hv, hv'v, one_smul, add_comm] at this
    exact this
  have e2 : reflect Q v' * reflect Q v * reflect Q v' = reflect Q (v + v') := by
    have := reflect_conj hv'O v
    rw [reflect_inv, reflect_apply_f2 hv'Q, hy1', one_smul] at this
    exact this
  refine ⟨v', hv'Q, hy1', ?_, ?_, ?_⟩
  · calc (reflect Q v * reflect Q v') ^ 3
        = (reflect Q v * reflect Q v' * reflect Q v) * (reflect Q v' * reflect Q v * reflect Q v') := by
          rw [pow_succ, pow_two]; group
      _ = reflect Q (v + v') * reflect Q (v + v') := by rw [e1, e2]
      _ = 1 := hsq _
  · intro h
    have h1 : reflect Q v = (reflect Q v')⁻¹ := mul_eq_one_iff_eq_inv.mp h
    rw [reflect_inv] at h1
    have h2 := reflect_eq_imp hQ hv hv'Q h1
    rw [← h2, polar_self_f2] at hy1'
    exact zero_ne_one hy1'
  · rw [mul_inv_rev, reflect_inv, reflect_inv]
    calc reflect Q v * (reflect Q v * reflect Q v') * reflect Q v
        = (reflect Q v * reflect Q v) * reflect Q v' * reflect Q v := by group
      _ = reflect Q v' * reflect Q v := by rw [hsq, one_mul]

end Prim

section Transvection

variable [FiniteDimensional K V]

theorem transvection_eq_reflect (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : ∀ x, Q (t x) = Q x) {v : V} (f : V →ₗ[K] K) (hv : v ≠ 0) (hf : f ≠ 0) (hfv : f v = 0)
    (htx : ∀ x, t x = x + f x • v) : Q v = 1 ∧ t = reflect Q v := by
  have h0 : ∀ x, f x * f x * Q v + f x * polar Q x v = 0 := fun x => by
    have h1 := ht x
    rw [htx x, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq] at h1
    linear_combination h1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (LinearMap.ext fun x => by simpa using hcon x)
  have hx₀1 : f x₀ = 1 := IsF2.eq_one_of_ne_zero hx₀
  have hA : ∀ x, f x = 1 → polar Q x v = Q v := fun x hx => by
    have := h0 x
    rw [hx] at this
    simp only [one_mul] at this
    rw [eq_neg_of_add_eq_zero_right this, IsF2.neg_eq_self]
  have hQv : Q v = 1 := by
    by_contra hQv0
    have hQv0' : Q v = 0 := (IsF2.eq_zero_or_one _).resolve_right hQv0
    have hall : ∀ y, polar Q y v = 0 := fun y => by
      rcases IsF2.eq_zero_or_one (f y) with hy | hy
      · have h1 : f (y + x₀) = 1 := by rw [map_add, hy, hx₀1, zero_add]
        have h2 := hA _ h1
        have h3 := hA _ hx₀1
        rw [polar_add_left, hQv0'] at h2
        rw [hQv0'] at h3
        rw [h3, add_zero] at h2
        exact h2
      · rw [hA y hy, hQv0']
    exact hv (eq_zero_of_polar_eq_zero hQ fun y => by rw [polar_comm]; exact hall y)
  refine ⟨hQv, LinearEquiv.ext fun x => ?_⟩
  rw [htx x, reflect_apply_f2 hQv]
  congr 2
  rcases IsF2.eq_zero_or_one (f x) with hx | hx
  · have h1 : f (x + x₀) = 1 := by rw [map_add, hx, hx₀1, zero_add]
    have h2 := hA _ h1
    have h3 := hA _ hx₀1
    rw [polar_add_left, h3, hQv] at h2
    rw [hx]
    exact (add_eq_right.mp h2).symm
  · rw [hx, hA x hx, hQv]

end Transvection

section Matrix

open CFSG.Open (StatedOmega)

variable {K : Type} [Field K] [IsF2 K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coatom_matrix (Q : QuadraticForm K (ι → K)) (Q₀ : (ι → K) → K) (hQ₀ : ⇑Q = Q₀)
    (hnd : (polarBilin Q).Nondegenerate) (hd : 6 ≤ Fintype.card ι)
    (hΩ : (StatedOmega Q₀).map (toLinEquiv ι K).toMonoidHom = elementaryGroup Q)
    (t : GL ι K) (v : ι → K) (f : (ι → K) →ₗ[K] K) (hv : v ≠ 0) (hf : f ≠ 0) (hfv : f v = 0)
    (htx : ∀ x, Matrix.mulVec (t : Matrix ι ι K) x = x + f x • v)
    (hQt : ∀ x, Q₀ (Matrix.mulVec (t : Matrix ι ι K) x) = Q₀ x)
    (H : Subgroup (GL ι K)) (hHΩ : H ≤ StatedOmega Q₀)
    (hHC : ∀ g ∈ StatedOmega Q₀, t * g * t⁻¹ = g → g ∈ H)
    (hH : ∃ g ∈ H, t * g * t⁻¹ ≠ g) : H = StatedOmega Q₀ := by
  classical
  set Φ := toLinEquiv ι K with hΦ
  have hrank : finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have hQt' : ∀ x, Q (Φ t x) = Q x := fun x => by
    have := hQt x
    rw [← hQ₀] at this
    simpa [hΦ, toLinEquiv_apply] using this
  obtain ⟨hvQ, ht'⟩ := transvection_eq_reflect hnd hQt' f hv hf hfv
    (fun x => by simpa [hΦ, toLinEquiv_apply] using htx x)
  have hΩE : ∀ g ∈ StatedOmega Q₀, Φ g ∈ elementaryGroup Q := fun g hg =>
    hΩ ▸ Subgroup.mem_map_of_mem _ hg
  have hEΩ : ∀ g' ∈ elementaryGroup Q, ∃ g ∈ StatedOmega Q₀, Φ g = g' := fun g' hg' => by
    rw [← hΩ] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    exact ⟨g, hg, rfl⟩
  have hcomm : ∀ g ∈ StatedOmega Q₀, (Φ g * reflect Q v = reflect Q v * Φ g ↔ t * g * t⁻¹ = g) :=
    fun g hg => by
      rw [← ht', ← map_mul, ← map_mul, Φ.injective.eq_iff]
      constructor
      · intro h
        calc t * g * t⁻¹ = g * t * t⁻¹ := by rw [← h]
          _ = g := by group
      · intro h
        calc g * t = t * g * t⁻¹ * t := by rw [h]
          _ = t * g := by group
  set H' := H.map Φ.toMonoidHom with hH'
  have hH'E : H' ≤ elementaryGroup Q := by
    rintro _ ⟨g, hg, rfl⟩
    exact hΩE g (hHΩ hg)
  have hC' : ∀ g' ∈ elementaryGroup Q, g' v = v → g' ∈ H' := by
    intro g' hg' hg'v
    obtain ⟨g, hg, rfl⟩ := hEΩ g' hg'
    have hcm := (commute_reflect_iff hnd (elementaryGroup_le_orthogonalGroup Q hg') hvQ).2 hg'v
    exact ⟨g, hHC g hg ((hcomm g hg).1 hcm), rfl⟩
  have hne' : ∃ g' ∈ H', g' v ≠ v := by
    obtain ⟨g, hg, hgt⟩ := hH
    refine ⟨Φ g, ⟨g, hg, rfl⟩, fun hgv => hgt ?_⟩
    have := (commute_reflect_iff hnd
      (elementaryGroup_le_orthogonalGroup Q (hΩE g (hHΩ hg))) hvQ).2 hgv
    exact (hcomm g (hHΩ hg)).1 this
  have hprim := primitive hnd (by omega) hvQ hH'E hC' hne'
  rw [← hΩ, hH'] at hprim
  exact Subgroup.map_injective Φ.injective hprim

theorem three_matrix (Q : QuadraticForm K (ι → K)) (Q₀ : (ι → K) → K) (hQ₀ : ⇑Q = Q₀)
    (hnd : (polarBilin Q).Nondegenerate) (hd : 6 ≤ Fintype.card ι)
    (hΩ : (StatedOmega Q₀).map (toLinEquiv ι K).toMonoidHom = elementaryGroup Q)
    (t : GL ι K) (v : ι → K) (f : (ι → K) →ₗ[K] K) (hv : v ≠ 0) (hf : f ≠ 0) (hfv : f v = 0)
    (htx : ∀ x, Matrix.mulVec (t : Matrix ι ι K) x = x + f x • v)
    (hQt : ∀ x, Q₀ (Matrix.mulVec (t : Matrix ι ι K) x) = Q₀ x) :
    ∃ g ∈ StatedOmega Q₀, g ≠ 1 ∧ g ^ 3 = 1 ∧ t * g * t⁻¹ = g⁻¹ := by
  classical
  set Φ := toLinEquiv ι K with hΦ
  have hrank : finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have hQt' : ∀ x, Q (Φ t x) = Q x := fun x => by
    have := hQt x
    rw [← hQ₀] at this
    simpa [hΦ, toLinEquiv_apply] using this
  obtain ⟨hvQ, ht'⟩ := transvection_eq_reflect hnd hQt' f hv hf hfv
    (fun x => by simpa [hΦ, toLinEquiv_apply] using htx x)
  obtain ⟨v', hv'Q, -, hcube, hne, hinv⟩ := exists_order_three hnd (by omega) hvQ
  have hg'E : reflect Q v * reflect Q v' ∈ elementaryGroup Q :=
    reflect_mul_reflect_mem_elementaryGroup hnd (by omega) hvQ hv'Q
  rw [← hΩ] at hg'E
  obtain ⟨g, hg, hgeq⟩ := hg'E
  refine ⟨g, hg, fun h1 => hne ?_, ?_, ?_⟩
  · rw [← hgeq, h1, map_one]
  · apply Φ.injective
    rw [map_pow, map_one]
    exact (by rw [← hgeq] at hcube; exact hcube : Φ g ^ 3 = 1)
  · apply Φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, ht']
    have : Φ g = reflect Q v * reflect Q v' := hgeq
    rw [this]
    exact hinv

end Matrix

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaPrim
