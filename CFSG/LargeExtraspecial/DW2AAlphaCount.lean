module

public import CFSG.LargeExtraspecial.DW2AAlpha

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

section Count

variable (hWW : W ≤ perp S W) {Y : Subgroup S.O}
  (hfix : ∀ y ∈ Y, ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)
  (hfaith : ∀ y ∈ Y, (∀ v ∈ perp S W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ W) → y = 1)
  (hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y)
  {x : S.Qt} (hxP : x ∈ perp S W) (hxW : x ∉ W) (hx : ∀ y ∈ Y, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x)
  {R : Submodule (ZMod 2) S.Qt} (hRW : R ≤ perp S W)
  (hR1 : ∀ y ∈ Y, ∀ v ∈ perp S W, polar S.q v x = 0 → (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ R)
  (hR2 : ∀ y ∈ Y, ∀ r ∈ R, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) r - r ∈ (ZMod 2 ∙ x) ⊔ W)
  (hR3 : ∀ r ∈ R, (∀ y ∈ Y, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) r - r ∈ W) → r ∈ (ZMod 2 ∙ x) ⊔ W)

omit [Finite G] in
theorem eq_add_of_mem_sup {v : S.Qt} (hv : v ∈ (ZMod 2 ∙ x) ⊔ W) (hvW : v ∉ W) :
    ∃ w ∈ W, v = x + w := by
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp ha
  rcases zmod2_cases μ with rfl | rfl
  · rw [zero_smul, zero_add] at hvW
    exact absurd hw hvW
  · exact ⟨w, hw, by rw [one_smul]⟩

include hcomm hxW hR1 hR2 hR3 in
theorem sub_mem_sup_of_fix {y : S.O} (hy : y ∈ Y)
    (hy0 : ∀ r ∈ R, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) r - r ∈ W) {v : S.Qt} (hv : v ∈ perp S W)
    (hvx : polar S.q v x = 0) : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2 ∙ x) ⊔ W := by
  set a := (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v with ha
  have haR : a ∈ R := hR1 y hy v hv hvx
  by_contra hna
  obtain ⟨t, ht, hta⟩ : ∃ t ∈ Y, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a ∉ W := by
    by_contra h
    push Not at h
    exact hna (hR3 a haR h)
  obtain ⟨w₀, hw₀, he₀⟩ := eq_add_of_mem_sup (hR2 t ht a haR) hta
  set b := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v with hb
  have hbR : b ∈ R := hR1 t ht v hv hvx
  have hw₁ := hy0 b hbR
  have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v + a + (x + w₀) := by
    have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + a := by rw [ha]; abel
    rw [e, map_add, ← he₀]
    abel
  have h2 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v + a + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) := by
    have e : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + b := by rw [hb]; abel
    rw [e, map_add, ha, hb]
    abel
  have hc : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    change ((t * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = ((y * t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    rw [hcomm t ht y hy]
  rw [h1, h2] at hc
  have hx' : x = ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b) - w₀ := by
    have := add_left_cancel hc
    rw [← this]
    abel
  exact hxW (hx' ▸ sub_mem hw₁ hw₀)

theorem polar_sub_smul_eq_zero {u v : S.Qt} (hu : polar S.q u x = 1) :
    polar S.q (v - polar S.q v x • u) x = 0 := by
  rw [polar_sub_left, polar_smul_left, hu, smul_eq_mul, mul_one, sub_self]

include hWW hfix hfaith hcomm hxP hxW hx hRW hR1 hR2 hR3 in
theorem eq_of_sub_mem {u : S.Qt} (huP : u ∈ perp S W) (hu : polar S.q u x = 1) {y y' : S.O}
    (hy : y ∈ Y) (hy' : y' ∈ Y)
    (h : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ W) : y = y' := by
  set e := y'⁻¹ * y with he
  have heY : e ∈ Y := Y.mul_mem (Y.inv_mem hy') hy
  have heu : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ W := by
    have h1 : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u = ((y'⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
      rw [map_sub]
      have : ((y'⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y' : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u := by
        change ((y'⁻¹ * y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u
        rw [inv_mul_cancel]
        rfl
      rw [this]
      rfl
    rw [h1, hfix _ (Y.inv_mem hy') _ h]
    exact h
  have he0 : ∀ r ∈ R, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) r - r ∈ W := by
    intro r hr
    by_contra hrW
    obtain ⟨w₀, hw₀, he₀⟩ := eq_add_of_mem_sup (hR2 e heY r hr) hrW
    have hiso := polar_apply_apply e u r
    have hr' : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) r = r + (x + w₀) := by rw [← he₀]; abel
    rw [hr'] at hiso
    have hpw : polar S.q ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u) w₀ = 0 := by
      have := polar_apply_apply e u w₀
      rw [hfix e heY w₀ hw₀] at this
      rw [this]
      exact mem_perp.mp huP w₀ hw₀ |> fun h0 => by rw [polar_comm]; exact h0
    have hpx : polar S.q ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u) x = 1 := by
      have := polar_apply_apply e u x
      rw [hx e heY] at this
      rw [this, hu]
    have hpr : polar S.q ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) r = 0 :=
      mem_perp.mp (hRW hr) _ heu
    rw [polar_add_right, polar_add_right, hpw, hpx, add_zero] at hiso
    rw [polar_sub_left] at hpr
    have : polar S.q ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u) r = polar S.q u r := by
      rw [← sub_eq_zero]; exact hpr
    rw [this] at hiso
    have h01 := congrArg (· - polar S.q u r) hiso
    simp at h01
  have he1 : e = 1 := by
    refine hfaith e heY fun v hv => ?_
    set v₀ := v - polar S.q v x • u with hv₀
    have hv₀P : v₀ ∈ perp S W := sub_mem hv (Submodule.smul_mem _ _ huP)
    have hv₀x : polar S.q v₀ x = 0 := polar_sub_smul_eq_zero hu
    obtain ⟨b, hb, w, hw, hbw⟩ := Submodule.mem_sup.mp
      (sub_mem_sup_of_fix hcomm hxW hR1 hR2 hR3 heY he0 hv₀P hv₀x)
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hμ : μ = 0 := by
      have hiso := polar_apply_apply e v₀ u
      obtain ⟨w', hw', hu'⟩ : ∃ w' ∈ W, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + w' :=
        ⟨_, heu, by abel⟩
      have hv' : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀ = v₀ + (μ • x + w) := by rw [hbw]; abel
      rw [hv', hu'] at hiso
      have p1 : polar S.q v₀ w' = 0 := by rw [polar_comm]; exact mem_perp.mp hv₀P w' hw'
      have p2 : polar S.q x w' = 0 := by rw [polar_comm]; exact mem_perp.mp hxP w' hw'
      have p3 : polar S.q w u = 0 := mem_perp.mp huP w hw
      have p4 : polar S.q w w' = 0 := mem_perp.mp (hWW hw') w hw
      have p5 : polar S.q x u = 1 := by rw [polar_comm]; exact hu
      simp only [polar_add_left, polar_add_right, polar_smul_left, p1, p2, p3, p4, p5,
        smul_eq_mul, mul_one, mul_zero, add_zero] at hiso
      have := congrArg (· - polar S.q v₀ u) hiso
      simpa [add_comm] using this
    subst hμ
    have hev : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
        ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀ - v₀) +
          polar S.q v x • ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by
      have : v = v₀ + polar S.q v x • u := by rw [hv₀]; abel
      conv_lhs => rw [this]
      rw [map_add, map_smul, smul_sub]
      abel
    rw [hev, ← hbw, zero_smul, zero_add]
    exact add_mem hw (Submodule.smul_mem _ _ heu)
  have := congrArg (y' * ·) he1
  simpa [he, mul_assoc] using this

include hWW hfix hfaith hcomm hxP hxW hx hRW hR1 hR2 hR3 in
theorem card_le_of_orbit [FiniteDimensional (ZMod 2) S.Qt] {u : S.Qt} (huP : u ∈ perp S W)
    (hu : polar S.q u x = 1) {U : Submodule (ZMod 2) S.Qt} (hWU : W ≤ U)
    (hYU : ∀ y ∈ Y, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ U) :
    Nat.card Y ≤ 2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) W) := by
  classical
  set K := W.comap U.subtype
  let f : Y → U ⧸ K := fun y => Submodule.Quotient.mk ⟨_, hYU y y.2⟩
  have hf : Function.Injective f := by
    intro y y' hyy'
    have h := (Submodule.Quotient.eq K).mp hyy'
    rw [Submodule.mem_comap] at h
    have h' : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ W := by
      have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
          ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) - ((y' : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
      rw [e]
      exact h
    exact Subtype.ext (eq_of_sub_mem hWW hfix hfaith hcomm hxP hxW hx hRW hR1 hR2 hR3 huP hu
      y.2 y'.2 h')
  have : Finite (U ⧸ K) := Module.finite_of_finite (ZMod 2)
  have hcard := Nat.card_le_card_of_injective f hf
  have hK : finrank (ZMod 2) K = finrank (ZMod 2) W :=
    (Submodule.comapSubtypeEquivOfLe hWU).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank K
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U ⧸ K), Nat.card_zmod] at hcard
  have : finrank (ZMod 2) (U ⧸ K) = finrank (ZMod 2) U - finrank (ZMod 2) W := by omega
  rwa [this] at hcard

end Count

variable (S) in
@[expose] noncomputable def radSing (P : Submodule (ZMod 2) S.Qt) : Submodule (ZMod 2) S.Qt where
  carrier := {v | v ∈ P ⊓ perp S P ∧ S.q v = 0}
  add_mem' := by
    rintro u v ⟨hu, hqu⟩ ⟨hv, hqv⟩
    refine ⟨add_mem hu hv, ?_⟩
    have h := mem_perp.mp hv.2 u hu.1
    rw [polar] at h
    linear_combination h + hqu + hqv
  zero_mem' := ⟨zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro c v ⟨hv, hq⟩
    refine ⟨Submodule.smul_mem _ c hv, ?_⟩
    rw [QuadraticMap.map_smul, hq, smul_zero]

theorem radSing_eq (hA : Hyp S W) {P : Submodule (ZMod 2) S.Qt} (hP : IsMbarInvariant S P)
    (hWP : W ≤ P) (hPW : P ≤ perp S W) : radSing S P = W := by
  have hRinv : IsMbarInvariant S (P ⊓ perp S P) := hP.inf hP.perp
  refine hA.max _ (fun m v hv => ⟨hRinv m v hv.1, by rw [q_ρ_apply]; exact hv.2⟩)
    (fun v hv => hv.2) fun w hw => ⟨⟨hWP hw, mem_perp.mpr fun p hp => ?_⟩, hA.sing w hw⟩
  rw [polar_comm]
  exact mem_perp.mp (hPW hp) w hw

theorem finrank_rad_le [FiniteDimensional (ZMod 2) S.Qt] (hA : Hyp S W)
    {P : Submodule (ZMod 2) S.Qt} (hP : IsMbarInvariant S P) (hWP : W ≤ P)
    (hPW : P ≤ perp S W) : finrank (ZMod 2) (P ⊓ perp S P : Submodule (ZMod 2) S.Qt) ≤
      finrank (ZMod 2) W + 1 := by
  set R := P ⊓ perp S P with hR
  have hRiso : ∀ u ∈ R, ∀ v ∈ R, polar S.q u v = 0 := fun u hu v hv => mem_perp.mp hv.2 u hu.1
  let φ : R →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => S.q v
      map_add' := fun u v => by
        have := hRiso u u.2 v v.2
        rw [polar] at this
        rw [Submodule.coe_add]
        linear_combination this
      map_smul' := fun c v => by
        rcases zmod2_cases c with rfl | rfl
        · simp
        · simp }
  have hker : (LinearMap.ker φ).map R.subtype = radSing S P := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, hq⟩
      exact ⟨⟨v, hv⟩, hq, rfl⟩
  rw [radSing_eq hA hP hWP hPW] at hker
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank (ZMod 2) (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_self] at this
  have h3 : finrank (ZMod 2) (LinearMap.ker φ) = finrank (ZMod 2) W := by
    rw [← hker]
    exact (Submodule.equivMapOfInjective _ R.injective_subtype _).finrank_eq
  omega

end Alpha

end CFSG.LargeExtraspecial.DW
