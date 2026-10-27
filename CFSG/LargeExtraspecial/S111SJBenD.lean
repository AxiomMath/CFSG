module

public import CFSG.LargeExtraspecial.S111SJBenB
public import CFSG.LargeExtraspecial.S111SIGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.Open CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender

section LinearAlgebra

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]



@[expose] noncomputable def fixedSpace (c : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.ker ((c : V →ₗ[ZMod 2] V) - LinearMap.id)

theorem mem_fixedSpace {c : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fixedSpace c ↔ c v = v := by
  rw [fixedSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

theorem add_self_eq_zero_of_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem finrank_le_two_mul_fixedSpace [FiniteDimensional (ZMod 2) V] {c : V ≃ₗ[ZMod 2] V}
    (hc : ∀ v, c (c v) = v) : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (fixedSpace c) := by
  set f : V →ₗ[ZMod 2] V := (c : V →ₗ[ZMod 2] V) - LinearMap.id with hf
  have hff : ∀ v, f (f v) = 0 := by
    intro v
    simp only [hf, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, hc]
    calc v - c v - (c v - v) = (v + v) - (c v + c v) := by abel
      _ = 0 := by rw [add_self_eq_zero_of_zmod2, add_self_eq_zero_of_zmod2, sub_zero]
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    exact hff v
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_mono hle
  change finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (LinearMap.ker f)
  omega

theorem inf_map_eq_bot {c y : V ≃ₗ[ZMod 2] V} (hy : ∀ v, y v = v → v = 0)
    (hcy : ∀ v, c (y v) = y (y (c v))) :
    fixedSpace c ⊓ (fixedSpace c).map (y : V →ₗ[ZMod 2] V) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, u, hu, rfl⟩
  rw [Submodule.mem_bot]
  have hv' : c (y u) = y u := mem_fixedSpace.mp hv
  have hu' : c u = u := mem_fixedSpace.mp hu
  rw [hcy, hu'] at hv'
  have h1 : y u = u := y.injective hv'
  have h0 := hy u h1
  change y u = 0
  rw [h0, map_zero]

theorem finrank_fixedSpace_eq [FiniteDimensional (ZMod 2) V] {c y : V ≃ₗ[ZMod 2] V} {w : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * w) (hc : ∀ v, c (c v) = v) (hy : ∀ v, y v = v → v = 0)
    (hcy : ∀ v, c (y v) = y (y (c v))) :
    finrank (ZMod 2) (fixedSpace c) = w ∧
      fixedSpace c ⊔ (fixedSpace c).map (y : V →ₗ[ZMod 2] V) = ⊤ := by
  have h1 := finrank_le_two_mul_fixedSpace hc
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace c)
    ((fixedSpace c).map (y : V →ₗ[ZMod 2] V))
  rw [inf_map_eq_bot hy hcy, finrank_bot, add_zero, LinearEquiv.finrank_map_eq] at h2
  have h3 := Submodule.finrank_le (fixedSpace c ⊔ (fixedSpace c).map (y : V →ₗ[ZMod 2] V))
  have hw : finrank (ZMod 2) (fixedSpace c) = w := by omega
  refine ⟨hw, Submodule.eq_top_of_finrank_eq ?_⟩
  omega



@[expose] noncomputable def repRestrict {K : Type*} [Group K] (ρ : K →* (V ≃ₗ[ZMod 2] V))
    (Y : Submodule (ZMod 2) V) (hY : ∀ k : K, ∀ v ∈ Y, ρ k v ∈ Y) :
    K →* (Y ≃ₗ[ZMod 2] Y) where
  toFun k :=
    { toFun := fun v => ⟨ρ k v, hY k v v.2⟩
      invFun := fun v => ⟨ρ k⁻¹ v, hY k⁻¹ v v.2⟩
      map_add' := fun v w => Subtype.ext (map_add (ρ k) (v : V) w)
      map_smul' := fun r v => Subtype.ext (map_smul (ρ k) r (v : V))
      left_inv := fun v => Subtype.ext (by
        change ρ k⁻¹ (ρ k v) = v
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one,
          id_eq])
      right_inv := fun v => Subtype.ext (by
        change ρ k (ρ k⁻¹ v) = v
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one,
          id_eq]) }
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' k k' := by
    ext v
    change ρ (k * k') v = ρ k (ρ k' v)
    rw [map_mul, LinearEquiv.mul_apply]

theorem repRestrict_apply {K : Type*} [Group K] (ρ : K →* (V ≃ₗ[ZMod 2] V))
    (Y : Submodule (ZMod 2) V) (hY : ∀ k : K, ∀ v ∈ Y, ρ k v ∈ Y) (k : K) (v : Y) :
    ((repRestrict ρ Y hY k v : Y) : V) = ρ k v := rfl

end LinearAlgebra

namespace LayerCfg

variable {X : Type} [Group X] {E O L : Subgroup X} {w : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)} {a : V}

theorem exists_gen_of_ne_bot [Finite X] [hOn : O.Normal] (C : LayerCfg E O L w ρ a)
    (hO : O ≠ ⊥) : ∃ y ∈ O, orderOf y = 3 ∧ O = zpowers y ∧
      ∀ x : X, x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹ := by
  have hO3 : Nat.card O = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp C.card_O with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hO
    · exact h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨y, hyO⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hO
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyo : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := hO3 ▸ Subgroup.orderOf_dvd_natCard _ hyO
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1'
    · exact h
  have hOy : O = zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyO) ?_).symm
    rw [Nat.card_zpowers, hyo, hO3]
  refine ⟨y, hyO, hyo, hOy, fun x => ?_⟩
  rcases eq_one_or_eq_or_eq_inv_of_orderOf_eq_three hyo
    (hOy ▸ hOn.conj_mem y hyO x) with h | h | h
  · exfalso
    apply hy1'
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exact Or.inr h

theorem eq_zero_of_fix [Finite X] (C : LayerCfg E O L w ρ a) {y : X} (hyo : orderOf y = 3)
    (hcases : ∀ x : X, x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹) {v : V} (hv : ρ y v = v) :
    v = 0 := by
  have hinv : ∀ u : V, ρ y u = u → ρ y⁻¹ u = u := fun u hu => by
    conv_lhs => rw [← hu]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one, id_eq]
  have hW : ∀ x : X, ∀ u ∈ fixedSpace (ρ y), ρ x u ∈ fixedSpace (ρ y) := by
    intro x u hu
    rw [mem_fixedSpace] at hu ⊢
    have hx : ρ (x⁻¹ * y * x) u = u := by
      rcases hcases x⁻¹ with h | h
      · rw [inv_inv] at h
        rw [h, hu]
      · rw [inv_inv] at h
        rw [h, hinv u hu]
    calc ρ y (ρ x u) = ρ x (ρ (x⁻¹ * y * x) u) := by
          rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ x u := by rw [hx]
  rcases C.irr _ hW with h | h
  · have : v ∈ fixedSpace (ρ y) := mem_fixedSpace.mpr hv
    rw [h, Submodule.mem_bot] at this
    exact this
  · exfalso
    have h1 : ρ y = 1 := by
      ext u
      have : u ∈ fixedSpace (ρ y) := by rw [h]; trivial
      exact mem_fixedSpace.mp this
    have h2 : y = 1 := C.rho_inj (by rw [h1, map_one])
    rw [h2, orderOf_one] at hyo
    omega

theorem false_of_inner_of_O_ne_bot_of_noModule [Finite X]
    [FiniteDimensional (ZMod 2) V] [E.Normal] [hOn : O.Normal] (C : LayerCfg E O L w ρ a)
    (hinner : ∀ l ∈ L.map (barAct E), ∃ q, l = MulAut.conj q) (hO : O ≠ ⊥)
    (hY : ∀ (Y : Type) [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
      (ρY : ↥E →* (Y ≃ₗ[ZMod 2] Y)), Function.Injective ρY → finrank (ZMod 2) Y ≠ w) :
    False := by
  have hperf := C.perfect
  obtain ⟨y, hyO, hyo, hOy, hcases⟩ := C.exists_gen_of_ne_bot hO
  have hyfix : ∀ v, ρ y v = v → v = 0 := fun v hv => C.eq_zero_of_fix hyo hcases hv
  have hy3 : y * y * y = 1 := by
    rw [← pow_three', ← hyo]
    exact pow_orderOf_eq_one y
  have hyi : y⁻¹ = y * y := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hy3]
  have hyne : y⁻¹ ≠ y := by
    intro h
    rw [inv_eq_iff_mul_eq_one] at h
    have : y = 1 := by
      calc y = y * y * y * (y * y)⁻¹ := by group
        _ = 1 := by rw [hy3, h, inv_one, one_mul]
    rw [this, orderOf_one] at hyo
    omega
  obtain ⟨ℓ₀, hℓ₀, hℓ₀y⟩ : ∃ ℓ ∈ L, ℓ * y * ℓ⁻¹ = y⁻¹ := by
    by_contra hno
    push Not at hno
    have hc : ∀ ℓ ∈ L, ℓ * y = y * ℓ := fun ℓ hℓ => by
      rcases hcases ℓ with h | h
      · calc ℓ * y = ℓ * y * ℓ⁻¹ * ℓ := by group
          _ = y * ℓ := by rw [h]
      · exact absurd h (hno ℓ hℓ)
    rcases C.fix_eq (ρ y a) (fun ℓ hℓ => by
        rw [← LinearEquiv.mul_apply, ← map_mul, hc ℓ hℓ, map_mul, LinearEquiv.mul_apply,
          C.a_fix ℓ hℓ]) with h | h
    · exact C.a_ne ((ρ y).injective (by rw [h, map_zero]))
    · exact C.a_ne (hyfix a h)
  obtain ⟨q, hq⟩ := hinner _ ⟨ℓ₀, hℓ₀, rfl⟩
  obtain ⟨e, -, he⟩ := C.exists_mul_of_barAct_eq_conj hq
  set d := (e : X)⁻¹ * ℓ₀ with hd
  have hdE : ∀ e' ∈ E, d * e' = e' * d := he
  have hey : (e : X) * y = y * e := C.commute_of_mem_O hyO e.2
  have hdy : d * y = y⁻¹ * d := by
    have h1 : (e : X)⁻¹ * y⁻¹ = y⁻¹ * (e : X)⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hey]
    calc d * y = (e : X)⁻¹ * (ℓ₀ * y * ℓ₀⁻¹) * ℓ₀ := by rw [hd]; group
      _ = y⁻¹ * d := by rw [hℓ₀y, ← mul_assoc, h1]
  have hddy : (d * d) * y = y * (d * d) := by
    have h1 : d * y⁻¹ = y * d := by
      calc d * y⁻¹ = (y * d⁻¹)⁻¹ := by group
        _ = (d⁻¹ * y⁻¹)⁻¹ := by
          congr 1
          calc y * d⁻¹ = d⁻¹ * (d * y) * d⁻¹ := by group
            _ = d⁻¹ * (y⁻¹ * d) * d⁻¹ := by rw [hdy]
            _ = d⁻¹ * y⁻¹ := by group
        _ = y * d := by group
    calc d * d * y = d * (y⁻¹ * d) := by rw [mul_assoc, hdy]
      _ = y * d * d := by rw [← mul_assoc, h1]
      _ = y * (d * d) := by group
  have hddF : d * d ∈ centralizer ((O ⊔ E : Subgroup X) : Set X) := by
    have hle : O ⊔ E ≤ centralizer ({d * d} : Set X) := by
      refine sup_le (fun o ho => ?_) (fun e' he' => ?_)
      · rw [hOy] at ho
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ho
        exact mem_centralizer_singleton_iff.mpr (Commute.zpow_left hddy.symm k).eq
      · have hc : Commute d e' := hdE e' he'
        exact mem_centralizer_singleton_iff.mpr (hc.mul_left hc).eq.symm
    exact mem_centralizer_iff.mpr fun z hz => mem_centralizer_singleton_iff.mp (hle hz)
  set k := orderOf (d * d) with hk
  have hk0 : 0 < k := orderOf_pos _
  have hkodd : Odd k := by
    by_contra hev
    obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.mp hev
    have hj0 : 0 < j := by omega
    have hu2 : (d * d) ^ j * (d * d) ^ j = 1 := by
      rw [← pow_add, ← hj, hk, pow_orderOf_eq_one]
    have hu1 := C.fstar_inv _ hu2 (Subgroup.pow_mem _ hddF j)
    have := Nat.le_of_dvd hj0 (orderOf_dvd_of_pow_eq_one hu1)
    omega
  obtain ⟨j, hj⟩ := hkodd
  set c := d ^ k with hcdef
  have hcd : c = (d * d) ^ j * d := by
    rw [hcdef, hj, pow_succ, ← pow_two, ← pow_mul, mul_comm 2 j, pow_mul, pow_two]
  have hc2 : c * c = 1 := by
    rw [hcdef, ← pow_add, ← two_mul, pow_mul, pow_two]
    exact pow_orderOf_eq_one _
  have hcy : c * y = y⁻¹ * c := by
    have h1 : (d * d) ^ j * y⁻¹ = y⁻¹ * (d * d) ^ j :=
      ((Commute.pow_left hddy j).inv_right).eq
    rw [hcd, mul_assoc, hdy, ← mul_assoc, h1, mul_assoc]
  have hcE : ∀ e' ∈ E, c * e' = e' * c := fun e' he' =>
    (Commute.pow_left (show Commute d e' from hdE e' he') k).eq
  have hρc : ∀ v, ρ c (ρ c v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, hc2, map_one, LinearEquiv.coe_one, id_eq]
  have hρcy : ∀ v, ρ c (ρ y v) = ρ y (ρ y (ρ c v)) := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, hcy, hyi, ← LinearEquiv.mul_apply,
      ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
  obtain ⟨hYw, hYtop⟩ := finrank_fixedSpace_eq C.finrank_eq hρc hyfix hρcy
  have hYinv : ∀ e' : E, ∀ v ∈ fixedSpace (ρ c), (ρ.comp E.subtype) e' v ∈ fixedSpace (ρ c) := by
    intro e' v hv
    rw [mem_fixedSpace] at hv ⊢
    change ρ c (ρ e' v) = ρ e' v
    rw [← LinearEquiv.mul_apply, ← map_mul, hcE e' e'.2, map_mul, LinearEquiv.mul_apply, hv]
  set ρY := repRestrict (ρ.comp E.subtype) (fixedSpace (ρ c)) hYinv with hρY
  have hρYinj : Function.Injective ρY := by
    rw [injective_iff_map_eq_one]
    intro e' he'
    have hfix : ∀ v ∈ fixedSpace (ρ c), ρ e' v = v := fun v hv => by
      have := congrArg (fun σ : fixedSpace (ρ c) ≃ₗ[ZMod 2] fixedSpace (ρ c) =>
        ((σ ⟨v, hv⟩ : fixedSpace (ρ c)) : V)) he'
      simpa [hρY, repRestrict_apply] using this
    have hey' : (e' : X) * y = y * e' := C.commute_of_mem_O hyO e'.2
    have hall : fixedSpace (ρ c) ⊔ (fixedSpace (ρ c)).map (ρ y : V →ₗ[ZMod 2] V) ≤
        fixedSpace (ρ e') := by
      refine sup_le (fun v hv => mem_fixedSpace.mpr (hfix v hv)) ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [mem_fixedSpace]
      change ρ e' (ρ y u) = ρ y u
      rw [← LinearEquiv.mul_apply, ← map_mul, hey', map_mul, LinearEquiv.mul_apply, hfix u hu]
    rw [hYtop, top_le_iff] at hall
    have h1 : ρ e' = 1 := by
      ext v
      have : v ∈ fixedSpace (ρ e') := by rw [hall]; trivial
      exact mem_fixedSpace.mp this
    exact Subtype.ext (C.rho_inj (by rw [h1, OneMemClass.coe_one, map_one]))
  exact hY _ ρY hρYinj hYw

theorem false_of_inner_of_O_ne_bot [Finite X]
    [FiniteDimensional (ZMod 2) V] [E.Normal] [hOn : O.Normal] (C : LayerCfg E O L w ρ a)
    (h6 : 6 ≤ w) {f : ℕ} (hB : BenderType (E ⧸ center E) f 1 1)
    (hinner : ∀ l ∈ L.map (barAct E), ∃ q, l = MulAut.conj q) (hO : O ≠ ⊥) : False := by
  refine C.false_of_inner_of_O_ne_bot_of_noModule hinner hO ?_
  intro Y _ _ _ ρY hρY hYw
  have hw := (C.width_le hB).2 (by norm_num)
  have hD' := two_mul_le_finrank_of_benderType ρY hρY hB (by omega)
  rw [hYw] at hD'
  have h2 := hB.two_le
  omega

end LayerCfg

end CFSG.LargeExtraspecial.S11
