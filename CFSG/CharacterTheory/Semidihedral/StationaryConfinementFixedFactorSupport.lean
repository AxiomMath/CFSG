module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementSupport

public section

namespace CFSG.Semidihedral.StationaryConfinement

section Elements

variable {G : Type*} [Group G]

theorem mem_sup_of_commute {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [hHK h₂ hh₂ k₁ hk₁]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        have hc : h⁻¹ * k⁻¹ = k⁻¹ * h⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hHK h hh k hk]
        rw [mul_inv_rev, hc] }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by rw [mul_one]⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by rw [one_mul]⟩)
  exact hle hx

theorem ambient_core_of_subgroup_map (K : Subgroup G) (H : Subgroup K) :
    (CFSG.pPrimeCore 2 (H.map K.subtype)).map (H.map K.subtype).subtype =
      ((CFSG.pPrimeCore 2 H).map H.subtype).map K.subtype := by
  let eH := H.equivMapOfInjective K.subtype K.subtype_injective
  have hcore := CFSG.pPrimeCore_map_iso 2 eH
  rw [← hcore, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem involution_trivial_mod_of_trivial_mod_product {R W A₀ : Subgroup G} {k : G}
    (hk : k * k = 1)
    (hWA : ∀ w ∈ W, ∀ a ∈ A₀, w * a = a * w) (hAodd : ∀ a ∈ A₀, Odd (orderOf a))
    (hkW : ∀ w ∈ W, k * w * k⁻¹ = w⁻¹) (hkA : ∀ a ∈ A₀, k * a * k⁻¹ = a)
    (hB : ∀ r ∈ R, r⁻¹ * (k * r * k⁻¹) ∈ W ⊔ A₀) :
    ∀ r ∈ R, r⁻¹ * (k * r * k⁻¹) ∈ W := by
  intro r hr
  obtain ⟨w, hw, a, ha, hwa⟩ := mem_sup_of_commute hWA (hB r hr)
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk
  have hkr : k * r * k⁻¹ = r * (w * a) := by rw [← hwa]; group
  have h2 : k * (k * r * k⁻¹) * k⁻¹ = r := by
    calc k * (k * r * k⁻¹) * k⁻¹ = (k * k) * r * (k * k)⁻¹ := by group
      _ = r := by rw [hk]; group
  rw [hkr] at h2
  have h3 : k * (r * (w * a)) * k⁻¹ = (k * r * k⁻¹) * (k * w * k⁻¹) * (k * a * k⁻¹) := by
    group
  rw [h3, hkr, hkW w hw, hkA a ha] at h2
  have h4 : a * a = 1 := by
    have h5 : r * (w * a) * w⁻¹ * a = r * (a * a) := by
      calc r * (w * a) * w⁻¹ * a = r * (w * (a * w⁻¹)) * a := by group
        _ = r * (w * (w⁻¹ * a)) * a := by
          rw [show a * w⁻¹ = w⁻¹ * a from by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hWA w hw a ha, ← mul_assoc,
              inv_mul_cancel, one_mul]]
        _ = r * (a * a) := by group
    rw [h5] at h2
    exact mul_left_cancel (h2.trans (mul_one r).symm)
  have ha1 : a = 1 := by
    have hsq : a = a⁻¹ := eq_inv_of_mul_eq_one_left h4
    exact eq_one_of_eq_inv_of_odd (hAodd a ha) hsq
  rw [ha1, mul_one] at hwa
  rw [hwa]
  exact hw

theorem mem_normalizer_of_trivial_mod [Finite G] {R X S : Subgroup G} {g : G}
    (hXS : X ≤ S) (hSR : S ≤ R) (hg : ∀ r ∈ R, r⁻¹ * (g * r * g⁻¹) ∈ X) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have h := hg x (hSR hx)
  have : g * x * g⁻¹ = x * (x⁻¹ * (g * x * g⁻¹)) := by group
  rw [this]
  exact S.mul_mem hx (hXS h)

theorem trivial_mod_inv {R X : Subgroup G} {k : G}
    (hkR : k ∈ Subgroup.normalizer (R : Set G))
    (hk : ∀ r ∈ R, r⁻¹ * (k * r * k⁻¹) ∈ X) :
    ∀ r ∈ R, r⁻¹ * (k⁻¹ * r * k⁻¹⁻¹) ∈ X := by
  intro r hr
  have hr' : k⁻¹ * r * k⁻¹⁻¹ ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkR) r).mp hr
    exact this
  have h := hk _ hr'
  have h2 : k * (k⁻¹ * r * k⁻¹⁻¹) * k⁻¹ = r := by group
  rw [h2] at h
  have h3 : r⁻¹ * (k⁻¹ * r * k⁻¹⁻¹) = (( k⁻¹ * r * k⁻¹⁻¹)⁻¹ * r)⁻¹ := by group
  rw [h3]
  exact X.inv_mem h

theorem odd_trivial_mod_of_inverted {R X : Subgroup G} {a k : G}
    (haR : a ∈ Subgroup.normalizer (R : Set G)) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (hkR : k ∈ Subgroup.normalizer (R : Set G))
    (hk : ∀ r ∈ R, r⁻¹ * (k * r * k⁻¹) ∈ X) (hka : k * a * k⁻¹ = a⁻¹)
    (ha : Odd (orderOf a)) :
    ∀ r ∈ R, r⁻¹ * (a * r * a⁻¹) ∈ X := by
  have hconjR : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ r ∈ R, g * r * g⁻¹ ∈ R :=
    fun g hg r hr => (Subgroup.mem_normalizer_iff.mp hg r).mp hr
  have hconjX : ∀ x ∈ X, a * x * a⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haX x).mp hx
  have hk' := trivial_mod_inv hkR hk
  have hstep : ∀ r ∈ R, (a * r * a⁻¹)⁻¹ * (a⁻¹ * r * a⁻¹⁻¹) ∈ X := by
    intro r hr
    have hainv : a⁻¹ = k * a * k⁻¹ := hka.symm
    set r₁ := k⁻¹ * r * k⁻¹⁻¹ with hr₁
    have hr₁R : r₁ ∈ R := hconjR _ (Subgroup.inv_mem _ hkR) r hr
    have h1 : r⁻¹ * r₁ ∈ X := hk' r hr
    set r₂ := a * r₁ * a⁻¹ with hr₂
    have hr₂R : r₂ ∈ R := hconjR _ haR r₁ hr₁R
    have h2 : (a * r * a⁻¹)⁻¹ * r₂ ∈ X := by
      have : (a * r * a⁻¹)⁻¹ * r₂ = a * (r⁻¹ * r₁) * a⁻¹ := by rw [hr₂]; group
      rw [this]
      exact hconjX _ h1
    have h3 : r₂⁻¹ * (k * r₂ * k⁻¹) ∈ X := hk r₂ hr₂R
    have h4 : a⁻¹ * r * a⁻¹⁻¹ = k * r₂ * k⁻¹ := by
      calc a⁻¹ * r * a⁻¹⁻¹ = (k * a * k⁻¹) * r * (k * a * k⁻¹)⁻¹ := by rw [hka]
        _ = k * r₂ * k⁻¹ := by rw [hr₂, hr₁]; group
    rw [h4]
    have : (a * r * a⁻¹)⁻¹ * (k * r₂ * k⁻¹) =
        ((a * r * a⁻¹)⁻¹ * r₂) * (r₂⁻¹ * (k * r₂ * k⁻¹)) := by group
    rw [this]
    exact X.mul_mem h2 h3
  have hsq : ∀ r ∈ R, r⁻¹ * (a ^ 2 * r * (a ^ 2)⁻¹) ∈ X := by
    intro r hr
    have h := hstep (a * r * a⁻¹) (hconjR _ haR r hr)
    have e1 : a⁻¹ * (a * r * a⁻¹) * a⁻¹⁻¹ = r := by group
    have e2 : a * (a * r * a⁻¹) * a⁻¹ = a ^ 2 * r * (a ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
      group
    rw [e1, e2] at h
    have : r⁻¹ * (a ^ 2 * r * (a ^ 2)⁻¹) = ((a ^ 2 * r * (a ^ 2)⁻¹)⁻¹ * r)⁻¹ := by group
    rw [this]
    exact X.inv_mem h
  have hpow : ∀ m : ℕ, ∀ r ∈ R, r⁻¹ * ((a ^ 2) ^ m * r * ((a ^ 2) ^ m)⁻¹) ∈ X := by
    intro m
    induction m with
    | zero => intro r hr; simp
    | succ m ih =>
      intro r hr
      have hr' : (a ^ 2) ^ m * r * ((a ^ 2) ^ m)⁻¹ ∈ R :=
        hconjR _ (Subgroup.pow_mem _ (Subgroup.pow_mem _ haR 2) m) r hr
      have h1 := ih r hr
      have h2 := hsq _ hr'
      have : r⁻¹ * ((a ^ 2) ^ (m + 1) * r * ((a ^ 2) ^ (m + 1))⁻¹) =
          (r⁻¹ * ((a ^ 2) ^ m * r * ((a ^ 2) ^ m)⁻¹)) *
            (((a ^ 2) ^ m * r * ((a ^ 2) ^ m)⁻¹)⁻¹ *
              (a ^ 2 * ((a ^ 2) ^ m * r * ((a ^ 2) ^ m)⁻¹) * (a ^ 2)⁻¹)) := by
        rw [pow_succ']
        group
      rw [this]
      exact X.mul_mem h1 h2
  obtain ⟨j, hj⟩ := ha
  have haeq : (a ^ 2) ^ (j + 1) = a := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf a + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  intro r hr
  have h := hpow (j + 1) r hr
  rwa [haeq] at h

end Elements

section Finite

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem cyclic_of_inf_eq_bot_of_commute {W A₀ A' : Subgroup G} [IsCyclic W]
    (hWA : ∀ w ∈ W, ∀ a ∈ A₀, w * a = a * w) (hA' : A' ≤ W ⊔ A₀) (hA'A : A' ⊓ A₀ = ⊥) :
    IsCyclic A' ∧ Nat.card A' ∣ Nat.card W := by
  set B := W ⊔ A₀ with hBdef
  have hWB : W ≤ B := le_sup_left
  have hAB : A₀ ≤ B := le_sup_right
  let A₀B := A₀.subgroupOf B
  have hnormal : A₀B.Normal := by
    constructor
    intro x hx b
    obtain ⟨w, hw, a, ha, hb⟩ := mem_sup_of_commute hWA b.2
    change (b : G) * (x : G) * (b : G)⁻¹ ∈ A₀
    rw [hb]
    have hxA : (x : G) ∈ A₀ := hx
    have hy : a * (x : G) * a⁻¹ ∈ A₀ := A₀.mul_mem (A₀.mul_mem ha hxA) (A₀.inv_mem ha)
    have : w * a * (x : G) * (w * a)⁻¹ = a * (x : G) * a⁻¹ := by
      calc w * a * (x : G) * (w * a)⁻¹ = w * (a * (x : G) * a⁻¹) * w⁻¹ := by group
        _ = (a * (x : G) * a⁻¹) * w * w⁻¹ := by rw [hWA w hw _ hy]
        _ = a * (x : G) * a⁻¹ := by group
    rw [this]
    exact hy
  let q := QuotientGroup.mk' A₀B
  let WB := W.subgroupOf B
  have hWsurj : Function.Surjective (q.comp WB.subtype) := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective A₀B y
    obtain ⟨w, hw, a, ha, hb⟩ := mem_sup_of_commute hWA b.2
    refine ⟨⟨⟨w, hWB hw⟩, hw⟩, ?_⟩
    change q ⟨w, hWB hw⟩ = q b
    apply QuotientGroup.eq.mpr
    change (w : G)⁻¹ * (b : G) ∈ A₀
    rw [hb, inv_mul_cancel_left]
    exact ha
  have hWBcyc : IsCyclic WB := by
    let e := (Subgroup.subgroupOfEquivOfLe hWB).symm
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hQcyc : IsCyclic (B ⧸ A₀B) := isCyclic_of_surjective _ hWsurj
  have hQcard : Nat.card (B ⧸ A₀B) ∣ Nat.card W := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWB).toEquiv]
    exact Subgroup.card_dvd_of_surjective hWsurj
  let A'B := A'.subgroupOf B
  have hinj : Function.Injective (q.comp A'B.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxA : ((x : B) : G) ∈ A₀ := (QuotientGroup.eq_one_iff (x : B)).mp hx
    have hxA' : ((x : B) : G) ∈ A' := x.2
    have hmem : ((x : B) : G) ∈ A' ⊓ A₀ := ⟨hxA', hxA⟩
    rw [hA'A, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have hA'B : Nat.card A'B = Nat.card A' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA').toEquiv
  have hA'Bcyc : IsCyclic A'B := by
    let e := MonoidHom.ofInjective hinj
    have : IsCyclic (q.comp A'B.subtype).range := Subgroup.isCyclic _
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨?_, ?_⟩
  · let e := Subgroup.subgroupOfEquivOfLe hA'
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  · rw [← hA'B]
    exact (Subgroup.card_dvd_of_injective _ hinj).trans hQcard

theorem mem_zpowers_of_pow_prime_eq_one {A : Subgroup G} [IsCyclic A] {x a : G}
    (hxA : x ∈ A) (haA : a ∈ A) {r : ℕ} (hr : r.Prime) (hx : orderOf x = r) (ha : a ^ r = 1) :
    a ∈ Subgroup.zpowers x := by
  have hdvd : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one ha
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · let x' : A := ⟨x, hxA⟩
    let a' : A := ⟨a, haA⟩
    have hcard : Nat.card (Subgroup.zpowers a') = Nat.card (Subgroup.zpowers x') := by
      rw [Nat.card_zpowers, Nat.card_zpowers, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact h1.trans hx.symm
    have heq : Subgroup.zpowers a' = Subgroup.zpowers x' :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
    have hmem : a' ∈ Subgroup.zpowers x' := heq ▸ Subgroup.mem_zpowers a'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

end Finite

end CFSG.Semidihedral.StationaryConfinement
