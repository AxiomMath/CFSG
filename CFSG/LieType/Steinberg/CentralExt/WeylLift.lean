module

public import CFSG.LieType.Steinberg.CentralExt.FieldThreeMultiplier

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.WeylLift

variable {τ : Tag}

theorem eq_zero_or_one_or_neg_one {k : Type} [Field k] [Finite k] (hk : Nat.card k = 3) (c : k) :
    c = 0 ∨ c = 1 ∨ c = -1 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have h2 : (2 : k) ≠ 0 := FieldThree.two_ne_zero_of_card_three hk
  have h10 : (1 : k) ≠ 0 := one_ne_zero
  have hm0 : (-1 : k) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have h1m : (1 : k) ≠ -1 := fun h => h2 (by linear_combination h)
  by_contra hc
  push Not at hc
  obtain ⟨hc0, hc1, hcm⟩ := hc
  have hcard : ({c, 0, 1, -1} : Finset k).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hc0, hc1, hcm]),
      Finset.card_insert_of_notMem (by simp [h10.symm, hm0.symm]),
      Finset.card_pair h1m]
  have hle := Finset.card_le_univ ({c, 0, 1, -1} : Finset k)
  rw [hcard, Fintype.card_eq_nat_card, hk] at hle
  omega

theorem three_eq_zero {k : Type} [Field k] [Finite k] (hk : Nat.card k = 3) : (3 : k) = 0 := by
  have : Fintype k := Fintype.ofFinite k
  have h := FiniteField.cast_card_eq_zero k
  rw [Fintype.card_eq_nat_card, hk] at h
  exact_mod_cast h

section Weyl

variable {G : Type*} [Group G] {k : Type*} [Field k] {r : ℕ} {x : (Fin r → ℤ) → k → G}

theorem inv_eq_of_add {γ : Fin r → ℤ} (hγ : ∀ c d, x γ (c + d) = x γ c * x γ d)
    (c : k) : (x γ c)⁻¹ = x γ (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← hγ, add_neg_cancel]
  have h0 := hγ 0 0
  rw [add_zero] at h0
  exact left_eq_mul.1 h0

theorem weylElement_neg_one {i : Fin r}
    (hp : ∀ c d, x (Pi.single i 1) (c + d) = x (Pi.single i 1) c * x (Pi.single i 1) d)
    (hn : ∀ c d, x (-Pi.single i 1) (c + d) = x (-Pi.single i 1) c * x (-Pi.single i 1) d) :
    weylElement x i (-1) = (weylElement x i 1)⁻¹ := by
  have hu : (((-1 : kˣ)⁻¹ : kˣ) : k) = -1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one, inv_neg, inv_one]
  simp only [weylElement, mul_inv_rev, inv_eq_of_add hp, inv_eq_of_add hn, inv_one, hu,
    Units.val_one, Units.val_neg, neg_neg, mul_assoc]

end Weyl

section Tag

variable {G : Type*} [Group G] {hA : TauCeti.IsFiniteType τ.cartan}
  {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k] {x : (Fin τ.rank → ℤ) → k → G}
  {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ} {O : CommOrder (RootSystem.ofCartan hA ∅)}
  (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
  (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)

include hroots in
theorem mem_roots {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : γ ∈ (tagDatum τ hA RG).roots := by
  rw [hroots]
  exact hγ

include hroots hE in
theorem x_add {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c d : k) : x γ (c + d) = x γ c * x γ d :=
  (hE.param γ (mem_roots hroots hγ)).2.1 c d

include hroots hE in
theorem x_injective {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : Function.Injective (x γ) :=
  (hE.param γ (mem_roots hroots hγ)).2.2

include hroots hE in
theorem weyl_conj_root (i : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ ε : k, ε * ε = 1 ∧
      (∀ u, weylElement x i 1 * x β u * (weylElement x i 1)⁻¹ = x (reflect τ i β) (ε * u)) ∧
      ∀ u, weylElement x i 1 * x (reflect τ i β) u * (weylElement x i 1)⁻¹ =
        x β (ε * (((-1 : kˣ) ^ (-cartanCoord β i) : kˣ) : k) * u) := by
  obtain ⟨ε, hε, h⟩ := hE.weyl i β (mem_roots hroots hβ)
  have href : CFSG.LieType.RootSystem.reflection (tagDatum τ hA RG).cartan i β = reflect τ i β :=
    reflection_cartan τ i β
  have hεε : (ε : k) * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  set ν : k := (((-1 : kˣ) ^ (-cartanCoord β i) : kˣ) : k) with hν
  have hνν : ν * ν = 1 := by
    rw [hν, ← Units.val_mul, ← mul_zpow, neg_mul_neg, one_mul, one_zpow, Units.val_one]
  have hw : weylElement x i (-1) = (weylElement x i 1)⁻¹ :=
    weylElement_neg_one (x_add hroots hE (IsRoot.basis i))
      (x_add hroots hE (IsRoot.neg (IsRoot.basis i)))
  refine ⟨ε, hεε, fun u => ?_, fun u => ?_⟩
  · have := h 1 u
    rw [href, one_zpow, Units.val_one, mul_one] at this
    exact this
  ·
    have h1 := h (-1) ((ε : k) * ν * u)
    have hνdef : (((-1 : kˣ) ^ (-∑ j, (tagDatum τ hA RG).cartan i j * β j) : kˣ) : k) = ν := rfl
    rw [href, hw, inv_inv, hνdef] at h1
    have e : (ε : k) * ν * ((ε : k) * ν * u) = u := by
      linear_combination (ν * ν * u) * hεε + u * hνν
    rw [e] at h1
    rw [← h1]
    group

section Lift

variable (T : (Fin τ.rank → kˣ) →* G)
  (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
    T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
  {E : Type*} [Group E] {π : E →* G} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π)

include hroots hE hT hcen hπ in
theorem conj_isRootLift {β β' : Fin τ.rank → ℤ} (hβ' : IsRoot τ β')
    {Y Y' : k → E} (hY : IsRootLift x T π β Y) (hY' : IsRootLift x T π β' Y') {n : G} {a : k}
    (ha : a * a = 1) (hn : ∀ u, n * x β u * n⁻¹ = x β' (a * u))
    (hnT : ∀ t, ∃ t', n * T t * n⁻¹ = T t') {t₀ : Fin τ.rank → kˣ} (ht₀ : rootChar k β t₀ ≠ 1)
    {ñ : E} (hñ : π ñ = n) (u : k) : ñ * Y u * ñ⁻¹ = Y' (a * u) := by
  set ψ : k → E := fun v => ñ * Y (a * v) * ñ⁻¹ with hψ
  have hψadd : ∀ s t, ψ (s + t) = ψ s * ψ t := fun s t => by
    simp only [hψ, mul_add, hY.1]
    group
  have hπψ : ∀ s, π (ψ s) = x β' s := fun s => by
    simp only [hψ, map_mul, map_inv, hñ, hY.2.1, hn, ← mul_assoc, ha, one_mul]
  obtain ⟨t', ht'⟩ := hnT t₀
  set b : k := (rootChar k β t₀ : k) with hb
  obtain ⟨e₀, he₀⟩ := hπ (T t₀)
  set e : E := ñ * e₀ * ñ⁻¹ with he
  have hπe : π e = T t' := by
    rw [he, map_mul, map_mul, map_inv, hñ, he₀, ht']
  have hψe : ∀ s, e * ψ s * e⁻¹ = ψ (b * s) := fun s => by
    have h1 := hY.2.2 t₀ e₀ he₀ (a * s)
    simp only [he, hψ]
    calc ñ * e₀ * ñ⁻¹ * (ñ * Y (a * s) * ñ⁻¹) * (ñ * e₀ * ñ⁻¹)⁻¹ =
        ñ * (e₀ * Y (a * s) * e₀⁻¹) * ñ⁻¹ := by group
      _ = ñ * Y (b * (a * s)) * ñ⁻¹ := by rw [h1]
      _ = ñ * Y (a * (b * s)) * ñ⁻¹ := by rw [show b * (a * s) = a * (b * s) by ring]
  have hbb : (rootChar k β' t' : k) = b := by
    have h1 : π (e * ψ 1 * e⁻¹) = x β' ((rootChar k β' t' : k) * 1) := by
      rw [map_mul, map_mul, map_inv, hπe, hπψ, hT t' β' hβ']
    rw [hψe, hπψ] at h1
    have := x_injective hroots hE hβ' h1
    rw [mul_one, mul_one] at this
    exact this.symm
  have hY'e : ∀ s, e * Y' s * e⁻¹ = Y' (b * s) := fun s => by
    rw [hY'.2.2 t' e hπe s, hbb]
  have hb1 : b ≠ 1 := fun h => ht₀ (Units.val_eq_one.1 h)
  have heq := TorusLift.lift_unique hcen hψadd hY'.1 hπψ hY'.2.1 hb1 hψe hY'e
  have := congrFun heq (a * u)
  simp only [hψ, ← mul_assoc, ha, one_mul] at this
  exact this

end Lift

end Tag

section Swap

variable {E : Type*} [Group E] {k : Type} [Field k] [Finite k]

theorem commute_of_swap (hk : Nat.card k = 3) {Y Y' : k → E}
    (hY : ∀ s t, Y (s + t) = Y s * Y t) (hY' : ∀ s t, Y' (s + t) = Y' s * Y' t)
    (hc : ∀ s t, ⁅Y s, Y' t⁆ ∈ Subgroup.center E) {ñ : E} {a : k} (ha : a * a = 1)
    (h1 : ∀ s, ñ * Y s * ñ⁻¹ = Y' (a * s)) (h2 : ∀ t, ñ * Y' t * ñ⁻¹ = Y (a * t)) (s t : k) :
    Y s * Y' t = Y' t * Y s := by
  have hcomm : ∀ (z : E), z ∈ Subgroup.center E → ∀ g, g * z = z * g := fun z hz g =>
    (Subgroup.mem_center_iff.1 hz) g
  set c : k → k → E := fun s t => ⁅Y s, Y' t⁆ with hcdef
  have hc' : ∀ s t g, g * c s t = c s t * g := fun s t g => hcomm _ (hc s t) g
  have hY0 : Y 0 = 1 := by
    have h := hY 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hY'0 : Y' 0 = 1 := by
    have h := hY' 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hadd1 : ∀ s s' t, c (s + s') t = c s t * c s' t := fun s s' t => by
    have e : c (s + s') t = Y s * c s' t * (Y s)⁻¹ * c s t := by
      simp only [hcdef, hY, commutatorElement_def]
      group
    rw [e, hc' s' t (Y s), mul_inv_cancel_right, hc' s t (c s' t)]
  have hadd2 : ∀ s t t', c s (t + t') = c s t * c s t' := fun s t t' => by
    have e : c s (t + t') = c s t * (Y' t * c s t' * (Y' t)⁻¹) := by
      simp only [hcdef, hY', commutatorElement_def]
      group
    rw [e, hc' s t' (Y' t), mul_inv_cancel_right]
  have hc0 : ∀ t, c 0 t = 1 := fun t => by
    simp only [hcdef, hY0, commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
  have hc0' : ∀ s, c s 0 = 1 := fun s => by
    simp only [hcdef, hY'0, commutatorElement_def, inv_one, mul_one, mul_inv_cancel]
  have hneg1 : ∀ t, c (-1) t = (c 1 t)⁻¹ := fun t => by
    have h := hadd1 1 (-1) t
    rw [add_neg_cancel, hc0] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hneg2 : ∀ s, c s (-1) = (c s 1)⁻¹ := fun s => by
    have h := hadd2 s 1 (-1)
    rw [add_neg_cancel, hc0'] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hsw : c 1 1 = (c 1 1)⁻¹ := by
    have h : ñ * c 1 1 * ñ⁻¹ = (c a a)⁻¹ := by
      have e : ñ * c 1 1 * ñ⁻¹ = ⁅ñ * Y 1 * ñ⁻¹, ñ * Y' 1 * ñ⁻¹⁆ := by
        simp only [hcdef, commutatorElement_def]
        group
      rw [e, h1, h2, mul_one]
      show ⁅Y' a, Y a⁆ = ⁅Y a, Y' a⁆⁻¹
      rw [commutatorElement_inv]
    rw [hc' 1 1 ñ, mul_inv_cancel_right] at h
    have haa : c a a = c 1 1 := by
      have ha' : a = 1 ∨ a = -1 := by
        have : (a - 1) * (a + 1) = 0 := by linear_combination ha
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h)
      rcases ha' with rfl | rfl
      · rfl
      · rw [hneg1, hneg2, inv_inv]
    calc c 1 1 = (c a a)⁻¹ := h
      _ = (c 1 1)⁻¹ := by rw [haa]
  have hcube : c 1 1 * c 1 1 * c 1 1 = 1 := by
    rw [← hadd1, ← hadd1, show (1 : k) + 1 + 1 = 3 by norm_num, WeylLift.three_eq_zero hk, hc0]
  have hone : c 1 1 = 1 := by
    have h2 : c 1 1 * c 1 1 = 1 := by
      calc c 1 1 * c 1 1 = c 1 1 * (c 1 1)⁻¹ := by rw [← hsw]
        _ = 1 := mul_inv_cancel _
    rwa [h2, one_mul] at hcube
  have hall : c s t = 1 := by
    rcases eq_zero_or_one_or_neg_one hk s with rfl | rfl | rfl <;>
      rcases eq_zero_or_one_or_neg_one hk t with rfl | rfl | rfl <;>
      simp only [hc0, hc0', hneg1, hneg2, hone, inv_one]
  have : ⁅Y s, Y' t⁆ = 1 := hall
  rw [commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem commute_of_swap_mod (hk : Nat.card k = 3) {Y Y' : k → E}
    (hY : ∀ s t, Y (s + t) = Y s * Y t) (hY' : ∀ s t, Y' (s + t) = Y' s * Y' t)
    (hc : ∀ s t, ⁅Y s, Y' t⁆ ∈ Subgroup.center E) {ñ : E} {a : k} (ha : a * a = 1)
    (h1 : ∀ s, (Y' (a * s))⁻¹ * (ñ * Y s * ñ⁻¹) ∈ Subgroup.center E)
    (h2 : ∀ t, (Y (a * t))⁻¹ * (ñ * Y' t * ñ⁻¹) ∈ Subgroup.center E) (s t : k) :
    Y s * Y' t = Y' t * Y s := by
  have hcomm : ∀ (z : E), z ∈ Subgroup.center E → ∀ g, g * z = z * g := fun z hz g =>
    (Subgroup.mem_center_iff.1 hz) g
  set c : k → k → E := fun s t => ⁅Y s, Y' t⁆ with hcdef
  have hc' : ∀ s t g, g * c s t = c s t * g := fun s t g => hcomm _ (hc s t) g
  have hY0 : Y 0 = 1 := by
    have h := hY 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hY'0 : Y' 0 = 1 := by
    have h := hY' 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hadd1 : ∀ s s' t, c (s + s') t = c s t * c s' t := fun s s' t => by
    have e : c (s + s') t = Y s * c s' t * (Y s)⁻¹ * c s t := by
      simp only [hcdef, hY, commutatorElement_def]
      group
    rw [e, hc' s' t (Y s), mul_inv_cancel_right, hc' s t (c s' t)]
  have hadd2 : ∀ s t t', c s (t + t') = c s t * c s t' := fun s t t' => by
    have e : c s (t + t') = c s t * (Y' t * c s t' * (Y' t)⁻¹) := by
      simp only [hcdef, hY', commutatorElement_def]
      group
    rw [e, hc' s t' (Y' t), mul_inv_cancel_right]
  have hc0 : ∀ t, c 0 t = 1 := fun t => by
    simp only [hcdef, hY0, commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
  have hc0' : ∀ s, c s 0 = 1 := fun s => by
    simp only [hcdef, hY'0, commutatorElement_def, inv_one, mul_one, mul_inv_cancel]
  have hneg1 : ∀ t, c (-1) t = (c 1 t)⁻¹ := fun t => by
    have h := hadd1 1 (-1) t
    rw [add_neg_cancel, hc0] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hneg2 : ∀ s, c s (-1) = (c s 1)⁻¹ := fun s => by
    have h := hadd2 s 1 (-1)
    rw [add_neg_cancel, hc0'] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hsw : c 1 1 = (c 1 1)⁻¹ := by
    have e1 : ñ * Y 1 * ñ⁻¹ = Y' (a * 1) * ((Y' (a * 1))⁻¹ * (ñ * Y 1 * ñ⁻¹)) := by group
    have e2 : ñ * Y' 1 * ñ⁻¹ = Y (a * 1) * ((Y (a * 1))⁻¹ * (ñ * Y' 1 * ñ⁻¹)) := by group
    have h : ñ * c 1 1 * ñ⁻¹ = (c a a)⁻¹ := by
      have e : ñ * c 1 1 * ñ⁻¹ = ⁅ñ * Y 1 * ñ⁻¹, ñ * Y' 1 * ñ⁻¹⁆ := by
        simp only [hcdef, commutatorElement_def]
        group
      rw [e, e1, e2, TorusLift.commutatorElement_mul_central_left (h1 1),
        TorusLift.commutatorElement_mul_central_right (h2 1), mul_one]
      show ⁅Y' a, Y a⁆ = ⁅Y a, Y' a⁆⁻¹
      rw [commutatorElement_inv]
    rw [hc' 1 1 ñ, mul_inv_cancel_right] at h
    have haa : c a a = c 1 1 := by
      have ha' : a = 1 ∨ a = -1 := by
        have : (a - 1) * (a + 1) = 0 := by linear_combination ha
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h)
      rcases ha' with rfl | rfl
      · rfl
      · rw [hneg1, hneg2, inv_inv]
    calc c 1 1 = (c a a)⁻¹ := h
      _ = (c 1 1)⁻¹ := by rw [haa]
  have hcube : c 1 1 * c 1 1 * c 1 1 = 1 := by
    rw [← hadd1, ← hadd1, show (1 : k) + 1 + 1 = 3 by norm_num, WeylLift.three_eq_zero hk, hc0]
  have hone : c 1 1 = 1 := by
    have h2 : c 1 1 * c 1 1 = 1 := by
      calc c 1 1 * c 1 1 = c 1 1 * (c 1 1)⁻¹ := by rw [← hsw]
        _ = 1 := mul_inv_cancel _
    rwa [h2, one_mul] at hcube
  have hall : c s t = 1 := by
    rcases eq_zero_or_one_or_neg_one hk s with rfl | rfl | rfl <;>
      rcases eq_zero_or_one_or_neg_one hk t with rfl | rfl | rfl <;>
      simp only [hc0, hc0', hneg1, hneg2, hone, inv_one]
  have : ⁅Y s, Y' t⁆ = 1 := hall
  rw [commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem commute_of_swap_lift (hk : Nat.card k = 3) {G : Type*} [Group G] {π : E →* G}
    (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π) {x x₁ : k → G}
    {Y Y₁ : k → E} (hY : ∀ s t, Y (s + t) = Y s * Y t) (hY₁ : ∀ s t, Y₁ (s + t) = Y₁ s * Y₁ t)
    (hπY : ∀ s, π (Y s) = x s) (hπY₁ : ∀ s, π (Y₁ s) = x₁ s)
    (hxx : ∀ s t, x s * x₁ t = x₁ t * x s) {g : G} {a : k} (ha : a * a = 1)
    (h1 : ∀ s, g * x s * g⁻¹ = x₁ (a * s)) (h2 : ∀ t, g * x₁ t * g⁻¹ = x (a * t)) (s t : k) :
    Y s * Y₁ t = Y₁ t * Y s := by
  obtain ⟨ñ, hñ⟩ := hπ g
  refine commute_of_swap_mod hk hY hY₁ (fun s t => hcen ?_) (ñ := ñ) ha (fun s => hcen ?_)
    (fun t => hcen ?_) s t
  · rw [MonoidHom.mem_ker, map_commutatorElement, hπY, hπY₁, commutatorElement_eq_one_iff_mul_comm]
    exact hxx s t
  · rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hπY, hπY₁, hñ, h1,
      inv_mul_cancel]
  · rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hπY, hπY₁, hñ, h2,
      inv_mul_cancel]

theorem commute_of_conj_lift {G : Type*} [Group G] {π : E →* G}
    (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π) {x x₁ x₂ x₃ : k → G}
    {Y Y₁ Y₂ Y₃ : k → E} (hπY : ∀ s, π (Y s) = x s) (hπY₁ : ∀ s, π (Y₁ s) = x₁ s)
    (hπY₂ : ∀ s, π (Y₂ s) = x₂ s) (hπY₃ : ∀ s, π (Y₃ s) = x₃ s)
    (hYY : ∀ s t, Y s * Y₁ t = Y₁ t * Y s) {g : G} {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : ∀ s, g * x s * g⁻¹ = x₂ (a * s)) (h2 : ∀ t, g * x₁ t * g⁻¹ = x₃ (b * t)) (s t : k) :
    Y₂ s * Y₃ t = Y₃ t * Y₂ s := by
  obtain ⟨ñ, hñ⟩ := hπ g
  have hz1 : (Y₂ s)⁻¹ * (ñ * Y (a⁻¹ * s) * ñ⁻¹) ∈ Subgroup.center E := hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hπY, hπY₂, hñ, h1,
      ← mul_assoc, mul_inv_cancel₀ ha, one_mul, inv_mul_cancel])
  have hz2 : (Y₃ t)⁻¹ * (ñ * Y₁ (b⁻¹ * t) * ñ⁻¹) ∈ Subgroup.center E := hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hπY₁, hπY₃, hñ, h2,
      ← mul_assoc, mul_inv_cancel₀ hb, one_mul, inv_mul_cancel])
  have h := hYY (a⁻¹ * s) (b⁻¹ * t)
  have hc : ⁅ñ * Y (a⁻¹ * s) * ñ⁻¹, ñ * Y₁ (b⁻¹ * t) * ñ⁻¹⁆ = 1 := by
    have e : ⁅ñ * Y (a⁻¹ * s) * ñ⁻¹, ñ * Y₁ (b⁻¹ * t) * ñ⁻¹⁆ =
        ñ * ⁅Y (a⁻¹ * s), Y₁ (b⁻¹ * t)⁆ * ñ⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, (commutatorElement_eq_one_iff_mul_comm).2 h, mul_one, mul_inv_cancel]
  have e1 : ñ * Y (a⁻¹ * s) * ñ⁻¹ = Y₂ s * ((Y₂ s)⁻¹ * (ñ * Y (a⁻¹ * s) * ñ⁻¹)) := by group
  have e2 : ñ * Y₁ (b⁻¹ * t) * ñ⁻¹ = Y₃ t * ((Y₃ t)⁻¹ * (ñ * Y₁ (b⁻¹ * t) * ñ⁻¹)) := by group
  rw [e1, e2, TorusLift.commutatorElement_mul_central_left hz1,
    TorusLift.commutatorElement_mul_central_right hz2, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

end Swap

inductive Reach (τ : Tag) : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Prop
  | single {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : Fin τ.rank) (heven : Even (cartanCoord γ j))
      (hc : ∀ p : ℕ × ℕ, 0 < p.1 → 0 < p.2 → ¬IsRoot τ (p.1 • γ + p.2 • reflect τ j γ)) :
      Reach τ γ (reflect τ j γ)
  | swap {γ δ : Fin τ.rank → ℤ} : Reach τ γ δ → Reach τ δ γ
  | step {γ δ : Fin τ.rank → ℤ} (i : Fin τ.rank) :
      Reach τ γ δ → Reach τ (reflect τ i γ) (reflect τ i δ)

theorem Reach.isRoot {γ δ : Fin τ.rank → ℤ} (h : Reach τ γ δ) : IsRoot τ γ ∧ IsRoot τ δ := by
  induction h with
  | single hγ j _ _ => exact ⟨hγ, .reflect j hγ⟩
  | swap _ ih => exact ⟨ih.2, ih.1⟩
  | step i _ ih => exact ⟨.reflect i ih.1, .reflect i ih.2⟩

@[expose] def reflectPath (τ : Tag) : List (Fin τ.rank) → (Fin τ.rank → ℤ) → Fin τ.rank → ℤ
  | [], v => v
  | i :: l, v => reflectPath τ l (reflect τ i v)

theorem Reach.path {γ δ : Fin τ.rank → ℤ} (h : Reach τ γ δ) (l : List (Fin τ.rank)) :
    Reach τ (reflectPath τ l γ) (reflectPath τ l δ) := by
  induction l generalizing γ δ with
  | nil => exact h
  | cons i l ih => exact ih (h.step i)

section Reach

variable {G : Type*} [Group G] {hA : TauCeti.IsFiniteType τ.cartan}
  {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k] [Finite k] {x : (Fin τ.rank → ℤ) → k → G}
  {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ} {O : CommOrder (RootSystem.ofCartan hA ∅)}
  (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
  (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O) (T : (Fin τ.rank → kˣ) →* G)
  (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
    T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
  {E : Type*} [Group E] {π : E →* G} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π)

omit [Finite k] in
include hroots hE in
theorem commute_x_of_not_isRoot {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hc : ∀ p : ℕ × ℕ, 0 < p.1 → 0 < p.2 → ¬IsRoot τ (p.1 • γ + p.2 • δ)) (s t : k) :
    ⁅x γ s, x δ t⁆ = 1 := by
  have hγδ : γ + δ ≠ 0 := fun h => by
    have hδ' : δ = -γ := eq_neg_of_add_eq_zero_right h
    apply hc (2, 1) (by norm_num) (by norm_num)
    have e : (2 : ℕ) • γ + (1 : ℕ) • δ = γ := by
      rw [hδ', two_nsmul, one_nsmul]
      abel
    rw [e]
    exact hγ
  rw [hE.comm γ (mem_roots hroots hγ) δ (mem_roots hroots hδ) hγδ s t]
  have hnil : O.list γ δ = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
    obtain ⟨hp1, hp2, hr⟩ :=
      (O.mem_iff γ (mem_roots hroots hγ) δ (mem_roots hroots hδ) hγδ p).1 hp
    have hr' : p.1 • γ + p.2 • δ ∈ (tagDatum τ hA RG).roots := hr
    rw [hroots] at hr'
    exact hc p hp1 hp2 hr'
  rw [hnil, List.map_nil, List.prod_nil]

include hroots hE hT hcen hπ in
theorem commute_X_of_reach (hk : Nat.card k = 3)
    (hnT : ∀ i t, ∃ t', weylElement x i 1 * T t * (weylElement x i 1)⁻¹ = T t')
    {Xf : (Fin τ.rank → ℤ) → k → E} (hlift : ∀ γ, IsRoot τ γ → IsRootLift x T π γ (Xf γ))
    (hsc : ∀ γ, IsRoot τ γ → ∃ t, rootChar k γ t ≠ 1) {γ δ : Fin τ.rank → ℤ}
    (h : Reach τ γ δ) : ∀ s t, Xf γ s * Xf δ t = Xf δ t * Xf γ s := by
  induction h with
  | @single γ hγ j heven hc =>
    intro s t
    have hδ : IsRoot τ (reflect τ j γ) := .reflect j hγ
    obtain ⟨ε, hε, hw1, hw2⟩ := weyl_conj_root hroots hE j hγ
    have hν : (((-1 : kˣ) ^ (-cartanCoord γ j) : kˣ) : k) = 1 := by
      rw [Even.neg_one_zpow (even_neg.2 heven), Units.val_one]
    obtain ⟨ñ, hñ⟩ := hπ (weylElement x j 1)
    obtain ⟨t₁, ht₁⟩ := hsc γ hγ
    obtain ⟨t₂, ht₂⟩ := hsc _ hδ
    have h1 := conj_isRootLift hroots hE T hT hcen hπ hδ (hlift γ hγ) (hlift _ hδ) hε hw1
      (hnT j) ht₁ hñ
    have h2 := conj_isRootLift hroots hE T hT hcen hπ hγ (hlift _ hδ) (hlift γ hγ) hε
      (fun u => by rw [hw2, hν, mul_one]) (hnT j) ht₂ hñ
    refine commute_of_swap hk (hlift γ hγ).1 (hlift _ hδ).1 (fun s t => hcen ?_) hε h1 h2 s t
    rw [MonoidHom.mem_ker, map_commutatorElement, (hlift γ hγ).2.1, (hlift _ hδ).2.1]
    exact commute_x_of_not_isRoot hroots hE hγ hδ hc s t
  | swap _ ih =>
    intro s t
    exact (ih t s).symm
  | @step γ δ i h ih =>
    intro s t
    obtain ⟨hγ, hδ⟩ := h.isRoot
    obtain ⟨εγ, hεγ, hγ1, -⟩ := weyl_conj_root hroots hE i hγ
    obtain ⟨εδ, hεδ, hδ1, -⟩ := weyl_conj_root hroots hE i hδ
    obtain ⟨ñ, hñ⟩ := hπ (weylElement x i 1)
    obtain ⟨t₁, ht₁⟩ := hsc γ hγ
    obtain ⟨t₂, ht₂⟩ := hsc δ hδ
    have hγ' := conj_isRootLift hroots hE T hT hcen hπ (.reflect i hγ) (hlift γ hγ)
      (hlift _ (.reflect i hγ)) hεγ hγ1 (hnT i) ht₁ hñ (εγ * s)
    have hδ' := conj_isRootLift hroots hE T hT hcen hπ (.reflect i hδ) (hlift δ hδ)
      (hlift _ (.reflect i hδ)) hεδ hδ1 (hnT i) ht₂ hñ (εδ * t)
    rw [← mul_assoc, hεγ, one_mul] at hγ'
    rw [← mul_assoc, hεδ, one_mul] at hδ'
    rw [← hγ', ← hδ']
    have := ih (εγ * s) (εδ * t)
    calc ñ * Xf γ (εγ * s) * ñ⁻¹ * (ñ * Xf δ (εδ * t) * ñ⁻¹) =
        ñ * (Xf γ (εγ * s) * Xf δ (εδ * t)) * ñ⁻¹ := by group
      _ = ñ * (Xf δ (εδ * t) * Xf γ (εγ * s)) * ñ⁻¹ := by rw [this]
      _ = ñ * Xf δ (εδ * t) * ñ⁻¹ * (ñ * Xf γ (εγ * s) * ñ⁻¹) := by group

end Reach

theorem exists_section_of_torus_three {G : Type*} [Group G]
    (hA : TauCeti.IsFiniteType τ.cartan) {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 3)
    {x : (Fin τ.rank → ℤ) → k → G} {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan hA ∅)}
    (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
    (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan hA ∅) x) (T : (Fin τ.rank → kˣ) →* G)
    (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
      T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
    (hprim : ∀ γ, IsRoot τ γ → ∃ m : Fin τ.rank → ℤ, ∑ j, m j * cartanCoord γ j = 1)
    (hnT : ∀ i t, ∃ t', weylElement x i 1 * T t * (weylElement x i 1)⁻¹ = T t')
    (hsep : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → LinIndepPair γ δ →
      (∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1) ∨ Reach τ γ δ)
    {E : Type*} [Group E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : G →* E, ∀ g, π (σ g) = g := by
  have hmem : ∀ {γ}, γ ∈ (tagDatum τ hA RG).roots → IsRoot τ γ := fun {γ} hγ => by
    rw [hroots] at hγ
    exact hγ
  have hx : ∀ γ, IsRoot τ γ → ∀ c d, x γ (c + d) = x γ c * x γ d := fun γ hγ =>
    x_add hroots hE hγ
  have hw1 : (-1 : kˣ) ≠ 1 := FieldThree.neg_one_ne_one_of_card_three hk
  have hk4 : Nat.card k ≠ 4 := by omega
  have hspec : ∀ γ, IsRoot τ γ → IsRootLift x T π γ (X x T π γ) := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ hγ
    exact X_isRootLift T (exists_isRootLift hx T hT hcen hπ hk4 hγ hm hw1)
  have hsc : ∀ γ, IsRoot τ γ → ∃ t, rootChar k γ t ≠ 1 := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ hγ
    exact ⟨tvec (-1) m, by rw [rootChar_tvec, hm, zpow_one]; exact hw1⟩
  refine HalfSpaceLift.exists_section_of_lift' hcen rfl hE hP (X := X x T π)
    (tor := fun t : Fin τ.rank → kˣ => TorusLift.lift hπ (T t))
    (χ := fun t γ => (rootChar k γ t : k)) (fun γ hγ => (hspec γ (hmem hγ)).1)
    (fun γ hγ => (hspec γ (hmem hγ)).2.1)
    (fun t γ hγ c => (hspec γ (hmem hγ)).2.2 t _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  rcases hsep γ δ (hmem hγ) (hmem hδ) hli with ⟨t, h1, h2⟩ | hr
  · exact Or.inl ⟨t, by rw [h1, Units.val_one], fun h => h2 (Units.val_eq_one.1 h)⟩
  · refine Or.inr fun s c => ?_
    have hc := commute_X_of_reach hroots hE T hT hcen hπ hk hnT hspec hsc hr s c
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
      (CFSG.LieType.Steinberg.xh_mem_chevRoot δ c))

theorem rootChar_reflect {k : Type} [Field k] (i : Fin τ.rank) (β : Fin τ.rank → ℤ)
    (t : Fin τ.rank → kˣ) :
    rootChar k (reflect τ i β) t =
      rootChar k β (t * Pi.mulSingle i (∏ l, t l ^ (-τ.cartan l i))) := by
  rw [map_mul, rootChar_mulSingle, rootChar_apply, rootChar_apply, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [cartanCoord_reflect, ← zpow_mul, ← zpow_add]
  congr 1
  ring

theorem weyl_conj_torus {G : Type*} [Group G]
    {hA : TauCeti.IsFiniteType τ.cartan}
    {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k] {x : (Fin τ.rank → ℤ) → k → G}
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ} {O : CommOrder (RootSystem.ofCartan hA ∅)}
    (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
    (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan hA ∅) x) (T : (Fin τ.rank → kˣ) →* G)
    (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
      T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
    (hZ : Subgroup.center G = ⊥) (i : Fin τ.rank) (t : Fin τ.rank → kˣ) :
    ∃ t', weylElement x i 1 * T t * (weylElement x i 1)⁻¹ = T t' := by
  set w := weylElement x i 1 with hw
  set t' := t * Pi.mulSingle i (∏ l, t l ^ (-τ.cartan l i)) with ht'
  refine ⟨t', ?_⟩
  set z := w * T t * w⁻¹ * (T t')⁻¹ with hz
  have hzx : ∀ γ, IsRoot τ γ → ∀ c, z * x γ c * z⁻¹ = x γ c := fun γ hγ c => by
    have hβ : IsRoot τ (reflect τ i γ) := .reflect i hγ
    obtain ⟨ε, hε, hw1, -⟩ := weyl_conj_root hroots hE i hβ
    rw [reflect_reflect] at hw1
    have hχ : rootChar k γ t' = rootChar k (reflect τ i γ) t := (rootChar_reflect i γ t).symm
    have h2 : ∀ c', w * T t * w⁻¹ * x γ c' * (w * T t * w⁻¹)⁻¹ =
        x γ ((rootChar k (reflect τ i γ) t : k) * c') := fun c' => by
      have hinv' : w⁻¹ * x γ c' * w = x (reflect τ i γ) (ε * c') := by
        have := hw1 (ε * c')
        rw [← mul_assoc, hε, one_mul, ← hw] at this
        rw [← this]
        group
      have e : w * T t * w⁻¹ * x γ c' * (w * T t * w⁻¹)⁻¹ =
          w * (T t * (w⁻¹ * x γ c' * w) * (T t)⁻¹) * w⁻¹ := by group
      rw [e, hinv', hT t _ hβ, hw, hw1, ← mul_assoc, mul_comm ε, mul_assoc, ← mul_assoc ε, hε,
        one_mul]
    have h3 : (T t')⁻¹ * x γ c * T t' = x γ ((((rootChar k γ t')⁻¹ : kˣ) : k) * c) := by
      have := hT t'⁻¹ γ hγ c
      rw [map_inv, inv_inv, map_inv] at this
      exact this
    have e : z * x γ c * z⁻¹ = (w * T t * w⁻¹) * ((T t')⁻¹ * x γ c * T t') *
        (w * T t * w⁻¹)⁻¹ := by
      rw [hz]
      group
    rw [e, h3, h2, hχ, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure (⋃ γ ∈ (RootSystem.ofCartan hA ∅).roots, Set.range (x γ)) := by
      rw [RankTwo.closure_range_eq_top_of_presentationB hP O]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_iUnion, Set.mem_range] at hg
      obtain ⟨γ, hγ, c, rfl⟩ := hg
      have hγ' : IsRoot τ γ := by
        have : γ ∈ (tagDatum τ hA RG).roots := hγ
        rw [hroots] at this
        exact this
      have := hzx γ hγ' c
      calc x γ c * z = z * (z⁻¹ * x γ c * z) := by group
        _ = z * x γ c := by
          congr 1
          calc z⁻¹ * x γ c * z = z⁻¹ * (z * x γ c * z⁻¹) * z := by rw [this]
            _ = x γ c := by group
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      calc a⁻¹ * z = a⁻¹ * (z * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * z) * a⁻¹ := by rw [ha]
        _ = z * a⁻¹ := by group
  rw [hZ, Subgroup.mem_bot, hz] at hzc
  exact mul_inv_eq_one.1 hzc

end CFSG.LieType.Steinberg.CentralExt.WeylLift
