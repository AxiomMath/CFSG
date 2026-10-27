module

public import CFSG.GH74.GLS.Stage4.T2P56Syl
public import CFSG.GH74.GLS.Bg.TwoGroups.L26Abel
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SwapExtension

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Aux

variable {Y : Type*} [Group Y]

theorem exists_invol_pow {x : Y} (hx2 : TwoElt x) (hx1 : x ≠ 1) :
    ∃ n : ℕ, x ^ n * x ^ n = 1 ∧ x ^ n ≠ 1 := by
  obtain ⟨k, hk⟩ := hx2
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have hord : orderOf (x ^ 2 ^ (j - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact Nat.pow_dvd_pow 2 (by omega)), hj,
      Nat.pow_div (by omega) (by norm_num)]
    have : j - (j - 1) = 1 := by omega
    rw [this]
  refine ⟨2 ^ (j - 1), ?_, ?_⟩
  · have h := pow_orderOf_eq_one (x ^ 2 ^ (j - 1))
    rwa [hord, pow_two] at h
  · intro h
    rw [h, orderOf_one] at hord
    omega

def twistedSub (T : Subgroup Y) (w : Y) (hwT : ∀ x ∈ T, w * x * w⁻¹ ∈ T) (hw2 : w * w ∈ T) :
    Subgroup Y where
  carrier := {x | x ∈ T ∨ ∃ t ∈ T, x = t * w}
  one_mem' := Or.inl T.one_mem
  mul_mem' := by
    rintro x y (hx | ⟨t₁, ht₁, rfl⟩) (hy | ⟨t₂, ht₂, rfl⟩)
    · exact Or.inl (T.mul_mem hx hy)
    · exact Or.inr ⟨x * t₂, T.mul_mem hx ht₂, by group⟩
    · refine Or.inr ⟨t₁ * (w * y * w⁻¹), T.mul_mem ht₁ (hwT y hy), by group⟩
    · refine Or.inl ?_
      have : t₁ * w * (t₂ * w) = t₁ * (w * t₂ * w⁻¹) * (w * w) := by group
      rw [this]
      exact T.mul_mem (T.mul_mem ht₁ (hwT t₂ ht₂)) hw2
  inv_mem' := by
    rintro x (hx | ⟨t, ht, rfl⟩)
    · exact Or.inl (T.inv_mem hx)
    · refine Or.inr ⟨(w * w)⁻¹ * (w * t⁻¹ * w⁻¹), T.mul_mem (T.inv_mem hw2)
        (hwT _ (T.inv_mem ht)), ?_⟩
      group

end Aux

section Action

variable {Y : Type} [Group Y] [Finite Y]

theorem not_trivial_action_absurd (T : Subgroup Y) (a w h : Y)
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT2 : ∀ x ∈ T, TwoElt x)
    (haT : ∀ x ∈ T, a * x * a⁻¹ ∈ T) (haT' : ∀ x ∈ T, a⁻¹ * x * a ∈ T)
    (ha3 : ∀ x ∈ T, a ^ 3 * x = x * a ^ 3) (hfix : ∀ x ∈ T, a * x * a⁻¹ = x → x = 1)
    (hwT : ∀ x ∈ T, w * x * w⁻¹ ∈ T) (hh : ∀ x ∈ T, h * x = x * h) (hwa : w * a * w⁻¹ = a⁻¹ * h)
    (hT1 : ∃ x ∈ T, x ≠ 1)
    (hstar : ∀ x ∈ T, ∃ r ∈ T, w * x * w⁻¹ = x * r ^ 2) : False := by
  let Cg : Y → Y → Prop := fun x y => ∃ s ∈ T, x = y * s ^ 2
  have Cg_symm : ∀ x y, Cg x y → Cg y x := by
    rintro x y ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, T.inv_mem hs, by rw [inv_pow]; group⟩
  have Cg_trans : ∀ x y v, Cg x y → Cg y v → Cg x v := by
    rintro x y v ⟨s, hs, rfl⟩ ⟨r, hr, rfl⟩
    refine ⟨r * s, T.mul_mem hr hs, ?_⟩
    have hc : Commute r s := hTc r hr s hs
    rw [hc.mul_pow]
    group
  have Cg_mul : ∀ x y x' y', y' ∈ T → Cg x y → Cg x' y' → Cg (x * x') (y * y') := by
    rintro x y x' y' hy' ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
    refine ⟨s * s', T.mul_mem hs hs', ?_⟩
    have hc : Commute s s' := hTc s hs s' hs'
    have hmul : (s * s') ^ 2 = s ^ 2 * s' ^ 2 := hc.mul_pow 2
    have h1 : s ^ 2 * y' = y' * s ^ 2 := hTc _ (T.pow_mem hs 2) y' hy'
    rw [hmul]
    calc y * s ^ 2 * (y' * s' ^ 2) = y * (s ^ 2 * y') * s' ^ 2 := by group
      _ = y * (y' * s ^ 2) * s' ^ 2 := by rw [h1]
      _ = y * y' * (s ^ 2 * s' ^ 2) := by group
  have Cg_conj' : ∀ x y, Cg x y → Cg (a⁻¹ * x * a) (a⁻¹ * y * a) := by
    rintro x y ⟨s, hs, rfl⟩
    exact ⟨a⁻¹ * s * a, haT' s hs, by simp only [pow_two]; group⟩
  have hα3 : ∀ x ∈ T, a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = x := by
    intro x hx
    have h3 : a * a * a * x = x * (a * a * a) := by
      have := ha3 x hx
      rwa [pow_three'] at this
    calc a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * x * (a * a * a)⁻¹ := by group
      _ = x := by rw [h3]; group
  have hstepa : ∀ x ∈ T, w * (a * x * a⁻¹) * w⁻¹ = a⁻¹ * (w * x * w⁻¹) * a := by
    intro x hx
    have hy : w * x * w⁻¹ ∈ T := hwT x hx
    have e1 : w * (a * x * a⁻¹) * w⁻¹ =
        (w * a * w⁻¹) * (w * x * w⁻¹) * (w * a * w⁻¹)⁻¹ := by group
    rw [e1, hwa]
    have e2 : a⁻¹ * h * (w * x * w⁻¹) * (a⁻¹ * h)⁻¹ = a⁻¹ * (h * (w * x * w⁻¹) * h⁻¹) * a := by
      group
    rw [e2, show h * (w * x * w⁻¹) * h⁻¹ = w * x * w⁻¹ by rw [hh _ hy]; group]
  have hstarCg : ∀ x ∈ T, Cg (w * x * w⁻¹) x := fun x hx => hstar x hx
  have hCg1 : ∀ x ∈ T, Cg (a * x * a⁻¹) (a⁻¹ * x * a) := by
    intro x hx
    have hx1 : a * x * a⁻¹ ∈ T := haT x hx
    have h1 : Cg (w * (a * x * a⁻¹) * w⁻¹) (a * x * a⁻¹) := hstarCg _ hx1
    rw [hstepa x hx] at h1
    have h2 : Cg (a⁻¹ * (w * x * w⁻¹) * a) (a⁻¹ * x * a) := Cg_conj' _ _ (hstarCg x hx)
    exact Cg_trans _ _ _ (Cg_symm _ _ h1) h2
  have hCg2 : ∀ x ∈ T, Cg x (a * x * a⁻¹) := by
    intro x hx
    have hy : a⁻¹ * x * a ∈ T := haT' x hx
    have h1 := hCg1 _ hy
    have e1 : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
    have e2 : a⁻¹ * (a⁻¹ * x * a) * a = a * x * a⁻¹ := by
      have h : a * a * a * (a * x * a⁻¹) = a * x * a⁻¹ * (a * a * a) := by
        have := ha3 (a * x * a⁻¹) (haT x hx)
        rwa [pow_three'] at this
      calc a⁻¹ * (a⁻¹ * x * a) * a = (a * a * a)⁻¹ * ((a * x * a⁻¹) * (a * a * a)) := by group
        _ = (a * a * a)⁻¹ * ((a * a * a) * (a * x * a⁻¹)) := by rw [h]
        _ = a * x * a⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have hsq : ∀ x ∈ T, ∃ r ∈ T, x = r ^ 2 := by
    intro x hx
    set y1 : Y := a * x * a⁻¹ with hy1
    set y2 : Y := a * y1 * a⁻¹ with hy2
    have hy1T : y1 ∈ T := haT x hx
    have hy2T : y2 ∈ T := haT y1 hy1T
    have c1 : Cg x y1 := hCg2 x hx
    have c2 : Cg y1 y2 := hCg2 y1 hy1T
    have cy1 : Cg y1 x := Cg_symm _ _ c1
    have cy2 : Cg y2 x := Cg_trans _ _ _ (Cg_symm _ _ c2) cy1
    have cx : Cg x x := ⟨1, T.one_mem, by simp⟩
    have hN : Cg (x * y1 * y2) (x * x * x) :=
      Cg_mul _ _ _ _ hx (Cg_mul _ _ _ _ hx cx cy1) cy2
    have hNfix : a * (x * y1 * y2) * a⁻¹ = x * y1 * y2 := by
      have e3 : a * y2 * a⁻¹ = x := hα3 x hx
      have e : a * (x * y1 * y2) * a⁻¹ = y1 * y2 * (a * y2 * a⁻¹) := by
        calc a * (x * y1 * y2) * a⁻¹ = (a * x * a⁻¹) * (a * y1 * a⁻¹) * (a * y2 * a⁻¹) := by group
          _ = y1 * y2 * (a * y2 * a⁻¹) := by rw [← hy1, ← hy2]
      rw [e, e3]
      have hc1 : x * y1 = y1 * x := hTc x hx y1 hy1T
      have hc2 : x * y2 = y2 * x := hTc x hx y2 hy2T
      have hc3 : y1 * y2 = y2 * y1 := hTc y1 hy1T y2 hy2T
      calc y1 * y2 * x = y1 * (y2 * x) := by group
        _ = y1 * (x * y2) := by rw [hc2]
        _ = (y1 * x) * y2 := by group
        _ = (x * y1) * y2 := by rw [hc1]
    have hN1 : x * y1 * y2 = 1 :=
      hfix _ (T.mul_mem (T.mul_mem hx hy1T) hy2T) hNfix
    rw [hN1] at hN
    obtain ⟨s, hs, hs1⟩ := hN
    refine ⟨x ^ 2 * s, T.mul_mem (T.pow_mem hx 2) hs, ?_⟩
    have hc : Commute (x ^ 2) s := hTc _ (T.pow_mem hx 2) s hs
    rw [hc.mul_pow]
    have : x = x * (x * x * x * s ^ 2) := by rw [← hs1, mul_one]
    calc x = x * (x * x * x * s ^ 2) := this
      _ = (x ^ 2) ^ 2 * s ^ 2 := by simp only [pow_two]; group
  obtain ⟨x₀, hx₀, hx₀1⟩ := hT1
  have : Nonempty ↥T := ⟨⟨1, T.one_mem⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun x : ↥T => orderOf (x : Y))
  have hm2 : 2 ≤ orderOf (m : Y) := by
    have h1 := hm ⟨x₀, hx₀⟩
    have h2 : 1 < orderOf x₀ := by
      rcases Nat.lt_or_ge 1 (orderOf x₀) with h | h
      · exact h
      · exfalso
        have : orderOf x₀ = 1 := by
          have := orderOf_pos x₀
          omega
        exact hx₀1 (orderOf_eq_one_iff.1 this)
    simp only at h1
    omega
  obtain ⟨r, hr, hmr⟩ := hsq m m.2
  have hrle : orderOf r ≤ orderOf (m : Y) := hm ⟨r, hr⟩
  obtain ⟨k, hk⟩ := hT2 r hr
  have hodv : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hodv
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [hmr] at hm2
    simp at hm2
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hr1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have hord : orderOf (m : Y) = orderOf r / Nat.gcd (orderOf r) 2 := by
    rw [hmr, orderOf_pow' r (by norm_num)]
  have hgcd : Nat.gcd (orderOf r) 2 = 2 := by
    rw [hj]
    have : 2 ∣ 2 ^ j := dvd_pow_self 2 hj0
    exact Nat.gcd_eq_right this
  rw [hgcd] at hord
  have hpos : 0 < orderOf r := orderOf_pos r
  omega

end Action

section Homocyclic

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem cycle_facts {z u a : Y} (hz2 : z * z = 1)
    (haz : a⁻¹ * z * a = u) (hau : a⁻¹ * u * a = z * u) :
    a * u * a⁻¹ = z ∧ a * z * a⁻¹ = u * z ∧ a * (z * u) * a⁻¹ = u := by
  have h1 : a * u * a⁻¹ = z := by
    rw [← haz]; group
  have h2 : a * (z * u) * a⁻¹ = u := by
    rw [← hau]; group
  have h3 : a * z * a⁻¹ = u * z := by
    have e : a * (z * u) * a⁻¹ = (a * z * a⁻¹) * (a * u * a⁻¹) := by group
    rw [e, h1] at h2
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    calc a * z * a⁻¹ = (a * z * a⁻¹) * z * z⁻¹ := by group
      _ = u * z⁻¹ := by rw [h2]
      _ = u * z := by rw [hz']
  exact ⟨h1, h3, h2⟩

omit [Finite Y] in
theorem fixed_point_free_of_data {T : Subgroup Y} {z u a : Y} (hT2 : ∀ x ∈ T, TwoElt x)
    (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hz1 : z ≠ 1) (hu1 : u ≠ 1)
    (hzne : z ≠ u) (hΩ : ∀ x ∈ T, x * x = 1 → x ∈ t2U z u)
    (haz : a⁻¹ * z * a = u) (hau : a⁻¹ * u * a = z * u) :
    ∀ x ∈ T, a * x * a⁻¹ = x → x = 1 := by
  intro x hx hax
  by_contra hx1
  obtain ⟨n, hn2, hn1⟩ := exists_invol_pow (hT2 x hx) hx1
  have hnT : x ^ n ∈ T := T.pow_mem hx n
  have hnfix : a * x ^ n * a⁻¹ = x ^ n := by rw [← conj_pow, hax]
  have hmem := (t2U_mem hz2 hu2 hzu).1 (hΩ _ hnT hn2)
  obtain ⟨hau', haz', hazu'⟩ := cycle_facts hz2 haz hau
  rcases hmem with h | h | h | h
  · exact hn1 h
  · rw [h, haz'] at hnfix
    exact hu1 (mul_right_cancel (hnfix.trans (one_mul z).symm))
  · rw [h, hau'] at hnfix
    exact hzne hnfix
  · rw [h, hazu'] at hnfix
    apply hz1
    have h5 : z * u = 1 * u := by rw [one_mul]; exact hnfix.symm
    exact mul_right_cancel h5

def mulProdEquiv (n : ℕ) :
    Multiplicative (ZMod n × ZMod n) ≃* Multiplicative (ZMod n) × Multiplicative (ZMod n) where
  toFun x := (Multiplicative.ofAdd (Multiplicative.toAdd x).1,
    Multiplicative.ofAdd (Multiplicative.toAdd x).2)
  invFun p := Multiplicative.ofAdd (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem homocyclic_of_data {T : Subgroup Y} {z u a : Y} (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hT2 : ∀ x ∈ T, TwoElt x) (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hzne : z ≠ u) (hzT : z ∈ T) (huT : u ∈ T)
    (hΩ : ∀ x ∈ T, x * x = 1 → x ∈ t2U z u)
    (haT : ∀ x ∈ T, a * x * a⁻¹ ∈ T) (haT' : ∀ x ∈ T, a⁻¹ * x * a ∈ T)
    (haz : a⁻¹ * z * a = u) (hau : a⁻¹ * u * a = z * u) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ x ∈ T, x ^ 2 ^ k = 1) ∧
      Nonempty (↥T ≃* Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k))) := by
  have hfix := fixed_point_free_of_data hT2 hz2 hu2 hzu hz1 hu1 hzne hΩ haz hau
  have hp : IsPGroup 2 ↥T := fun g => by
    obtain ⟨k, hk⟩ := hT2 g g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  let α : MulAut ↥T :=
    { toFun := fun x => ⟨a * x * a⁻¹, haT x x.2⟩
      invFun := fun x => ⟨a⁻¹ * x * a, haT' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hUT : t2U z u ≤ T := t2U_le_of_mem hz2 hu2 hzu hzT huT
  have hEcard : Nat.card ↥((t2U z u).subgroupOf T) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUT).toEquiv]
    exact t2U_card hz2 hu2 hzu hz1 hu1 hzne
  obtain ⟨k, a₀, hk1, -, -, ⟨φ⟩⟩ := Bg.TwoGroups.L26.homocyclic hp α (⊤ : Subgroup ↥T)
    ((t2U z u).subgroupOf T) (fun x _ y _ => Subtype.ext (hTc x x.2 y y.2))
    (fun x _ => Subgroup.mem_top _)
    (fun x _ hx => Subtype.ext (hfix x x.2 (congrArg Subtype.val hx))) le_top hEcard
    (fun e he => Subtype.ext (by
      have h := t2S_closure_sq hz2 hu2 hzu.symm (e : Y) (Subgroup.mem_subgroupOf.mp he)
      simpa using h))
    (fun x _ hx => Subgroup.mem_subgroupOf.mpr (hΩ x x.2 (by simpa using congrArg Subtype.val hx)))
  let ψ : ↥T ≃* Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k)) :=
    (Subgroup.topEquiv (G := ↥T)).symm.trans (φ.trans (mulProdEquiv _))
  have hCm : ∀ c : Multiplicative (ZMod (2 ^ k)), c ^ 2 ^ k = 1 := fun c => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨k, hk1, ?_, ⟨ψ⟩⟩
  intro x hx
  have h1 : ψ ⟨x, hx⟩ ^ 2 ^ k = 1 := Prod.ext (hCm _) (hCm _)
  have h2 : (⟨x, hx⟩ : ↥T) ^ 2 ^ k = 1 := ψ.injective (by rw [map_pow, h1, map_one])
  simpa using congrArg Subtype.val h2

end Homocyclic

section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem hasWreathedSylow_of_data {T : Subgroup Y} {z u a w h : Y}
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT2 : ∀ x ∈ T, TwoElt x)
    (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hz1 : z ≠ 1) (hu1 : u ≠ 1)
    (hzne : z ≠ u) (hzT : z ∈ T) (huT : u ∈ T)
    (hΩ : ∀ x ∈ T, x * x = 1 → x ∈ t2U z u)
    (hcent : ∀ g : Y, g * z = z * g → g * u = u * g → TwoElt g → g ∈ T)
    (hT4 : ∃ x ∈ T, x * x ≠ 1)
    (haT : ∀ x ∈ T, a * x * a⁻¹ ∈ T) (haT' : ∀ x ∈ T, a⁻¹ * x * a ∈ T)
    (ha3 : ∀ x ∈ T, a ^ 3 * x = x * a ^ 3) (haz : a⁻¹ * z * a = u) (hau : a⁻¹ * u * a = z * u)
    (hw2 : w * w = z) (hwT : ∀ x ∈ T, w * x * w⁻¹ ∈ T) (hwu : w * u * w⁻¹ = u * z)
    (hh : ∀ x ∈ T, h * x = x * h) (hwa : w * a * w⁻¹ = a⁻¹ * h) :
    ∃ S : Sylow 2 Y, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup Y) ≃* CFSG.Open.WreathedTwoGroup m) := by
  classical
  have hw2T : w * w ∈ T := hw2 ▸ hzT
  set R₀ : Subgroup Y := twistedSub T w hwT hw2T with hR₀
  have hTR : T ≤ R₀ := fun x hx => Or.inl hx
  have hwR : w ∈ R₀ := Or.inr ⟨1, T.one_mem, by simp⟩
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hwz : w * z = z * w := by
    rw [← hw2]; group
  have hwiz : w⁻¹ * z * w = z := by
    calc w⁻¹ * z * w = w⁻¹ * (z * w) := by group
      _ = w⁻¹ * (w * z) := by rw [hwz]
      _ = z := by group
  have hwzw : w * z * w⁻¹ = z := by rw [hwz]; group
  have hwzu : w * (z * u) * w⁻¹ = u := by
    calc w * (z * u) * w⁻¹ = (w * z * w⁻¹) * (w * u * w⁻¹) := by group
      _ = z * (u * z) := by rw [hwzw, hwu]
      _ = u := by
          calc z * (u * z) = (z * u) * z := by group
            _ = (u * z) * z := by rw [hzu]
            _ = u * (z * z) := by group
            _ = u := by rw [hz2, mul_one]
  have hwiu : w⁻¹ * u * w = u * z := by
    have h1 : u = (w⁻¹ * u * w) * z := by
      calc u = w⁻¹ * (w * u * w⁻¹) * w := by group
        _ = w⁻¹ * (u * z) * w := by rw [hwu]
        _ = (w⁻¹ * u * w) * (w⁻¹ * z * w) := by group
        _ = (w⁻¹ * u * w) * z := by rw [hwiz]
    calc w⁻¹ * u * w = (w⁻¹ * u * w) * (z * z) := by rw [hz2, mul_one]
      _ = ((w⁻¹ * u * w) * z) * z := by group
      _ = u * z := by rw [← h1]
  have hwT' : w ∉ T := by
    intro hw
    have h1 : u * w = w * u := hTc u huT w hw
    have e : w * u * w⁻¹ = u := by
      calc w * u * w⁻¹ = (u * w) * w⁻¹ := by rw [h1]
        _ = u := by group
    rw [e] at hwu
    exact hz1 (by
      have h5 : u * z = u * 1 := by rw [mul_one]; exact hwu.symm
      exact mul_left_cancel h5)
  have hR₀2 : ∀ x ∈ R₀, TwoElt x := by
    rintro x (hx | ⟨t, ht, rfl⟩)
    · exact hT2 x hx
    · have hsq : (t * w) * (t * w) = t * (w * t * w⁻¹) * (w * w) := by group
      have hmem : (t * w) * (t * w) ∈ T := by
        rw [hsq]; exact T.mul_mem (T.mul_mem ht (hwT t ht)) hw2T
      obtain ⟨k, hk⟩ := hT2 _ hmem
      exact ⟨k + 1, by rw [pow_succ', pow_mul, pow_two]; exact hk⟩
  have hR₀p : IsPGroup 2 ↥R₀ := fun g => by
    obtain ⟨k, hk⟩ := hR₀2 g g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨P, hRP⟩ := hR₀p.exists_le_sylow
  have hidx : (T.subgroupOf R₀).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨w, hwR⟩, ?_⟩
    rintro ⟨b, hb⟩
    rcases hb with hb | ⟨t, ht, rfl⟩
    · refine Or.inr ⟨?_, ?_⟩
      · show b ∈ T
        exact hb
      · intro hbw
        apply hwT'
        have : b⁻¹ * (b * w) ∈ T := T.mul_mem (T.inv_mem hb) hbw
        simpa using this
    · refine Or.inl ⟨?_, ?_⟩
      · show t * w * w ∈ T
        have : t * w * w = t * (w * w) := by group
        rw [this]; exact T.mul_mem ht hw2T
      · intro htw
        apply hwT'
        have : t⁻¹ * (t * w) ∈ T := T.mul_mem (T.inv_mem ht) htw
        simpa using this
  have hQn : (T.subgroupOf R₀).Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨k, hk1, hexp, ⟨ψ⟩⟩ := homocyclic_of_data hTc hT2 hz2 hu2 hzu hz1 hu1 hzne hzT huT hΩ haT haT'
    haz hau
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk' : k = 1 := by omega
    obtain ⟨x, hx, hx1⟩ := hT4
    apply hx1
    have := hexp x hx
    simpa [hk', pow_two] using this
  have hQ : Nonempty (↥(T.subgroupOf R₀) ≃*
      Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k))) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hTR).trans ψ⟩
  have htQ : (⟨w, hwR⟩ : ↥R₀) ∉ T.subgroupOf R₀ := fun hmem => hwT' hmem
  have hfix := fixed_point_free_of_data hT2 hz2 hu2 hzu hz1 hu1 hzne hΩ haz hau
  have hnontriv : ∃ q ∈ T.subgroupOf R₀, ∀ r ∈ T.subgroupOf R₀,
      (⟨w, hwR⟩ : ↥R₀) * q * (⟨w, hwR⟩ : ↥R₀)⁻¹ ≠ q * r ^ 2 := by
    by_contra hcon
    push Not at hcon
    refine not_trivial_action_absurd T a w h hTc hT2 haT haT' ha3 hfix hwT hh hwa ⟨z, hzT, hz1⟩ ?_
    intro x hx
    obtain ⟨r, hr, hreq⟩ := hcon ⟨x, hTR hx⟩ (Subgroup.mem_subgroupOf.2 hx)
    refine ⟨(r : Y), Subgroup.mem_subgroupOf.1 hr, ?_⟩
    have := congrArg Subtype.val hreq
    simpa using this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨e, -⟩, hchar⟩ :=
    CFSG.RankTwoShapes.homocyclic_swap_extension (n := k) hk1 (T.subgroupOf R₀) hQn hidx hQ
      ⟨w, hwR⟩ htQ hnontriv
  have hchar' : (T.subgroupOf R₀).Characteristic := (hchar hk2).2.2
  have hP2 : ∀ g ∈ (P : Subgroup Y), TwoElt g := fun g hg => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hEq : R₀ = (P : Subgroup Y) := by
    by_contra hne
    have hnc : NormalizerCondition ↥(P : Subgroup Y) :=
      @Group.normalizerCondition_of_isNilpotent _ _ P.isPGroup'.isNilpotent
    have hlt : R₀.subgroupOf (P : Subgroup Y) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact fun h => hne (le_antisymm hRP h)
    have h' := hnc _ hlt
    rw [← Subgroup.subgroupOf_normalizer_eq hRP] at h'
    obtain ⟨g, hgN, hgR⟩ := IsConcreteLE.exists_of_lt h'
    rw [Subgroup.mem_subgroupOf] at hgN hgR
    set g' : Y := (g : Y) with hg'
    have hgP : g' ∈ (P : Subgroup Y) := g.2
    have hnormR : ∀ r, r ∈ R₀ ↔ g' * r * g'⁻¹ ∈ R₀ := Subgroup.mem_normalizer_iff.1 hgN
    have hnormR' : ∀ r ∈ R₀, g'⁻¹ * r * g' ∈ R₀ := fun r hr =>
      (hnormR (g'⁻¹ * r * g')).2 (by rw [show g' * (g'⁻¹ * r * g') * g'⁻¹ = r by group]; exact hr)
    let φ : MulAut ↥R₀ :=
      { toFun := fun r => ⟨g' * r * g'⁻¹, (hnormR r).1 r.2⟩
        invFun := fun r => ⟨g'⁻¹ * r * g', hnormR' r r.2⟩
        left_inv := fun r => Subtype.ext (by simp [mul_assoc])
        right_inv := fun r => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun r s => Subtype.ext (by simp [mul_assoc]) }
    have hgT : ∀ x ∈ T, g' * x * g'⁻¹ ∈ T := by
      intro x hx
      have h1 := SetLike.ext_iff.mp (hchar'.fixed φ) ⟨x, hTR hx⟩
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
      exact h1.2 hx
    have hzc : ∀ r ∈ R₀, z * r = r * z := by
      rintro r (hr | ⟨t, ht, rfl⟩)
      · exact hTc z hzT r hr
      · calc z * (t * w) = (z * t) * w := by group
          _ = (t * z) * w := by rw [hTc z hzT t ht]
          _ = t * (z * w) := by group
          _ = t * (w * z) := by rw [hwz]
          _ = (t * w) * z := by group
    have hgzc : ∀ r ∈ R₀, (g' * z * g'⁻¹) * r = r * (g' * z * g'⁻¹) := by
      intro r hr
      have h1 := hzc _ (hnormR' r hr)
      calc (g' * z * g'⁻¹) * r = g' * (z * (g'⁻¹ * r * g')) * g'⁻¹ := by group
        _ = g' * ((g'⁻¹ * r * g') * z) * g'⁻¹ := by rw [h1]
        _ = r * (g' * z * g'⁻¹) := by group
    have hgzT : g' * z * g'⁻¹ ∈ T := hgT z hzT
    have hgzsq : (g' * z * g'⁻¹) * (g' * z * g'⁻¹) = 1 := by
      calc (g' * z * g'⁻¹) * (g' * z * g'⁻¹) = g' * (z * z) * g'⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    have hgz : g' * z * g'⁻¹ = z := by
      rcases (t2U_mem hz2 hu2 hzu).1 (hΩ _ hgzT hgzsq) with h1 | h1 | h1 | h1
      · exfalso; apply hz1
        have : z = g'⁻¹ * (g' * z * g'⁻¹) * g' := by group
        rw [this, h1]; group
      · exact h1
      · exfalso
        have h2 := hgzc w hwR
        rw [h1] at h2
        have e : w * u * w⁻¹ = u := by
          calc w * u * w⁻¹ = (u * w) * w⁻¹ := by rw [h2]
            _ = u := by group
        rw [e] at hwu
        exact hz1 (by
          have h5 : u * z = u * 1 := by rw [mul_one]; exact hwu.symm
          exact mul_left_cancel h5)
      · exfalso
        have h2 := hgzc w hwR
        rw [h1] at h2
        have e : w * (z * u) * w⁻¹ = z * u := by
          calc w * (z * u) * w⁻¹ = ((z * u) * w) * w⁻¹ := by rw [h2]
            _ = z * u := by group
        rw [hwzu] at e
        exact hz1 (by
          have h5 : z * u = 1 * u := by rw [one_mul]; exact e.symm
          exact mul_right_cancel h5)
    have hguT : g' * u * g'⁻¹ ∈ T := hgT u huT
    have hgusq : (g' * u * g'⁻¹) * (g' * u * g'⁻¹) = 1 := by
      calc (g' * u * g'⁻¹) * (g' * u * g'⁻¹) = g' * (u * u) * g'⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hgu : g' * u * g'⁻¹ = u ∨ g' * u * g'⁻¹ = z * u := by
      rcases (t2U_mem hz2 hu2 hzu).1 (hΩ _ hguT hgusq) with h1 | h1 | h1 | h1
      · exfalso; apply hu1
        have : u = g'⁻¹ * (g' * u * g'⁻¹) * g' := by group
        rw [this, h1]; group
      · exfalso
        have e1 : u = g'⁻¹ * z * g' := by
          calc u = g'⁻¹ * (g' * u * g'⁻¹) * g' := by group
            _ = g'⁻¹ * z * g' := by rw [h1]
        have e2 : z = g'⁻¹ * z * g' := by
          calc z = g'⁻¹ * (g' * z * g'⁻¹) * g' := by group
            _ = g'⁻¹ * z * g' := by rw [hgz]
        exact hzne (e2.trans e1.symm)
      · exact Or.inl h1
      · exact Or.inr h1
    have hcomm_of_conj : ∀ x y : Y, x * y * x⁻¹ = y → x * y = y * x := by
      intro x y hxy
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [hxy]
    have hgz' : g' * z = z * g' := hcomm_of_conj _ _ hgz
    rcases hgu with hgu | hgu
    · exact hgR (hTR (hcent g' hgz' (hcomm_of_conj _ _ hgu) (hP2 g' hgP)))
    · set g'' : Y := w⁻¹ * g' with hg''
      have hwP : w ∈ (P : Subgroup Y) := hRP hwR
      have hg''P : g'' ∈ (P : Subgroup Y) := (P : Subgroup Y).mul_mem ((P : Subgroup Y).inv_mem hwP) hgP
      have hg''z : g'' * z * g''⁻¹ = z := by
        calc g'' * z * g''⁻¹ = w⁻¹ * (g' * z * g'⁻¹) * w := by rw [hg'']; group
          _ = w⁻¹ * z * w := by rw [hgz]
          _ = z := hwiz
      have hg''u : g'' * u * g''⁻¹ = u := by
        calc g'' * u * g''⁻¹ = w⁻¹ * (g' * u * g'⁻¹) * w := by rw [hg'']; group
          _ = w⁻¹ * (z * u) * w := by rw [hgu]
          _ = z * (w⁻¹ * u * w) := by
              calc w⁻¹ * (z * u) * w = (w⁻¹ * z * w) * (w⁻¹ * u * w) := by group
                _ = z * (w⁻¹ * u * w) := by rw [hwiz]
          _ = z * (u * z) := by rw [hwiu]
          _ = u := by
              calc z * (u * z) = (z * u) * z := by group
                _ = (u * z) * z := by rw [hzu]
                _ = u * (z * z) := by group
                _ = u := by rw [hz2, mul_one]
      have hg''T : g'' ∈ T :=
        hcent g'' (hcomm_of_conj _ _ hg''z) (hcomm_of_conj _ _ hg''u) (hP2 g'' hg''P)
      apply hgR
      have : g' = w * g'' := by rw [hg'']; group
      rw [this]
      exact R₀.mul_mem hwR (hTR hg''T)
  exact ⟨P, k, hk2, ⟨(MulEquiv.subgroupCongr hEq.symm).trans e⟩⟩

end Main

end CFSG.GH74.GLS.Stage4.Rest
