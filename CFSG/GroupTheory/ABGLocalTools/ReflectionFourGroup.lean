module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.ABGLocalTools

private theorem rfg_scalar_of_card_le {G : Type*} [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : Subgroup G} (hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hPr : ∀ x ∈ P, x ^ r = 1) (hPcard : Nat.card P ≤ r) {b : G}
    (hbP : ∀ x ∈ P, b * x * b⁻¹ ∈ P) (hb2 : ∀ x ∈ P, b * (b * x * b⁻¹) * b⁻¹ = x) :
    (∀ x ∈ P, b * x * b⁻¹ = x) ∨ (∀ x ∈ P, b * x * b⁻¹ = x⁻¹) := by
  have : Fact r.Prime := ⟨hr⟩
  by_cases hfix : ∃ x ∈ P, x ≠ 1 ∧ b * x * b⁻¹ = x
  · left
    obtain ⟨x, hxP, hx1, hbx⟩ := hfix
    have hox : orderOf x = r := orderOf_eq_prime (hPr x hxP) hx1
    have hzp : Subgroup.zpowers x = P := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP)
      rw [Nat.card_zpowers, hox]
      exact hPcard
    intro y hy
    rw [← hzp] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hbx]
  · right
    intro y hy
    have hu : y * (b * y * b⁻¹) ∈ P := P.mul_mem hy (hbP y hy)
    have hfu : b * (y * (b * y * b⁻¹)) * b⁻¹ = y * (b * y * b⁻¹) := by
      have h1 : b * (y * (b * y * b⁻¹)) * b⁻¹ = (b * y * b⁻¹) * (b * (b * y * b⁻¹) * b⁻¹) := by
        group
      rw [h1, hb2 y hy]
      exact hPab _ (hbP y hy) _ hy
    have hu1 : y * (b * y * b⁻¹) = 1 := by
      by_contra hne
      exact hfix ⟨_, hu, hne, hfu⟩
    exact eq_inv_of_mul_eq_one_right hu1

theorem exists_scalar_of_reflection_four_group {G : Type*} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {W : Subgroup G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWr : ∀ w ∈ W, w ^ r = 1) {a b : G}
    (ha : a ∈ Subgroup.normalizer (W : Set G)) (hb : b ∈ Subgroup.normalizer (W : Set G))
    (ha2 : a * a = 1) (hb2 : b * b ∈ Subgroup.centralizer (W : Set G))
    (hab : a * b * a⁻¹ * b ∈ Subgroup.centralizer (W : Set G))
    (hrefl : (W ⊓ Subgroup.centralizer {a}).relIndex W = r) (hcard : Nat.card W ≤ r ^ 2) :
    ∃ y ∈ ({a, b, a * b} : Set G), (∀ w ∈ W, y * w * y⁻¹ = w) ∨ (∀ w ∈ W, y * w * y⁻¹ = w⁻¹) := by
  have haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun w hw => (Subgroup.mem_normalizer_iff.mp ha w).mp hw
  have hbW : ∀ w ∈ W, b * w * b⁻¹ ∈ W := fun w hw => (Subgroup.mem_normalizer_iff.mp hb w).mp hw
  have hbW' : ∀ w ∈ W, b⁻¹ * w * b ∈ W := by
    intro w hw
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) w).mp hw
    rwa [inv_inv] at h
  have haa : ∀ w : G, a * (a * w * a⁻¹) * a⁻¹ = w := by
    intro w
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hainv]
    calc a * (a * w * a) * a = (a * a) * w * (a * a) := by group
      _ = w := by rw [ha2, one_mul, mul_one]
  have hbb : ∀ w ∈ W, b * (b * w * b⁻¹) * b⁻¹ = w := by
    intro w hw
    have h := Subgroup.mem_centralizer_iff.mp hb2 w hw
    calc b * (b * w * b⁻¹) * b⁻¹ = (w * (b * b)) * (b * b)⁻¹ := by rw [h]; group
      _ = w := by group
  have hbinv : ∀ w ∈ W, b⁻¹ * w * b = b * w * b⁻¹ := by
    intro w hw
    have h := Subgroup.mem_centralizer_iff.mp hb2 w hw
    calc b⁻¹ * w * b = b⁻¹ * (w * (b * b)) * b⁻¹ := by group
      _ = b⁻¹ * ((b * b) * w) * b⁻¹ := by rw [h]
      _ = b * w * b⁻¹ := by group
  have hab' : ∀ w ∈ W, a * (b * w * b⁻¹) * a⁻¹ = b * (a * w * a⁻¹) * b⁻¹ := by
    intro w hw
    have h := Subgroup.mem_centralizer_iff.mp hab _ (hbW' _ (haW w hw))
    calc a * (b * w * b⁻¹) * a⁻¹ =
        (a * b * a⁻¹ * b) * (b⁻¹ * (a * w * a⁻¹) * b) * (a * b * a⁻¹ * b)⁻¹ := by group
      _ = (b⁻¹ * (a * w * a⁻¹) * b) * (a * b * a⁻¹ * b) * (a * b * a⁻¹ * b)⁻¹ := by rw [← h]
      _ = b⁻¹ * (a * w * a⁻¹) * b := by group
      _ = b * (a * w * a⁻¹) * b⁻¹ := hbinv _ (haW w hw)
  let φ : W →* G :=
    { toFun := fun w => (w : G)⁻¹ * (a * w * a⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have hy : ((y : G))⁻¹ ∈ W := W.inv_mem y.2
        have hx : (x : G)⁻¹ * (a * x * a⁻¹) ∈ W := W.mul_mem (W.inv_mem x.2) (haW x x.2)
        simp only [Subgroup.coe_mul]
        calc ((x : G) * (y : G))⁻¹ * (a * ((x : G) * (y : G)) * a⁻¹) =
            (y : G)⁻¹ * ((x : G)⁻¹ * (a * x * a⁻¹)) * (a * y * a⁻¹) := by group
          _ = ((x : G)⁻¹ * (a * x * a⁻¹)) * (y : G)⁻¹ * (a * y * a⁻¹) := by
            rw [hWab _ hy _ hx]
          _ = (x : G)⁻¹ * (a * x * a⁻¹) * ((y : G)⁻¹ * (a * y * a⁻¹)) := by group }
  have hφ : ∀ w : W, φ w = (w : G)⁻¹ * (a * w * a⁻¹) := fun w => rfl
  have hφW : ∀ w : W, φ w ∈ W := fun w => W.mul_mem (W.inv_mem w.2) (haW w w.2)
  have hker : φ.ker = (W ⊓ Subgroup.centralizer {a}).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, hφ, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨w.2, ?_⟩
      have h1 : a * w * a⁻¹ = w := by
        have := congrArg (fun g => (w : G) * g) h
        simpa using this
      calc (w : G) * a = a * w * a⁻¹ * a := by rw [h1]
        _ = a * w := by group
    · rintro ⟨-, h⟩
      rw [← h]
      group
  set I : Subgroup G := φ.range with hI
  have hIcard : Nat.card I = r := by
    rw [hI, ← Subgroup.index_ker, hker]
    exact hrefl
  have hIW : I ≤ W := by
    rintro _ ⟨w, rfl⟩
    exact hφW w
  have haI : ∀ x ∈ I, a * x * a⁻¹ = x⁻¹ := by
    rintro _ ⟨w, rfl⟩
    rw [hφ]
    calc a * ((w : G)⁻¹ * (a * w * a⁻¹)) * a⁻¹ =
        (a * w * a⁻¹)⁻¹ * (a * (a * w * a⁻¹) * a⁻¹) := by group
      _ = ((w : G)⁻¹ * (a * w * a⁻¹))⁻¹ := by rw [haa]; group
  have hbI : ∀ x ∈ I, b * x * b⁻¹ ∈ I := by
    rintro _ ⟨w, rfl⟩
    refine ⟨⟨b * w * b⁻¹, hbW w w.2⟩, ?_⟩
    rw [hφ, hφ]
    change (b * w * b⁻¹)⁻¹ * (a * (b * w * b⁻¹) * a⁻¹) = _
    rw [hab' w w.2]
    group
  set Cw : Subgroup G := W ⊓ Subgroup.centralizer {a} with hCw
  have hCwW : Cw ≤ W := inf_le_left
  have haC : ∀ c ∈ Cw, a * c * a⁻¹ = c := by
    intro c hc
    have h := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    rw [← h]
    group
  have hbC : ∀ c ∈ Cw, b * c * b⁻¹ ∈ Cw := by
    intro c hc
    refine ⟨hbW c hc.1, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := hab' c hc.1
    rw [haC c hc] at h
    calc b * c * b⁻¹ * a = a * (b * c * b⁻¹) * a⁻¹ * a := by rw [h]
      _ = a * (b * c * b⁻¹) := by group
  have hCcard : Nat.card Cw ≤ r := by
    have h1 := Subgroup.card_mul_index (Cw.subgroupOf W)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCwW).toEquiv] at h1
    have h2 : (Cw.subgroupOf W).index = r := hrefl
    rw [h2] at h1
    have hr0 : 0 < r := hr.pos
    have h3 : Nat.card Cw * r ≤ r * r := by rw [h1, ← pow_two]; exact hcard
    exact Nat.le_of_mul_le_mul_right h3 hr0
  have hC := rfg_scalar_of_card_le hr (fun x hx y hy => hWab x (hCwW hx) y (hCwW hy))
    (fun x hx => hWr x (hCwW hx)) hCcard hbC (fun x hx => hbb x (hCwW hx))
  have hIs := rfg_scalar_of_card_le hr (fun x hx y hy => hWab x (hIW hx) y (hIW hy))
    (fun x hx => hWr x (hIW hx)) hIcard.le hbI (fun x hx => hbb x (hIW hx))
  have hdec : ∀ w ∈ W, ∃ c ∈ Cw, ∃ i ∈ I, w = c * i := by
    intro w hw
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
    set x := φ ⟨w, hw⟩ with hx
    have hxI : x ∈ I := ⟨⟨w, hw⟩, rfl⟩
    have hxr : x ^ (2 * k + 1) = 1 := by
      rw [← hk]
      exact hWr x (hIW hxI)
    have hax : a * x * a⁻¹ = x⁻¹ := haI x hxI
    have haxk : a * x ^ k * a⁻¹ = (x⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hax]
    have hwx : a * w * a⁻¹ = w * x := by
      show a * w * a⁻¹ = w * (w⁻¹ * (a * w * a⁻¹))
      group
    have hpow : x ^ (k + 1) = (x ^ k)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, show k + 1 + k = 2 * k + 1 by omega, hxr]
    have hac : a * (w * (x ^ k)⁻¹) * a⁻¹ = w * (x ^ k)⁻¹ := by
      calc a * (w * (x ^ k)⁻¹) * a⁻¹ = (a * w * a⁻¹) * (a * x ^ k * a⁻¹)⁻¹ := by group
        _ = w * (x * x ^ k) := by rw [hwx, haxk, inv_pow, inv_inv, mul_assoc]
        _ = w * (x ^ k)⁻¹ := by rw [← pow_succ', hpow]
    refine ⟨w * (x ^ k)⁻¹, ⟨W.mul_mem hw (W.inv_mem (W.pow_mem (hIW hxI) k)), ?_⟩, x ^ k,
      I.pow_mem hxI k, by group⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc w * (x ^ k)⁻¹ * a = (a * (w * (x ^ k)⁻¹) * a⁻¹) * a := by rw [hac]
      _ = a * (w * (x ^ k)⁻¹) := by group
  rcases hC with hC | hC <;> rcases hIs with hIs | hIs
  · refine ⟨b, by simp, Or.inl fun w hw => ?_⟩
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec w hw
    calc b * (c * i) * b⁻¹ = (b * c * b⁻¹) * (b * i * b⁻¹) := by group
      _ = c * i := by rw [hC c hc, hIs i hi]
  · refine ⟨a * b, by simp, Or.inl fun w hw => ?_⟩
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec w hw
    calc a * b * (c * i) * (a * b)⁻¹ = a * ((b * c * b⁻¹) * (b * i * b⁻¹)) * a⁻¹ := by group
      _ = (a * c * a⁻¹) * (a * i * a⁻¹)⁻¹ := by rw [hC c hc, hIs i hi]; group
      _ = c * i := by rw [haC c hc, haI i hi, inv_inv]
  · refine ⟨a * b, by simp, Or.inr fun w hw => ?_⟩
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec w hw
    calc a * b * (c * i) * (a * b)⁻¹ = a * ((b * c * b⁻¹) * (b * i * b⁻¹)) * a⁻¹ := by group
      _ = (a * c * a⁻¹)⁻¹ * (a * i * a⁻¹) := by rw [hC c hc, hIs i hi]; group
      _ = c⁻¹ * i⁻¹ := by rw [haC c hc, haI i hi]
      _ = (c * i)⁻¹ := by
        rw [mul_inv_rev, hWab _ (W.inv_mem (hCwW hc)) _ (W.inv_mem (hIW hi))]
  · refine ⟨b, by simp, Or.inr fun w hw => ?_⟩
    obtain ⟨c, hc, i, hi, rfl⟩ := hdec w hw
    calc b * (c * i) * b⁻¹ = (b * c * b⁻¹) * (b * i * b⁻¹) := by group
      _ = c⁻¹ * i⁻¹ := by rw [hC c hc, hIs i hi]
      _ = (c * i)⁻¹ := by
        rw [mul_inv_rev, hWab _ (W.inv_mem (hCwW hc)) _ (W.inv_mem (hIW hi))]

end CFSG.ABGLocalTools
