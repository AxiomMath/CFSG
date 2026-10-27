module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.Open

variable {K L : Type} [Group K] [Group L]

theorem eq_one_of_mem_of_map_eq_one {W : Subgroup K} (f : ↥W →* L)
    (hker : ∀ w : ↥W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup K}
    (hE : IsPGroup 3 ↥E) {x : ↥W} (hx : (x : K) ∈ E) (hfx : f x = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hE ⟨x, hx⟩
  have hk' : x ^ 3 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (3 ^ k) := (hker x hfx).symm.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem injOn_of_isPGroup {W : Subgroup K} (f : ↥W →* L)
    (hker : ∀ w : ↥W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup K}
    (hE : IsPGroup 3 ↥E) {x y : ↥W} (hx : (x : K) ∈ E) (hy : (y : K) ∈ E) (hxy : f x = f y) :
    x = y := by
  have h1 : x * y⁻¹ = 1 := by
    apply eq_one_of_mem_of_map_eq_one f hker hE
    · exact E.mul_mem hx (E.inv_mem hy)
    · rw [map_mul, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp h1

theorem nonempty_mulEquiv_of_map_eq {W : Subgroup K} (f : ↥W →* L)
    (hker : ∀ w : ↥W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup K} (hEW : E ≤ W)
    (hE : IsPGroup 3 ↥E) {TL : Subgroup L} (hmap : (E.subgroupOf W).map f = TL) :
    Nonempty (↥E ≃* ↥TL) := by
  set E' := E.subgroupOf W
  let φ : ↥E' →* L := f.comp E'.subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact injOn_of_isPGroup f hker hE x.2 y.2 hxy
  have hrange : φ.range = TL := by
    rw [← hmap, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(Subgroup.subgroupOfEquivOfLe hEW).symm.trans
    ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem sq_conj_eq_inv_of_map {W : Subgroup K} (f : ↥W →* L)
    (hker : ∀ w : ↥W, f w = 1 → Nat.Coprime 3 (orderOf w)) {E : Subgroup K} (hEW : E ≤ W)
    (hE : IsPGroup 3 ↥E) {TL : Subgroup L} (hmap : (E.subgroupOf W).map f = TL) {t : L}
    (ht : ∀ a ∈ TL, t ^ 2 * a * (t ^ 2)⁻¹ = a⁻¹) {w : ↥W} (hwt : f w = t)
    (hwN : (w : K) ∈ Subgroup.normalizer (E : Set K)) :
    ∀ a ∈ E, (w : K) ^ 2 * a * ((w : K) ^ 2)⁻¹ = a⁻¹ := by
  intro a ha
  have hw2N : (w : K) ^ 2 ∈ Subgroup.normalizer (E : Set K) := Subgroup.pow_mem _ hwN 2
  set a' : ↥W := ⟨a, hEW ha⟩
  have hb : ((w ^ 2 * a' * (w ^ 2)⁻¹ : ↥W) : K) ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp hw2N a).mp ha
    simpa [a'] using this
  have hfa : f a' ∈ TL := by
    rw [← hmap]
    exact ⟨a', Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hfb : f (w ^ 2 * a' * (w ^ 2)⁻¹) = f a'⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_pow, hwt, ht _ hfa, map_inv]
  have hinj := injOn_of_isPGroup f hker hE hb (E.inv_mem ha) hfb
  have := congrArg Subtype.val hinj
  simpa [a'] using this

end CFSG.HardMathSupport.Foote.SPLScalar
