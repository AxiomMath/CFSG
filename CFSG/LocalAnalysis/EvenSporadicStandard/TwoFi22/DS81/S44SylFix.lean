module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Syl

open Subgroup MulAction

structure TwoOrderGe11 (p : ℕ) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  not_dvd : ∀ k < 11, 0 < k → ¬ p ∣ 2 ^ k - 1

theorem twoOrderGe11_23 : TwoOrderGe11 23 := ⟨by norm_num, by norm_num, by decide⟩

theorem twoOrderGe11_89 : TwoOrderGe11 89 := ⟨by norm_num, by norm_num, by decide⟩

theorem exp_cases {p d f : ℕ} (hp : TwoOrderGe11 p) (hfd : f ≤ d) (hd : d ≤ 11)
    (h : 2 ^ d ≡ 2 ^ f [MOD p]) : f = d ∨ (f = 0 ∧ d = 11) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfd
  have hcop : Nat.gcd p (2 ^ f) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.prime Nat.prime_two).2 hp.ne_two)
  have h' : 2 ^ k ≡ 1 [MOD p] := by
    have : 2 ^ f * 2 ^ k ≡ 2 ^ f * 1 [MOD p] := by rwa [← pow_add, mul_one]
    exact Nat.ModEq.cancel_left_of_coprime hcop this
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · left
    simp
  · by_cases hk11 : k < 11
    · exfalso
      exact hp.not_dvd k hk11 hk ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h'.symm)
    · right
      omega

section Fixed

variable {V : Type} [CommGroup V]

def fixSub (a : MulAut V) : Subgroup V where
  carrier := {v | a v = v}
  mul_mem' := by
    intro x y hx hy
    change a x = x at hx
    change a y = y at hy
    change a (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one a
  inv_mem' := by
    intro x hx
    change a x = x at hx
    change a x⁻¹ = x⁻¹
    rw [map_inv, hx]

@[simp] theorem mem_fixSub {a : MulAut V} {v : V} : v ∈ fixSub a ↔ a v = v := Iff.rfl

theorem exists_card_pow [Finite V] (hV : Nat.card V = 2 ^ 11) (W : Subgroup V) :
    ∃ d ≤ 11, Nat.card W = 2 ^ d := by
  have h := Subgroup.card_subgroup_dvd_card W
  rw [hV] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

theorem card_modEq_card_fix [Finite V] (a : MulAut V) {p : ℕ} [Fact p.Prime] (ha : a ^ p = 1)
    (W : Subgroup V) (hW : ∀ w, a w ∈ W ↔ w ∈ W) :
    Nat.card W ≡ Nat.card ((fixSub a).subgroupOf W) [MOD p] := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hW' : ∀ x, (MulAut.toPerm V a) x ∈ W ↔ x ∈ W := hW
  have hσ : MulAut.toPerm V a ^ p = 1 := by rw [← map_pow, ha, map_one]
  have hτ : ((MulAut.toPerm V a).subtypePerm hW') ^ p ^ 1 = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext x
    simp [hσ]
  have h1 := Equiv.Perm.card_compl_support_modEq hτ
  have h2 : Nat.card ((fixSub a).subgroupOf W) =
      (Equiv.Perm.support ((MulAut.toPerm V a).subtypePerm hW'))ᶜ.card := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun w => ?_
    rw [mem_subgroupOf, Finset.mem_compl, Equiv.Perm.mem_support, not_not, mem_fixSub,
      Subtype.ext_iff, Equiv.Perm.subtypePerm_apply]
    rfl
  rw [h2, Nat.card_eq_fintype_card]
  exact h1.symm

theorem fix_dichotomy [Finite V] (hV : Nat.card V = 2 ^ 11) (a : MulAut V) {p : ℕ}
    (hp : TwoOrderGe11 p) (ha : a ^ p = 1) (W : Subgroup V) (hW : ∀ w, a w ∈ W ↔ w ∈ W) :
    (∀ w ∈ W, a w = w) ∨ (Nat.card W = Nat.card V ∧ ∀ w ∈ W, a w = w → w = 1) := by
  have := Fact.mk hp.prime
  obtain ⟨d, hd, hWd⟩ := exists_card_pow hV W
  have hF : Nat.card ((fixSub a).subgroupOf W) ∣ 2 ^ d :=
    hWd ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨f, hf, hFf⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hF
  have hmod := card_modEq_card_fix a ha W hW
  rw [hWd, hFf] at hmod
  rcases exp_cases hp hf hd hmod with rfl | ⟨rfl, rfl⟩
  · left
    have htop : (fixSub a).subgroupOf W = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).1 (hFf.trans hWd.symm)
    intro w hw
    have : (⟨w, hw⟩ : W) ∈ (fixSub a).subgroupOf W := by rw [htop]; trivial
    simpa [mem_subgroupOf] using this
  · right
    refine ⟨by rw [hWd, hV], fun w hw hfix => ?_⟩
    have hbot : (fixSub a).subgroupOf W = ⊥ := by
      rw [← Subgroup.card_eq_one]
      simpa using hFf
    have : (⟨w, hw⟩ : W) ∈ (fixSub a).subgroupOf W := by simpa [mem_subgroupOf] using hfix
    rw [hbot, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this

theorem eq_one_of_fixed [Finite V] (hV : Nat.card V = 2 ^ 11) {a : MulAut V} {p : ℕ}
    (hp : TwoOrderGe11 p) (ha : a ^ p = 1) (ha1 : a ≠ 1) {v : V} (hv : a v = v) : v = 1 := by
  rcases fix_dichotomy hV a hp ha ⊤ (by simp) with h | ⟨_, h⟩
  · exact absurd (MulEquiv.ext fun w => by rw [MulAut.one_apply]; exact h w trivial) ha1
  · exact h v trivial hv

def orbitSet (a : MulAut V) (v : V) : Set V := Set.range fun i : ℤ => (a ^ i) v

theorem image_orbitSet (a : MulAut V) (v : V) :
    (fun w => a w) '' orbitSet a v = orbitSet a v := by
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨1 + i, ?_⟩
    show (a ^ (1 + i)) v = a ((a ^ i) v)
    rw [zpow_add, zpow_one, MulAut.mul_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨i - 1, rfl⟩, ?_⟩
    show a ((a ^ (i - 1)) v) = (a ^ i) v
    rw [← MulAut.mul_apply, ← zpow_one_add, add_sub_cancel]

theorem mem_closure_orbitSet_iff (a : MulAut V) (v w : V) :
    a w ∈ closure (orbitSet a v) ↔ w ∈ closure (orbitSet a v) := by
  have hmap : (closure (orbitSet a v)).map a.toMonoidHom = closure (orbitSet a v) := by
    rw [MonoidHom.map_closure]
    congr 1
    exact image_orbitSet a v
  constructor
  · intro h
    rw [← hmap] at h
    obtain ⟨w', hw', hw'w⟩ := h
    have : w' = w := a.injective hw'w
    exact this ▸ hw'
  · intro h
    rw [← hmap]
    exact ⟨w, h, rfl⟩

theorem closure_orbitSet_eq_top [Finite V] (hV : Nat.card V = 2 ^ 11) {a : MulAut V} {p : ℕ}
    (hp : TwoOrderGe11 p) (ha : a ^ p = 1) (ha1 : a ≠ 1) {v : V} (hv : v ≠ 1) :
    closure (orbitSet a v) = ⊤ := by
  have hv_mem : v ∈ closure (orbitSet a v) := subset_closure ⟨0, by simp⟩
  rcases fix_dichotomy hV a hp ha (closure (orbitSet a v)) (mem_closure_orbitSet_iff a v) with
    h | ⟨hc, -⟩
  · exact absurd (eq_one_of_fixed hV hp ha ha1 (h v hv_mem)) hv
  · exact (Subgroup.card_eq_iff_eq_top _).1 hc

theorem eq_one_of_commute [Finite V] (hV : Nat.card V = 2 ^ 11) {a c : MulAut V} {p : ℕ}
    (hp : TwoOrderGe11 p) (ha : a ^ p = 1) (ha1 : a ≠ 1) (hc : Commute c a) {v : V}
    (hv : v ≠ 1) (hcv : c v = v) : c = 1 := by
  have hsub : orbitSet a v ⊆ (fixSub c : Set V) := by
    rintro _ ⟨i, rfl⟩
    show c ((a ^ i) v) = (a ^ i) v
    have h1 : c * a ^ i = a ^ i * c := (hc.zpow_right i).eq
    calc c ((a ^ i) v) = (c * a ^ i) v := rfl
      _ = (a ^ i * c) v := by rw [h1]
      _ = (a ^ i) (c v) := rfl
      _ = (a ^ i) v := by rw [hcv]
  have htop : fixSub c = ⊤ := by
    rw [eq_top_iff, ← closure_orbitSet_eq_top hV hp ha ha1 hv]
    exact (closure_le _).2 hsub
  ext w
  have : w ∈ fixSub c := by rw [htop]; trivial
  simpa using this

theorem card_dvd_of_free [Finite V] {H : Type} [Group H] [Finite H] [MulAction H V]
    (h1 : ∀ h : H, h • (1 : V) = 1)
    (hfree : ∀ (h : H) (v : V), v ≠ 1 → h • v = v → h = 1) :
    Nat.card H ∣ Nat.card V - 1 := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have : Fintype V := Fintype.ofFinite V
  have : Fintype (Quotient (orbitRel H V)) := Fintype.ofFinite _
  have : ∀ g : H, Fintype (fixedBy V g) := fun g => Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H V
  have hfix1 : Fintype.card (fixedBy V (1 : H)) = Nat.card V := by
    rw [Fintype.card_eq_nat_card, fixedBy_one_eq_univ, Nat.card_univ]
  have hfixg : ∀ g : H, g ≠ 1 → Fintype.card (fixedBy V g) = 1 := by
    intro g hg
    rw [Fintype.card_eq_nat_card]
    have : fixedBy V g = {1} := by
      ext v
      simp only [mem_fixedBy, Set.mem_singleton_iff]
      constructor
      · intro hv
        by_contra hv1
        exact hg (hfree g v hv1 hv)
      · rintro rfl
        exact h1 g
    rw [this]
    simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H)), hfix1] at hB
  have hsum : ∑ g ∈ Finset.univ.erase (1 : H), Fintype.card (fixedBy V g) = Nat.card H - 1 := by
    rw [Finset.sum_congr rfl (fun g hg => hfixg g (Finset.ne_of_mem_erase hg))]
    simp [Finset.card_erase_of_mem, Nat.card_eq_fintype_card]
  rw [hsum, ← Nat.card_eq_fintype_card (α := H)] at hB
  have hH : 0 < Nat.card H := Nat.card_pos
  have hV : 0 < Nat.card V := Nat.card_pos
  have : Nat.card H * Fintype.card (Quotient (orbitRel H V)) = Nat.card H + (Nat.card V - 1) := by
    rw [mul_comm, ← hB]
    omega
  exact (Nat.dvd_add_right (dvd_refl _)).1 (this ▸ dvd_mul_right _ _)

end Fixed

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Syl
