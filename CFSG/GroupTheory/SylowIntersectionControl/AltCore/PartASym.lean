module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartA
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.GoodY
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.BlockSetoid
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.OrbitCount

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)
open scoped Pointwise

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} {x₀ : Fin n}

def smallSet (H : Subgroup (Perm (Fin n))) (x₀ : Fin n) (c : ℕ) : Set (Fin n) :=
  {x | x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧ Nat.card (orbit H x) < c}

def largeSet (H : Subgroup (Perm (Fin n))) (x₀ : Fin n) (c : ℕ) : Set (Fin n) :=
  {x | x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧ c ≤ Nat.card (orbit H x)}

theorem smallSet_apply_iff {c : ℕ} {a : Perm (Fin n)}
    (ha : a ∈ normalizer (H : Set (Perm (Fin n)))) (x : Fin n) :
    a x ∈ smallSet H x₀ c ↔ x ∈ smallSet H x₀ c := by
  simp only [smallSet, Set.mem_setOf_eq, card_orbit_eq_of_normalizer ha x,
    orbit_mem_setStab x₀ ha x]

theorem largeSet_apply_iff {c : ℕ} {a : Perm (Fin n)}
    (ha : a ∈ normalizer (H : Set (Perm (Fin n)))) (x : Fin n) :
    a x ∈ largeSet H x₀ c ↔ x ∈ largeSet H x₀ c := by
  simp only [largeSet, Set.mem_setOf_eq, card_orbit_eq_of_normalizer ha x,
    orbit_mem_setStab x₀ ha x]

theorem ncard_orbit_add_smallSet_add_largeSet (c : ℕ) :
    (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard + (smallSet H x₀ c).ncard +
      (largeSet H x₀ c).ncard = n := by
  classical
  have h1 : (smallSet H x₀ c) ∪ (largeSet H x₀ c) =
      (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)ᶜ := by
    ext x
    simp only [smallSet, largeSet, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hc : Nat.card (orbit H x) < c
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, by omega⟩
  have h2 : Disjoint (smallSet H x₀ c) (largeSet H x₀ c) :=
    Set.disjoint_left.mpr fun x hx hy => absurd hy.2 (not_le.mpr hx.2)
  rw [add_assoc, ← Set.ncard_union_eq h2, h1, Set.ncard_add_ncard_compl,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem dvd_ncard_largeSet (hH : IsPGroup 2 H) (i : ℕ) :
    2 ^ i ∣ (largeSet H x₀ (2 ^ i)).ncard := by
  refine dvd_ncard_of_forall_dvd (P := H)
    (fun g hg x hx => (largeSet_apply_iff (le_normalizer hg) x).mpr hx) fun x hx => ?_
  obtain ⟨a, ha⟩ := exists_card_orbit_eq_two_pow' hH x
  have hle := hx.2
  rw [ha] at hle ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)

theorem ncard_smallSet_add_le (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) {lo m : ℕ} (hlm : lo ≤ m)
    (hlo : ∀ x ∈ smallSet H x₀ (2 ^ m), 2 ^ lo ≤ Nat.card (orbit H x)) :
    (smallSet H x₀ (2 ^ m)).ncard + 2 ^ lo ≤ 2 ^ m := by
  refine ncard_add_le_of_card_orbit_injective (P := H) hlm
    (fun g hg x hx => (smallSet_apply_iff (le_normalizer hg) x).mpr hx) (fun x hx => ?_)
    fun x hx y hy hxy => orbit_eq_of_card_orbit_eq hH hiso he hx.1 hy.1 hxy
  obtain ⟨a, ha⟩ := exists_card_orbit_eq_two_pow' hH x
  have h1 := hlo x hx
  have h2 := hx.2
  rw [ha] at h1 h2
  exact ⟨a, (Nat.pow_le_pow_iff_right (by norm_num)).mp h1,
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2, ha⟩

theorem dvd_ncard_orbit_of_blocks {i : ℕ}
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (hE : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ i) :
    2 ^ i ∣ (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard := by
  refine dvd_ncard_of_forall_dvd (fun g hg x hx => ?_) fun x hx => by rw [hE x hx]
  exact (fixOutside_le_setStab _ (restrSub_le_fixOutside (omegaOneCenter_le _ hg)) x).mpr hx

theorem exists_isEvenSet_orbit_of_isPIsolatedOver (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H) :
    ∃ x₀, IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) := by
  obtain ⟨x, hxN, hxH, hx2⟩ := IsPIsolatedOver.exists_sq_mem hiso hH
  obtain ⟨x₀, -, he⟩ := exists_isEvenSet_orbit hH (isRadical_of_isPIsolatedOver hH hiso) _
    Set.univ rfl (fun a _ => mem_setStab.mpr fun z => by simp)
    ⟨x, hxN, fun z hz => absurd (Set.mem_univ z) hz, hxH, hx2⟩
  exact ⟨x₀, he⟩

private theorem ncard_smallSet_eq_mod (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) {i : ℕ}
    (hdvd : 2 ^ i ∣ (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard) :
    (smallSet H x₀ (2 ^ i)).ncard = n % 2 ^ i := by
  have hsum := ncard_orbit_add_smallSet_add_largeSet (H := H) (x₀ := x₀) (2 ^ i)
  obtain ⟨a, ha⟩ := hdvd
  obtain ⟨b, hb⟩ := dvd_ncard_largeSet (x₀ := x₀) hH i
  have hlt := ncard_smallSet_add_le hH hiso he (lo := 0) (Nat.zero_le i) fun x _ => by
    have : Nonempty (orbit H x) := ⟨⟨x, mem_orbit_self x⟩⟩
    rw [pow_zero]
    exact Nat.card_pos
  obtain ⟨c, hc⟩ : ∃ c, (smallSet H x₀ (2 ^ i)).ncard = c := ⟨_, rfl⟩
  rw [hc] at hsum hlt ⊢
  rw [ha, hb] at hsum
  rw [pow_zero] at hlt
  rw [← hsum, show 2 ^ i * a + c + 2 ^ i * b = c + 2 ^ i * (a + b) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem card_class_sym [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    {i : ℕ} (hE : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ i)
    {t : Setoid (Fin n)} (hto : ∀ x y, t.r x y → y ∈ orbit H x)
    (htS : ∀ x ∈ largeSet H x₀ (2 ^ i), Nat.card {y // t.r x y} = 2 ^ i) (x : Fin n)
    (hx : x ∉ smallSet H x₀ (2 ^ i)) :
    Nat.card {y // (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
      (smallSet H x₀ (2 ^ i)) (orbitRel (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) (Fin n)) t).r x y} =
      2 ^ i := by
  have hO := orbit_mem_setStab (H := H) x₀
  by_cases hxO : x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀
  · rw [card_pieceSetoid_of_mem (fun k hk y => mem_setStab.mp (fixOutside_le_setStab _
      (restrSub_le_fixOutside (omegaOneCenter_le _ hk))) y) hxO]
    exact hE x hxO
  · have hxS : x ∈ largeSet H x₀ (2 ^ i) := ⟨hxO, not_lt.mp fun h => hx ⟨hxO, h⟩⟩
    rw [card_pieceSetoid_of_not_mem hxO hx fun y hy => ?_]
    · exact htS x hxS
    obtain ⟨⟨g, hg⟩, rfl⟩ := hto x y hy
    exact ⟨fun h => hxO ((mem_setStab.mp (hO (le_normalizer hg)) x).mp h),
      fun h => hx ((smallSet_apply_iff (le_normalizer hg) x).mp h)⟩

theorem exists_goodY_sym_of_not_mem_fixSet (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (hH : IsPGroup 2 H) (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) (hx₀ : x₀ ∉ fixSet H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∀ a ∈ normalizer (H : Set (Perm (Fin n))), a ^ 2 ∈ H → a ∈ Y := by
  classical
  have hO := orbit_mem_setStab (H := H) x₀
  have hKN : normalizer (H : Set (Perm (Fin n))) ≤
      normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) :=
    fun a ha => mem_normalizer_fintype fun k hk => conj_mem_restrSub ha (hO ha) hk
  obtain ⟨i, hi, hE⟩ := exists_card_orbit_omegaOneCenterOf_eq hH hiso he hx₀
  obtain ⟨t, ht, hto, htS, -⟩ := exists_setoid_blocks hH i (S := largeSet H x₀ (2 ^ i))
    (fun x hx g hg => (largeSet_apply_iff (le_normalizer hg) x).mpr hx) fun x hx => hx.2
  obtain ⟨Y, hY, hYa⟩ := exists_goodY_of_classes hn hn2 hi
    (s := pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) (smallSet H x₀ (2 ^ i))
      (orbitRel (omegaOneCenterOf (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
        H)) (Fin n)) t)
    (fun x hx y => by
      rw [pieceSetoid_iff_of_mem_delta hx.1 hx]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩)
    ((Nat.card_coe_set_eq _).trans
      (ncard_smallSet_eq_mod hH hiso he (dvd_ncard_orbit_of_blocks hE)))
    (card_class_sym hE hto htS)
    (good := fun a => a ∈ normalizer (H : Set (Perm (Fin n))) ∧ a ^ 2 ∈ H)
    (fun a ha => mem_partStab_of_sq_mem hH hiso he
      (hKN.trans (normalizer_le_normalizer_omegaOneCenterOf _))
      (fun a ha x => smallSet_apply_iff ha x) ht hto ha.1 ha.2)
    fun a ha x => smallSet_apply_iff ha.1 x
  exact ⟨Y, hY, fun a ha ha2 => hYa a ⟨ha, ha2⟩⟩

theorem two_le_card_orbit_of_mem_fixSet (hx₀ : x₀ ∈ fixSet H) {x : Fin n}
    (hx : x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀) : 2 ≤ Nat.card (orbit H x) := by
  by_contra h
  have : Nonempty (orbit H x) := ⟨⟨x, mem_orbit_self x⟩⟩
  have h1 : Nat.card (orbit H x) = 1 := by
    have := Nat.card_pos (α := orbit H x)
    omega
  obtain ⟨w, hw⟩ := Nat.card_eq_one_iff_exists.mp h1
  exact hx (fixSet_subset_orbit hx₀ fun g hg =>
    congrArg Subtype.val ((hw ⟨g x, ⟨⟨g, hg⟩, rfl⟩⟩).trans (hw ⟨x, mem_orbit_self x⟩).symm))

theorem two_dvd_card_orbit_of_mem_fixSet (hH : IsPGroup 2 H) (hx₀ : x₀ ∈ fixSet H) {x : Fin n}
    (hx : x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀) : 2 ∣ Nat.card (orbit H x) := by
  obtain ⟨j, hj⟩ := exists_card_orbit_eq_two_pow' hH x
  have h2 := two_le_card_orbit_of_mem_fixSet hx₀ hx
  rw [hj] at h2 ⊢
  rcases j with _ | j
  · simp at h2
  · exact dvd_pow_self 2 (Nat.succ_ne_zero j)

private theorem smallSet_four_eq_empty (h3 : n % 4 = 3) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) (hx₀ : x₀ ∈ fixSet H)
    (hO3 : (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard = 3) :
    smallSet H x₀ (2 ^ 2) = ∅ := by
  have hsum := ncard_orbit_add_smallSet_add_largeSet (H := H) (x₀ := x₀) (2 ^ 2)
  obtain ⟨b, hb⟩ := dvd_ncard_largeSet (x₀ := x₀) hH 2
  have hlt := ncard_smallSet_add_le hH hiso he (lo := 1) (m := 2) (by norm_num) fun x hx => by
    simpa using two_le_card_orbit_of_mem_fixSet hx₀ hx.1
  obtain ⟨c, hc⟩ := dvd_ncard_of_forall_dvd (P := H) (S := smallSet H x₀ (2 ^ 2))
    (fun g hg x hx => (smallSet_apply_iff (le_normalizer hg) x).mpr hx)
    fun x hx => two_dvd_card_orbit_of_mem_fixSet hH hx₀ hx.1
  rw [← Set.ncard_eq_zero]
  rw [hO3, hb, hc] at hsum
  rw [hc] at hlt ⊢
  norm_num at hlt hsum ⊢
  omega

theorem exists_goodY_sym_of_mem_fixSet_three (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (h3 : n % 4 = 3) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) (hx₀ : x₀ ∈ fixSet H)
    (hO3 : (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard = 3) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∀ a ∈ normalizer (H : Set (Perm (Fin n))), a ^ 2 ∈ H → a ∈ Y := by
  classical
  have hO := orbit_mem_setStab (H := H) x₀
  have hsmall := smallSet_four_eq_empty h3 hH hiso he hx₀ hO3
  obtain ⟨t, ht, hto, htS, -⟩ := exists_setoid_blocks hH 2 (S := largeSet H x₀ (2 ^ 2))
    (fun x hx g hg => (largeSet_apply_iff (le_normalizer hg) x).mpr hx) fun x hx => hx.2
  have hD : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀, ∀ y,
      (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ∅
        (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)) t).r x y ↔
        y ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ := by
    intro x hx y
    rw [pieceSetoid_iff_of_mem hx]
    refine ⟨fun h => h.1, fun hy => ⟨hy, ?_⟩⟩
    change x ∈ orbit _ y
    rw [orbit_eq_iff.mpr hy]
    exact hx
  have hcls : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ →
      Nat.card {y // (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ∅
        (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)) t).r x y} = 2 ^ 2 := by
    intro x hx
    have hxS : x ∈ largeSet H x₀ (2 ^ 2) := ⟨hx, not_lt.mp fun h => by
      have : x ∈ smallSet H x₀ (2 ^ 2) := ⟨hx, h⟩
      rw [hsmall] at this
      exact this⟩
    rw [card_pieceSetoid_of_not_mem hx (Set.notMem_empty x) fun y hy => ?_]
    · exact htS x hxS
    obtain ⟨⟨g, hg⟩, rfl⟩ := hto x y hy
    exact ⟨fun h => hx ((mem_setStab.mp (hO (le_normalizer hg)) x).mp h), Set.notMem_empty _⟩
  obtain ⟨Y, hY, hYa⟩ := exists_goodY_of_classes hn hn2 (Or.inr rfl) hD
    (by rw [Nat.card_coe_set_eq, hO3]; omega) hcls
    (good := fun a => a ∈ normalizer (H : Set (Perm (Fin n))) ∧ a ^ 2 ∈ H)
    (fun a ha => mem_partStab_of_sq_mem hH hiso he le_normalizer (fun _ _ _ => by simp) ht hto
      ha.1 ha.2)
    fun a ha x => mem_setStab.mp (hO ha.1) x
  exact ⟨Y, hY, fun a ha ha2 => hYa a ⟨ha, ha2⟩⟩

theorem smul_eq_of_apply_mem_iff {S : Set (Fin n)} {a : Perm (Fin n)}
    (h : ∀ x, a x ∈ S ↔ x ∈ S) : a • S = S := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← h (a⁻¹ • y)]
  change a (a⁻¹ y) ∈ S ↔ y ∈ S
  rw [show a (a⁻¹ y) = y from a.apply_symm_apply y]

theorem exists_goodY_sym_of_mem_fixSet_one (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (h1 : n % 4 = 1) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) (hx₀ : x₀ ∈ fixSet H)
    (hO3 : (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard = 3) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∀ a ∈ normalizer (H : Set (Perm (Fin n))), a ^ 2 ∈ H → a ∈ Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := orbit_mem_setStab (H := H) x₀
  have hm : 2 ^ padicValNat 2 (n - 1) ∣ n - 1 ∧ ¬ 2 ^ (padicValNat 2 (n - 1) + 1) ∣ n - 1 :=
    ⟨pow_padicValNat_dvd, pow_succ_padicValNat_not_dvd (by omega)⟩
  have hm1 : 1 ≤ padicValNat 2 (n - 1) := by
    by_contra h0
    rw [show padicValNat 2 (n - 1) = 0 by omega, zero_add, pow_one] at hm
    exact hm.2 ⟨(n - 1) / 2, by omega⟩
  have hsum := ncard_orbit_add_smallSet_add_largeSet (H := H) (x₀ := x₀)
    (2 ^ padicValNat 2 (n - 1))
  have hlarge := dvd_ncard_largeSet (x₀ := x₀) hH (padicValNat 2 (n - 1))
  have hlt := ncard_smallSet_add_le hH hiso he (lo := 1) hm1 fun x hx => by
    simpa using two_le_card_orbit_of_mem_fixSet hx₀ hx.1
  rw [pow_one] at hlt
  have hdvd : 2 ^ padicValNat 2 (n - 1) ∣
      (smallSet H x₀ (2 ^ padicValNat 2 (n - 1))).ncard + 2 := by
    refine (Nat.dvd_add_left hlarge).mp ?_
    have : (smallSet H x₀ (2 ^ padicValNat 2 (n - 1))).ncard + 2 +
        (largeSet H x₀ (2 ^ padicValNat 2 (n - 1))).ncard = n - 1 := by omega
    rw [this]
    exact hm.1
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hΓ : (orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∪
      smallSet H x₀ (2 ^ padicValNat 2 (n - 1))).toFinset.card =
      2 ^ padicValNat 2 (n - 1) + 1 := by
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_union_eq
      (Set.disjoint_right.mpr fun x hx => hx.1), hO3]
    omega
  refine ⟨_, goodY_setStab hn h1 hm (hn2 _) (Or.inr hΓ), fun a ha _ => ?_⟩
  rw [MulAction.mem_stabilizer_iff, Set.coe_toFinset]
  exact smul_eq_of_apply_mem_iff fun x => by
    rw [Set.mem_union, Set.mem_union, mem_setStab.mp (hO ha) x, smallSet_apply_iff ha x]

theorem exists_goodY_sym_of_mem_fixSet (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (hH : IsPGroup 2 H) (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H)
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) (hx₀ : x₀ ∈ fixSet H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∀ a ∈ normalizer (H : Set (Perm (Fin n))), a ^ 2 ∈ H → a ∈ Y := by
  have hO3 : (orbit (normalizer (H : Set (Perm (Fin n)))) x₀).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact card_orbit_eq_three_of_mem_fixSet hH hiso hx₀ he
  have hsum := ncard_orbit_add_smallSet_add_largeSet (H := H) (x₀ := x₀) 2
  obtain ⟨b, hb⟩ := dvd_ncard_of_forall_dvd (P := H) (S := largeSet H x₀ 2)
    (fun g hg x hx => (largeSet_apply_iff (le_normalizer hg) x).mpr hx)
    fun x hx => two_dvd_card_orbit_of_mem_fixSet hH hx₀ hx.1
  have hs : (smallSet H x₀ 2).ncard = 0 := by
    rw [Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem fun x hx =>
      absurd (two_le_card_orbit_of_mem_fixSet hx₀ hx.1) (not_le.mpr hx.2)
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h | h
  · exact exists_goodY_sym_of_mem_fixSet_one hn hn2 h hH hiso he hx₀ hO3
  · exact exists_goodY_sym_of_mem_fixSet_three hn hn2 h hH hiso he hx₀ hO3

theorem exists_goodY_sym (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1) (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∀ a ∈ normalizer (H : Set (Perm (Fin n))), a ^ 2 ∈ H → a ∈ Y := by
  obtain ⟨x₀, he⟩ := exists_isEvenSet_orbit_of_isPIsolatedOver hH hiso
  by_cases hx₀ : x₀ ∈ fixSet H
  · exact exists_goodY_sym_of_mem_fixSet hn hn2 hH hiso he hx₀
  · exact exists_goodY_sym_of_not_mem_fixSet hn hn2 hH hiso he hx₀

end CFSG.GroupTheory.AltCore
