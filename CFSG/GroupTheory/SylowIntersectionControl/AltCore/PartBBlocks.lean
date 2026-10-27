module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartA
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.BlockSetoid
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.OrbitCount
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartASym
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.AltOrbits
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.GoodY

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} {x₀ : Fin n}

theorem ncard_add_ncard_add_ncard {A B : Set (Fin n)} (hB : ∀ x ∈ B, x ∉ A) :
    A.ncard + B.ncard + {x | x ∉ A ∧ x ∉ B}.ncard = n := by
  have hd1 : Disjoint A B := Set.disjoint_right.mpr hB
  have hd2 : Disjoint (A ∪ B) {x | x ∉ A ∧ x ∉ B} := Set.disjoint_left.mpr fun x hx hx' => by
    rcases hx with h | h
    · exact hx'.1 h
    · exact hx'.2 h
  have hu : (A ∪ B) ∪ {x | x ∉ A ∧ x ∉ B} = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    tauto
  rw [← Set.ncard_union_eq hd1, ← Set.ncard_union_eq hd2, hu, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem card_class_four [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (hE : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ 2)
    (hR4 : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ → x ∉ fixSet H →
      (orbit (normalizer (H : Set (Perm (Fin n)))) x).ncard = 4) (x : Fin n) (hx : x ∉ fixSet H) :
    Nat.card {y // (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) (fixSet H)
      (orbitRel (omegaOneCenterOf (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H))
        (Fin n)) (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n))).r x y} = 2 ^ 2 := by
  have hO := orbit_mem_setStab (H := H) x₀
  by_cases hxO : x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀
  · rw [card_pieceSetoid_of_mem (fun k hk y => fixOutside_le_setStab _
      (restrSub_le_fixOutside (omegaOneCenter_le _ hk)) y) hxO]
    exact hE x hxO
  · rw [card_pieceSetoid_of_not_mem hxO hx fun y hy => ?_]
    · rw [show Nat.card {y // (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)).r x y} =
        Nat.card (orbit (normalizer (H : Set (Perm (Fin n)))) x) from
        Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_orbit_symm),
        Nat.card_coe_set_eq, hR4 x hxO hx]
      rfl
    · obtain ⟨⟨g, hg⟩, rfl⟩ := mem_orbit_symm.mp hy
      exact ⟨fun h => hxO ((hO hg x).mp h), fun h => hx ((fixSet_mem_setStab hg x).mp h)⟩

theorem exists_goodY_alt_four (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (hE : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ 2)
    (hR4 : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ → x ∉ fixSet H →
      (orbit (normalizer (H : Set (Perm (Fin n)))) x).ncard = 4)
    (hΦ : ∀ x ∈ fixSet H, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
    (hΦ3 : (fixSet H).ncard ≤ 3) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧ normalizer (H : Set (Perm (Fin n))) ≤ Y := by
  have hO := orbit_mem_setStab (H := H) x₀
  have hKN : normalizer (H : Set (Perm (Fin n))) ≤
      normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) :=
    fun a ha => mem_normalizer_fintype fun k hk => conj_mem_restrSub ha (hO ha) hk
  have hEN := hKN.trans (normalizer_le_normalizer_omegaOneCenterOf _)
  obtain ⟨a, ha⟩ := dvd_ncard_orbit_of_blocks hE
  obtain ⟨b, hb⟩ : 4 ∣ {x | x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧
      x ∉ fixSet H}.ncard :=
    dvd_ncard_of_forall_dvd (P := normalizer (H : Set (Perm (Fin n))))
      (fun g hg x hx => ⟨fun h => hx.1 ((hO hg x).mp h),
        fun h => hx.2 ((fixSet_mem_setStab hg x).mp h)⟩)
      fun x hx => by rw [Nat.card_coe_set_eq, hR4 x hx.1 hx.2]
  have hsum := ncard_add_ncard_add_ncard hΦ
  norm_num at ha
  obtain ⟨Y, hY, hYa⟩ := exists_goodY_of_classes hn hn2 (Or.inr rfl)
    (s := pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) (fixSet H)
      (orbitRel (omegaOneCenterOf (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H))
        (Fin n)) (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)))
    (fun x hx y => by
      rw [pieceSetoid_iff_of_mem_delta (hΦ x hx) hx]
      exact ⟨fun h => h.2, fun h => ⟨hΦ y h, h⟩⟩)
    (by rw [Nat.card_coe_set_eq]; show _ = n % 4; omega)
    (card_class_four hE hR4)
    (good := (· ∈ normalizer (H : Set (Perm (Fin n)))))
    (fun g hg => mem_partStab_pieceSetoid (hO hg) (fixSet_mem_setStab hg)
      (fun x _ y _ => orbitRel_apply_iff (hEN hg) x y)
      fun x _ _ y _ _ => orbitRel_apply_iff (le_normalizer hg) x y)
    fun g hg x => fixSet_mem_setStab hg x
  exact ⟨Y, hY, fun g hg => hYa g hg⟩

private theorem apply_mem_iff_of_subset_fixSet {a : Perm (Fin n)} (ha : a ∈ H)
    {C : Set (Fin n)} (hC : C ⊆ fixSet H) (x : Fin n) : a x ∈ C ↔ x ∈ C := by
  by_cases hx : x ∈ fixSet H
  · rw [hx a ha]
  · have hax : a x ∉ fixSet H := fun h => hx ((fixSet_mem_setStab (le_normalizer ha) x).mp h)
    exact iff_of_false (fun h => hax (hC h)) fun h => hx (hC h)

private theorem apply_mem_iff_of_mem_fixOutside {O C : Set (Fin n)} {a : Perm (Fin n)}
    (ha : a ∈ fixOutside O) (hC : ∀ x ∈ C, x ∉ O) (x : Fin n) : a x ∈ C ↔ x ∈ C := by
  by_cases hx : x ∈ O
  · have hax : a x ∈ O := (fixOutside_le_setStab _ ha x).mpr hx
    exact iff_of_false (fun h => hC _ h hax) fun h => hC _ h hx
  · rw [ha x hx]

private theorem exists_subset_fixSet_ncard :
    ∃ P ⊆ fixSet H, P.ncard = 2 * ((fixSet H).ncard / 2) := by
  classical
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq (s := (fixSet H).toFinset)
    (n := 2 * ((fixSet H).ncard / 2)) (by rw [← Set.ncard_eq_toFinset_card']; omega)
  exact ⟨t, fun x hx => Set.mem_toFinset.mp (ht hx), by rw [Set.ncard_coe_finset, htc]⟩

private theorem card_class_two [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (hE : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ 1)
    (hΦ : ∀ x ∈ fixSet H, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
    (hΦ3 : (fixSet H).ncard ≤ 3) {P : Set (Fin n)} (hPΦ : P ⊆ fixSet H)
    (hPc : P.ncard = 2 * ((fixSet H).ncard / 2)) {t : Setoid (Fin n)}
    (htS : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ → x ∉ fixSet H →
      Nat.card {y // t.r x y} = 2 ^ 1)
    (hSorb : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ → x ∉ fixSet H → ∀ y,
      t.r x y → y ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧ y ∉ fixSet H)
    (x : Fin n) (hx : x ∉ fixSet H \ P) :
    Nat.card {y // (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) (fixSet H \ P)
      (orbitRel (omegaOneCenterOf (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H))
        (Fin n)) (pieceSetoid P ∅ ⊤ t)).r x y} = 2 ^ 1 := by
  by_cases hxO : x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀
  · rw [card_pieceSetoid_of_mem (fun k hk y => fixOutside_le_setStab _
      (restrSub_le_fixOutside (omegaOneCenter_le _ hk)) y) hxO]
    exact hE x hxO
  by_cases hxP : x ∈ P
  · rw [card_pieceSetoid_of_not_mem hxO hx fun y hy =>
      ⟨hΦ y (hPΦ ((pieceSetoid_iff_of_mem hxP).mp hy).1),
        fun h => h.2 ((pieceSetoid_iff_of_mem hxP).mp hy).1⟩]
    rw [show Nat.card {y // (pieceSetoid P ∅ ⊤ t).r x y} = Nat.card P from
      Nat.card_congr (Equiv.subtypeEquivRight fun y => by
        rw [pieceSetoid_iff_of_mem hxP]
        exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩), Nat.card_coe_set_eq, hPc]
    have : 0 < P.ncard := (Set.ncard_pos (Set.toFinite P)).mpr ⟨x, hxP⟩
    rw [hPc] at this
    show _ = 2
    omega
  have hxΦ : x ∉ fixSet H := fun h => hx ⟨h, hxP⟩
  have hiff : ∀ y, (pieceSetoid P ∅ ⊤ t).r x y ↔ t.r x y := fun y => by
    rw [pieceSetoid_iff_of_not_mem hxP (Set.notMem_empty x)]
    exact ⟨fun h => h.2.2, fun h => ⟨fun hy => (hSorb x hxO hxΦ y h).2 (hPΦ hy),
      Set.notMem_empty y, h⟩⟩
  rw [card_pieceSetoid_of_not_mem hxO hx fun y hy =>
    ⟨(hSorb x hxO hxΦ y ((hiff y).mp hy)).1, fun h => (hSorb x hxO hxΦ y ((hiff y).mp hy)).2 h.1⟩,
    Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact htS x hxO hxΦ

private theorem mem_partStab_two
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (hΦ : ∀ x ∈ fixSet H, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
    {P : Set (Fin n)} (hPΦ : P ⊆ fixSet H) {t : Setoid (Fin n)}
    (ht : ∀ g ∈ H, ∀ x y, t.r (g x) (g y) ↔ t.r x y) {a : Perm (Fin n)}
    (ha : a ∈ normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) ∨ a ∈ H) :
    a ∈ partStab (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) (fixSet H \ P)
      (orbitRel (omegaOneCenterOf (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H))
        (Fin n)) (pieceSetoid P ∅ ⊤ t)) := by
  have hO := orbit_mem_setStab (H := H) x₀
  rcases ha with hM | hH'
  · have haO := (mem_inf.mp (mem_inf.mp hM).1).2
    exact mem_partStab_pieceSetoid (fixOutside_le_setStab _ haO)
      (apply_mem_iff_of_mem_fixOutside haO fun y hy => hΦ y hy.1)
      (fun x _ y _ => orbitRel_apply_iff (normalizer_le_normalizer_omegaOneCenterOf _
        (mem_inf.mp (mem_inf.mp hM).1).1) x y)
      fun x hx _ y hy _ => by rw [haO x hx, haO y hy]
  · have hEN : normalizer (H : Set (Perm (Fin n))) ≤ normalizer (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H) : Set (Perm (Fin n))) :=
      le_trans (fun a ha => mem_normalizer_fintype fun k hk => conj_mem_restrSub ha (hO ha) hk)
        (normalizer_le_normalizer_omegaOneCenterOf _)
    have ht₂ : a ∈ partStab (pieceSetoid P ∅ ⊤ t) := mem_partStab_pieceSetoid
      (apply_mem_iff_of_subset_fixSet hH' hPΦ) (fun x => by simp)
      (fun _ _ _ _ => iff_of_true trivial trivial) fun x _ _ y _ _ => ht a hH' x y
    exact mem_partStab_pieceSetoid (hO (le_normalizer hH'))
      (apply_mem_iff_of_subset_fixSet hH' Set.diff_subset)
      (fun x _ y _ => orbitRel_apply_iff (hEN (le_normalizer hH')) x y)
      fun x _ _ y _ _ => mem_partStab_iff.mp ht₂ x y

theorem exists_goodY_alt_two (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1) (hH : IsPGroup 2 H)
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (hE : ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ 1)
    (hΦ : ∀ x ∈ fixSet H, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
    (hΦ3 : (fixSet H).ncard ≤ 3) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) ≤ Y ∧ H ≤ Y := by
  have hO := orbit_mem_setStab (H := H) x₀
  obtain ⟨P, hPΦ, hPc⟩ := exists_subset_fixSet_ncard (H := H)
  obtain ⟨t, ht, hto, htS, -⟩ := exists_setoid_blocks hH 1
    (S := {x | x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧ x ∉ fixSet H})
    (fun x hx g hg => ⟨fun h => hx.1 ((hO (le_normalizer hg) x).mp h),
      fun h => hx.2 ((fixSet_mem_setStab (le_normalizer hg) x).mp h)⟩) fun x hx => by
      have : Nonempty (orbit H x) := ⟨⟨x, mem_orbit_self x⟩⟩
      rw [pow_one]
      exact Nat.le_of_dvd Nat.card_pos (two_dvd_card_orbit_of_not_mem_fixSet hH hx.2)
  have hSorb : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ → x ∉ fixSet H → ∀ y,
      t.r x y → y ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧ y ∉ fixSet H :=
    fun x hxO hxΦ y hy => by
      obtain ⟨⟨g, hg⟩, rfl⟩ := hto x y hy
      exact ⟨fun h => hxO ((hO (le_normalizer hg) x).mp h),
        fun h => hxΦ ((fixSet_mem_setStab (le_normalizer hg) x).mp h)⟩
  obtain ⟨a, ha⟩ := dvd_ncard_orbit_of_blocks hE
  obtain ⟨b, hb⟩ : 2 ∣ {x | x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ ∧
      x ∉ fixSet H}.ncard := dvd_ncard_of_forall_dvd (P := H) (fun g hg x hx =>
      ⟨fun h => hx.1 ((hO (le_normalizer hg) x).mp h),
        fun h => hx.2 ((fixSet_mem_setStab (le_normalizer hg) x).mp h)⟩)
      fun x hx => two_dvd_card_orbit_of_not_mem_fixSet hH hx.2
  have hsum := ncard_add_ncard_add_ncard hΦ
  have hD := Set.ncard_diff hPΦ
  norm_num at ha
  obtain ⟨Y, hY, hYa⟩ := exists_goodY_of_classes hn hn2 (Or.inl rfl)
    (fun x hx y => by
      rw [pieceSetoid_iff_of_mem_delta (hΦ x hx.1) hx]
      exact ⟨fun h => h.2, fun h => ⟨hΦ y h.1, h⟩⟩)
    (by rw [Nat.card_coe_set_eq, hD, hPc]; show _ = n % 2; omega)
    (card_class_two hE hΦ hΦ3 hPΦ hPc (fun x hxO hxΦ => htS x ⟨hxO, hxΦ⟩) hSorb)
    (good := fun a => a ∈ normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) ∨ a ∈ H)
    (fun a ha => mem_partStab_two hΦ hPΦ ht ha)
    fun a ha x => ha.elim
      (fun hM => apply_mem_iff_of_mem_fixOutside (mem_inf.mp (mem_inf.mp hM).1).2
        (fun y hy => hΦ y hy.1) x)
      fun hH' => apply_mem_iff_of_subset_fixSet hH' Set.diff_subset x
  exact ⟨Y, hY, fun a ha => hYa a (Or.inl ha), fun a ha => hYa a (Or.inr ha)⟩

end CFSG.GroupTheory.AltCore
