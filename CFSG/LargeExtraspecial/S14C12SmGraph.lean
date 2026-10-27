module

public import CFSG.LargeExtraspecial.S14C12SmDefs
public import CFSG.LargeExtraspecial.S14C12SmQ
public import CFSG.Timmesfeld.Closure.MinCex

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SmithGraph

open Subgroup CFSG.Open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G]

theorem commute_conj_iff (c a b : G) : Commute (c⁻¹ * a * c) (c⁻¹ * b * c) ↔ Commute a b := by
  have h := Commute.conj_iff (a := a) (b := b) c⁻¹
  rwa [inv_inv] at h

theorem isConj_conj {z x : G} (hx : IsConj z x) (c : G) : IsConj z (c⁻¹ * x * c) :=
  hx.trans (isConj_iff.mpr ⟨c⁻¹, by group⟩)

theorem shortcut_of_path {z : G}
    (hP : ∀ x w y : G, IsConj z x → IsConj z w → IsConj z y →
      Commute x z → Commute z w → Commute w y →
        ¬ Commute x w → ¬ Commute z y → ¬ Commute x y →
          ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y)
    {x u w y : G} (hx : IsConj z x) (hu : IsConj z u) (hw : IsConj z w) (hy : IsConj z y)
    (hxu : Commute x u) (huw : Commute u w) (hwy : Commute w y) :
    ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  by_cases hxw : Commute x w
  · exact ⟨w, hw, hxw, hwy⟩
  by_cases huy : Commute u y
  · exact ⟨u, hu, hxu, huy⟩
  by_cases hxy : Commute x y
  · exact ⟨x, hx, Commute.refl x, hxy⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp hu
  have hzc : c⁻¹ * (c * z * c⁻¹) * c = z := by group
  have h1 := (commute_conj_iff c x (c * z * c⁻¹)).mpr hxu
  have h2 := (commute_conj_iff c (c * z * c⁻¹) w).mpr huw
  have h3' := (commute_conj_iff c (c * z * c⁻¹) y).mp
  rw [hzc] at h1 h2 h3'
  have h3 : ¬ Commute z (c⁻¹ * y * c) := fun h => huy (h3' h)
  obtain ⟨v, hv, hxv, hvy⟩ := hP _ _ _ (isConj_conj hx c) (isConj_conj hw c) (isConj_conj hy c)
    h1 h2 ((commute_conj_iff c w y).mpr hwy) (fun h => hxw ((commute_conj_iff c x w).mp h)) h3
    (fun h => hxy ((commute_conj_iff c x y).mp h))
  refine ⟨c * v * c⁻¹, hv.trans (isConj_iff.mpr ⟨c, rfl⟩), ?_, ?_⟩
  · rw [← commute_conj_iff c, show c⁻¹ * (c * v * c⁻¹) * c = v by group]
    exact hxv
  · rw [← commute_conj_iff c, show c⁻¹ * (c * v * c⁻¹) * c = v by group]
    exact hvy

theorem exists_common_of_reach {z : G}
    (hP : ∀ x w y : G, IsConj z x → IsConj z w → IsConj z y →
      Commute x z → Commute z w → Commute w y →
        ¬ Commute x w → ¬ Commute z y → ¬ Commute x y →
          ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y)
    {x y : G} (hx : IsConj z x) (h : Reach (conjugatesOf z) x y) :
    ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y := by
  induction h with
  | refl => exact ⟨x, hx, Commute.refl x, Commute.refl x⟩
  | tail _ hbc ih =>
    obtain ⟨v, hv, hxv, hvb⟩ := ih
    exact shortcut_of_path hP hx hv hbc.1 hbc.2.1 hxv hvb hbc.2.2

theorem local_of_input (hLoc : SmithU62LocalInput) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) (x y : G)
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  by_cases hxQ : x ∈ S.QG
  · by_cases hyQ : y ∈ S.QG
    · exact SmithQ.orderOf_mul_mem_of_mem_QG S hxQ hyQ
    · obtain ⟨h1, h2⟩ := hLoc G S hw hU y x hy hx hyM hxM hyQ
      have hord : orderOf (y * x) = orderOf (x * y) := by
        rw [show y * x = MulAut.conj y (x * y) by rw [MulAut.conj_apply]; group,
          MulEquiv.orderOf_eq]
      rw [hord] at h1 h2
      refine ⟨h1, fun h4 => ?_⟩
      rw [show (x * y) ^ 2 = x * (y * x) ^ 2 * x⁻¹ by rw [_root_.sq, _root_.sq]; group]
      exact (h2 h4).trans (isConj_iff.mpr ⟨x, rfl⟩)
  · exact hLoc G S hw hU x y hx hy hxM hyM hxQ

theorem threeFour_of_common (S : Setting G)
    (hloc : ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M →
      orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
        (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)))
    {a b v : G} (ha : IsConj S.z a) (hb : IsConj S.z b) (hv : IsConj S.z v)
    (hav : Commute a v) (hvb : Commute v b) :
    orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (a * b) = 4 → IsConj S.z ((a * b) ^ 2)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hv
  have hzc : c⁻¹ * (c * S.z * c⁻¹) * c = S.z := by group
  have haM : c⁻¹ * a * c ∈ S.M := by
    have h := (commute_conj_iff c a (c * S.z * c⁻¹)).mpr hav
    rw [hzc] at h
    exact mem_centralizer_singleton_iff.mpr h.eq
  have hbM : c⁻¹ * b * c ∈ S.M := by
    have h := (commute_conj_iff c b (c * S.z * c⁻¹)).mpr hvb.symm
    rw [hzc] at h
    exact mem_centralizer_singleton_iff.mpr h.eq
  obtain ⟨h1, h2⟩ := hloc _ _ (isConj_conj ha c) (isConj_conj hb c) haM hbM
  have hab : c⁻¹ * a * c * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
  have hord : orderOf (c⁻¹ * (a * b) * c) = orderOf (a * b) := by
    rw [show c⁻¹ * (a * b) * c = MulAut.conj c⁻¹ (a * b) by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq]
  rw [hab, hord] at h1 h2
  refine ⟨h1, fun h4 => ?_⟩
  have h5 := h2 h4
  rw [show (c⁻¹ * (a * b) * c) ^ 2 = c⁻¹ * (a * b) ^ 2 * c by
    rw [_root_.sq, _root_.sq]; group] at h5
  exact h5.trans (isConj_iff.mpr ⟨c, by group⟩)

end SmithGraph

end CFSG.LargeExtraspecial.S14
