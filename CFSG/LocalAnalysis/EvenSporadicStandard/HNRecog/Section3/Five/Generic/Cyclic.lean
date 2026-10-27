module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

theorem nonempty_mulEquiv_zmod_prod_of_commute {x y : G} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hx : orderOf x = m) (hy : orderOf y = n) (hcop : Nat.Coprime m n) (hxy : x * y = y * x) :
    Nonempty (↥(Subgroup.closure ({x, y} : Set G)) ≃* Multiplicative (ZMod m) × Multiplicative (ZMod n)) := by
  have hgx : ∀ z : Subgroup.zpowers x,
      z ∈ Subgroup.zpowers (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  have hgy : ∀ z : Subgroup.zpowers y,
      z ∈ Subgroup.zpowers (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  have hcardx : Nat.card (Subgroup.zpowers x) = m := by rw [Nat.card_zpowers, hx]
  have hcardy : Nat.card (Subgroup.zpowers y) = n := by rw [Nat.card_zpowers, hy]
  let ex : Multiplicative (ZMod m) ≃* Subgroup.zpowers x :=
    zmodMulEquivOfGenerator (G := Subgroup.zpowers x) (g := ⟨x, Subgroup.mem_zpowers x⟩) hgx hcardx
  let ey : Multiplicative (ZMod n) ≃* Subgroup.zpowers y :=
    zmodMulEquivOfGenerator (G := Subgroup.zpowers y) (g := ⟨y, Subgroup.mem_zpowers y⟩) hgy hcardy
  let f : Multiplicative (ZMod m) →* G :=
    (Subgroup.subtype (Subgroup.zpowers x)).comp ex.toMonoidHom
  let g : Multiplicative (ZMod n) →* G :=
    (Subgroup.subtype (Subgroup.zpowers y)).comp ey.toMonoidHom
  have hfrange : f.range = Subgroup.zpowers x := by
    change ((Subgroup.subtype (Subgroup.zpowers x)).comp ex.toMonoidHom).range = Subgroup.zpowers x
    rw [MonoidHom.range_comp, show ex.toMonoidHom.range = ⊤ from ex.range_eq_top,
      Subgroup.map_top, Subgroup.range_subtype]
  have hgrange : g.range = Subgroup.zpowers y := by
    change ((Subgroup.subtype (Subgroup.zpowers y)).comp ey.toMonoidHom).range = Subgroup.zpowers y
    rw [MonoidHom.range_comp, show ey.toMonoidHom.range = ⊤ from ey.range_eq_top,
      Subgroup.map_top, Subgroup.range_subtype]
  have hfinj : Function.Injective f := (Subgroup.zpowers x).subtype_injective.comp ex.injective
  have hginj : Function.Injective g := (Subgroup.zpowers y).subtype_injective.comp ey.injective
  have hdisj : Disjoint f.range g.range := by
    rw [hfrange, hgrange, Subgroup.disjoint_def]
    intro z hzx hzy
    have h1 : orderOf z ∣ m := by rw [← hx]; exact orderOf_dvd_of_mem_zpowers hzx
    have h2 : orderOf z ∣ n := by rw [← hy]; exact orderOf_dvd_of_mem_zpowers hzy
    have hdvd : orderOf z ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have hcomm : ∀ a b, Commute (f a) (g b) := by
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (show f a ∈ Subgroup.zpowers x from (ex a).2)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (show g b ∈ Subgroup.zpowers y from (ey b).2)
    rw [← hi, ← hj]
    exact (show Commute x y from hxy).zpow_zpow i j
  have hφinj : Function.Injective (MonoidHom.noncommCoprod f g hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨hfinj, hginj, hdisj⟩
  have hφrange : (MonoidHom.noncommCoprod f g hcomm).range = Subgroup.closure ({x, y} : Set G) := by
    rw [MonoidHom.noncommCoprod_range, hfrange, hgrange, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  exact ⟨((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)).symm⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
