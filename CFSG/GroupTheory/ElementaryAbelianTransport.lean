module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Open

variable {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}

theorem isElemAbelian_iff_isElementaryAbelian :
    IsElemAbelian p E ↔ CFSG.IsElementaryAbelian p E :=
  (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).symm

theorem IsElemAbelian.isElementaryAbelian (h : IsElemAbelian p E) :
    CFSG.IsElementaryAbelian p E :=
  isElemAbelian_iff_isElementaryAbelian.mp h

theorem isElemAbelian_of_isElementaryAbelian [h : CFSG.IsElementaryAbelian p E] :
    IsElemAbelian p E :=
  isElemAbelian_iff_isElementaryAbelian.mpr h

theorem isElemAbelian_bot (p : ℕ) : IsElemAbelian p (⊥ : Subgroup G) :=
  ⟨⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])⟩⟩,
    fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩

theorem IsElemAbelian.mono {F : Subgroup G} (h : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := by
  have := h.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => h.2 x (hFE hx)⟩
  have hc := congrArg Subtype.val (mul_comm' (⟨a, hFE a.2⟩ : E) ⟨b, hFE b.2⟩)
  exact Subtype.ext (by simpa using hc)

theorem IsElemAbelian.subgroupOf (h : IsElemAbelian p E) (K : Subgroup G) :
    IsElemAbelian p (E.subgroupOf K) := by
  have := h.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have hc := congrArg Subtype.val (mul_comm' (⟨((x : K) : G), x.2⟩ : E) ⟨((y : K) : G), y.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hc
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.2 _ hx

theorem IsElemAbelian.map {H : Type*} [Group H] (h : IsElemAbelian p E) (f : G →* H) :
    IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map h f

theorem IsElemAbelian.isPGroup (h : IsElemAbelian p E) : IsPGroup p E :=
  fun y => ⟨1, Subtype.ext (by simpa using h.2 y y.2)⟩

theorem isElemAbelian_zpowers {x : G} (hx : x ^ p = 1) : IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self x i j).eq
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end CFSG.Open

namespace CFSG

theorem IsElementaryAbelian.of_le {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (hA : IsElementaryAbelian p A) (hBA : B ≤ A) : IsElementaryAbelian p B :=
  Open.isElemAbelian_iff_isElementaryAbelian.mp
    ((Open.isElemAbelian_iff_isElementaryAbelian.mpr hA).mono hBA)

theorem IsElementaryAbelian.subgroup_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {A : Subgroup G} (hA : IsElementaryAbelian p A) (f : G →* H) :
    IsElementaryAbelian p (A.map f) :=
  Open.isElemAbelian_iff_isElementaryAbelian.mp
    ((Open.isElemAbelian_iff_isElementaryAbelian.mpr hA).map f)

theorem IsElementaryAbelian.of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsElementaryAbelian p A) : IsElementaryAbelian p B where
  toIsMulCommutative := ⟨⟨fun a b => by
    have := h.toIsMulCommutative
    apply e.symm.injective
    rw [map_mul, map_mul, mul_comm' (e.symm a)]⟩⟩
  exponent_dvd_p := Monoid.exponent_eq_of_mulEquiv e ▸ h.exponent_dvd_p

end CFSG
