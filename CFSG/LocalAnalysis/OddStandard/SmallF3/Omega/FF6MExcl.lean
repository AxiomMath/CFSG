module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Kinds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

theorem ff_kind_layer [Finite G] (hM : FF6MClass) (h : IsOm6M L) {s : G} (hs2 : orderOf s = 2)
    (hs : s ∈ normalizer (L : Set G)) :
    (KindM L s 0 → layerCent L s = ⊥) ∧ (KindM L s 1 → IsL29 (layerCent L s)) ∧
      (KindM L s 2 → IsOmega5 (layerCent L s)) ∧ (KindM L s 3 → layerCent L s = ⊥) ∧
      (KindM L s 4 → IsU33 (layerCent L s)) ∧ (KindM L s 5 → IsL29 (layerCent L s)) := by
  refine ⟨fun k => ?_, hM.layer_i4m G L h s hs2 hs, hM.layer_i1 G L h s hs2 hs, fun k => ?_,
    hM.layer_rho G L h s hs2 hs, hM.layer_gamma G L h s hs2 hs⟩
  · exact (hM.layer_trivial G L h s hs2 hs).mpr (Or.inl k)
  · exact (hM.layer_trivial G L h s hs2 hs).mpr (Or.inr k)

theorem ff_kind_zero_three_excl [Finite G] (hM : FF6MClass) (h : IsOm6M L) {s : G}
    (hs2 : orderOf s = 2) (hs : s ∈ normalizer (L : Set G)) :
    KindM L s 0 → KindM L s 3 → False := by
  intro k0 k3
  have hin : InnerOn L s := ((hM.inner_iff G L h s hs2 hs).mpr k0).1
  obtain ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hx, hα⟩ := k3
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  exact ff6m_KM3_not_inner hQ hdim ⟨α, hα⟩ ((ff6m_innerOn_iff h.1 hQ h5 e hx).mp hin)

theorem ff_kind_one_five_excl {s : G} : KindM L s 1 → KindM L s 5 → False := by
  rintro ⟨V', _, _, _, Q', hQ', e', x', hd', hsg', hx', hty⟩
    ⟨V, _, _, _, Q, hQ, e, x, hd, hsg, hx, -, hxG⟩
  obtain ⟨t, -, -, ht⟩ := simHasDim_of_inducesViaP hQ hQ' ⟨hd, hsg⟩ ⟨hd', hsg'⟩ e e' hx hx'
    hty.simHasDim
  exact hxG ⟨toProj Q t, ht⟩

theorem ff_kinds_excl_lt [Finite G] (hM : FF6MClass) (h : IsOm6M L) {s : G} (hs2 : orderOf s = 2)
    (hs : s ∈ normalizer (L : Set G)) {a b : ℕ} (hab : a < b) (hb : b < 6) :
    KindM L s a → KindM L s b → False := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := ff_kind_layer hM h hs2 hs
  have ha : a < 6 := lt_trans hab hb
  interval_cases a <;> interval_cases b <;> intro ka kb
  · exact ff_isL29_ne_bot (l1 kb) (l0 ka)
  · exact ff_isOmega5_ne_bot (l2 kb) (l0 ka)
  · exact ff_kind_zero_three_excl hM h hs2 hs ka kb
  · exact ff_isU33_ne_bot (l4 kb) (l0 ka)
  · exact ff_isL29_ne_bot (l5 kb) (l0 ka)
  · exact ff_not_isOmega5_and_isL29 (l2 kb) (l1 ka)
  · exact ff_isL29_ne_bot (l1 ka) (l3 kb)
  · exact ff_not_isU33_and_isL29 (l4 kb) (l1 ka)
  · exact ff_kind_one_five_excl ka kb
  · exact ff_isOmega5_ne_bot (l2 ka) (l3 kb)
  · exact ff_not_isU33_and_isOmega5 (l4 kb) (l2 ka)
  · exact ff_not_isOmega5_and_isL29 (l2 ka) (l5 kb)
  · exact ff_isU33_ne_bot (l4 kb) (l3 ka)
  · exact ff_isL29_ne_bot (l5 kb) (l3 ka)
  · exact ff_not_isU33_and_isL29 (l4 ka) (l5 kb)

theorem ff_asc82Tab6MExcl_of (hM : FF6MClass) : Asc82Tab6MExcl := by
  intro G _ _ L h s hs2 hs i j hi hj hij ka kb
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ff_kinds_excl_lt hM h hs2 hs hlt hj ka kb
  · exact ff_kinds_excl_lt hM h hs2 hs hgt hi kb ka

theorem ff_asc82Tab6MExcl : Asc82Tab6MExcl :=
  ff_asc82Tab6MExcl_of ffTab6MClass_holds

end CFSG.OddStandard.SmallF3.Omega
