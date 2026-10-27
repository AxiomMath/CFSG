module

public import CFSG.GroupTheory.AschbacherBlock
public import CFSG.GroupTheory.FusionFamilyControl
public import CFSG.GroupTheory.SylowIntersectionControl.PairSelection
import CFSG.GroupTheory.SylowIntersectionControl.Fusion
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GroupTheory.GNPairChoice

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

private lemma C₁_characteristic (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hTp : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    ((c.C₁ T).subgroupOf T).Characteristic := by
  have hbT : baum T ≠ ⊥ := C1GN.baum_ne_bot hTp hT0
  have hC1charB : ((c.fst (baum T)).subgroupOf (baum T)).Characteristic :=
    (hc (baum T) (hTp.to_le (C1GN.baum_le T)) (C1GN.baum_baum T) hbT).1
  have hC1B : c.C₁ T ≤ baum T :=
    (c.C₁_le_omegaOneCenterOf_baum hTp).trans
      ((C1GN.omegaOneCenterOf_le_centerOf (baum T)).trans inf_le_left)
  exact C1GN.characteristic_subgroupOf_trans (C1GN.baum_le T) hC1B
    (C1GN.characteristic_baum T) hC1charB

private lemma C₂_characteristic (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hTp : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    ((c.C₂ T).subgroupOf T).Characteristic := by
  have hbT : baum T ≠ ⊥ := C1GN.baum_ne_bot hTp hT0
  have hC2charB : ((c.snd (baum T)).subgroupOf (baum T)).Characteristic :=
    (hc (baum T) (hTp.to_le (C1GN.baum_le T)) (C1GN.baum_baum T) hbT).2
  have hC2B : c.C₂ T ≤ baum T := c.C₂_le_baum hTp
  exact C1GN.characteristic_subgroupOf_trans (C1GN.baum_le T) hC2B
    (C1GN.characteristic_baum T) hC2charB

private lemma C₁_inf_omegaOneCenterOf_ne_bot (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hTp : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    c.C₁ T ⊓ omegaOneCenterOf T ≠ ⊥ := by
  have hC1charT : ((c.C₁ T).subgroupOf T).Characteristic :=
    C₁_characteristic c hc hTp hT0
  have hC1normal : ((c.C₁ T).subgroupOf T).Normal :=
    Subgroup.normal_of_characteristic ((c.C₁ T).subgroupOf T)
  have hC1T : c.C₁ T ≤ T :=
    ((c.C₁_le_omegaOneCenterOf_baum hTp).trans
      ((C1GN.omegaOneCenterOf_le_centerOf (baum T)).trans inf_le_left)).trans
      (C1GN.baum_le T)
  have hne : (c.C₁ T).subgroupOf T ≠ ⊥ := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (c.C₁_ne_bot hTp hT0)
    intro hbot
    have hxT : (⟨(x : G), hC1T x.2⟩ : ↥T) ∈ (c.C₁ T).subgroupOf T := x.2
    rw [hbot, Subgroup.mem_bot] at hxT
    exact hx (Subtype.ext (congrArg (fun z : ↥T => (z : G)) hxT))
  have hnil : Group.IsNilpotent ↥T := hTp.isNilpotent
  have hZne : (c.C₁ T).subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (H := (c.C₁ T).subgroupOf T) hne
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hyC1 : ((y : ↥T) : G) ∈ c.C₁ T := Subgroup.mem_subgroupOf.mp y.2.1
  have hyCentT : (y : ↥T) ∈ (centerOf T).subgroupOf T := by
    rw [C1GN.centerOf_subgroupOf T]
    exact y.2.2
  have hyCent : ((y : ↥T) : G) ∈ centerOf T := Subgroup.mem_subgroupOf.mp hyCentT
  have hyOmega : ((y : ↥T) : G) ∈ omegaOneCenterOf T :=
    Subgroup.subset_closure ⟨hyCent,
      sq_eq_one_of_mem_omegaOneCenter (baum T) (c.C₁_le_omegaOneCenterOf_baum hTp hyC1)⟩
  intro hbot
  have hy : ((y : ↥T) : G) ∈ c.C₁ T ⊓ omegaOneCenterOf T := ⟨hyC1, hyOmega⟩
  rw [hbot, Subgroup.mem_bot] at hy
  exact hy1 (Subtype.ext (Subtype.ext hy))

private lemma C₁_inf_omegaOneCenterOf_characteristic (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hTp : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    ((c.C₁ T ⊓ omegaOneCenterOf T).subgroupOf T).Characteristic := by
  have hC1 : ((c.C₁ T).subgroupOf T).Characteristic := C₁_characteristic c hc hTp hT0
  have hOmega : ((omegaOneCenterOf T).subgroupOf T).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T
  change ((c.C₁ T).subgroupOf T ⊓ (omegaOneCenterOf T).subgroupOf T).Characteristic
  exact Subgroup.characteristic_inf

private lemma exists_conj_eq_of_sylow {S T H : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hT : IsSylowOf 2 T ⊤) (hSH : S ≤ H) (hHsys : IsSylowOf 2 (T ⊓ H) H) :
    ∃ k ∈ H, T = S.map (MulAut.conj k).toMonoidHom ∧
      H.map (MulAut.conj k).toMonoidHom = H := by
  have hSHsyl : IsSylowOf 2 S H := hS.of_le hSH le_top
  have hTH : T ⊓ H = T := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    exact le_of_eq (calc
      Nat.card ↥T = Nat.card ↥S := hT.card_eq.trans hS.card_eq.symm
      _ = Nat.card ↥(T ⊓ H) := hSHsyl.card_eq.trans hHsys.card_eq.symm)
  have hTleH : T ≤ H := inf_eq_left.mp hTH
  have hTHsyl : IsSylowOf 2 T H := hT.of_le hTleH le_top
  obtain ⟨k, hkH, hk⟩ := hSHsyl.exists_mem_conj hTHsyl
  have hmapT : T = S.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hk x, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨k, hkH, hmapT, ?_⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkH)

private lemma exists_le_charNormalizers_of_mem_gomiD_centralizer
    (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hT0 : T ≠ ⊥) {S H : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hHsys : IsSylowOf 2 (T ⊓ H) H)
    (hHeq : H = Subgroup.centralizer
      ((c.C₁ S ⊓ omegaOneCenterOf S : Subgroup G) : Set G)) :
    ∃ H' ∈ charNormalizers T, H ≤ H' := by
  have hSH : S ≤ H := by
    rw [hHeq]
    exact Subgroup.le_centralizer_iff.mpr
      (inf_le_right.trans ((C1GN.omegaOneCenterOf_le_centerOf S).trans inf_le_right))
  obtain ⟨k, _, hmapT, hHfix⟩ := exists_conj_eq_of_sylow hS hT hSH hHsys
  have hCmap : (c.C₁ S ⊓ omegaOneCenterOf S).map (MulAut.conj k).toMonoidHom =
      c.C₁ T ⊓ omegaOneCenterOf T := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective,
      ← c.C₁_map_conj hS.isPGroup k, omegaOneCenterOf_map_mulEquiv (MulAut.conj k) S,
      hmapT]
  have hHeq' : H = Subgroup.centralizer
      ((c.C₁ T ⊓ omegaOneCenterOf T : Subgroup G) : Set G) := by
    rw [← hHfix, hHeq, centralizer_map_mulEquiv, hCmap]
  refine ⟨Subgroup.normalizer ((c.C₁ T ⊓ omegaOneCenterOf T : Subgroup G) : Set G),
    ⟨_, C₁_inf_omegaOneCenterOf_ne_bot c hc hT.isPGroup hT0,
      inf_le_right.trans (C1GN.omegaOneCenterOf_le_self T),
      C₁_inf_omegaOneCenterOf_characteristic c hc hT.isPGroup hT0, rfl⟩, ?_⟩
  rw [hHeq']
  exact Subgroup.centralizer_le_normalizer _

private lemma exists_le_charNormalizers_of_mem_gomiD_normalizer
    (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hT0 : T ≠ ⊥) {S H : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hHsys : IsSylowOf 2 (T ⊓ H) H)
    (hHeq : H = Subgroup.normalizer ((c.C₂ S : Subgroup G) : Set G)) :
    ∃ H' ∈ charNormalizers T, H ≤ H' := by
  have hSH : S ≤ H := by
    rw [hHeq]
    exact Subgroup.le_normalizer.trans ((normalizer_le_normalizer_baum S).trans
      (c.normalizer_baum_le_normalizer_C₂ hS.isPGroup))
  obtain ⟨k, _, hmapT, hHfix⟩ := exists_conj_eq_of_sylow hS hT hSH hHsys
  have hCmap : (c.C₂ S).map (MulAut.conj k).toMonoidHom = c.C₂ T := by
    rw [← c.C₂_map_conj hS.isPGroup k, hmapT]
  have hHeq' : H = Subgroup.normalizer ((c.C₂ T : Subgroup G) : Set G) := by
    rw [← hHfix, hHeq, Subgroup.map_equiv_normalizer_eq, hCmap]
  exact ⟨Subgroup.normalizer ((c.C₂ T : Subgroup G) : Set G),
    ⟨_, c.C₂_ne_bot hT.isPGroup hT0,
      (c.C₂_le_baum hT.isPGroup).trans (C1GN.baum_le T),
      C₂_characteristic c hc hT.isPGroup hT0, rfl⟩, le_of_eq hHeq'⟩

private lemma exists_le_charNormalizers_of_mem_sylowMembers
    (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hT0 : T ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ sylowMembers 2 c.gomiD T) :
    ∃ H' ∈ charNormalizers T, H ≤ H' := by
  obtain ⟨hHmem, hHsys⟩ := hH
  obtain ⟨S, hS, hHeq | hHeq⟩ := hHmem
  · exact exists_le_charNormalizers_of_mem_gomiD_centralizer c hc hT hT0 hS hHsys hHeq
  · exact exists_le_charNormalizers_of_mem_gomiD_normalizer c hc hT hT0 hS hHsys hHeq

theorem familyControlsFusion_charNormalizers (c : GNPairChoice G)
    (hc : ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      ((c.fst T).subgroupOf T).Characteristic ∧ ((c.snd T).subgroupOf T).Characteristic)
    (hreg : ∀ M : Subgroup G, Maximal (CFSG.IsPLocal 2) M → c.selection.IsRegular M)
    {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) :
    FamilyControlsFusion (charNormalizers T) T := by
  by_cases hT0 : T = ⊥
  · rw [hT0]
    intro x y hx hy _
    rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy]
    exact Relation.EqvGen.refl 1
  · have hsing : c.selection.singularMaxLocals = ∅ := by
      ext M
      constructor
      · rintro ⟨hmax, hnot⟩
        exact (hnot (hreg M hmax)).elim
      · intro h
        simp at h
    have hctrl : ControlsSylowIntersections 2 c.gomiD ⊤ := by
      simpa [hsing] using c.controlsSylowIntersections_gomiD_union
    have hgomi : IsNormalSetIn c.gomiD ⊤ := by
      refine ⟨fun _ _ => le_top, ?_⟩
      rintro X ⟨S, hS, hX | hX⟩ g -
      · refine ⟨S.map (MulAut.conj g).toMonoidHom, ?_, Or.inl ?_⟩
        · have hm := isSylowOf_map_conj hS g
          rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hm
        · rw [hX, centralizer_map_mulEquiv, Subgroup.map_inf_eq _ _ _
            (MulAut.conj g).injective,
            ← c.C₁_map_conj hS.isPGroup g, omegaOneCenterOf_map_mulEquiv]
      · refine ⟨S.map (MulAut.conj g).toMonoidHom, ?_, Or.inr ?_⟩
        · have hm := isSylowOf_map_conj hS g
          rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hm
        · rw [hX, Subgroup.map_equiv_normalizer_eq, ← c.C₂_map_conj hS.isPGroup g]
    have hfam := hctrl.familyControlsFusion hgomi hT
    intro x y hx hy hconj
    refine Relation.EqvGen.mono (fun a b hab => ?_) x y (hfam x y hx hy hconj)
    obtain ⟨ha, hb, H, hH, g, hg, rfl⟩ := hab
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact ⟨ha, hb, Subgroup.normalizer (T : Set G),
        ⟨T, hT0, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance, rfl⟩,
        g, hg, rfl⟩
    · obtain ⟨H', hH', hHH'⟩ :=
        exists_le_charNormalizers_of_mem_sylowMembers c hc hT hT0 hH
      exact ⟨ha, hb, H', hH', g, hHH' hg, rfl⟩

end CFSG.GroupTheory.GNPairChoice

end
