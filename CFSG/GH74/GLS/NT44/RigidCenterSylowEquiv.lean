module

public import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
public import CFSG.GH74.GLS.C3.Layer1.Defs
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.GLS.NT44.ActualCover

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.GLS.Stage1.Thm2.Recip

private theorem exists_actual_center_equiv_of_isSylowOf_zStar
    {G : Type} [Group G] [Finite G] {J W : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar J))
    (hZ2 : IsPGroup 2 (Subgroup.center (kBar J))) :
    ∃ eZ : ↥W ≃* Subgroup.center (kBar J),
      ∀ w : ↥W, (eZ w : kBar J) = hatMk J ⟨(w : G), (hW.le w.2).1⟩ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZJ : zStar J ≤ J := inf_le_left
  have hWJ : W ≤ J := hW.le.trans hZJ
  let f : zStar J →* center (kBar J) :=
    ((hatMk J).comp (inclusion hZJ)).codRestrict _
      (fun z => (Alt51.mem_zStar_iff_hat_mem_center (K := J)
        ⟨(z : G), z.2.1⟩).mp z.2)
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨j, hj⟩ := hatMk_surjective J c.val
    have hjZ : (j : G) ∈ zStar J :=
      (Alt51.mem_zStar_iff_hat_mem_center j).mpr (hj ▸ c.2)
    refine ⟨⟨(j : G), hjZ⟩, ?_⟩
    apply Subtype.ext
    exact hj
  obtain ⟨P, hP⟩ := hW.exists_sylow_eq_subgroupOf
  have hmap : (P : Subgroup (zStar J)).map f = ⊤ := by
    have h := (P.mapSurjective hf).is_maximal' (hZ2.to_subgroup ⊤) le_top
    simpa only [Sylow.coe_mapSurjective] using h.symm
  let fW : W →* center (kBar J) := f.comp (inclusion hW.le)
  have hfinj : Function.Injective fW := by
    intro a b hab
    apply Subtype.ext
    exact eq_of_hatMk_eq hWJ hW.isPGroup a.2 b.2
      (congrArg Subtype.val hab)
  have hfsur : Function.Surjective fW := by
    intro c
    have hc : c ∈ (P : Subgroup (zStar J)).map f := by
      rw [hmap]
      exact mem_top c
    obtain ⟨z, hz, hzc⟩ := hc
    have hzW : (z : G) ∈ W := by
      rw [hP] at hz
      exact hz
    refine ⟨⟨(z : G), hzW⟩, ?_⟩
    change f (inclusion hW.le ⟨(z : G), hzW⟩) = c
    have heq : inclusion hW.le ⟨(z : G), hzW⟩ = z := Subtype.ext rfl
    rw [heq]
    exact hzc
  exact ⟨MulEquiv.ofBijective fW ⟨hfinj, hfsur⟩, fun w => rfl⟩


theorem exists_rigid_center_sylow_equiv_of_center_equiv
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {J S : Subgroup G}
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S
      (Subgroup.centralizer ({x} : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center (CFSG.GH74.GLS.kBar J)))
    (eQ : Subgroup.center (CFSG.GH74.GLS.kBar J) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 2))) :
    ∃ eW : ↥(S ⊓ CFSG.GH74.GLS.zStar J) ≃*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 2)),
      ∀ w : ↥(S ⊓ CFSG.GH74.GLS.zStar J),
        (eW w : Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) =
          eQ ⟨CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨(w : G), w.2.2.1⟩,
            (Alt51.mem_zStar_iff_hat_mem_center (K := J)
              ⟨(w : G), w.2.2.1⟩).mp w.2.2⟩ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSI := P92.sylow_inf hJ hS
  have hW : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ zStar J) (zStar J) := by
    have h := hSI.inf_of_le_normalizer (show zStar J ≤ J from inf_le_left)
      (fun j hj => Alt51.mem_normalizer_zStar (Subgroup.le_normalizer hj))
    simpa only [inf_assoc, inf_eq_right.mpr (show zStar J ≤ J from inf_le_left)] using h
  obtain ⟨eZ, heZ⟩ := exists_actual_center_equiv_of_isSylowOf_zStar hW hZ2
  refine ⟨eZ.trans eQ, ?_⟩
  intro w
  rw [MulEquiv.trans_apply]
  rw [show eZ w = ⟨CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J
      ⟨(w : G), w.2.2.1⟩,
    (Alt51.mem_zStar_iff_hat_mem_center (K := J)
      ⟨(w : G), w.2.2.1⟩).mp w.2.2⟩ from Subtype.ext (heZ w)]

theorem exists_rigid_center_sylow_equiv_of_center_card_sixteen :
∀
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {J S : Subgroup G}
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hS : CFSG.ABGLocalTools.IsSylowOf 2 S
      (Subgroup.centralizer ({x} : Set G)))
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16),
    ∃ (eZ : ↥(S ⊓ CFSG.GH74.GLS.zStar J) ≃*
        Subgroup.center (CFSG.GH74.GLS.kBar J))
      (_e4 : Subgroup.center (CFSG.GH74.GLS.kBar J) ≃*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))),
      ∀ w : ↥(S ⊓ CFSG.GH74.GLS.zStar J),
        (eZ w : CFSG.GH74.GLS.kBar J) =
          CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨(w : G), w.2.2.1⟩ := by
  intro G instG instFinite fullQ instFullQ
    x J S hJ hS hL34 h16
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSI := P92.sylow_inf hJ hS
  have hW : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ zStar J) (zStar J) := by
    have h := hSI.inf_of_le_normalizer (show zStar J ≤ J from inf_le_left)
      (fun j hj => Alt51.mem_normalizer_zStar (Subgroup.le_normalizer hj))
    simpa only [inf_assoc, inf_eq_right.mpr (show zStar J ≤ J from inf_le_left)] using h
  obtain ⟨eJ⟩ := hJ.2
  have hcardZ : Nat.card (Subgroup.center (kBar J)) = 16 :=
    (Nat.card_congr (Subgroup.centerCongr eJ).toEquiv).trans h16
  have hZ2 : IsPGroup 2 (Subgroup.center (kBar J)) :=
    IsPGroup.of_card (n := 4) (by rw [hcardZ]; norm_num)
  obtain ⟨eZ, heZ⟩ := exists_actual_center_equiv_of_isSylowOf_zStar hW hZ2
  have hfin : Finite fullQ := Finite.of_equiv (kBar J) eJ.toEquiv
  have hfullQ : CFSG.IsQuasisimple fullQ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ
      (TwoThin.isQuasisimple_hat (P92.rig_pcomp hJ))
  obtain ⟨_, _, eF, _⟩ :=
    @actualCoverOfL34 fullQ instFullQ hfin hfullQ hL34 h16
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨eModel⟩⟩ := modelStructure
  let e4 : Subgroup.center (CFSG.GH74.GLS.kBar J) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    ((Subgroup.centerCongr eJ).trans (Subgroup.centerCongr eF).symm).trans eModel
  exact ⟨eZ, e4, heZ⟩

theorem exists_rigid_center_sylow_equiv_of_center_equiv_to
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {J S : Subgroup G} {C : Type*} [Group C]
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S
      (Subgroup.centralizer ({x} : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center (CFSG.GH74.GLS.kBar J)))
    (eQ : Subgroup.center (CFSG.GH74.GLS.kBar J) ≃* C) :
    ∃ eW : ↥(S ⊓ CFSG.GH74.GLS.zStar J) ≃* C,
      ∀ w : ↥(S ⊓ CFSG.GH74.GLS.zStar J),
        eW w = eQ ⟨CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨(w : G), w.2.2.1⟩,
          (Alt51.mem_zStar_iff_hat_mem_center (K := J)
            ⟨(w : G), w.2.2.1⟩).mp w.2.2⟩ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSI := P92.sylow_inf hJ hS
  have hW : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ zStar J) (zStar J) := by
    have h := hSI.inf_of_le_normalizer (show zStar J ≤ J from inf_le_left)
      (fun j hj => Alt51.mem_normalizer_zStar (Subgroup.le_normalizer hj))
    simpa only [inf_assoc, inf_eq_right.mpr (show zStar J ≤ J from inf_le_left)] using h
  obtain ⟨eZ, heZ⟩ := exists_actual_center_equiv_of_isSylowOf_zStar hW hZ2
  refine ⟨eZ.trans eQ, ?_⟩
  intro w
  rw [MulEquiv.trans_apply]
  rw [show eZ w = ⟨CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J
      ⟨(w : G), w.2.2.1⟩,
    (Alt51.mem_zStar_iff_hat_mem_center (K := J)
      ⟨(w : G), w.2.2.1⟩).mp w.2.2⟩ from Subtype.ext (heZ w)]

end CFSG.GH74.GLS.NT44

end
