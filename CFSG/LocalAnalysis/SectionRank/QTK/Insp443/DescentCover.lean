module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup

theorem map_pCore_eq_of_surjective_of_ker_le_center {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {f : A →* B} (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center A) :
    (CFSG.pCore 2 A).map f = CFSG.pCore 2 B := by
  refine le_antisymm (CFSG.LieType.BorelTits.map_pCore_le 2 f hf) ?_
  let P : Subgroup A := (CFSG.pCore 2 B).comap f
  have hPnormal : P.Normal := (CFSG.pCore_normal (p := 2) (G := B)).comap f
  let φ : P →* ↥(CFSG.pCore 2 B) :=
    (f.domRestrict P).codRestrict (CFSG.pCore 2 B) fun x => x.2
  have hφsurj : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨⟨a, hb⟩, rfl⟩
  have hφker : φ.ker ≤ Subgroup.center P := by
    intro x hx
    have hxker : (x : A) ∈ f.ker := by
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hxker) (y : A))
  haveI hPbarNil : Group.IsNilpotent ↥(CFSG.pCore 2 B) :=
    (CFSG.pCore_isPGroup (p := 2) (G := B)).isNilpotent
  haveI hPnil : Group.IsNilpotent P := Subgroup.isNilpotent_of_ker_le_center φ hφker
  let Q : Sylow 2 P := Classical.arbitrary (Sylow 2 P)
  have hQnormal : (Q : Subgroup P).Normal := Group.IsNilpotent.sylow_normal hPnil 2 Q
  have hQchar : (Q : Subgroup P).Characteristic := Sylow.characteristic_of_normal Q hQnormal
  have hQAnormal : (Q.map P.subtype).Normal := by
    have hnorm : Subgroup.normalizer (P : Set A) ≤
        Subgroup.normalizer (Q.map P.subtype : Set A) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := P)
        (Q : Subgroup P)
    rw [Subgroup.normalizer_eq_top_iff.mpr hPnormal] at hnorm
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique hnorm)
  have hQle : Q.map P.subtype ≤ CFSG.pCore 2 A :=
    CFSG.LieType.BorelTits.le_pCore 2 hQAnormal (Q.isPGroup'.map P.subtype)
  have hQtop : (Q.map φ : Subgroup ↥(CFSG.pCore 2 B)) = ⊤ := by
    have h := (Q.mapSurjective hφsurj).is_maximal'
      ((CFSG.pCore_isPGroup (p := 2) (G := B)).to_subgroup
        (⊤ : Subgroup ↥(CFSG.pCore 2 B))) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hmap : (Q.map P.subtype).map f =
      (Q.map φ).map (CFSG.pCore 2 B).subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hfQ : (Q.map P.subtype).map f = CFSG.pCore 2 B := by
    rw [hmap, hQtop, Subgroup.map_top, Subgroup.range_subtype]
  calc CFSG.pCore 2 B = (Q.map P.subtype).map f := hfQ.symm
    _ ≤ (CFSG.pCore 2 A).map f := Subgroup.map_mono hQle

theorem center_quot_pCore_of_le {K : Type} [Group K] [Finite K] {Z L : Subgroup K} [Z.Normal]
    (hZ : Z ≤ Subgroup.center K) (hodd : Odd (Nat.card Z)) (hZL : Z ≤ L)
    (hc : Subgroup.center (↥(L.map (QuotientGroup.mk' Z)) ⧸
      CFSG.pCore 2 ↥(L.map (QuotientGroup.mk' Z))) = ⊥) :
    Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = Nat.card Z ∧
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ↥(L.map (QuotientGroup.mk' Z)) ⧸ CFSG.pCore 2 ↥(L.map (QuotientGroup.mk' Z))) := by
  classical
  let q : K →* K ⧸ Z := QuotientGroup.mk' Z
  let Lbar : Subgroup (K ⧸ Z) := L.map q
  let qL : L →* Lbar := q.subgroupMap L
  have hqL : Function.Surjective qL := q.subgroupMap_surjective L
  let P : Subgroup L := CFSG.pCore 2 L
  let Pbar : Subgroup Lbar := CFSG.pCore 2 Lbar
  have hqLker : qL.ker = Z.subgroupOf L := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : q (x : K) = 1 := by
        have h2 : ((qL x : Lbar) : K ⧸ Z) = ((1 : Lbar) : K ⧸ Z) :=
          congrArg (fun y : Lbar => (y : K ⧸ Z)) hx
        rw [MonoidHom.subgroupMap_apply_coe] at h2
        simpa using h2
      rw [Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff (x : K)).mp hx'
    · intro hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one]
      exact (QuotientGroup.eq_one_iff (x : K)).mpr (Subgroup.mem_subgroupOf.mp hx)
  have hqLker_center : qL.ker ≤ Subgroup.center L := by
    rw [hqLker]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext
      (Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hx)) (y : K))
  have hPmap : P.map qL = Pbar :=
    map_pCore_eq_of_surjective_of_ker_le_center hqL hqLker_center
  haveI : P.Normal := CFSG.pCore_normal
  haveI : Pbar.Normal := CFSG.pCore_normal
  have hle : P ≤ Subgroup.comap qL Pbar :=
    Subgroup.map_le_iff_le_comap.mp (le_of_eq hPmap)
  let ρ : (L ⧸ P) →* (Lbar ⧸ Pbar) := QuotientGroup.map P Pbar qL hle
  have hρsurj : Function.Surjective ρ := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨l, rfl⟩ := hqL x
      exact ⟨QuotientGroup.mk l, by
        change (QuotientGroup.map P Pbar qL hle) (QuotientGroup.mk l) =
          QuotientGroup.mk (qL l)
        rw [QuotientGroup.map_mk]⟩
  have hker_eq : ρ.ker = (qL.ker).map (QuotientGroup.mk' P) := by
    have hcomap : Subgroup.comap qL Pbar = P ⊔ qL.ker := by
      rw [← hPmap]
      exact Subgroup.comap_map_eq qL P
    change (QuotientGroup.map P Pbar qL hle).ker = _
    rw [QuotientGroup.ker_map, hcomap, Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq]
  have hcenter_le_ker : Subgroup.center (L ⧸ P) ≤ ρ.ker := by
    intro x hx
    have hx' : ρ x ∈ Subgroup.center (Lbar ⧸ Pbar) :=
      Subgroup.map_center_le_center hρsurj (Subgroup.mem_map_of_mem ρ hx)
    rw [hc, Subgroup.mem_bot] at hx'
    exact MonoidHom.mem_ker.mpr hx'
  have hker_le_center : ρ.ker ≤ Subgroup.center (L ⧸ P) := by
    rw [hker_eq]
    calc (qL.ker).map (QuotientGroup.mk' P)
        ≤ (Subgroup.center L).map (QuotientGroup.mk' P) := Subgroup.map_mono hqLker_center
      _ ≤ Subgroup.center (L ⧸ P) :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective P)
  have hcenter_eq : Subgroup.center (L ⧸ P) = ρ.ker :=
    le_antisymm hcenter_le_ker hker_le_center
  have hPcop : Nat.Coprime (Nat.card (Z.subgroupOf L)) (Nat.card P) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    have hZodd : Odd (Nat.card (Z.subgroupOf L)) := by
      rw [show Nat.card (Z.subgroupOf L) = Nat.card Z from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]
      exact hodd
    rw [hn]
    exact (hZodd.coprime_two_right).pow_right n
  have hinf : qL.ker ⊓ P = ⊥ := by
    rw [hqLker]
    exact Subgroup.inf_eq_bot_of_coprime hPcop
  have hcard_image : Nat.card ((qL.ker).map (QuotientGroup.mk' P)) = Nat.card (qL.ker) := by
    refine CFSG.card_map_eq_card_of_inf_ker_eq_bot (QuotientGroup.mk' P) ?_
    rw [QuotientGroup.ker_mk']
    exact hinf
  have hcard_ker : Nat.card (qL.ker) = Nat.card Z := by
    rw [hqLker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv
  have hcard_center : Nat.card (Subgroup.center (L ⧸ P)) = Nat.card Z := by
    rw [hcenter_eq, hker_eq]
    calc Nat.card ((qL.ker).map (QuotientGroup.mk' P)) = Nat.card (qL.ker) := hcard_image
      _ = Nat.card Z := hcard_ker
  refine ⟨hcard_center, ⟨(QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj)⟩⟩

end CFSG.SectionRank.QTK.Insp443

end
