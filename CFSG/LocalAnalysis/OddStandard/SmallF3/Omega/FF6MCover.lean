module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MCoverAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MCoverAux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Abstract

variable {A B : Type} [Group A] [Group B] {ρ : A →* B}

theorem ff6m_cover_solvable_iff (hρ : OddCentralCover ρ) :
    Group.IsSolvable A ↔ Group.IsSolvable B := by
  constructor
  · intro hA
    haveI := hA
    exact Group.isSolvable_of_surjective (f := ρ) hρ.surjective
  · intro hB
    haveI := hB
    have hcomm : IsMulCommutative ↥ρ.ker :=
      IsMulCommutative.of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hρ.ker_le_center a.2) (b : A)).symm
    haveI := hcomm
    refine Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ ?_
    rw [Subgroup.range_subtype]

theorem ff6m_cover_twoRes (hρ : OddCentralCover ρ) :
    (twoRes (⊤ : Subgroup A)).map ρ = twoRes (⊤ : Subgroup B) := by
  unfold twoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨-, haodd⟩, rfl⟩
    exact ⟨Subgroup.mem_top _, haodd.of_dvd_nat (orderOf_map_dvd ρ a)⟩
  · rintro ⟨-, hbodd⟩
    obtain ⟨a, ha⟩ := hρ.surjective b
    refine ⟨a, ⟨Subgroup.mem_top _, ?_⟩, ha⟩
    have hker : a ^ orderOf b ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ha, pow_orderOf_eq_one]
    have hpow : (a ^ orderOf b) ^ Nat.card ρ.ker = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hker)
    have hdvd : orderOf a ∣ orderOf b * Nat.card ρ.ker := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hpow
    exact (hbodd.mul hρ.odd_card_ker).of_dvd_nat hdvd

theorem ff6m_cover_lift_involution (hρ : OddCentralCover ρ) {w : B}
    (hw : w ∈ twoRes (⊤ : Subgroup B)) (hw2 : w * w = 1) :
    ∃ u ∈ twoRes (⊤ : Subgroup A), u * u = 1 ∧ ρ u = w := by
  have hw' : w ∈ (twoRes (⊤ : Subgroup A)).map ρ := by
    rw [ff6m_cover_twoRes hρ]
    exact hw
  obtain ⟨a, ha, haρ⟩ := Subgroup.mem_map.mp hw'
  have hpow := hρ.pow_card_ker (a := a) (by rw [haρ]; exact hw2)
  exact ⟨a ^ Nat.card ρ.ker, Subgroup.pow_mem _ ha _, hpow.1, by rw [hpow.2, haρ]⟩

end Abstract

section InGroup

variable {G : Type} [Group G] [Finite G] {C : Subgroup G} {B : Type} [Group B] [Finite B]
  {ρ : ↥C →* B}

theorem ff6m_cover_isL29 (hρ : OddCentralCover ρ) (h : LayerModel B .PSL 2 2) :
    IsL29 (CFSG.inSubgroup CFSG.layer C) ∧
      twoPrimeRes (twoRes C) = CFSG.inSubgroup CFSG.layer C := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  haveI : E.Normal := hE
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psl2 hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psl2 hlie]; norm_num
  obtain ⟨⟨e⟩, hx⟩ := ff6m_cover_layer (A := ↥C) hρ E hs hnc hev hp
  have hL : IsL29 (CFSG.layer ↥C) := LieModel.of_mulEquiv e.symm hlie
  have hX : IsL29 (CFSG.inSubgroup CFSG.layer C) :=
    (ff_isL29_congr ((CFSG.layer ↥C).equivMapOfInjective C.subtype
      C.subtype_injective).symm).mpr hL
  exact ⟨hX, by rw [ff_XOut_eq_map C, hx]; rfl⟩

theorem ff6m_cover_isOmega5 (hρ : OddCentralCover ρ) (h : LayerModel B .PSp 2 1) :
    IsOmega5 (CFSG.inSubgroup CFSG.layer C) ∧
      twoPrimeRes (twoRes C) = CFSG.inSubgroup CFSG.layer C := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  haveI : E.Normal := hE
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psp hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psp hlie]; norm_num
  obtain ⟨⟨e⟩, hx⟩ := ff6m_cover_layer (A := ↥C) hρ E hs hnc hev hp
  have hL : IsOmega5 (CFSG.layer ↥C) := LieModel.of_mulEquiv e.symm hlie
  have hX : IsOmega5 (CFSG.inSubgroup CFSG.layer C) :=
    (ff_isOmega5_congr ((CFSG.layer ↥C).equivMapOfInjective C.subtype
      C.subtype_injective).symm).mpr hL
  exact ⟨hX, by rw [ff_XOut_eq_map C, hx]; rfl⟩

theorem ff6m_cover_isU33 (hρ : OddCentralCover ρ) (h : LayerModel B .PSU 3 1) :
    IsU33 (CFSG.inSubgroup CFSG.layer C) ∧
      twoPrimeRes (twoRes C) = CFSG.inSubgroup CFSG.layer C := by
  obtain ⟨E, hE, hlie, hp⟩ := h
  haveI : E.Normal := hE
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psu3 hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psu3 hlie]; norm_num
  obtain ⟨⟨e⟩, hx⟩ := ff6m_cover_layer (A := ↥C) hρ E hs hnc hev hp
  have hL : IsU33 (CFSG.layer ↥C) := LieModel.of_mulEquiv e.symm hlie
  have hX : IsU33 (CFSG.inSubgroup CFSG.layer C) :=
    (ff_lieModel_quot_oddCore_iff ((CFSG.layer ↥C).equivMapOfInjective C.subtype
      C.subtype_injective).symm (t := .PSU) (n := 3) (p := 3) (f := 1)).mpr hL
  exact ⟨hX, by rw [ff_XOut_eq_map C, hx]; rfl⟩

theorem ff6m_cover_layer_eq_bot (hρ : OddCentralCover ρ) (h : Group.IsSolvable B) :
    CFSG.inSubgroup CFSG.layer C = ⊥ := by
  have hA : Group.IsSolvable ↥C := (ff6m_cover_solvable_iff (A := ↥C) hρ).mpr h
  have hlayer : CFSG.layer ↥C = ⊥ := ff_layer_eq_bot_of_solvable (B := ↥C) hA
  unfold CFSG.inSubgroup
  rw [hlayer, Subgroup.map_bot]

theorem ff6m_cover_X_eq_pCore (hρ : OddCentralCover ρ) (h : XTwoCore B) :
    twoPrimeRes (twoRes C) = CFSG.inSubgroup (CFSG.pCore 2) (twoRes C) := by
  have hX : XTwoCore ↥C := ff6m_cover_xTwoCore (A := ↥C) hρ h
  have h2 : (CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup ↥C))).map C.subtype =
      CFSG.inSubgroup (CFSG.pCore 2) (twoRes C) := by
    rw [ff_inSubgroup_map (CFSG.pCore 2) (fun _ _ _ _ ε => CFSG.pCore_map_iso 2 ε)
      C.subtype C.subtype_injective, ff_map_twoRes _ C.subtype_injective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  unfold XTwoCore at hX
  rw [ff_XOut_eq_map C, hX, h2]

theorem ff6m_cover_lift_involution_in (hρ : OddCentralCover ρ) {w : B}
    (hw : w ∈ twoRes (⊤ : Subgroup B)) (hw2 : w * w = 1) :
    ∃ (u : G) (hu : u ∈ C), u ∈ twoRes C ∧ u * u = 1 ∧ ρ ⟨u, hu⟩ = w := by
  obtain ⟨u', hu'mem, hu'inv, hu'ρ⟩ := ff6m_cover_lift_involution (A := ↥C) hρ hw hw2
  refine ⟨(u' : G), u'.2, ?_, congrArg Subtype.val hu'inv, hu'ρ⟩
  rw [ff_twoRes_eq_map C]
  exact Subgroup.mem_map_of_mem C.subtype hu'mem

end InGroup

end CFSG.OddStandard.SmallF3.Omega