module

public import CFSG.LargeExtraspecial.AS35ESixTen
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

@[expose] def BStab : Subgroup G where
  carrier := {x | ∀ b, b ∈ S.BSet ↔ x * b * x⁻¹ ∈ S.BSet}
  mul_mem' := by
    intro x y hx hy b
    rw [hy b, hx (y * b * y⁻¹), show x * (y * b * y⁻¹) * x⁻¹ = x * y * b * (x * y)⁻¹ by group]
  one_mem' := fun b => by rw [one_mul, inv_one, mul_one]
  inv_mem' := by
    intro x hx b
    rw [hx (x⁻¹ * b * x⁻¹⁻¹), show x * (x⁻¹ * b * x⁻¹⁻¹) * x⁻¹ = b by group]

variable [Finite G]

theorem mem_BStab_iff (hS : S.SixFourConcl)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet) (hzB : S.z ∈ S.BSet)
    {x : G} : x ∈ S.BStab ↔ x * S.z * x⁻¹ ∈ S.BSet := by
  refine ⟨fun hx => (hx S.z).mp hzB, fun hx b => ?_⟩
  have hB := S.BAt_eq_BSet hS h69 hx
  constructor
  · intro hb
    have := S.conj_mem_BAt (c := x) hb
    rwa [mul_one, hB] at this
  · intro hb
    rw [← hB, S.mem_BAt_iff] at hb
    rwa [show x⁻¹ * (x * b * x⁻¹) * x = b by group] at hb

omit [Finite G] in
theorem zGen_eq_involutionPointHull :
    S.zGen = CFSG.ShultStronglyClosedTI.involutionPointHull S.z := by
  rw [zGen, CFSG.ShultStronglyClosedTI.involutionPointHull]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, CFSG.ShultStronglyClosedTI.involutionPointClass, Set.mem_range,
    CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem, isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩

omit [Finite G] in
theorem commutator_zGen_eq (hsimp : IsSimpleGroup S.zGen)
    (hC : centralizer (S.zGen : Set G) = ⊥) : ⁅S.zGen, S.zGen⁆ = S.zGen := by
  have hcomm : commutator S.zGen = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S.zGen) with h | h
    · exfalso
      have hz : S.z ∈ centralizer (S.zGen : Set G) := by
        rw [mem_centralizer_iff]
        intro l hl
        have h1 : ⁅(⟨l, hl⟩ : S.zGen), ⟨S.z, S.z_mem_zGen⟩⁆ ∈ commutator S.zGen :=
          commutator_mem_commutator (mem_top _) (mem_top _)
        rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact congrArg Subtype.val h1
      rw [hC, mem_bot] at hz
      exact S.z_ne_one hz
    · exact h
  have h1 := Subgroup.map_commutator (⊤ : Subgroup S.zGen) ⊤ S.zGen.subtype
  rw [← _root_.commutator_def, hcomm, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1.symm

theorem two_le_twoRank (hS : S.SixFourConcl) {t : G} (ht : t ∈ S.DSet) :
    2 ≤ CFSG.Open.twoRank S.zGen := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
  have htL : t ∈ S.zGen := hh ▸ S.conj_mem_zGen h
  have htM := S.mem_M_of_mem_ESet hS ht.1
  have hz2 : orderOf (⟨S.z, S.z_mem_zGen⟩ : S.zGen) = 2 := by
    rw [Subgroup.orderOf_mk, S.orderOf_z]
  have ht2 : orderOf (⟨t, htL⟩ : S.zGen) = 2 := by
    rw [Subgroup.orderOf_mk, ← hh, orderOf_conj_eq h S.z, S.orderOf_z]
  have hcomm : (⟨S.z, S.z_mem_zGen⟩ : S.zGen) * ⟨t, htL⟩ = ⟨t, htL⟩ * ⟨S.z, S.z_mem_zGen⟩ :=
    Subtype.ext (S.mem_M_iff.mp htM).symm
  have hne : (⟨S.z, S.z_mem_zGen⟩ : S.zGen) ≠ ⟨t, htL⟩ := fun h1 =>
    S.ne_z_of_mem_ESet ht.1 (congrArg Subtype.val h1).symm
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hz2 ht2 hcomm hne
  unfold CFSG.Open.twoRank CFSG.Open.pRank
  refine le_csSup ⟨Nat.card S.zGen, ?_⟩ ⟨V, le_top, ?_, by rw [hVcard]; norm_num⟩
  · rintro k ⟨E, -, -, hE⟩
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card S.zGen := card_le_card_group E
  · refine ⟨hV.toIsMulCommutative, fun x hx => ?_⟩
    have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hV.exponent_dvd_p ⟨x, hx⟩
    exact congrArg Subtype.val h1

theorem isSolvable_M_of (htop : S.zGen ⊔ S.QG = ⊤)
    (h : Group.IsSolvable (centralizer ({⟨S.z, S.z_mem_zGen⟩} : Set S.zGen))) :
    Group.IsSolvable S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := S.zGen_normal
  have hQs : Group.IsSolvable S.QG := by
    have := S.isPGroup_QG.isNilpotent
    infer_instance
  have hsurj : Function.Surjective ((QuotientGroup.mk' S.zGen).comp S.QG.subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective S.zGen y
    obtain ⟨l, hl, q, hq, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := S.zGen)).mp (htop ▸ mem_top x)
    refine ⟨⟨q, hq⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  have hGL : Group.IsSolvable (G ⧸ S.zGen) := Group.isSolvable_of_surjective hsurj
  let f : centralizer ({⟨S.z, S.z_mem_zGen⟩} : Set S.zGen) →* S.M :=
    { toFun := fun c => ⟨((c : S.zGen) : G), by
        rw [S.mem_M_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_ker_le_range f ((QuotientGroup.mk' S.zGen).comp S.M.subtype) ?_
  intro m hm
  have hmL : (m : G) ∈ S.zGen := by
    rw [MonoidHom.mem_ker] at hm
    exact (QuotientGroup.eq_one_iff _).mp hm
  refine ⟨⟨⟨m, hmL⟩, ?_⟩, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (S.mem_M_iff.mp m.2)

theorem not_isSolvable_M (h65 : S.SixFiveConcl) : ¬ Group.IsSolvable S.M := by
  intro hM
  have h1 : Group.IsSolvable S.Mbar :=
    Group.isSolvable_of_surjective (f := S.ρ.rangeRestrict) S.ρ.rangeRestrict_surjective
  have hle : closure S.DbarAsc ≤ S.Mbar := by
    rw [closure_le]
    rintro _ ⟨t, -, htM, rfl⟩
    exact ⟨⟨t, htM⟩, rfl⟩
  have h2 : Group.IsSolvable (closure S.DbarAsc) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have h3 : Group.IsSolvable (closure S.DbarAsc ⧸ center (closure S.DbarAsc)) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := h65.psu
  have h4 : Group.IsSolvable (CFSG.Open.timmesfeldPSU S.width) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hn := h65.four_le_width
  have h5 : Group.IsSolvable (CFSG.Fischer.Classification.Unitary.PG S.width) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (CFSG.LargeExtraspecial.AS35U.pgEquiv (m := S.width) (by omega)).toMonoidHom)
      (CFSG.LargeExtraspecial.AS35U.pgEquiv (m := S.width) (by omega)).injective
  have hsimp := CFSG.Fischer.Classification.Unitary.isSimpleGroup_PG hn
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr h5
  have hc := CFSG.Fischer.Classification.Unitary.center_PG hn
  have htop : center (CFSG.Fischer.Classification.Unitary.PG S.width) = ⊤ :=
    eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun y => hcomm y x
  rw [htop] at hc
  exact top_ne_bot hc

end Setting

namespace S14

@[expose] def AschbacherSixElevenFusionStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet) →
    (∀ a ∈ S.BSet, ∀ b ∈ S.BSet, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) →
      ∀ g : G, g * S.z * g⁻¹ ∈ S.BStab → g * S.z * g⁻¹ ∈ S.BSet

end S14

end CFSG.LargeExtraspecial
