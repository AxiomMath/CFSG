module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.ClassicalInvolution.Q3.Q3TIModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Lie

variable {G : Type} [Group G]

theorem normal_range_of_lieSystemData {ι : Type} {Φ : Set (Subgroup G)}
    (S : LieSystemData3 ι G Φ) (i : ι) : (S.hom i).range.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← S.generate]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      rw [S.commute j i hij a b]
      group
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have h2 : y = (S.hom j a)⁻¹ * S.hom i b * S.hom j a := by
        rw [hb]
        group
      rw [h2, mul_assoc, ← S.commute j i hij a b]
      group

variable {T : Subgroup G} [hTn : T.Normal] [IsSimpleGroup T]

theorem le_of_lieSystemData (hnab : ∃ a b : T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set G) = ⊥) {ι : Type} {Φ : Set (Subgroup G)}
    (S : LieSystemData3 ι G Φ) {J : Subgroup G} (hJ : J ∈ Φ) (hJ1 : J ≠ ⊥) : J ≤ T := by
  obtain ⟨i, R, -, rfl⟩ := S.fundamental J hJ
  set A := (S.hom i).range with hA
  have hJA : R.map (S.hom i) ≤ A := Subgroup.map_le_range _ _
  have hA1 : A ≠ ⊥ := fun h => hJ1 (le_bot_iff.mp (h ▸ hJA))
  have hTA : T ≤ A := le_of_normal_of_ne_bot hC (normal_range_of_lieSystemData S i) hA1
  rcases CompData.range_isQuasisimple_or_isSolvable m11Facts (S.valid i) (S.hom i)
      (S.ker_le_center i) with hqs | hsolv
  · rcases Q3T.normal_le_center_or_eq_top_qs hqs (hTn.subgroupOf A) with hcen | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : (⟨a, hTA a.2⟩ : A) ∈ Subgroup.center A :=
        hcen (Subgroup.mem_subgroupOf.mpr a.2)
      have h1 : (⟨a, hTA a.2⟩ : A) * ⟨b, hTA b.2⟩ = ⟨b, hTA b.2⟩ * ⟨a, hTA a.2⟩ :=
        (Subgroup.mem_center_iff.mp ha ⟨b, hTA b.2⟩).symm
      exact hab (Subtype.ext (congrArg (fun x : A => (x : G)) h1))
    · exact hJA.trans (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    have : Group.IsSolvable T :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hTA)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 this a b)

end Lie

section Inner

variable {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y} [hTn : T.Normal] [IsSimpleGroup T]

theorem le_of_cit3Below_of_sup_ne_top (hnab : ∃ a b : T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) (hBelow : CIT3Below (Nat.card Y)) {z : Y}
    {J : Subgroup Y} (hJ : IsClassicalMember3 J z) (hne : T ⊔ J ≠ ⊤) : J ≤ T := by
  set H : Subgroup Y := T ⊔ J with hH
  have hTH : T ≤ H := le_sup_left
  have hJH : J ≤ H := le_sup_right
  set TH : Subgroup H := T.subgroupOf H with hTHdef
  have hTHn : TH.Normal := hTn.subgroupOf H
  let eT : TH ≃* T := Subgroup.subgroupOfEquivOfLe hTH
  have : IsSimpleGroup TH := eT.isSimpleGroup
  have hnabH : ∃ a b : TH, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eT.symm a, eT.symm b, fun h => hab ?_⟩
    have := congrArg eT h
    simpa using this
  have hCH : Subgroup.centralizer (TH : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hcY : (c : Y) ∈ Subgroup.centralizer (T : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h1 := Subgroup.mem_centralizer_iff.mp hc ⟨t, hTH ht⟩
        (Subgroup.mem_subgroupOf.mpr ht)
      exact congrArg Subtype.val h1
    rw [hC, Subgroup.mem_bot] at hcY
    exact Subgroup.mem_bot.mpr (Subtype.ext hcY)
  have hJ' := hJ.subgroupOf hJH
  have hJ'1 : J.subgroupOf H ≠ ⊥ := by
    intro h
    have hm := hJ'.mem
    rw [h, Subgroup.mem_bot] at hm
    exact hJ.ne_one (congrArg Subtype.val hm)
  have hgen : Subgroup.normalClosure ((J.subgroupOf H : Subgroup H) : Set H) = ⊤ := by
    have hJle : J.subgroupOf H ≤ Subgroup.normalClosure ((J.subgroupOf H : Subgroup H) : Set H) :=
      Subgroup.subset_normalClosure
    have hTle : TH ≤ Subgroup.normalClosure ((J.subgroupOf H : Subgroup H) : Set H) :=
      le_of_normal_of_ne_bot hCH Subgroup.normalClosure_normal
        (fun h => hJ'1 (le_bot_iff.mp (h ▸ hJle)))
    have hsup : TH ⊔ J.subgroupOf H = ⊤ := by
      rw [hTHdef, ← Subgroup.subgroupOf_sup hTH hJH]
      exact Subgroup.subgroupOf_self H
    rw [eq_top_iff, ← hsup]
    exact sup_le hTle hJle
  have hΛ := Q3B.inClass3_conjClass hJ' hgen
  have hcard : Nat.card H < Nat.card Y := by
    rw [← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
  obtain ⟨ι, _, ⟨S⟩⟩ := hBelow H hcard _ hΛ
  have hOH : classicalInvolutionOddCore H = ⊥ := oddCore_eq_bot_of_normal_simple hnabH hCH
  let e : H ⧸ classicalInvolutionOddCore H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hOH).trans QuotientGroup.quotientBot
  have he : ∀ x : H, e (QuotientGroup.mk' (classicalInvolutionOddCore H) x) = x := fun x => rfl
  have hmem : J.subgroupOf H ∈ Subgroup.map e.toMonoidHom ''
      oddQuotientFamily (Q3B.conjClass (J.subgroupOf H)) := by
    refine ⟨(J.subgroupOf H).map (QuotientGroup.mk' (classicalInvolutionOddCore H)),
      ⟨J.subgroupOf H, Q3B.mem_conjClass_self _, rfl⟩, ?_⟩
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore H)) =
        MonoidHom.id H := MonoidHom.ext he
    rw [hid, Subgroup.map_id]
  have hle := le_of_lieSystemData hnabH hCH (S.congr e) hmem hJ'1
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr hx :
    (⟨x, hJH hx⟩ : H) ∈ J.subgroupOf H))

variable [IsSimpleGroup (genFittingFStar Y)]

theorem le_fstar_of_sup_ne_top (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    (hBelow : CIT3Below (Nat.card Y)) {z : Y} {J : Subgroup Y} (hJ : IsClassicalMember3 J z)
    (hne : genFittingFStar Y ⊔ J ≠ ⊤) : J ≤ genFittingFStar Y :=
  have : (genFittingFStar Y).Normal := fstar_normal
  le_of_cit3Below_of_sup_ne_top hnab (centralizer_fstar_eq_bot hnab) hBelow hJ hne

end Inner

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
