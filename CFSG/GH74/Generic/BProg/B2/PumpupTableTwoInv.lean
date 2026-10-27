module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
import CFSG.GH74.Generic.BProg.B1.PilotS3
import CFSG.GH74.Generic.BProg.B1.Stage3aRankRee
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.LieType.Simplicity.ReeSmall
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.Models

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5 CFSG.GH74.Generic.BProg.B2.PumpupTableBasic

@[expose] def HasTwoInvolutions {N : Type} [Group N] (L : Subgroup N) : Prop :=
  ∃ a ∈ L, ∃ b ∈ L, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b

theorem isPGroup_q8_prod : IsPGroup 2 (Q8 × Q8) := by
  refine IsPGroup.of_card (n := 6) ?_
  rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem center_eq_bot_of_perfect_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : X, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    exact Group.IsPerfect.not_isMulCommutative X ⟨⟨hc⟩⟩

theorem isQuasisimple_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N} {L : Subgroup N}
    (hs : ShapeInCent H t L) : IsQuasisimple ↥L :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hs.comp.1) hs.comp.2.1

theorem hasTwoInvolutions_of_shape1 {N : Type} [Group N] [Finite N] {L : Subgroup N}
    {Z : Subgroup ↥L} (hZ : Z.Normal) (hZo : Odd (Nat.card ↥Z)) (h1 : QShape1 (↥L ⧸ Z)) :
    HasTwoInvolutions L := by
  have := hZ
  obtain ⟨z, φ, w, -, -, hφ, -⟩ := IsSL4Model.exists_q8_frame h1
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    exact fun h => (Nat.not_even_iff_odd.mpr hZo) (even_iff_two_dvd.mpr h)
  obtain ⟨ψ, hψ, -⟩ := exists_lift_hom_two (QuotientGroup.mk' Z) hker isPGroup_q8_prod φ hφ
    (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)]; exact le_top)
  have ha2 : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide
  have ha1 : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide
  refine ⟨(ψ (QuaternionGroup.a 2, 1) : N), (ψ _).2, (ψ (1, QuaternionGroup.a 2) : N), (ψ _).2,
    ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg ψ (show ((QuaternionGroup.a 2, 1) : Q8 × Q8) * (QuaternionGroup.a 2, 1) = 1 by
      simp [ha2])
    rw [map_mul, map_one] at this
    exact congrArg Subtype.val this
  · have := congrArg ψ (show ((1, QuaternionGroup.a 2) : Q8 × Q8) * (1, QuaternionGroup.a 2) = 1 by
      simp [ha2])
    rw [map_mul, map_one] at this
    exact congrArg Subtype.val this
  · intro h
    have : ψ (QuaternionGroup.a 2, 1) = 1 := Subtype.ext h
    exact ha1 (by simpa using hψ (this.trans (map_one ψ).symm))
  · intro h
    have : ψ (1, QuaternionGroup.a 2) = 1 := Subtype.ext h
    exact ha1 (by simpa using hψ (this.trans (map_one ψ).symm))
  · intro h
    have : ψ (QuaternionGroup.a 2, 1) = ψ (1, QuaternionGroup.a 2) := Subtype.ext h
    have := hψ this
    exact ha1 (by simpa using congrArg Prod.fst this)

section Simple


theorem isSimpleGroup_of_shape345 {X : Type} [Group X] (h : QShape3 X ∨ QShape4 X ∨ QShape5 X) :
    IsSimpleGroup X := by
  rcases h with h | ⟨f, hm⟩ | h5
  · exact CFSG.GH74.Generic.BProg.B1.PilotS3.isSimpleGroup_of_qShape3 h
  · exact (CFSG.LieType.Simplicity.fam_2g2_simplicity X 3 f
      (CFSG.GH74.Generic.BProg.B1.reeTitsModel_of_lieModel_twistedG2 hm)).2
  · obtain ⟨e0⟩ := h5
    have hJ : IsSimpleGroup CFSG.Open.walterJ1 := CFSG.Walter.J1Props.J1_simple
    exact (e0.trans CFSG.Walter.walterJ1EquivNative.symm).isSimpleGroup

theorem hasTwoInvolutions_of_shape345 {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {Z : Subgroup ↥L} (hZ : Z.Normal)
    (hZc : Z ≤ Subgroup.center ↥L) (hZo : Odd (Nat.card ↥Z))
    (h : QShape3 (↥L ⧸ Z) ∨ QShape4 (↥L ⧸ Z) ∨ QShape5 (↥L ⧸ Z)) : HasTwoInvolutions L := by
  have := hZ
  have hq : IsQuasisimple ↥L := isQuasisimple_of_shapeInCent hs
  have hsimple := isSimpleGroup_of_shape345 h
  have hperf : Group.IsPerfect ↥L := hq.1
  have := hsimple
  have hcenX : Subgroup.center (↥L ⧸ Z) = ⊥ := center_eq_bot_of_perfect_of_simple
  have hcenL : Subgroup.center ↥L = Z := by
    refine le_antisymm (fun g hg => ?_) hZc
    have himg : (QuotientGroup.mk g : ↥L ⧸ Z) ∈ Subgroup.center (↥L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hg x'
    rw [hcenX, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at himg
    exact himg
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by rw [hcenL]; exact hZo
  obtain ⟨V, hV, hV4⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq hodd)
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have := hV.2 x hx
    rw [← pow_two]
    exact this
  obtain ⟨a, haV, ha1⟩ : ∃ a ∈ V, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact hcon
    rw [this, Subgroup.card_bot] at hV4
    omega
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hV2 a haV) ha1
  obtain ⟨b, hbV, hb1, hba⟩ : ∃ b ∈ V, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ Subgroup.zpowers a := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · rw [hcon x hx hx1]; exact Subgroup.mem_zpowers a
    have := Subgroup.card_le_of_le hle
    rw [hV4, Nat.card_zpowers, ha2] at this
    omega
  have hb2 : b * b = 1 := hV2 b hbV
  exact ⟨(a : N), a.2, (b : N), b.2, congrArg Subtype.val (hV2 a haV), congrArg Subtype.val hb2,
    fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h), fun h => hba (Subtype.ext h).symm⟩

theorem hasTwoInvolutions_of_shapeInCent {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) : HasTwoInvolutions L := by
  obtain ⟨Z, hZc, hZo, hZn, hsh⟩ := hs.shape
  rcases hsh with h1 | h3 | h4 | h5
  · exact hasTwoInvolutions_of_shape1 hZn hZo h1
  · exact hasTwoInvolutions_of_shape345 hs hZn hZc hZo (Or.inl h3)
  · exact hasTwoInvolutions_of_shape345 hs hZn hZc hZo (Or.inr (Or.inl h4))
  · exact hasTwoInvolutions_of_shape345 hs hZn hZc hZo (Or.inr (Or.inr h5))

end Simple

end CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv
