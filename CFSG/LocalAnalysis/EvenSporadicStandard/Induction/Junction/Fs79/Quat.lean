module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.DisconnectedInvolutionGraph.Helpers

theorem two_le_pRank_of_commuting_involutions {X : Type} [Group X] [Finite X] {x y : X}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    2 ≤ CFSG.pRank 2 X := by
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hx hy
      hxy hne
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨V, hV, by rw [hVcard]; norm_num⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group B

theorem sylow_cyclic_or_quaternion {X : Type} [Group X] [Finite X] (hr : CFSG.pRank 2 X = 1)
    (P : Sylow 2 X) :
    IsCyclic ↥P ∨ ∃ e : ℕ, 1 ≤ e ∧ Nonempty (QuaternionGroup (2 ^ e) ≃* ↥P) := by
  refine rank_one_two_cyclic_or_quaternion P.isPGroup' ?_
  intro first second hcomm
  by_contra hne
  have hx : orderOf ((first.1 : ↥P) : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact first.2
  have hy : orderOf ((second.1 : ↥P) : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact second.2
  have hxy : ((first.1 : ↥P) : X) * ((second.1 : ↥P) : X) =
      ((second.1 : ↥P) : X) * ((first.1 : ↥P) : X) := congrArg Subtype.val hcomm
  have hne' : ((first.1 : ↥P) : X) ≠ ((second.1 : ↥P) : X) := fun h =>
    hne (Subtype.ext (Subtype.ext h))
  have := two_le_pRank_of_commuting_involutions hx hy hxy hne'
  omega

theorem quaternion_gen (m : ℕ) [NeZero m] :
    Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup m) ⊔
      Subgroup.zpowers (QuaternionGroup.xa 0) = ⊤ := by
  have : NeZero (2 * m) := ⟨by have := NeZero.pos m; omega⟩
  have hapow : ∀ i : ZMod (2 * m),
      (QuaternionGroup.a i : QuaternionGroup m) ∈ Subgroup.zpowers (QuaternionGroup.a 1) :=
    fun i => Subgroup.mem_zpowers_iff.2 ⟨i.val, by
      rw [zpow_natCast, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]⟩
  rw [eq_top_iff]
  intro x _
  cases x with
  | a i => exact Subgroup.mem_sup_left (hapow i)
  | xa i =>
    have : (QuaternionGroup.xa i : QuaternionGroup m) =
        QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_left (hapow i))

theorem quaternion_rel (m : ℕ) [NeZero m] :
    (QuaternionGroup.xa 0 : QuaternionGroup m) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0 : QuaternionGroup m)⁻¹ * QuaternionGroup.a 1 = 1 := by
  have hm : (m : ZMod (2 * m)) + m = 0 := by
    simpa only [two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)
  have hinv : (QuaternionGroup.xa 0 : QuaternionGroup m)⁻¹ =
      QuaternionGroup.xa (m : ZMod (2 * m)) :=
    inv_eq_of_mul_eq_one_right (by
      rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.one_def]
      congr 1
      linear_combination hm)
  rw [hinv, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa, QuaternionGroup.a_mul_a,
    QuaternionGroup.one_def]
  congr 1
  linear_combination hm

theorem mem_center_of_mk_mem_center_oddCore {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) {t : X}
    (ht : (QuotientGroup.mk t : X ⧸ CFSG.oddCore X) ∈ Subgroup.center (X ⧸ CFSG.oddCore X)) :
    t ∈ center X := by
  have hO : CFSG.oddCore X ≤ center X := oddCore_le_center_of_isQuasisimple hq
  let f : X ⧸ CFSG.oddCore X →* X ⧸ center X :=
    QuotientGroup.map (CFSG.oddCore X) (center X) (MonoidHom.id X) hO
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk y', rfl⟩
  have hc : f (QuotientGroup.mk t) ∈ Subgroup.center (X ⧸ center X) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := hf y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ht y']
  have hbot : Subgroup.center (X ⧸ center X) = ⊥ := by
    have := hq.2.1
    rcases (Subgroup.center (X ⧸ center X)).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hq.2.2
      exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a) hab
  rw [hbot, Subgroup.mem_bot] at hc
  have : (QuotientGroup.mk t : X ⧸ center X) = 1 := hc
  exact (QuotientGroup.eq_one_iff t).1 this

end CFSG.EvenSporadicStandard.Induction.Junction
