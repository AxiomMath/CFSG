module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.LargeExtraspecial.O62Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open Module

namespace Sec2

section Model

variable {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsExtraspecialPGroup 2 Q)

omit [Finite Q] in
include hQ in
theorem natCard_abelianization (h128 : Nat.card Q = 2 ^ 7) :
    Nat.card (Additive (Abelianization Q)) = 64 := by
  have hcomm : Nat.card (commutator Q) = 2 := by
    rw [hQ.2.1]
    exact hQ.2.2.2
  have h := Subgroup.card_mul_index (commutator Q)
  rw [hcomm, h128] at h
  change (commutator Q).index = 64
  omega

variable [Module (ZMod 2) (Additive (Abelianization Q))]

include hQ in
theorem finrank_abelianization (h128 : Nat.card Q = 2 ^ 7) :
    finrank (ZMod 2) (Additive (Abelianization Q)) = 6 := by
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Abelianization Q))
  rw [natCard_abelianization hQ h128, Nat.card_zmod] at h
  have h6 : (2 : ℕ) ^ 6 = 2 ^ finrank (ZMod 2) (Additive (Abelianization Q)) := by
    rw [← h]
    norm_num
  exact (Nat.pow_right_injective (le_refl 2) h6).symm

theorem not_isPlus (h128 : Nat.card Q = 2 ^ 7)
    (hno : ¬ ∃ U : Subgroup Q, IsElemAbelian 2 U ∧ Nat.card U = 16) :
    ¬ LargeExtraspecial.O62.IsPlus
      (CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ) := by
  classical
  rintro ⟨W, hW3, hW0⟩
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  have hWcard : Nat.card W = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod, show finrank (ZMod 2) W = 3 by omega] at h
    rw [h]
    norm_num
  let W' : Subgroup (Abelianization Q) :=
    { carrier := {a | Additive.ofMul a ∈ W}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul (a * b) ∈ W
        rw [ofMul_mul]
        exact W.add_mem ha hb
      one_mem' := by
        change Additive.ofMul (1 : Abelianization Q) ∈ W
        rw [ofMul_one]
        exact W.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul a⁻¹ ∈ W
        rw [ofMul_inv]
        exact W.neg_mem ha }
  have hW'card : Nat.card W' = 8 := by
    rw [← hWcard]
    exact Nat.card_congr
      { toFun := fun a => ⟨Additive.ofMul a.1, a.2⟩
        invFun := fun w => ⟨Additive.toMul w.1, w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hW'idx : W'.index = 8 := by
    have h := Subgroup.card_mul_index W'
    rw [hW'card, show Nat.card (Abelianization Q) = 64 from natCard_abelianization hQ h128] at h
    omega
  let U : Subgroup Q := W'.comap Abelianization.of
  have hUidx : U.index = 8 := by
    rw [Subgroup.index_comap_of_surjective W' QuotientGroup.mk_surjective, hW'idx]
  have hUcard : Nat.card U = 16 := by
    have h := Subgroup.card_mul_index U
    rw [hUidx, h128] at h
    omega
  apply hno
  refine ⟨U, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hUcard⟩
  · have ha : Additive.ofMul (Abelianization.of (a : Q)) ∈ W := a.2
    have hb : Additive.ofMul (Abelianization.of (b : Q)) ∈ W := b.2
    have hp : QuadraticMap.polar (CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ)
        (Additive.ofMul (Abelianization.of (a : Q)))
        (Additive.ofMul (Abelianization.of (b : Q))) = 0 := by
      rw [QuadraticMap.polar, hW0 _ (W.add_mem ha hb), hW0 _ ha, hW0 _ hb, sub_zero, sub_zero]
    exact (CFSG.RankThree.Literature.FSmith.polar_extraspecialQuadForm_eq_zero_iff hQ _ _).mp hp
  · have hq := hW0 _ (show Additive.ofMul (Abelianization.of x) ∈ W from hx)
    rw [CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_apply] at hq
    split_ifs at hq with hne
    · exact hne
    · exact absurd hq one_ne_zero

theorem exists_linearEquiv_qMinus (h128 : Nat.card Q = 2 ^ 7)
    (hno : ¬ ∃ U : Subgroup Q, IsElemAbelian 2 U ∧ Nat.card U = 16) :
    ∃ L : Additive (Abelianization Q) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2), ∀ v,
      LargeExtraspecial.O62.qMinus (L v) =
        CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hQ v := by
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  exact LargeExtraspecial.O62.exists_linearEquiv_qMinus (finrank_abelianization hQ h128)
    (CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_nondegenerate hQ)
    (not_isPlus hQ h128 hno)

end Model

theorem exists_psi {G : Type} [Group G] [Finite G] {Q : Subgroup G} {z : G} (hQ8 : IsQ8Cube Q)
    (hcen : centerIn Q = zpowers z) :
    ∃ ψ : G → (Fin 6 → ZMod 2), (∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b) ∧
      (∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v) ∧ (∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z) ∧
      (∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) := by
  classical
  have hext : CFSG.IsExtraspecialPGroup 2 ↥Q := hQ8.1
  let _ := CFSG.GroupTheory.extraspecialQuotientModule hext
  have hno : ¬ ∃ U : Subgroup ↥Q, IsElemAbelian 2 U ∧ Nat.card U = 16 := by
    rintro ⟨U, hU, hU16⟩
    apply hQ8.2.2
    refine ⟨U.map Q.subtype, map_subtype_le U, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      show (a : G) * b = b * a
      exact congrArg Subtype.val (congrArg Subtype.val (hU.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := hU.2 a ha
      change (a : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    · rw [card_map_of_injective Q.subtype_injective, hU16]
  obtain ⟨L, hL⟩ := exists_linearEquiv_qMinus hext hQ8.2.1 hno
  let ψ : G → (Fin 6 → ZMod 2) := fun a =>
    if h : a ∈ Q then L (Additive.ofMul (Abelianization.of (⟨a, h⟩ : ↥Q))) else 0
  have hψ : ∀ a (h : a ∈ Q), ψ a = L (Additive.ofMul (Abelianization.of (⟨a, h⟩ : ↥Q))) :=
    fun a h => by simp [ψ, h]
  refine ⟨ψ, fun a ha b hb => ?_, fun v => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · rw [hψ _ (Q.mul_mem ha hb), hψ a ha, hψ b hb, ← map_add,
      ← CFSG.RankThree.Literature.FSmith.ofMul_of_mul]
    rfl
  · obtain ⟨x, hx⟩ := CFSG.RankThree.Literature.FSmith.exists_ofMul_of (L.symm v)
    refine ⟨x, x.2, ?_⟩
    rw [hψ _ x.2]
    simp [hx]
  · rw [hψ a ha, LinearEquiv.map_eq_zero_iff,
      CFSG.RankThree.Literature.FSmith.ofMul_of_eq_zero_iff hext, ← hcen]
    constructor
    · intro h
      exact ⟨ha, mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (mem_center_iff.mp h ⟨y, hy⟩)⟩
    · rintro ⟨-, hc⟩
      exact mem_center_iff.mpr fun h => Subtype.ext (mem_centralizer_iff.mp hc h h.2)
  · have h1 := hL (Additive.ofMul (Abelianization.of (⟨a, ha⟩ : ↥Q)))
    rw [LargeExtraspecial.O62.qMinus_apply] at h1
    have e : qMinus (ψ a) = CFSG.RankThree.Literature.FSmith.extraspecialQuadForm hext
        (Additive.ofMul (Abelianization.of (⟨a, ha⟩ : ↥Q))) := by
      rw [hψ a ha, ← h1]
      rfl
    have hsq : (⟨a, ha⟩ : ↥Q) ^ 2 = 1 ↔ a * a = 1 := by
      rw [← sq, Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]
    rw [e, CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_apply]
    split_ifs with h
    · exact ⟨fun _ => hsq.mp h, fun _ => rfl⟩
    · exact ⟨fun h' => absurd h' one_ne_zero, fun h' => absurd (hsq.mpr h') h⟩

end Sec2

end CFSG.ComponentClassification.AS81
