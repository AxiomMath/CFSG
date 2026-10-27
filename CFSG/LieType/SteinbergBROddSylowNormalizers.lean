module

public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.LieType.SteinbergBROddSylowCore

public section

namespace CFSG.LieType.SteinbergBR.OddSylow

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

theorem isPGroup_outer_of_equiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (h : IsPGroup 2 (Outer H)) : IsPGroup 2 (Outer G) := by
  have := finite_mulAut G
  have := finite_mulAut H
  obtain ⟨m, hm⟩ := h.exists_card_eq
  exact IsPGroup.of_card (n := m) (by rw [card_outer_congr e, hm])

@[expose] noncomputable def alternatingEightEquiv :
    alternatingGroup (Fin 8) ≃* projectiveSL 4 (ZMod 2) :=
  (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm).trans
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      (CFSG.QuasithinUnique.Setup.Family.scalars_zmod_two 4).symm))

end CFSG.LieType.SteinbergBR.OddSylow

namespace CFSG.LieType

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.OddSylow

theorem small_alternating_and_binary_linear_odd_Sylow_normalizers_are_trivial
    (S : Type*) [Group S] [Finite S] (_hS : IsSimpleGroup S) (_hnab : ∃ a b : S, a * b ≠ b * a)
    (U : Sylow 2 S) (α : MulAut S) (hα : Odd (orderOf α))
    (hαU : (U : Subgroup S).map α.toMonoidHom = U)
    (hcase : (∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      ∃ (n : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 3 ≤ n ∧ Nat.card k = 2 ∧
        Nonempty (S ≃* projectiveSL n k)) :
    Subgroup.normalizer (U : Set S) = U ∧ IsPGroup 2 (Outer S) ∧ α = 1 := by
  have key : (∃ P : Sylow 2 S, Subgroup.normalizer (P : Set S) = P) ∧ IsPGroup 2 (Outer S) := by
    rcases hcase with ⟨n, hn, ⟨e⟩⟩ | ⟨n, k, _, _, hn, hk, ⟨e⟩⟩
    · rcases hn with rfl | rfl | rfl
      · obtain ⟨P, hP⟩ := SmallAlt.exists_selfNormalizing_six
        exact ⟨exists_selfNormalizing_of_equiv e P hP,
          isPGroup_outer_of_equiv e SmallAlt.isPGroup_outer_six⟩
      · obtain ⟨P, hP⟩ := SmallAlt.exists_selfNormalizing_seven
        exact ⟨exists_selfNormalizing_of_equiv e P hP,
          isPGroup_outer_of_equiv e SmallAlt.isPGroup_outer_seven⟩
      · obtain ⟨⟨P, hP⟩, hO⟩ := BinaryLinear.binary_linear_key (k := ZMod 2) (n := 4)
          (by norm_num) (Nat.card_zmod 2)
        exact ⟨exists_selfNormalizing_of_equiv (e.trans alternatingEightEquiv) P hP,
          isPGroup_outer_of_equiv (e.trans alternatingEightEquiv) hO⟩
    · obtain ⟨⟨P, hP⟩, hO⟩ := BinaryLinear.binary_linear_key hn hk
      exact ⟨exists_selfNormalizing_of_equiv e P hP, isPGroup_outer_of_equiv e hO⟩
  obtain ⟨⟨P, hP⟩, hOut⟩ := key
  have hN := normalizer_eq_of_one P hP U
  exact ⟨hN, hOut, eq_one_of_odd U hN hOut α hα hαU⟩

end CFSG.LieType
