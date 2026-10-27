module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Bar
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Card
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap510
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

theorem isL3Type_of_exc {Y : Type*} [Group Y] (h : IsSLThreeExc Y ∨ IsSUThreeExc Y) :
    IsL3Type Y := by
  rcases h with ⟨K, hK, hf, h9, ⟨e⟩⟩ | ⟨K, hK, hf, q, hc, h9, ⟨e⟩⟩
  · exact Or.inl ⟨K, hK, hf, by omega, Or.inr ⟨e⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, hc, by omega, Or.inr ⟨e⟩⟩

theorem isExtremalType_of_isLThreeEps {Y : Type*} [Group Y] (h : Lemma25Ns.IsLThreeEps Y)
    (h8 : ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ^ 2 ∧
      Nonempty (Y ≃* StatedProj (StatedSU 3 8 K))) : IsExtremalType Y := by
  rcases h with h | ⟨K, hK, hf, q, hc, hq, ⟨e⟩⟩
  · exact Or.inl h
  · refine Or.inr ⟨K, hK, hf, q, hc, hq, ?_, ⟨e⟩⟩
    rintro rfl
    exact h8 ⟨K, hK, hf, hc, ⟨e⟩⟩

theorem input14_3_L3_of_inputs (h61 : Input6_1) (h : C143Alt) : Lemma25Ns.Input14_3_L3 := by
  intro G _ _ _ _ _ X Js J b _ hL hty _ hbN hb3 hJ hexc
  have hq : CFSG.Open.IsQuasisimple (barOf 3 Js) := isQuasisimple_quotient_of_glaPComponent hL
  obtain ⟨hZp, ⟨e⟩⟩ := centre_quot_equiv hL
  obtain ⟨Jh, hJh, ⟨eJ⟩, hdvd⟩ := exists_hat_component hbN hb3 hJ
  rcases hty with hLe | hAlt
  · by_cases h8 : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ^ 2 ∧
        Nonempty ((↥Js ⧸ oPrimeP 3 ↥Js) ≃* StatedProj (StatedSU 3 8 K))
    · exfalso
      obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h8
      obtain ⟨k, hk⟩ := hZp.exists_card_eq
      have hquot : Nat.card (barOf 3 Js ⧸ Subgroup.center (barOf 3 Js)) = 5515776 := by
        rw [Nat.card_congr (e.trans f).toEquiv]
        exact card_psu_three_eight hK
      have hcard : Nat.card (barOf 3 Js) = 3 ^ k * 5515776 := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 Js)), hquot,
          hk, mul_comm]
      exact exc_card_absurd (isQuasisimple_quotient_of_glaPComponent hJ) hexc k (hcard ▸ hdvd)
    · have hty' := type_of_ext_quot h61 hL (isExtremalType_of_isLThreeEps hLe h8)
      obtain ⟨_, hfld⟩ := amb_inner gap510_Inner_holds hL hty' hbN hb3 hJ (isL3Type_of_exc hexc)
      exact fun y hy => (amb_centre gap510_Centre_holds hL hty' hbN hb3 hfld hJ).2
        ⟨oPrimePOf_le_self J hy, hy⟩
  · exfalso
    exact h (barOf 3 Js) hq hZp (isAltType_of_mulEquiv e.symm hAlt) _ (barAut_pow_three hbN hb3)
      Jh hJh (by
        rcases hexc with h1 | h1
        · exact Or.inl (isSLThreeExc_of_mulEquiv eJ h1)
        · exact Or.inr (isSUThreeExc_of_mulEquiv eJ h1))

end CFSG.HardMathSupport.Solomon.Coordinator
