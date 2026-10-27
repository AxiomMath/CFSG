module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32H

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_pump_data_seven (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : 7 ≤ n)
    (hmax : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n)
    {c s : X} (hc : orderOf c = 2) (hs : orderOf s = 2) (hsc : s ∈ centralizer ({c} : Set X))
    {Jc : Subgroup X} (hJcC : Jc ≤ centralizer ({s} : Set X) ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({s} : Set X) ⊓ centralizer ({c} : Set X))))
    (eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 7)) :
    ∃ N : Subgroup X, N ≤ centralizer ({c} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({c} : Set X))) ∧
      Jc ≤ N ⊔ N.map (MulAut.conj s).toMonoidHom ∧
      ((∃ r : ℕ, Odd r ∧ 7 ≤ r ∧ r ≤ n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)) ∧
          N.map (MulAut.conj s).toMonoidHom = N ∧
          IsPComponent 2 (Jc.subgroupOf (N ⊓ centralizer ({s} : Set X)))) ∨
        (N.map (MulAut.conj s).toMonoidHom = N ∧
          IsPComponent 2 (Jc.subgroupOf (N ⊓ centralizer ({s} : Set X))) ∧
          Nonempty (↥N ⧸ Open.fusionZStar ↥N ≃* Blueprint.NativeSporadic.He)) ∨
        (N.map (MulAut.conj s).toMonoidHom ≠ N ∧
          Nonempty (↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 7)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hCne : centralizer ({c} : Set X) ≠ ⊤ := centralizer_ne_top_of_ne_one hnab hc1
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({c} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top hKP hCne
  have hTY : Jc ≤ centralizer ({c} : Set X) ⊓ centralizer ({s} : Set X) := by
    rw [inf_comm]
    exact hJcC
  have hTpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({c} : Set X) ⊓ centralizer ({s} : Set X))) := by
    rw [inf_comm]
    exact hJcpc
  obtain ⟨N, hNY, hNpc, hJcN, hJcNpc, htype⟩ :=
    pump_type_in hPump hK hsc hs hTY hTpc (by decide) le_rfl eJc
  have hexact : ∀ r : ℕ, Odd r → 9 ≤ r →
      Nonempty (↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin r)) →
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)) ∧ r ≤ n := by
    rintro r hr hr9 ⟨eN⟩
    have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
    have hCc' : centralizer ((zpowers c : Subgroup X) : Set X) = centralizer ({c} : Set X) :=
      centralizer_zpowers_eq' c
    have hNC' : N ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by rw [hCc']; exact hNY
    have hNpc' : IsPComponent 2 (N.subgroupOf (centralizer ((zpowers c : Subgroup X) :
        Set X))) := by rw [hCc']; exact hNpc
    have hZ := hN1 X hnab hKP hunb hnU (zpowers c) r N hT (isPGroup_zpowers_of_mul_self hc2) hr
      hr9 hNC' hNpc' ⟨eN⟩
    have eN' : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eN
    exact ⟨⟨eN'⟩, hmax c N r ⟨hc, hNY, hNpc, ⟨eN'⟩⟩ hr⟩
  refine ⟨N, hNY, hNpc, hJcN, ?_⟩
  rcases htype with ⟨hfix, ⟨m', hm', hkm', ⟨eN⟩⟩ | ⟨-, heN⟩⟩ | ⟨hne, heN⟩
  · rw [hfix, sup_idem] at hJcNpc
    by_cases h9 : 9 ≤ m'
    · obtain ⟨hθ, hmn⟩ := hexact m' hm' h9 ⟨eN⟩
      exact Or.inl ⟨m', hm', hkm', hmn, hθ, hfix, hJcNpc⟩
    ·
      have hm7 : m' = 7 := by
        obtain ⟨a, ha⟩ := hm'
        omega
      subst hm7
      have hJcN' : Jc ≤ N := by
        have h1 := hJcN
        rwa [hfix, sup_idem] at h1
      have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNY hNpc
      exact Or.inl ⟨7, by decide, le_rfl, hn,
        nonempty_coreQuot_of_le hJcN' hNperf (by norm_num) eJc eN, hfix, hJcNpc⟩
  · rw [hfix, sup_idem] at hJcNpc
    exact Or.inr (Or.inl ⟨hfix, hJcNpc, heN⟩)
  · exact Or.inr (Or.inr ⟨hne, heN⟩)

end CFSG.ComponentClassification.SolMax
