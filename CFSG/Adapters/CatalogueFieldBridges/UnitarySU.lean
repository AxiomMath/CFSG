module

public import CFSG.Open.StatedSUFieldChange
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Adapters.CatalogueFieldBridges

open CFSG.Open

theorem exists_twistedA_mulEquiv_centerQuotient_statedSU {K : Type} [Field K] [Fintype K]
    {m q : ℕ} (hK : Fintype.card K = q ^ 2) (hm : 3 ≤ m) (hne : (m, q) ≠ (3, 2)) :
    ∃ (q' : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA (m - 1) q').Valid),
      q'.p = ringChar K ∧ q'.card = q ∧
        Nonempty (↥(StatedSU m q K) ⧸ Subgroup.center ↥(StatedSU m q K) ≃*
          (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA (m - 1) q', hv⟩).Group) := by
  classical
  haveI := ringChar.charP K
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Fintype.card K := Fintype.one_lt_card
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> simp at hK
      all_goals omega
    · exact h
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hqf
      omega
    · exact h0
  subst hqf
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨hp⟩
  have hNat : Nat.card K = (ringChar K ^ f) ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hK
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat hm hne
  let q' : TauCeti.PrimePower := ⟨ringChar K, f, hp, hf⟩
  have hq'p : q'.p = ringChar K := rfl
  have hq'card : q'.card = ringChar K ^ f := by simp [q']
  have hv : (TauCeti.LieTypeIndex.twistedA (m - 1) q').Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨by omega, fun hr => ?_⟩
    rw [hq'card]
    by_contra h3
    exact hne (by rw [show m = 3 by omega, show ringChar K ^ f = 2 by omega])
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (m - 1) q' hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at e₀
  have hKK : Fintype.card K = Fintype.card K₀ := by
    rw [hK, Fintype.card_eq_nat_card (α := K₀), hK₀]
  let eK : K ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK m (ringChar K ^ f)
  let eC := QuotientGroup.quotientMulEquivOfEq hQ.2
  exact ⟨q', hv, hq'p, hq'card, ⟨(eC.trans eP).trans e₀.symm⟩⟩

end CFSG.Adapters.CatalogueFieldBridges

end
