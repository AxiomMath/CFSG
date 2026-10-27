module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankSmallSources
public import CFSG.GH74.GLS.C3.Layer1.Thm1AutModel

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

theorem ringChar_ne_two_of_odd_card (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  intro h
  have hc : CharP F 2 := h ▸ ringChar.charP F
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact Nat.even_pow.2 ⟨even_two, PNat.ne_zero n⟩
  exact (Nat.not_even_iff_odd.2 hodd) this

theorem two_le_pRank_of_shape {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    2 ≤ pRank 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hr : pRank 2 (kBar K) = pRank 2 ↥K :=
    GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two (pPrimeCore 2 ↥K)
      hodd
  rw [← hr]
  rcases hshape with h | ⟨⟨e7⟩⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
    rw [Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' (e.trans (IVK.L2.equivPSL F))]
    exact ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_psl_two
      (ringChar_ne_two_of_odd_card F hF.1)
  · rw [Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' e7]
    exact ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_alternating_seven

theorem map_conj_eq_self_of_mem {G : Type} [Group G] {C : Subgroup G} {c : G} (hc : c ∈ C) :
    C.map (MulAut.conj c).toMonoidHom = C := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : (MulAut.conj c).toMonoidHom w = c * w * c⁻¹ := by simp [MulAut.conj_apply]
    rw [this]
    exact C.mul_mem (C.mul_mem hc hw) (C.inv_mem hc)
  · intro hy
    refine ⟨c⁻¹ * y * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hy) hc, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end CFSG.GH74.GLS.C3.Layer1.Thm1

