module

public import CFSG.LargeExtraspecial.S14NQSixFaith
public import CFSG.LargeExtraspecial.S14Cent
public import CFSG.LargeExtraspecial.S14NQNine
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.S14NQBasic
public import CFSG.LargeExtraspecial.S14NQSixModC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

theorem nqPlus6Stmt_of (hCE : CentralExtInput.{0}) : NQPlus6Stmt := by
  intro G _ _ _ S g t hSt hocc hext
  have h7 := claim14_7 hCE G S g t _ hSt hocc hext
  obtain ⟨⟨hΩ, hpl⟩, -, hcard⟩ := hocc
  obtain ⟨H, C, ht, ht1, hVQ, hΩc, hdim⟩ := hΩ
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  obtain ⟨Dd⟩ := S8.Std.nonempty hCE hNo hΩc
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ Dd.hgen Dd.hN0 Dd.hh Dd.hb
  have hRD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩc Dd.hN0 Dd.hh Dd.hb Dd.hX Dd.hE
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have htN := self_mem_Nbar H ht
  obtain ⟨ht', W, hW, hWs⟩ := hpl
  have hT : ∀ x ∈ W, Dd.Q x = 0 := fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    · exact (Dd.hsing x hx0).mpr (hWs x hx hx0)
  have hW3 : 3 ≤ finrank (ZMod 2) W := by omega
  obtain ⟨e₁, f₁, e₂, f₂, B⟩ := exists_hypBasis Dd.hQ hdim Dd.hQa Dd.polar_aV_bV hT hW3
  have hNQ8 : finrank (ZMod 2) (NQ S g t) = 8 :=
    finrank_NQ_of_card ht1 htt htN (e := 8) hcard
  have P : Plus6 (nqRep S g t Dd.hX) (aV ht) (bV (mem_Lbar_of_pair H ht Dd.hh)) e₁ f₁ e₂ f₂ :=
    ⟨hdim, hNQ8, aV_ne_zero H ht, Dd.hQa, Dd.Q_bV, Dd.polar_aV_bV, hRD, B,
      fun y hyF hyA => eq_one_of_fix_A0 hNo hΩc Dd hext h7.1 y hyF hyA⟩
  obtain ⟨W₁, W₂, h1, h2, d1, d2, h12, hcl⟩ := P.lattice
  have hinv : ∀ D : Subgroup S.O, zpowers t ≤ D → D ≤ Nbar S g t →
      (∀ r ∈ Rbar S g t, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
        ∀ x : omegaGroup Dd.Q Dd.hQ, ∀ v ∈ nqSub S g t D, nqRep S g t Dd.hX x v ∈ nqSub S g t D :=
    fun D htD _ hDR x _ hv => nqRep_mem_nqSub Dd.hX (htD (mem_zpowers t)) hDR x hv
  have hU : ∀ Wi : Submodule (ZMod 2) (NQ S g t),
      (∀ x : omegaGroup Dd.Q Dd.hQ, ∀ v ∈ Wi, nqRep S g t Dd.hX x v ∈ Wi) →
        ∀ r ∈ Rbar S g t, ∀ u ∈ nqPre S g t Wi, r * u * r⁻¹ ∈ nqPre S g t Wi :=
    fun Wi hWi r hr u hu => conj_mem_nqPre Dd.hX hWi hr hu
  refine ⟨nqPre S g t W₁, nqPre S g t W₂, zpowers_le_nqPre htN W₁, nqPre_le W₁,
    zpowers_le_nqPre htN W₂, nqPre_le W₂, hU W₁ h1, hU W₂ h2, ?_, ?_, ?_, ?_⟩
  · rw [nqPre_inf, h12, nqPre_bot htN]
  · rw [card_nqPre ht1 htt htN, d1]; norm_num
  · rw [card_nqPre ht1 htt htN, d2]; norm_num
  · intro D htD hDN hDR
    rcases hcl _ (hinv D htD hDN hDR) with h | h | h | h
    · left
      rw [← nqPre_nqSub htD hDN, h, nqPre_bot htN]
    · right; left
      rw [← nqPre_nqSub htD hDN, h]
    · right; right; left
      rw [← nqPre_nqSub htD hDN, h]
    · right; right; right
      refine le_antisymm hDN fun x hx => ?_
      rw [← nqPre_nqSub htD hDN, h]
      exact ⟨hx, Submodule.mem_top⟩

theorem claim14_9Plus6_of (hCE : CentralExtInput.{0}) : Claim14_9Plus6 :=
  claim14_9Plus6_of_nqPlus6 (nqPlus6Stmt_of hCE)

end CFSG.LargeExtraspecial.S14
