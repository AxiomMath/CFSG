module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.GammaLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndN1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

namespace EndN

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x : G} {q : ℕ} {W D₁ D₂ : Subgroup G}

namespace Data

variable (E : Data T M H S L D n t M₀ x q W D₁ D₂)
include E

omit [Finite G] E in
theorem U₂_eq : blockU (conjR L t) = conjR (blockU L) t := DoubleA3.blockU_conjR L t

theorem U₁_le_R₁ : blockU L ≤ thompsonJ S ⊓ L := le_inf E.B.U₁_le_R (blockU_le L)

theorem normalizer_L₂_le_U₂ : Subgroup.normalizer ((conjR L t : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((blockU (conjR L t) : Subgroup G) : Set G) := by
  intro g hg
  rw [← conjR_eq_self_iff, ← E.B.pCore_L₂, ← conjR_pCoreOf, conjR_eq_of_mem_normalizer hg]

theorem L₂_le_normalizer_R₁ : conjR L t ≤
    Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => E.B.comm_elem a ha.2 b hb

theorem not_L₂_le_M : ¬ conjR L t ≤ M := by
  intro h
  have htM : t ∈ M := E.cs.setting.le (E.B.S_le_T E.B.ht)
  have h1 := conjR_mono h t⁻¹
  rw [conjR_conjR_inv, conjR_eq_of_mem (M.inv_mem htM)] at h1
  exact E.cs.not_le h1

theorem U₂_ne_conj : blockU (conjR L t) ≠ conjR (blockU (conjR L t)) x := by
  intro h
  have O : S2Ok T M H S L D n t M₀ x q W D₁ D₂ := ⟨E.B, E.hT₁, E.hT₂, E.hD, E.hC, E.hDx⟩
  have h1 : blockU (conjR L t) ⊓ conjR (blockU (conjR L t)) x = conjR W t := O.UT3_R₂.inf_eq
  rw [← h, inf_idem] at h1
  have h2 := O.UT3_R₂.card_U
  have h3 := O.UT3_R₂.card_W
  rw [h1, h3] at h2
  have hq := O.UT3_R₂.one_lt
  nlinarith

theorem isSylowTwoOf_normalizer_R₁ {S₂ : Subgroup G} (hS₂T : S₂ ≤ T)
    (hS₂R₁ : S₂ ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G))
    (hS₂U₂ : S₂ ≤ Subgroup.normalizer ((blockU (conjR L t) : Subgroup G) : Set G))
    (hR1 : AppE.R1 S L ≤ S₂) (hcard : Nat.card S ≤ Nat.card S₂) :
    IsSylowTwoOf S₂ (Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) := by
  have hT2 : IsPGroup 2 T := E.B.T_isPGroup
  have hS₂2 : IsPGroup 2 S₂ := hT2.to_le hS₂T
  have hS₂M : S₂ ≤ M := hS₂T.trans E.cs.setting.le
  have hR₁S : thompsonJ S ⊓ L ≤ S := inf_le_left.trans (thompsonJ_le_self S)
  have hU₂R : blockU (conjR L t) ≤ thompsonJ S := E.B.U₂_le_R
  have hXS : thompsonJ S ⊓ L ⊔ blockU (conjR L t) ≤ S :=
    sup_le hR₁S (hU₂R.trans (thompsonJ_le_self S))
  set X : Subgroup G := thompsonJ S ⊓ L ⊔ blockU (conjR L t) with hX
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN
  have hX2 : IsPGroup 2 X := hT2.to_le (hXS.trans E.B.S_le_T)
  have hXne : X ≠ ⊥ := fun h => E.B.R₁_ne_bot (le_bot_iff.1 (h ▸ le_sup_left))
  have hS₂N : S₂ ≤ N := by
    intro g hg
    rw [hN, ← conjR_eq_self_iff, hX, conjR_sup, conjR_eq_of_mem_normalizer (hS₂R₁ hg),
      conjR_eq_of_mem_normalizer (hS₂U₂ hg)]
  have hL₂U : conjR L t ≤ Subgroup.normalizer ((blockU (conjR L t) : Subgroup G) : Set G) := by
    intro g hg
    have := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (conjR L t) hg
    rwa [E.B.pCore_L₂] at this
  have hL₂N : conjR L t ≤ N := by
    intro g hg
    rw [hN, ← conjR_eq_self_iff, hX, conjR_sup,
      conjR_eq_of_mem_normalizer (E.L₂_le_normalizer_R₁ hg), conjR_eq_of_mem_normalizer (hL₂U hg)]
  have hTne : T ≠ ⊥ := fun h =>
    E.B.R₁_ne_bot (le_bot_iff.1 (h ▸ hR₁S.trans E.B.S_le_T))
  obtain ⟨z, hzT, hz1, hzc⟩ :=
    exists_mem_inf_center_of_normal hT2 le_rfl Subgroup.le_normalizer hTne
  have hQS : pCoreOf 2 H ≤ S :=
    E.B.sylow.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hzQ : z ∈ pCoreOf 2 H := by
    have hzS : z ∈ S := E.cs.center_le ⟨hzT, hzc⟩
    have hct : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := E.cs.charTwo
    have hzcQ : z ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun p hp =>
        Subgroup.mem_centralizer_iff.1 hzc p (E.B.S_le_T (hQS hp))
    exact hct ⟨E.B.S_le_H hzS, hzcQ⟩
  have hQX : pCoreOf 2 H ≤ X := by
    rw [E.pCore_eq, hX]
    exact sup_le_sup E.U₁_le_R₁ (U₂_eq (L := L) (t := t)).symm.le
  have hzDZ : X ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := fun h =>
    hz1 (Subgroup.mem_bot.1 (h ▸ (⟨hQX hzQ, hzT, hzc⟩ :
      z ∈ X ⊓ (T ⊓ Subgroup.centralizer (T : Set G)))))
  have hCharN : CharTwo N :=
    charTwo_normalizer_of_inf_center E.cs.setting.qtke.2.1 E.cs.setting.sylow hX2 hzDZ
  have hconf : IsConfining M S₂ := E.B.isConfining_R1.of_le hS₂2 hR1
  have hpcoreN : pCoreOf 2 N ≠ ⊥ := fun h => hXne (le_bot_iff.1 (h ▸
    le_pCoreOf_of_normalizes (Subgroup.le_normalizer : X ≤ N) le_rfl hX2))
  have hNM : ¬ N ≤ M := fun h => E.not_L₂_le_M (hL₂N.trans h)
  have hpN : IsWitnessPair M S₂ N := ⟨hconf, hS₂N, hpcoreN, hCharN, hNM⟩
  have hH : IsGamma0 M H := E.cs.gamma0
  have hSH : Nat.card S = twoPart H := E.cs.sylow.card_eq
  have hleN : twoPart H ≤ twoPart N := by
    rw [← hSH]
    exact hcard.trans (card_le_twoPart hS₂N hS₂2)
  obtain ⟨hNeq, -, -, -⟩ := IsGamma0.of_isWitnessPair_of_twoPart_le E.cs.setting hH hpN hleN
  have hSylN : IsSylowTwoOf S₂ N :=
    (isSylowTwoOf_of_twoPart_le hS₂N hS₂M hS₂2 (by rw [hNeq, ← hSH]; exact hcard)).1
  have hPNS₂ : pCoreOf 2 N ≤ S₂ :=
    hSylN.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N)
  set H₁ : Subgroup G := S₂ ⊔ conjR L t with hH₁
  have hH₁N : H₁ ≤ N := sup_le hS₂N hL₂N
  have hCharH₁ : CharTwo H₁ :=
    charTwo_of_pCore_centralizer_le hCharN hH₁N (inf_le_left.trans (hPNS₂.trans le_sup_left))
  have hR₁S₂ : thompsonJ S ⊓ L ≤ S₂ := fun r hr =>
    hR1 (AppE.mem_R1_iff.2 ⟨hR₁S hr, conjR_eq_of_mem_normalizer (Subgroup.le_normalizer hr.2)⟩)
  have hXH₁ : X ≤ H₁ := sup_le (hR₁S₂.trans le_sup_left)
    ((blockU_le _).trans le_sup_right)
  have hpcoreH₁ : pCoreOf 2 H₁ ≠ ⊥ := fun h => hXne (le_bot_iff.1 (h ▸
    le_pCoreOf_of_normalizes hXH₁ hH₁N hX2))
  have hpH₁ : IsWitnessPair M S₂ H₁ :=
    ⟨hconf, le_sup_left, hpcoreH₁, hCharH₁, fun h => E.not_L₂_le_M (le_sup_right.trans h)⟩
  have hleH₁ : twoPart H ≤ twoPart H₁ := by
    rw [← hSH]
    exact hcard.trans (card_le_twoPart (le_sup_left : S₂ ≤ H₁) hS₂2)
  obtain ⟨hH₁eq, hH₁0, -, -⟩ := IsGamma0.of_isWitnessPair_of_twoPart_le E.cs.setting hH hpH₁ hleH₁
  have hSylH₁ := isSylowTwoOf_of_twoPart_le (le_sup_left : S₂ ≤ H₁) hS₂M hS₂2
    (by rw [hH₁eq, ← hSH]; exact hcard)
  have hH₁K : H₁ ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
    sup_le hS₂R₁ E.L₂_le_normalizer_R₁
  have hR₁2 : IsPGroup 2 (thompsonJ S ⊓ L : Subgroup G) := hT2.to_le (hR₁S.trans E.B.S_le_T)
  have hpcoreK : pCoreOf 2 (Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) ≠ ⊥ :=
    fun h => E.B.R₁_ne_bot (le_bot_iff.1 (h ▸
      le_pCoreOf_of_normalizes (Subgroup.le_normalizer : thompsonJ S ⊓ L ≤ _) le_rfl hR₁2))
  have hΓK := hpH₁.isGamma_of_le hH₁K hpcoreK
  exact (IsGamma0.overgroup_of_le E.cs.setting hH₁0 hSylH₁.2 hΓK hH₁K).2.1

end Data

end EndN

end CFSG.QuasithinUnique.Lin2
