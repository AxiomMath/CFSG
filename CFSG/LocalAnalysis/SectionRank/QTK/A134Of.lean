module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134Defs
import CFSG.LocalAnalysis.SectionRank.QTK.A134PiB
import CFSG.LocalAnalysis.SectionRank.QTK.A134Frob

public section

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.LocalCores CFSG.Quasithin.A3Facts

theorem IsoComponentBound.of_pi {H : Type} [Group H] [Finite H] {r : ℕ} (hr : r.Prime)
    (hPi : ∀ R : Subgroup (∀ K : ComponentIndex H, ↥K.1 ⧸ center ↥K.1), R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank r
        (normalizer (R : Set (∀ K : ComponentIndex H, ↥K.1 ⧸ center ↥K.1))) ≤ 2) :
    IsoComponentBound H r := by
  refine ⟨fun L₁ L₂ h₁ h₂ hne _ R hR hR2 => ?_,
    fun L₁ L₂ L₃ h₁ h₂ h₃ h12 h13 h23 _ _ R hR hR2 => ?_⟩
  · exact pi_pair_pRank_le (S := fun K : ComponentIndex H => ↥K.1 ⧸ center ↥K.1) hr.one_lt hPi
      (i₁ := ⟨L₁, h₁⟩) (i₂ := ⟨L₂, h₂⟩) (fun h => hne (congrArg Subtype.val h)) hR hR2
  · exact pi_triple_pRank_le (S := fun K : ComponentIndex H => ↥K.1 ⧸ center ↥K.1) hr.one_lt hPi
      (i₁ := ⟨L₁, h₁⟩) (i₂ := ⟨L₂, h₂⟩) (i₃ := ⟨L₃, h₃⟩) (fun h => h12 (congrArg Subtype.val h))
      (fun h => h13 (congrArg Subtype.val h)) (fun h => h23 (congrArg Subtype.val h)) hR hR2

theorem a134Fact_of'
    (hL : QTLayerCentreFactOne) (hList : QTA134List) :
    CFSG.Quasithin.A134Fact := by
  intro H _ _ hQT hK L₁ L₂ h₁ h₂ hne ⟨e⟩
  by_cases hexc : ∃ M₁ M₂ : Subgroup H, CFSG.IsComponent M₁ ∧ CFSG.IsComponent M₂ ∧
      M₁ ≠ M₂ ∧ CFSG.layer H = M₁ ⊔ M₂ ∧ (Nonempty (↥M₁ ≃* ↥M₂) →
        CFSG.Quasithin.IsSU3 8 ↥M₁ ∧ CFSG.Open.pRank 3 (M₁ ⊔ M₂) = 3)
  · obtain ⟨M₁, M₂, hM₁, hM₂, hMne, hlayer, hsu⟩ := hexc
    have hc : ∀ {L : Subgroup H}, CFSG.IsComponent L → L = M₁ ∨ L = M₂ := fun hL =>
      eq_or_eq_of_layer_eq_sup hM₁ hM₂ hlayer hL
    rcases hc h₁ with h1 | h1 <;> rcases hc h₂ with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1 h2
      exact ⟨fun L hL _ => hc hL, Or.inr (hsu ⟨e⟩)⟩
    · subst h1 h2
      obtain ⟨hsu1, hsu2⟩ := hsu ⟨e.symm⟩
      refine ⟨fun L hL _ => (hc hL).symm, Or.inr ⟨isSU3_of_mulEquiv e hsu1, ?_⟩⟩
      rw [sup_comm]
      exact hsu2
    · exact absurd (h1.trans h2.symm) hne
  · have hbound : ∀ r : ℕ, r.Prime → r ≠ 2 → IsoComponentBound H r := by
      intro r hr hr2
      by_cases hrZ : r ∣ Nat.card (center ↥(CFSG.layer H))
      · rcases hL H hQT hK r hr hr2 hrZ with hb | ⟨-, hex⟩
        · exact hb
        · exact absurd hex hexc
      · exact IsoComponentBound.of_pi hr (pRank_normalizer_le_of_mulEquiv
          (layerCentralQuotientEquiv H) hr.one_lt fun R hR hR2 =>
            pRank_normalizer_le_two_of_not_dvd hQT hr hr2 hrZ hR hR2)
    have e₂ : (↥L₁ ⧸ center ↥L₁) ≃* (↥L₂ ⧸ center ↥L₂) := centerQuotientEquiv e
    have hs : IsSimpleGroup (↥L₁ ⧸ center ↥L₁) := h₁.1.2.1
    have hnab : ∃ a b : ↥L₁ ⧸ center ↥L₁, a * b ≠ b * a := h₁.1.2.2
    obtain ⟨r₀, hr₀, hr₀2, R₀, hR₀, hR₀2, x, hxN, hxo⟩ := exists_odd_prime_mem_normalizer hnab
    have hxr : x ^ r₀ = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    have hxc : Nat.card (zpowers x) = r₀ ^ 1 := by rw [Nat.card_zpowers, hxo, pow_one]
    have hN1 : 1 ≤ CFSG.Open.pRank r₀ (normalizer (R₀ : Set (↥L₁ ⧸ center ↥L₁))) :=
      le_pRank_of_le hr₀.one_lt (zpowers_le.2 hxN) (isElemAbelian_zpowers hxr) hxc
    have hT1 : 1 ≤ CFSG.Open.pRank r₀ (⊤ : Subgroup (↥L₁ ⧸ center ↥L₁)) :=
      le_pRank_of_le hr₀.one_lt le_top (isElemAbelian_zpowers hxr) hxc
    refine ⟨fun L hL ⟨eL⟩ => ?_, Or.inl ?_⟩
    · by_contra hcon
      push Not at hcon
      have e₃ : (↥L₁ ⧸ center ↥L₁) ≃* (↥L ⧸ center ↥L) := centerQuotientEquiv eL.symm
      have h3 := (hbound r₀ hr₀ hr₀2).2 L₁ L₂ L h₁ h₂ hL hne (fun h => hcon.1 h.symm)
        (fun h => hcon.2 h.symm) ⟨e⟩ ⟨eL.symm⟩ R₀ hR₀ hR₀2
      have h4 := pRank_top_eq_of_mulEquiv hr₀.one_lt e₂
      have h5 := pRank_top_eq_of_mulEquiv hr₀.one_lt e₃
      omega
    · have hpair : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ R : Subgroup (↥L₁ ⧸ center ↥L₁), R ≠ ⊥ →
          IsPGroup 2 R → CFSG.Open.pRank r (normalizer (R : Set (↥L₁ ⧸ center ↥L₁))) +
            CFSG.Open.pRank r (⊤ : Subgroup (↥L₁ ⧸ center ↥L₁)) ≤ 2 := by
        intro r hr hr2 R hR hR2
        have h := (hbound r hr hr2).1 L₁ L₂ h₁ h₂ hne ⟨e⟩ R hR hR2
        have h' := pRank_top_eq_of_mulEquiv hr.one_lt e₂
        omega
      have hsqt : CFSG.IsStronglyQuasithin (↥L₁ ⧸ center ↥L₁) := by
        rw [CFSG.SectionRank.isStronglyQuasithin_iff]
        intro q hq hq2
        have h := hpair q hq hq2 R₀ hR₀ hR₀2
        omega
      have hcat : CFSG.Blueprint.Catalog (↥L₁ ⧸ center ↥L₁) :=
        CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK L₁
          (QuotientGroup.mk' (center ↥L₁)) (QuotientGroup.mk'_surjective _)
      exact hList _ hs hnab (CFSG.Milestones.cl_lit_sqtk_simple_list _ hnab hsqt hcat) hpair

end CFSG.SectionRank.QTK
