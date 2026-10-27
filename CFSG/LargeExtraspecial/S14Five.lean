module

public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.S8List
public import CFSG.LargeExtraspecial.S9ThreeMain
public import CFSG.LargeExtraspecial.S9FiveB
public import CFSG.LargeExtraspecial.S8FiveC
public import CFSG.LargeExtraspecial.S14Claims

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem rnPlus_iff_not_isMinus {g : G} {H : Hyp4 S g} {C : Cons311 S g} {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} (D : S8.Std H C ht ht1 hVQ) :
    RNPlus S g t ↔ ¬ D.IsMinus := by
  constructor
  · rintro ⟨ht', W, hW, hWs⟩ hmin
    have hT : ∀ x ∈ W, D.Q x = 0 := fun x hx => by
      by_cases hx0 : x = 0
      · rw [hx0, map_zero]
      · exact (D.hsing x hx0).mpr (hWs x hx hx0)
    have h1 := hmin W hT
    have h2 := D.hdim
    omega
  · intro hmin
    unfold S8.Std.IsMinus at hmin
    push Not at hmin
    obtain ⟨T, hT, hTm⟩ := hmin
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := T) hTm
    refine ⟨ht, Submodule.span (ZMod 2) (Set.range (T.subtype ∘ f)), ?_, ?_⟩
    · rw [finrank_span_eq_card (hf.map' T.subtype (Submodule.ker_subtype T)), Fintype.card_fin,
        D.hdim]
    · intro w hw hw0
      have hwT : w ∈ T := (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (f i).2)) hw
      exact (D.hsing w hw0).mp (hT w hwT)

theorem claim_14_5 [IsSimpleGroup G] (hCE : CentralExtInput.{0}) (h111 : S11_1Stmt)
    (h118 : S11_8M2Stmt) (hA4L : S11Alt4Stmt) (h139 : S13_9Stmt) (hA4O : S10Alt4Stmt)
    {g : G} (H : Hyp4 S g) (C : Cons311 S g) (hnoAll : S11.NoA2All S) (hirr : ¬ S.IsReducible)
    (hn : 6 ≤ S.width) (hex : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) :
    (∃ t, Stage S g t ∧ Hyp89 S g t) ∨ Bridge.TimmesfeldConclusion G S.width S.Mbar := by
  have hNo : NoA2 S g := noA2_of (hnoAll g H.conj_mem H.conj_ne)
  by_cases hlin : ∀ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 →
      Rbar S g t = S.Lbar g ∨ LinCase S g ht
  · right
    have hy : S11.Hyp S g := ⟨H, C, hnoAll, fun {t} ht ht1 => hlin t ht ht1⟩
    obtain ⟨hw6, k, u, τ, hyk, K, h3⟩ :=
      S11.timmesfeld_11_9 hy (h111 G S g hy hirr hn hex) hCE hn (h118 G S)
    exact Bridge.TimmesfeldConclusion.of_alt4 (hA4L G S k u τ hyk K h3 hw6 hirr)
  push Not at hlin
  obtain ⟨t, ht, ht1, hR, hL⟩ := hlin
  have hVQ : ¬ V S g t ≤ S.Qa g := by
    intro hVQ
    rcases timmesfeld_4_5 H hNo C ht ht1 with h | h | ⟨h, -⟩
    · exact hR h
    · exact hL h
    · exact h hVQ
  rcases claim_14_4 hCE H hNo C hirr (by omega) ht ht1 hR hVQ with hA | hc
  swap
  · exact Or.inr hc
  have hSt : Stage S g t := ⟨hn, H, hnoAll, C, hirr, ht, ht1, hR, hA⟩
  rcases timmesfeld_4_5_of_not_le H hNo C ht ht1 hVQ with hSp | hA6 | hΩ | hP
  · exact Or.inl ⟨t, hSt, H, C, ht, ht1, hVQ, Or.inr (Or.inl hSp)⟩
  · exact Or.inl ⟨t, hSt, H, C, ht, ht1, hVQ, Or.inr (Or.inr (Or.inl hA6))⟩
  · by_cases h4p : finrank (ZMod 2) (Vt S g t) = 4 ∧ RNPlus S g t
    · right
      obtain ⟨h4, hp⟩ := h4p
      obtain ⟨ht', W, hW, hWs⟩ := hp
      have X : S10.Hyp10 S g t := ⟨H, hNo, C, ht, ht1, hR, hA, hVQ, hΩ, h4, W, by omega, hWs⟩
      rcases Nat.lt_or_ge S.width 7 with h7 | h7
      · exact Bridge.TimmesfeldConclusion.of_alt4 (hA4O G S g t X hnoAll hirr (by omega))
      · exact Bridge.TimmesfeldConclusion.of_alt3 (h139 G S g t X hnoAll hirr h7)
    · exact Or.inl ⟨t, hSt, H, C, ht, ht1, hVQ, Or.inl ⟨hΩ, h4p⟩⟩
  · exact Or.inl ⟨t, hSt, H, C, ht, ht1, hVQ, Or.inr (Or.inr (Or.inr hP))⟩

theorem exists_config [IsSimpleGroup G] (hCorB : S8.TimmesfeldCorBInput)
    (hFacts : S8.CorBListFacts) (hCE : CentralExtInput.{0}) (h83 : S8_3Stmt)
    (hRes : S9.Timmesfeld93Residual.{0}) (h9 : S9A6PGLStmt) {g : G} {t : S.O}
    (hSt : Stage S g t) (h89 : Hyp89 S g t) :
    ∃ c : Config, c.Occurs S g t ∧ IsExtraspecialPGroup 2 (Nbar S g t) := by
  obtain ⟨H, C, ht, ht1, hVQ, ⟨hΩ, h4p⟩ | hSp | hA6 | hP⟩ := h89
  ·
    have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
    obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
    have hpl := rnPlus_iff_not_isMinus D
    have hdim := D.hdim
    have hRN : ∀ d, finrank (ZMod 2) (Vt S g t) = d → RNOmega S g t d :=
      fun d hd => ⟨H, C, ht, ht1, hVQ, hΩ, hd⟩
    have hext := S8.timmesfeld_8_5 hNo hΩ D hSt.abar_ne
    have h44 : ¬ (D.m = 2 ∧ ¬ D.IsMinus) := fun ⟨h2, hm⟩ => h4p ⟨by omega, hpl.mpr hm⟩
    have h83' : (D.m = 2 ∧ D.IsMinus) ∨ (D.m = 3 ∧ ¬ D.IsMinus) ∨ (D.m = 4 ∧ ¬ D.IsMinus) →
        (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨
          (D.m = 3 ∧ ¬ D.IsMinus ∧ S.width = 10) ∨ (D.m = 4 ∧ ¬ D.IsMinus ∧ S.width = 12) := by
      intro hcase
      have hcase' : (RNOmega S g t 4 ∧ ¬ RNPlus S g t) ∨ (RNOmega S g t 6 ∧ RNPlus S g t) ∨
          (RNOmega S g t 8 ∧ RNPlus S g t) := by
        rcases hcase with ⟨h2, hm⟩ | ⟨h3, hm⟩ | ⟨h4, hm⟩
        · exact Or.inl ⟨hRN 4 (by omega), fun hp => hpl.mp hp hm⟩
        · exact Or.inr (Or.inl ⟨hRN 6 (by omega), hpl.mpr hm⟩)
        · exact Or.inr (Or.inr ⟨hRN 8 (by omega), hpl.mpr hm⟩)
      rcases h83 G S g t hSt hcase' with h | ⟨⟨-, -, -, -, -, -, h6⟩, hp, hw⟩ |
          ⟨⟨-, -, -, -, -, -, h8⟩, hp, hw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by omega, hpl.mp hp, hw⟩)
      · exact Or.inr (Or.inr ⟨by omega, hpl.mp hp, hw⟩)
    rcases S8.timmesfeld_8_4 hCorB hFacts hCE (irr_of_not_isReducible hSt.irr) hNo hΩ D
        hSt.abar_ne h44 h83' with ⟨hm, h4, hw, hc⟩ | ⟨hm, h3, hw, hc⟩ | ⟨hm, h6, hw, hc⟩ |
        ⟨hm, h5, hw, hc⟩ | ⟨hm, h4, ⟨hw, hc⟩ | ⟨hw, hc⟩⟩ | ⟨hm, h3, hw, hc⟩
    · exact ⟨.omegaMinus8, ⟨⟨hRN 8 (by omega), fun hp => hpl.mp hp hm⟩, hw, hc⟩, hext⟩
    · exact ⟨.omegaMinus6, ⟨⟨hRN 6 (by omega), fun hp => hpl.mp hp hm⟩, hw, hc⟩, hext⟩
    · exact ⟨.omegaPlus12, ⟨⟨hRN 12 (by omega), hpl.mpr hm⟩, hw, hc⟩, hext⟩
    · exact ⟨.omegaPlus10, ⟨⟨hRN 10 (by omega), hpl.mpr hm⟩, hw, hc⟩, hext⟩
    · exact ⟨.omegaPlus8a, ⟨⟨hRN 8 (by omega), hpl.mpr hm⟩, hw, hc⟩, hext⟩
    · exact ⟨.omegaPlus8b, ⟨⟨hRN 8 (by omega), hpl.mpr hm⟩, hw, hc⟩, hext⟩
    · exact ⟨.omegaPlus6, ⟨⟨hRN 6 (by omega), hpl.mpr hm⟩, hw, hc⟩, hext⟩
  ·
    have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
    have hext := S9.timmesfeld_9_5 hCE H hNo C ht ht1 hVQ hSp hSt.abar_ne
    rcases S9.timmesfeld_9_4_sp hRes hCorB hFacts hCE (irr_of_not_isReducible hSt.irr) H hNo C
        ht ht1 hVQ hSp hSt.abar_ne with ⟨h6, hw, hc⟩ | ⟨h8, hw, hc⟩
    · exact ⟨.sp6, ⟨⟨H, C, ht, ht1, hVQ, hSp, h6⟩, hw, hc⟩, hext⟩
    · exact ⟨.sp8, ⟨⟨H, C, ht, ht1, hVQ, hSp, h8⟩, hw, hc⟩, hext⟩
  · exact (h9 G S g t hSt H C ht ht1 hVQ (Or.inl hA6)).elim
  · exact (h9 G S g t hSt H C ht ht1 hVQ (Or.inr hP)).elim

end CFSG.LargeExtraspecial.S14
