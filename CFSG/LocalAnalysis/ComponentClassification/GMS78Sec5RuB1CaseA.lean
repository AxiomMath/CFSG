module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Ru

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace SzMinCounter

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

theorem centralizer_le_normalizer_of_oddCoreIn_ne_bot
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {L₀ : Subgroup G}
    (hfr : Sec3.B1Frame L T L₀) {f : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1)
    (hP : AS76b.oddCoreIn (centralizer ({f} : Set G)) ≠ ⊥) :
    centralizer ({f} : Set G) ≤
      normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := by
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hWdef
  set P := AS76b.oddCoreIn (centralizer ({f} : Set G)) with hPdef
  set H := normalizer (P : Set G) with hHdef
  have hPodd : Odd (Nat.card P) := AS76b.odd_card_oddCoreIn _
  have hCH : centralizer ({f} : Set G) ≤ H := AS76b.le_normalizer_oddCoreIn _
  have hAL : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  have hfL : f ∈ L := hAL hfA
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h3 hF
  have hfV : f ∈ gmsV L T := (le_sup_left : gmsA L T ≤ gmsV L T) hfA
  have hVC : gmsV L T ≤ centralizer ({f} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hv⟩ ⟨f, hfV⟩))
  have hPW : P ≤ W := hM.le_oddCoreIn_of_le_normalizer_gmsV h3 hF hZ h4 hPodd (hVC.trans hCH)
  have hL₀C : L₀ ≤ centralizer (W : Set G) := le_centralizer_iff.mp hfr.centralizer_eq.ge
  have hL₀H : L₀ ≤ H := hL₀C.trans ((centralizer_le hPW).trans (centralizer_le_normalizer P))
  have hLH : L ≤ H := hfr.le.trans hL₀H
  have hKH : centralizer (L : Set G) ≤ H :=
    (centralizer_le (Set.singleton_subset_iff.mpr hfL)).trans hCH
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hn : P.Normal := normalizer_eq_top_iff.mp htop
    have h1 := RankTwoSporadic.le_standardComponentOddCore hn hPodd
    rw [hM.hyp.oddCore, le_bot_iff] at h1
    exact hP h1
  obtain ⟨e⟩ := hfr.ru
  have hsRu : IsSimpleGroup NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hs₀ : IsSimpleGroup L₀ := @MulEquiv.isSimpleGroup L₀ _ NativeSporadic.Ru _ hsRu e
  have hf₀ : (⟨f, hfr.le hfL⟩ : L₀) ≠ 1 := fun h => hf1 (congrArg Subtype.val h)
  have hle : ∀ X : Subgroup G, L₀ ≤ normalizer (X : Set G) → f ∈ X → L₀ ≤ X := by
    intro X hX hfX
    have hn : (X.subgroupOf L₀).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      have h1 := (mem_normalizer_iff.mp (hX g.2) x).mp hx
      simpa using h1⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal L₀ _ hs₀ _ hn with h | h
    · exfalso
      have h1 : (⟨f, hfr.le hfL⟩ : L₀) ∈ X.subgroupOf L₀ := mem_subgroupOf.mpr hfX
      rw [h, mem_bot] at h1
      exact hf₀ h1
    · intro x hx
      have h1 : (⟨x, hx⟩ : L₀) ∈ X.subgroupOf L₀ := h ▸ mem_top _
      exact mem_subgroupOf.mp h1
  have hnn : ¬ (L.subgroupOf H).Normal := by
    intro hn
    have hLn : L₀ ≤ normalizer (L : Set G) := fun g hg => by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 := hn.conj_mem ⟨x, hLH hx⟩ (mem_subgroupOf.mpr hx) ⟨g, hL₀H hg⟩
        rw [mem_subgroupOf] at h1
        simpa using h1
      · intro hx
        have h1 := hn.conj_mem ⟨g * x * g⁻¹, hLH hx⟩ (mem_subgroupOf.mpr hx)
          ⟨g, hL₀H hg⟩⁻¹
        rw [mem_subgroupOf] at h1
        simpa [mul_assoc] using h1
    have hL₀L : L₀ ≤ L := hle L hLn hfL
    have hKW : centralizer (L : Set G) ≤ W :=
      (centralizer_le hL₀L).trans hfr.centralizer_eq.le
    have hdvd := Subgroup.card_dvd_of_le
      ((inf_le_right : T ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G)).trans hKW)
    rw [h4] at hdvd
    have hWodd : Odd (Nat.card W) := AS76b.odd_card_oddCoreIn _
    rw [Nat.odd_iff] at hWodd
    omega
  obtain ⟨e₁⟩ := hM.nonempty_closureIn_mulEquiv_ru hHtop hLH hKH hnn
  have hL₁N : H ≤ normalizer
      (((rankTwoX (L.subgroupOf H)).map H.subtype : Subgroup G) : Set G) := by
    have : (rankTwoX (L.subgroupOf H)).Normal := normalClosure_normal
    exact AS76b.le_normalizer_map_subtype_of_normal H _
  have hLL₁ : L ≤ (rankTwoX (L.subgroupOf H)).map H.subtype := fun l hl =>
    ⟨⟨l, hLH hl⟩, subset_normalClosure (mem_subgroupOf.mpr hl), rfl⟩
  have hL₀L₁ : L₀ ≤ (rankTwoX (L.subgroupOf H)).map H.subtype :=
    hle _ (hL₀H.trans hL₁N) (hLL₁ hfL)
  have hL₀eq : L₀ = (rankTwoX (L.subgroupOf H)).map H.subtype :=
    Subgroup.eq_of_le_of_card_ge hL₀L₁ (by rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e.toEquiv])
  calc centralizer ({f} : Set G) ≤ H := hCH
    _ ≤ normalizer (((rankTwoX (L.subgroupOf H)).map H.subtype : Subgroup G) : Set G) := hL₁N
    _ = normalizer (L₀ : Set G) := by rw [← hL₀eq]
    _ = normalizer (W : Set G) := hfr.normalizer_eq'

end SzMinCounter

end CFSG.ComponentClassification.GMS78
