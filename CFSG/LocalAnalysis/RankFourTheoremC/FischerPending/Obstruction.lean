module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Core

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

private noncomputable def weight (P : Subgroup G) (D : Subgroup G) : ℕ :=
  Nat.card ↥(P ⊓ normalizer (D : Set G)) * (Nat.card G + 1) + (Nat.card G - Nat.card D)

omit [Finite G] in
private theorem weight_lt_of_card_lt {P D P' D' : Subgroup G}
    (h : Nat.card ↥(P ⊓ normalizer (D : Set G)) < Nat.card ↥(P' ⊓ normalizer (D' : Set G))) :
    weight P D < weight P' D' := by
  unfold weight
  have h1 : Nat.card G - Nat.card D ≤ Nat.card G := Nat.sub_le _ _
  nlinarith

private theorem weight_lt_of_card_le_of_lt {P D P' D' : Subgroup G}
    (h : Nat.card ↥(P ⊓ normalizer (D : Set G)) ≤ Nat.card ↥(P' ⊓ normalizer (D' : Set G)))
    (hD : Nat.card D' < Nat.card D) : weight P D < weight P' D' := by
  unfold weight
  have hD' : Nat.card D ≤ Nat.card G := Subgroup.card_le_card_group D
  have : Nat.card G - Nat.card D < Nat.card G - Nat.card D' := by omega
  nlinarith

theorem ObstructionSetting.exists_extremal_obstruction (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (hfail : ¬ FullCoreLocal G) :
    ∃ p ∈ rankThreeSigmaA G, ∃ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D := by
  classical
  have hex : ∃ p ∈ rankThreeSigmaA G, ∃ (P : Sylow p G) (M D : Subgroup G),
      IsObstruction p P M D := by
    by_contra hnone
    apply hfail
    intro p hp P M hM
    apply (gamma_le_iff 2 p (P : Subgroup G) M).mpr
    intro D hDP hD
    by_contra hDM
    exact hnone ⟨p, hp, P, M, D, hM, hDP, hD, hDM⟩
  obtain ⟨p, hp, P₀, M₀, D₀, hobs₀⟩ := hex
  have hprime := sigmaA_prime p hp
  let T := {t : Sylow p G × Subgroup G × Subgroup G | IsObstruction p t.1 t.2.1 t.2.2}
  have : Nonempty T := ⟨⟨(P₀, M₀, D₀), hobs₀⟩⟩
  obtain ⟨⟨⟨P, M, D⟩, hobs⟩, hmax⟩ :=
    Finite.exists_max (fun t : T => weight ((t : Sylow p G × Subgroup G × Subgroup G).1 :
      Subgroup G) (t : Sylow p G × Subgroup G × Subgroup G).2.2)
  have hle : ∀ (P' : Sylow p G) (M' D' : Subgroup G), IsObstruction p P' M' D' →
      weight (P' : Subgroup G) D' ≤ weight (P : Subgroup G) D :=
    fun P' M' D' hobs' => hmax ⟨(P', M', D'), hobs'⟩
  obtain ⟨hM, hDP, hD2, hDM⟩ : IsObstruction p P M D := hobs
  have hPM := hS.sylow_le hp hM
  have hrank : Open.pRank p D = 2 := by
    by_contra hne
    exact hDM (normalizer_le_of_three_le_pRank hD1 hp hM (hDP.trans hPM) (by omega))
  have hprod : Open.pRank p (D ⊔ ((P : Subgroup G) ⊓ centralizer (D : Set G))) = 2 := by
    have hlow := pRank_mono p hprime.one_lt
      (le_sup_left : D ≤ D ⊔ ((P : Subgroup G) ⊓ centralizer (D : Set G)))
    by_contra hne
    exact hDM ((aschCore_normalizer_le 2 p (P : Subgroup G) D hDP hD2 (by omega)).trans hM.2)
  refine ⟨p, hp, P, M, D, ⟨⟨hM, hDP, hD2, hDM⟩, hrank, hprod, ?_, ?_, ?_⟩⟩
  ·
    intro X hXD hX2 hnorm
    by_contra hXne
    have hXlt : X < D := lt_of_le_of_ne hXD hXne
    have hobsX : IsObstruction p P M X :=
      ⟨hM, hXD.trans hDP, hX2, fun h => hDM (hnorm.trans h)⟩
    have hcardX : Nat.card X < Nat.card D := Subgroup.card_lt_of_lt hXlt
    have hNle : Nat.card ↥((P : Subgroup G) ⊓ normalizer (D : Set G)) ≤
        Nat.card ↥((P : Subgroup G) ⊓ normalizer (X : Set G)) :=
      Subgroup.card_le_of_le (inf_le_inf_left _ hnorm)
    have := weight_lt_of_card_le_of_lt hNle hcardX
    exact absurd (hle P M X hobsX) (not_le.mpr this)
  ·
    intro P' M' D' hobs'
    by_contra hlt
    push Not at hlt
    exact absurd (hle P' M' D' hobs') (not_le.mpr (weight_lt_of_card_lt hlt))
  ·
    intro h3 S hSp hle1 hle2
    by_contra hSne
    have hlt : (P : Subgroup G) ⊓ normalizer (D : Set G) < S := lt_of_le_of_ne hle1 (Ne.symm hSne)
    obtain ⟨P', hSP'⟩ := hSp.exists_le_sylow
    obtain ⟨M', hM', -⟩ := hS.exists_isCoreMaxLocal hp P'
    have hDM' : ¬ normalizer (D : Set G) ≤ M' := by
      intro hN
      have hinf : 3 ≤ Open.pRank p (M' ⊓ M) :=
        h3.trans (pRank_mono p hprime.one_lt (le_inf (inf_le_right.trans hN)
          (inf_le_left.trans hPM)))
      have hM'M : M' ≤ M := le_of_three_le_pRank_inf hD1 hp hM hM'.1.1 hinf
      have heq : M = M' := hM'.1.2 M hM.1.1 hM'M
      exact hDM (heq ▸ hN)
    have hDP' : D ≤ (P' : Subgroup G) :=
      (le_inf hDP Subgroup.le_normalizer).trans (hle1.trans hSP')
    have hobs' : IsObstruction p P' M' D := ⟨hM', hDP', hD2, hDM'⟩
    have hcard : Nat.card S ≤ Nat.card ↥((P' : Subgroup G) ⊓ normalizer (D : Set G)) :=
      Subgroup.card_le_of_le (le_inf hSP' hle2)
    have hlt' := Subgroup.card_lt_of_lt hlt
    have := weight_lt_of_card_lt (P := (P : Subgroup G)) (D := D)
      (P' := (P' : Subgroup G)) (D' := D) (hlt'.trans_le hcard)
    exact absurd (hle P' M' D hobs') (not_le.mpr this)

end CFSG.LocalAnalysis.RankFourTheoremC
