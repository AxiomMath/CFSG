module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngReach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.Eng

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {IsK : GroupClass}
  {S Up Lo : List TauCeti.SporadicName} {R : GroupClass}

theorem maximal_isTypeL (thm22 : Sol78Thm22At H) (hUH : Balance.UHered H) (hUp : UpCtx S Up H)
    (rc : ReachFacts IsK S Up Lo R) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hnotN : ¬ R ↥N)
    {M : Subgroup H} (hmax : Maximal M)
    (hRM : R (↥M ⧸ center ↥M))
    (hLo : Odd (Nat.card ↥(center ↥M)) → ¬ ∃ s ∈ Lo, IsSporadic (↥M ⧸ center ↥M) s)
    (hev : KEven IsK → ∀ (X : Type) [Group X], IsK X →
      Nonempty ((↥M ⧸ center ↥M) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥M)) →
        HasEvenCover ↥N) : ∃ s ∈ S, OddCover s M := by
  have hMq : CFSG.IsQuasisimple ↥M := hmax.1.isQuasisimple
  by_cases hsp : ∃ s' ∈ S ++ Up, IsSporadic (↥M ⧸ center ↥M) s'
  · obtain ⟨s', hs', hsc⟩ := hsp
    rcases List.mem_append.1 hs' with hS | hU
    · by_cases hodd : Odd (Nat.card ↥(center ↥M))
      · exact ⟨s', hS, hMq, hodd, hsc⟩
      · have hstd : StdBare M :=
          stdBare_of_maximal thm22 hkp hN hidx hmax (rc.rank _ hMq hRM fun h => absurd h hodd)
        have hsol : SolStd M := solStd_of_inL_of_stdBare hmax.1 hstd
        obtain ⟨s'', hs'', hsN⟩ := rc.evenOut s' hS H hUH N hN hidx hkp M hsol hMq hsc hodd
        exact (hnotN (rc.up_reach s'' hs'' _ hsN)).elim
    · exact (hUp.nu M hmax.1 s' hU hsc).elim
  · have hstd : StdBare M :=
      stdBare_of_maximal thm22 hkp hN hidx hmax (rc.rank _ hMq hRM fun _ => hsp)
    have hsol : SolStd M := solStd_of_inL_of_stdBare hmax.1 hstd
    exact (hnotN (rc.closure H hUH N hN hidx hkp M hsol hMq hRM hsp hLo hev)).elim

theorem chain_link5b_isK (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H)
    (hUp : UpCtx S Up H) (rc : ReachFacts IsK S Up Lo R) (hKiso : IsK.IsoInv)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {M : Subgroup H}
    {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) (hL0 : InL (L 0))
    {K₁ : Subgroup H} (hK₁L : InL K₁) (hK₁ : KLike IsK K₁)
    {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m) (h5b : Sol78Link5b (L i) (L (i - 1)) (s i))
    (hRP : Reached R K₁ (L (i - 1))) (hQ : ∃ s' ∈ S, OddCover s' (L i)) :
    IsK (↥(L (i - 1)) ⧸ CFSG.oddCore ↥(L (i - 1))) := by
  obtain ⟨hTp, hLc⟩ := hch.comp i him
  obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem i hi him
  obtain ⟨hincl, -⟩ := hch.incl i hi him
  have hLq : CFSG.IsQuasisimple ↥(L i) := hLc.isQuasisimple
  have hPq : CFSG.IsQuasisimple ↥(L (i - 1)) := hLp.isQuasisimple
  have hLL : InL (L i) := chain_inL hch hT hi him
  have hLne : L i ≠ N := inL_ne_of_fStarSimple hN hLL
  have hLk : InL (L (i - 1)) := by
    rcases Nat.eq_zero_or_pos (i - 1) with h | h
    · rw [h]; exact hL0
    · exact chain_inL hch hT h (by omega)
  have hne : L (i - 1) ≠ L i := fun h => by
    have := hch.inj (i - 1) (by omega) i him h
    omega
  by_cases hsp' : ∃ s' ∈ S ++ Up, IsSporadic (↥(L (i - 1)) ⧸ center ↥(L (i - 1))) s'
  · exact (hUp.out hLk hne (hT i hi him) (chain_link5bData hch hi him h5b) hsp').elim
  · obtain ⟨-, hPQ, -, -, -⟩ := link5b_setup hPq hne hLc hs2 hLp hincl h5b
    obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩, π, hπ, hπk,
        hπc⟩ :=
      link5b_section hN hidx hkp hLq hLne hPq hne hLc hs2 hLp hincl h5b
    have hRP' : R (↥P' ⧸ center ↥P') := rc.iso _ _ e hRP.1
    have hns : ¬ ∃ s ∈ S ++ Up, IsSporadic (↥P' ⧸ center ↥P') s := by
      rintro ⟨s', hs', ⟨f⟩⟩
      exact hsp' ⟨s', hs', ⟨e.trans f⟩⟩
    obtain ⟨s', hs', hQq, hQodd, ⟨f⟩⟩ := hQ
    have hNS : ∃ s ∈ S, IsSporadic ↥N' s := ⟨s', hs', ⟨g.symm.trans f⟩⟩
    have hlow : Odd (Nat.card ↥(center ↥P')) → ¬ ∃ s ∈ Lo, IsSporadic (↥P' ⧸ center ↥P') s := by
      rintro hodd ⟨s'', hs'', hsc⟩
      exact false_of_odd_standard ih hsecY hcard hFS hidx' hkp' hsol hq' hodd
        (List.mem_append_right _ hs'') hsc (rc.fi23_lo s'' hs'')
    have hev : KEven IsK → ∀ (X : Type) [Group X], IsK X →
        Nonempty ((↥P' ⧸ center ↥P') ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P')) →
          HasEvenCover ↥N' := fun hKeven X _ hXK hcq hodd =>
      hasEvenCover_of_section rc hKeven hK₁L.isQuasisimple hK₁ hPq hLq hPQ hRP π hπ hπk hπc g hXK
        hcq hodd
    have hK' : IsK (↥P' ⧸ CFSG.oddCore ↥P') :=
      rc.pair_into Y (ih.uHered.of_section hsecY) N' hFS hidx' hkp' P' hsol hq' hRP' hns
        hlow hev hNS
    have hkodd : Odd (Nat.card π.ker) := hQodd.of_dvd_nat (card_ker_dvd_center hPQ π hπc)
    obtain ⟨e'⟩ := oddQuot_equiv_of_surj π hπ hkodd
    exact hKiso _ _ e'.symm hK'

end CFSG.EvenSporadicStandard.Induction.Fi.Eng
