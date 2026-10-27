module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1MSide
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Rank3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Rank2
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Num
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.RankThree.PartOne.KE.E7FourStabFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFactP65RankThree KFactP65RankTwo
  KFactP65RankThreeAt KFactP65RankTwoAt
  IsMaxFInvariantIn IsFInvariantIn p65_exists_f_counterexample p65_exists_max
  p65_normalizer_le_of_enlarged)

variable {G : Type} [Group G] [Finite G]

private theorem p65_exists_isMax {B F M : Subgroup G} {f : ℕ} (hF : IsFInvariantIn f B M F) :
    ∃ Fs : Subgroup G, F ≤ Fs ∧ IsMaxFInvariantIn f B M Fs := by
  classical
  obtain ⟨Fs, ⟨hFs, hFFs⟩, hmax⟩ := Set.exists_max_image
    {F' : Subgroup G | IsFInvariantIn f B M F' ∧ F ≤ F'} (fun F' => Nat.card F')
    (Set.toFinite _) ⟨F, hF, le_rfl⟩
  refine ⟨Fs, hFFs, hFs, fun F' hF' hle => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (hmax F' ⟨hF', hFFs.trans hle⟩)).symm

@[expose] def P65AfterLemma68 (p : ℕ) (M : Subgroup G) (x z : G) : Prop :=
  ∀ (f : ℕ) (F Fs R : Subgroup G), f.Prime → f ≠ 2 → f ≠ p → IsPGroup f F → F ≠ ⊥ → F ≤ Fs →
    Fs ≤ M → IsPGroup f Fs → zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) →
    ¬ normalizer (F : Set G) ≤ M → zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G) →
    (∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) →
      Fs ≤ F' → F' = Fs) →
    normalizer (Fs : Set G) ≤ M →
    (∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (Fs : Set G), m = d * n) →
    R ≤ M ⊓ normalizer (Fs : Set G) → 3 ≤ Open.pRank p R →
    IsCyclic (R ⊓ centralizer (Fs : Set G) : Subgroup G) → False

theorem p65_engineAt {p : ℕ} (hK1 : KFactP65RankThreeAt G) (hK2 : KFactP65RankTwoAt G)
    (hKA : KFactP65SingleAt p) (hβ : NoTwoComponentsAt p) {P : Sylow p G} {M : Subgroup G}
    (hS : Sit G p P M) {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (htail : P65AfterLemma68 p M x z) {F : Subgroup G} (hF1 : F ≠ ⊥) (hFM : F ≤ M)
    (hcop : Nat.Coprime p (Nat.card F)) (hodd : Odd (Nat.card F))
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G)) : normalizer (F : Set G) ≤ M := by
  by_contra hFnot
  have hprime := hS.prime
  have hpl := hS.plane hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBM : zpowers x ⊔ zpowers z ≤ M := (hpl.isIsolatedPlane.1).trans hS.sylow_le
  obtain ⟨f₀, hf₀, hf₀2, hf₀p, F₁, hF₁p, hF₁F, hF₁1, hBF₁, hF₁not⟩ :=
    p65_exists_f_counterexample hF1 hodd hcop hBF hFnot
  obtain ⟨F, ⟨⟨f, hf, hf2, hfp, hFp⟩, hFM, hF1, hBF, hHM⟩, hmaxc⟩ := p65_exists_max
    (C := fun F' : Subgroup G => (∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ IsPGroup f F') ∧ F' ≤ M ∧
      F' ≠ ⊥ ∧ zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) ∧
      ¬ normalizer (F' : Set G) ≤ M)
    ⟨F₁, ⟨f₀, hf₀, hf₀2, hf₀p, hF₁p⟩, hF₁F.trans hFM, hF₁1, hBF₁, hF₁not⟩
  have hmax : ∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → F' ≠ ⊥ →
      zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → Nat.card F < Nat.card F' →
      normalizer (F' : Set G) ≤ M := by
    intro F' hF'M hF'p hF'1 hBF' hcard
    by_contra hnot
    exact absurd (hmaxc F' ⟨⟨f, hf, hf2, hfp, hF'p⟩, hF'M, hF'1, hBF', hnot⟩) (not_le.mpr hcard)
  obtain ⟨Fs, hFFs', hFsmax⟩ := p65_exists_isMax (M := M)
    (show IsFInvariantIn f (zpowers x ⊔ zpowers z) M F from ⟨hFM, hFp, hBF⟩)
  have hmS := fun {F' : Subgroup G} (hF' : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F') =>
    p65_mSide hKA hβ hS hx hz hf hf2 hfp hF'
  rcases hFFs'.eq_or_lt with heq | hFFs
  ·
    subst heq
    obtain ⟨hM1, hM2⟩ := hmS hFsmax
    exact p65_false_of_isMaxAt hK1 hS hx hz hf hf2 hfp hFsmax hF1 hHM hM1 (Or.inl hM2)
  · obtain ⟨hFsM, hFsp, hBFs⟩ := hFsmax.1
    obtain ⟨hM1, hM2⟩ := hmS hFsmax
    have hR3' : 3 ≤ Open.pRank p (M ⊓ normalizer (Fs : Set G)) :=
      hS.three_le_pRank.trans hM1
    have hBle : zpowers x ⊔ zpowers z ≤ M ⊓ normalizer (Fs : Set G) := le_inf hBM hBFs
    obtain ⟨R, hBR, hRH, hRp, hRidx⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_le_of_isPGroup hprime hBle hB3
    have hR3 : 3 ≤ Open.pRank p R := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow hprime hRH hRp hRidx]
      exact hR3'
    have hRM : R ≤ M := hRH.trans inf_le_left
    have hRFs : R ≤ normalizer (Fs : Set G) := hRH.trans inf_le_right
    have hrankH : Open.pRank p (normalizer (F : Set G)) ≤ 2 := by
      by_contra hr3
      push Not at hr3
      obtain ⟨E, hFE, hEp, hBE, hEO, hOM⟩ := p65_rank_three_enlargeAt hK1 hS hx hz hf hf2 hfp hFp
        hF1 hBF hHM hFsp hFsM hBFs hFFs (by omega)
      exact hHM (p65_normalizer_le_of_enlarged hprime hf hB3 hmax hBF hOM hFE hEp hBE hEO)
    have hcyc := p65_centralizer_cyclicAt hK2 hS hx hz hf hf2 hfp hFp hF1 hBF hHM hFsp hFsM hBFs
      hFFs hmax hrankH hRp hRM hBR hRFs hR3
    have hFs1 : Fs ≠ ⊥ := fun h => hF1 (le_bot_iff.mp (h ▸ hFFs.le))
    have hNFs : normalizer (Fs : Set G) ≤ M :=
      hmax Fs hFsM hFsp hFs1 hBFs (Subgroup.card_lt_of_lt hFFs)
    exact htail f F Fs R hf hf2 hfp hFp hF1 hFFs.le hFsM hFsp hBF hHM hBFs
      (fun F' h1 h2 h3 h4 => hFsmax.2 F' ⟨h1, h2, h3⟩ h4) hNFs hM2 hRH hR3 hcyc

theorem p65_engine {p : ℕ} (hK1 : KFactP65RankThree) (hK2 : KFactP65RankTwo)
    (hKA : KFactP65SingleAt p) (hβ : NoTwoComponentsAt p) {P : Sylow p G} {M : Subgroup G}
    (hS : Sit G p P M) {x z : G} (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (htail : P65AfterLemma68 p M x z) {F : Subgroup G} (hF1 : F ≠ ⊥) (hFM : F ≤ M)
    (hcop : Nat.Coprime p (Nat.card F)) (hodd : Odd (Nat.card F))
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G)) : normalizer (F : Set G) ≤ M :=
  p65_engineAt (hK1 G) (hK2 G) hKA hβ hS hx hz htail hF1 hFM hcop hodd hBF

theorem stepP65OddFive_of_kfacts (hK1 : KFactP65RankThree) (hK2 : KFactP65RankTwo)
    (hK3 : KFactP65SingleE3) (hβ : NoTwoComponentsE3) : StepP65OddFive := by
  intro G _ _ hSet hD1 P M hsit x z hx hz F hF1 hFM hcop5 hodd hBF
  have hU0 : FullCoreLocal G := fullCoreLocal_of_theoremD1_situation_five hSet hD1 hsit
  have hS : Sit G 5 P M := ⟨hSet, hU0, hsit, le_rfl⟩
  refine p65_engine hK1 hK2 hK3.toAt hβ.toAt hS hx hz ?_ hF1 hFM hcop5 hodd hBF
  intro f F Fs R hf hf2 hfp _ _ _ hFsM hFsp _ _ _ _ _ hM2 hRH hR3 hcyc
  have hprime : (5 : ℕ).Prime := Nat.prime_five
  obtain ⟨hDM, hMD, hDp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 M
  have hX3 : Open.pRank f M ≤ 3 :=
    (local_pRank_le_evenRank f hf hf2 M hS.isTwoLocal).trans hSet.rank.le
  have hX7 : 7 ≤ f → Open.pRank f M ≤ 2 := fun h7 =>
    pRank_le_two_of_five_mem hSet.rank hsit.mem_sigmaA hf (by omega) hS.isTwoLocal
  exact lemma69_e3 (X := M) (D := rankThreePrimeCore 5 M) (Fs := Fs) (R := R) rfl hf hf2 hfp
    (fun N _ hN => hS.eq_top_of_isPGroup_quotient N hN) hDM
    (fun y hy d hd => (mem_normalizer_iff.mp (hMD hy) d).mp hd)
    ((Nat.Prime.coprime_iff_not_dvd hprime).mp hDp)
    hFsp hFsM hM2 hRH hR3 hcyc hX3 hX7

theorem slotProp65Five_of_kfacts (hK1 : KFactP65RankThree) (hK2 : KFactP65RankTwo)
    (hK3 : KFactP65SingleE3) (hβ : NoTwoComponentsE3) : SlotProp65Five :=
  slotProp65Five_of_stepP65OddFive (stepP65OddFive_of_kfacts hK1 hK2 hK3 hβ)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
