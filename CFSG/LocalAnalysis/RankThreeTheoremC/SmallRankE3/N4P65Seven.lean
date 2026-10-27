module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65U0Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Sit
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Num7
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19F

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFactP65RankThree KFactP65RankTwo
  KFactP65RankThreeS)

@[expose] def P65ClauseBResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
    ∀ (p : ℕ), 7 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ∀ (f : ℕ) (F Fs R : Subgroup G) (Ft : Sylow f G), f.Prime → p < f →
          f ∈ rankThreeSigmaA G → IsCoreMaxLocal f Ft M → rankThreeClauseB M (Ft : Subgroup G) f →
          IsPGroup f F → F ≠ ⊥ → F ≤ Fs → Fs ≤ (Ft : Subgroup G) → IsPGroup f Fs →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → ¬ normalizer (F : Set G) ≤ M →
          zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G) →
          (∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' →
            zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → Fs ≤ F' → F' = Fs) →
          normalizer (Fs : Set G) ≤ M → R ≤ M ⊓ normalizer (Fs : Set G) → 3 ≤ Open.pRank p R →
          False

variable {G : Type} [Group G] [Finite G]

theorem n4_one_le_pRank_of_ne_bot {f : ℕ} (hf : f.Prime) {F : Subgroup G} (hFp : IsPGroup f F)
    (hF1 : F ≠ ⊥) : 1 ≤ Open.pRank f F := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hF1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  have hdvd : f ∣ Nat.card F := by
    rw [hk]
    exact dvd_pow_self f hk1
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' f hdvd
  have hgo : orderOf (g : G) = f := by rw [Subgroup.orderOf_coe]; exact hg
  have hgf : (g : G) ^ f = 1 := by rw [← hgo]; exact pow_orderOf_eq_one _
  have hE : IsElemAbelian f (zpowers (g : G)) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian f _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hgf)
  have hcard : Nat.card (zpowers (g : G)) = f ^ 1 := by
    rw [Nat.card_zpowers, hgo, pow_one]
  exact CFSG.SectionRank.le_pRank hf.one_lt (zpowers_le.mpr g.2) hE hcard

theorem n4_isCyclic_of_pRank_le_one {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {F : Subgroup G}
    (hF : IsPGroup f F) (hr : CFSG.Open.pRank f F ≤ 1) : IsCyclic F := by
  have h1 : CFSG.pRank f ↥F = CFSG.Open.pRank f F :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top f ↥F).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := f) F).symm
  have h2 : ¬ 2 ≤ CFSG.pRank f ↥F := by
    rw [h1]
    omega
  exact CFSG.GH74.GLS.Stage2.Final.Thm4.isCyclic_of_not_two_le_pRank f hf2 hF h2

theorem n4_zpowers_eq_of_cyclic {f : ℕ} (hf : f.Prime) {F : Subgroup G} (hF : IsCyclic F) {y y' : G}
    (hy : y ∈ F) (hy' : y' ∈ F) (ho : orderOf y = f) (ho' : orderOf y' = f) :
    zpowers y = zpowers y' := by
  have ha : orderOf (⟨y, hy⟩ : ↥F) = f := (Subgroup.orderOf_mk y hy).trans ho
  have hb : orderOf (⟨y', hy'⟩ : ↥F) = f := (Subgroup.orderOf_mk y' hy').trans ho'
  have hab : zpowers (⟨y, hy⟩ : ↥F) = zpowers (⟨y', hy'⟩ : ↥F) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb])
  have h := congrArg (Subgroup.map F.subtype) hab
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
  exact h

theorem n4_mem_normalizer_of_conj_eq {Y : Subgroup G} {g : G} (h : rankThreeConj g Y = Y) :
    g ∈ normalizer (Y : Set G) := by
  have hmem : ∀ v : G, v ∈ rankThreeConj g Y ↔ ∃ u ∈ Y, g⁻¹ * u * g = v := by
    intro v
    simp only [rankThreeConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
  have heq : ∀ v : G, v ∈ rankThreeConj g Y ↔ v ∈ Y := fun v => by rw [h]
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := (hmem w).1 ((heq w).2 hw)
    simpa [mul_assoc] using hu
  · intro hw
    have h1 := (heq _).1 ((hmem _).2 ⟨_, hw, rfl⟩)
    simpa [mul_assoc] using h1

theorem n4_conj_le_of_mem_normalizer {Y T : Subgroup G} {g : G} (hYT : Y ≤ T)
    (hg : g ∈ normalizer (T : Set G)) : rankThreeConj g Y ≤ T := by
  rintro w hw
  simp only [rankThreeConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  have hg' : g⁻¹ ∈ normalizer (T : Set G) := inv_mem hg
  have := (mem_normalizer_iff.mp hg' u).mp (hYT hu)
  simpa [mul_assoc] using this

theorem p65ClauseBResidue_of_kfactS (hK1 : KFactP65RankThreeS) : P65ClauseBResidue := by
  intro G _ _ hS hD1 hU0 p hp7 P M hsit x z hx hz f F Fs R Ft hf hpf hfS hcore hclB hFp hF1 hFFs
    hFsFt hFsp hBF hHM hBFs hFsmax hNFs hRN hR3
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  have hp5 : 5 ≤ p := by omega
  have hf2 : f ≠ 2 := by omega
  have hfp : f ≠ p := by omega
  have hSit : N1.Sit G p P M := ⟨hS, hU0, hsit, hp5⟩
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) (hSit.plane hx hz).card_eq
  have hFtM : (Ft : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hfS hcore).1
  have hFFt : F ≤ (Ft : Subgroup G) := hFFs.trans hFsFt
  have hFrank : Open.pRank f F ≤ 1 := by
    by_contra h
    push Not at h
    exact hHM ((CFSG.HardMathSupport.Timmesfeld.Proving.le_GLBCore_of_le_normalizer hFFt
      (by omega : 2 ≤ Open.pRank f F) le_rfl).trans (hU0 f hfS Ft M hcore))
  have hFcyc : IsCyclic F := n4_isCyclic_of_pRank_le_one hf2 hFp hFrank
  have hfd : f ∣ Nat.card F := by
    obtain ⟨k, hk⟩ := hFp.exists_card_eq
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hF1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    rw [hk]
    exact dvd_pow_self f hk1
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) f hfd
  have hyo : orderOf (y' : G) = f := by rw [Subgroup.orderOf_coe]; exact hy'
  have hyF : (y' : G) ∈ F := y'.2
  set y : G := (y' : G) with hy
  have hYF : zpowers y ≤ F := zpowers_le.mpr hyF
  have hYcard : Nat.card (zpowers y) = f := by rw [Nat.card_zpowers, hyo]
  have hNFY : normalizer (F : Set G) ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
    intro n hn
    have hnyF : n * y * n⁻¹ ∈ F := (mem_normalizer_iff.mp hn y).mp hyF
    have hnyo : orderOf (n * y * n⁻¹) = f := by
      have h1 := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective y
      rw [← hyo]
      simpa [MulAut.conj_apply] using h1
    have hz1 : zpowers (n * y * n⁻¹) = zpowers y :=
      n4_zpowers_eq_of_cyclic hf hFcyc hnyF hyF hnyo hyo
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : n * y ^ k * n⁻¹ = (n * y * n⁻¹) ^ k := by simp [conj_zpow]
      rw [this, ← hz1]
      exact zpow_mem_zpowers _ _
    · intro hw
      have hw' : n * w * n⁻¹ ∈ zpowers (n * y * n⁻¹) := by rw [hz1]; exact hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have : n * y ^ k * n⁻¹ = (n * y * n⁻¹) ^ k := by simp [conj_zpow]
      rw [← this] at hk
      have hw2 : w = y ^ k := by
        have := congrArg (fun t => n⁻¹ * t * n) hk
        simpa [mul_assoc] using this.symm
      rw [hw2]
      exact zpow_mem_zpowers _ _
  obtain ⟨-, -, P₀, hP₀Ft, hP₀c, hwc, -, -, -, hother⟩ := hclB
  have hYP₀ : zpowers y = P₀ := by
    by_contra hne
    exact hHM (hNFY.trans (hother (zpowers y) (hYF.trans hFFt) hYcard hne))
  rw [hYP₀] at hNFY hYF hYcard
  have hP₀Fs : P₀ ≤ Fs := hYF.trans hFFs
  have hNP₀ : ∀ g : G, g ∈ normalizer (Fs : Set G) → g ∈ normalizer (P₀ : Set G) := fun g hg =>
    n4_mem_normalizer_of_conj_eq (hwc g ((n4_conj_le_of_mem_normalizer hP₀Fs hg).trans hFsFt))
  have hFsN : Fs ≤ normalizer (P₀ : Set G) := fun g hg => hNP₀ g (Subgroup.le_normalizer hg)
  have hRN' : R ≤ normalizer (P₀ : Set G) := fun g hg => hNP₀ g (mem_inf.mp (hRN hg)).2
  have hP₀1 : P₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    exact hf.one_lt.ne hYcard
  have hP₀M : P₀ ≤ M := hP₀Fs.trans (hFsFt.trans hFtM)
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer (P₀ : Set G) := hBF.trans hNFY
  have hHM' : ¬ normalizer (P₀ : Set G) ≤ M := fun h => hHM (hNFY.trans h)
  obtain ⟨Q, hBQ, hQH, hQp, hQidx⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_le_of_isPGroup hprime hBN hB3
  have hrank : 3 ≤ Open.pRank p (normalizer (P₀ : Set G)) :=
    hR3.trans (CFSG.SectionRank.pRank_mono hprime.one_lt hRN')
  obtain ⟨-, hbw, -⟩ :=
    N1.p65_rankThree_applyAt (hK1 G hS) hSit hx hz hP₀1 hP₀M hBN hHM' hQH hQp hQidx hBQ hrank
  have hcop : Nat.Coprime (Nat.card Fs) (2 * p) := by
    obtain ⟨k, hk⟩ := hFsp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right
      ((Nat.coprime_primes hf Nat.prime_two).mpr hf2) ((Nat.coprime_primes hf hprime).mpr hfp))
  have hFsO : Fs ≤ rankThreePrimeCore p (normalizer (P₀ : Set G)) := hbw Fs hFsN hBFs hcop
  have hOM : rankThreePrimeCore p (normalizer (P₀ : Set G)) ≤ M :=
    N1.p65_primeCore_le_of_rank_three hSit hx hz hQH hQp hQidx hrank hBQ
  obtain ⟨-, hNO, hOp⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (normalizer (P₀ : Set G))
  have hOp' : ¬ p ∣ Nat.card (rankThreePrimeCore p (normalizer (P₀ : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp hOp
  obtain ⟨S, hSsyl, hFsS, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hprime
    hf hB3 hOp' (hBN.trans hNO) hFsO hFsp hBFs
  have hSM : S ≤ M := hSsyl.1.trans hOM
  have hSFs : S = Fs := hFsmax S hSM hSsyl.2.1 hBS hFsS
  rw [hSFs] at hSsyl
  exact hHM' (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.p65_le_of_normalizer_le hprime hf hOp'
    hNO hOM hSsyl hNFs)

theorem p65ClauseBResidue_of_kfact (hK1 : KFactP65RankThree) : P65ClauseBResidue :=
  p65ClauseBResidue_of_kfactS hK1.toS

theorem p65AfterLemma68_of_clauseB (hclB : P65ClauseBResidue) (hS : Setting G)
    (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) {p : ℕ} (hp7 : 7 ≤ p) {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) : N1.P65AfterLemma68 p M x z := by
  intro f F Fs R hf hf2 hfp hFp hF1 hFFs hFsM hFsp hBF hHM hBFs hFsmax hNFs hM2 hRH hR3 hcyc
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by omega
  have hMloc : IsTwoLocal M := hsit.isCoreMaxLocal.1.1
  obtain ⟨hDM, hMD, hDp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hX3 : Open.pRank f M ≤ 3 :=
    (local_pRank_le_evenRank f hf hf2 M hMloc).trans hS.rank.le
  obtain ⟨h3Fs, hpf⟩ := N1.lemma69_ge5_lt hp hp5 hf hf2 hfp (X := M)
    (D := rankThreePrimeCore p M) (Fs := Fs) (R := R)
    (fun N _ hN => n4_eq_top_of_isPGroup_quotient hS hsit N hN) hDM
    (fun y hy d hd => (mem_normalizer_iff.mp (hMD hy) d).mp hd)
    ((Nat.Prime.coprime_iff_not_dvd hp).mp hDp) hFsp hFsM hM2 hRH hR3 hcyc hX3
  have hfS : f ∈ rankThreeSigmaA G :=
    N1.f_mem_sigmaA_of_pRank hS.rank hp7 hsit.mem_sigmaA hf hpf hMloc
      (h3Fs.trans (CFSG.SectionRank.pRank_mono hf.one_lt hFsM))
  obtain ⟨Ft, hFsFt⟩ := hFsp.exists_le_sylow
  obtain ⟨M₁, hM₁, hFtM₁, -, -, -⟩ := exists_isCoreMaxLocal hS hfS Ft
  have hMM₁ : M ≤ M₁ :=
    hD1 f hfS Ft M₁ hM₁.1.1 hM₁.2 (fun K hK _ hMK => hM₁.1.2 K hK hMK) M hMloc
      (h3Fs.trans (CFSG.SectionRank.pRank_mono hf.one_lt
        (le_inf hFsM (hFsFt.trans hFtM₁))))
  have hM₁M : M₁ = M := hsit.isCoreMaxLocal.1.2 M₁ hM₁.1.1 hMM₁
  subst hM₁M
  have hU := hsit.largerPrimesUnique f hfS hpf Ft M₁ hM₁
  rcases hU.1 with hΓ | hb | ⟨hf3, -⟩
  ·
    exact hHM (le_trans (CFSG.HardMathSupport.Timmesfeld.Proving.le_GLBCore_of_le_normalizer
      (hFFs.trans hFsFt) (n4_one_le_pRank_of_ne_bot hf hFp hF1) le_rfl) hΓ)
  · exact hclB G hS hD1 hU0 p hp7 P M₁ hsit x z hx hz f F Fs R Ft hf hpf hfS hM₁ hb hFp hF1 hFFs
      hFsFt hFsp hBF hHM hBFs hFsmax hNFs hRH hR3
  · omega

theorem stepP65OddSevenU0_of_clauseB (hclB : P65ClauseBResidue) (hK1 : KFactP65RankThree)
    (hK2 : KFactP65RankTwo) (hKA : ∀ p : ℕ, 7 ≤ p → N1.KFactP65SingleAt p)
    (hβ : ∀ p : ℕ, 7 ≤ p → N1.NoTwoComponentsAt p) : StepP65OddSevenU0 := by
  intro G _ _ hS hD1 hU0 p hp7 P M hsit x z hx hz F hF1 hFM hcop hodd hBF
  have hSit : N1.Sit G p P M := ⟨hS, hU0, hsit, by omega⟩
  exact N1.p65_engine hK1 hK2 (hKA p hp7) (hβ p hp7) hSit hx hz
    (p65AfterLemma68_of_clauseB hclB hS hD1 hU0 hp7 hsit hx hz) hF1 hFM hcop hodd hBF

theorem stepP65OddSevenU0_of_kfacts (hK1 : KFactP65RankThree) (hK2 : KFactP65RankTwo)
    (hKA : ∀ p : ℕ, 7 ≤ p → N1.KFactP65SingleAt p)
    (hβ : ∀ p : ℕ, 7 ≤ p → N1.NoTwoComponentsAt p) : StepP65OddSevenU0 :=
  stepP65OddSevenU0_of_clauseB (p65ClauseBResidue_of_kfact hK1) hK1 hK2 hKA hβ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
