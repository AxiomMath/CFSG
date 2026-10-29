module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec11Small
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13Small
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec9Remarks
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Proof
public import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem p131_pCore_le_glaPPrime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G) :
    pCoreOf 2 H ≤ GLAPPrimeCoreOf p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  obtain ⟨k, hkc⟩ := IsPGroup.iff_card.1 hk
  refine sec11_le_glaPPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) ?_ ?_
  · intro h hh n hn
    exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) n).1 hn
  · rw [hkc]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem p131_pCore_le_of_le {M N : Subgroup G} (hNM : N ≤ M) (hO : pCoreOf 2 M ≤ N) :
    pCoreOf 2 M ≤ pCoreOf 2 N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 hO ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  refine ⟨fun n hn g => Subgroup.mem_subgroupOf.2 ?_⟩
  have hnM : (n : G) ∈ pCoreOf 2 M := Subgroup.mem_subgroupOf.1 hn
  have := (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hNM g.2))
    (n : G)).1 hnM
  simpa using this

theorem p131_prop127 {m p : ℕ} {B M E A D N : Subgroup G} (h127 : Prop127_of_cexStatement)
    (hs : Sec11 G m p B M E A) (hD : IsEkIn p 2 A D) (hN : IsTwoLocal N)
    (h1 : pCoreOf 2 M ≤ N) (h2 : Subgroup.normalizer (D : Set G) ≤ N) :
    pCoreOf 2 M ≤ pCoreOf 2 N := by
  by_contra hc
  exact h127 (⟨hs, hN, hD, h1, h2, hc⟩ : Cex127 G m p B M E A N D)

abbrev Fam131 (M D T : Subgroup G) : Prop :=
  T ≤ M ∧ IsPGroup 2 ↥T ∧ Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (T : Set G) ∧
    pCoreOf 2 M ≤ T

theorem fam131_gammaOne {m p : ℕ} {B M E A D : Subgroup G} (h127 : Prop127_of_cexStatement)
    (hs : Sec11 G m p B M E A) (hD : IsEkIn p 2 A D) {T : Subgroup G} (hT : Fam131 M D T) :
    Fam131 M D (gammaOne T) := by
  obtain ⟨hTM, hTp, hTn, hTO⟩ := hT
  refine ⟨(gammaOne_le T).trans hTM, hTp.to_le (gammaOne_le T),
    hTn.trans (normalizer_le_normalizer_gammaOne T), ?_⟩
  intro x hx
  rw [mem_gammaOne]
  refine ⟨hTO hx, fun T₀ hT₀ hchar => ?_⟩
  have hN2 : IsTwoLocal (Subgroup.normalizer (T₀ : Set G)) :=
    ⟨T₀, hT₀, hTp.to_le hchar.1, rfl⟩
  have h1 : pCoreOf 2 M ≤ Subgroup.normalizer (T₀ : Set G) :=
    hTO.trans (Subgroup.le_normalizer.trans hchar.normalizer_le)
  have h2 : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (T₀ : Set G) :=
    hTn.trans hchar.normalizer_le
  exact p131_prop127 h127 hs hD hN2 h1 h2 hx

theorem fam131_gammaIter {m p : ℕ} {B M E A D : Subgroup G} (h127 : Prop127_of_cexStatement)
    (hs : Sec11 G m p B M E A) (hD : IsEkIn p 2 A D) {T : Subgroup G} (hT : Fam131 M D T) (n : ℕ) :
    Fam131 M D (gammaIter T n) := by
  induction n with
  | zero => exact hT
  | succ n ih => exact fam131_gammaOne h127 hs hD ih

end Helpers

section Prop131Main

variable {G : Type} [Group G] [Finite G]

theorem prop131_of_inputs (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_corStatement) (h127 : Prop127_of_cexStatement) : Prop131Statement := by
  intro G _ _ m p B M E A h D hD
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hDA : D ≤ A := hD.1
  have hD1 : IsElemAbelian p D := hD.2.1
  have hDcard : Nat.card D = p ^ 2 := hD.2.2
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hsig_le : sigmaStar D ≤ M := by
    refine iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => ?_
    exact (p131_pCore_le_glaPPrime hp hp2 _).trans (h111 h (hDA hdD) hd1)
  have hpi_le : piStar p D ≤ M := by
    refine iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => ?_
    exact sup_le (h1117 h (hDA hdD) hd1) (h111 h (hDA hdD) hd1)
  have hsig_pi : sigmaStar D ≤ piStar p D := by
    refine iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => ?_
    exact (p131_pCore_le_glaPPrime hp hp2 _).trans
      (le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_sup_right)))
  have hO2_sig : pCoreOf 2 M ≤ sigmaStar D := by
    have hcop : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
      rw [hk]
      exact (Nat.Prime.coprime_iff_not_dvd hp).1
        (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
    have hpow : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by simpa using hD1.2 (x : G) x.2)
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      p hp D (pCoreOf 2 M) hpow hDcard hcop
      (hDM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    refine hgen.le.trans (iSup_le fun d => iSup_le fun hd1 => ?_)
    have hd1' : (d : G) ≠ 1 := fun h' => hd1 (Subtype.ext h')
    exact (h121 h (hDA d.2) hd1').trans
      (le_iSup_of_le (d : G) (le_iSup_of_le d.2 (le_iSup_of_le hd1' le_rfl)))
  have hO2_pi : pCoreOf 2 M ≤ piStar p D := hO2_sig.trans hsig_pi
  have hfam_sig : Fam131 M D (sigmaOf D) := by
    refine ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 (sigmaStar D)).trans hsig_le,
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, ?_, ?_⟩
    · intro g hg
      rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
      rw [← sigmaOf_gLBConj, hg]
    · exact p131_pCore_le_of_le hsig_le hO2_sig
  have hgammaD : pCoreOf 2 M ≤ gammaD D := by
    obtain ⟨n, hn, -⟩ := exists_gammaInf_eq_gammaIter (sigmaOf D)
    have hfam := fam131_gammaIter h127 h hD hfam_sig n
    show pCoreOf 2 M ≤ gammaInf (sigmaOf D)
    rw [hn]
    exact hfam.2.2.2
  refine ⟨?_, ?_⟩
  · show pCoreOf 2 M ≤ gammaD D ⊓ pCoreOf 2 (piStar p D)
    exact le_inf hgammaD (p131_pCore_le_of_le hpi_le hO2_pi)
  · show gammaD D ⊓ pCoreOf 2 (piStar p D) ≤ M
    exact inf_le_right.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hpi_le)

end Prop131Main

section Lemma133Setup

variable {G : Type} [Group G] [Finite G]

def IsPiTypeGroup (p : ℕ) (Y : Type) [Group Y] : Prop :=
  (∃ k : ℕ, Nonempty (Y ≃* alternatingGroup (Fin (k * p + 2)))) ∨
    (∃ (n : ℕ) (ε : Bool), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) Y ∧ HasFixedPointFreeOrder ε n p) ∨
    (p = 3 ∧ Nonempty (Y ≃* alternatingGroup (Fin 7)))

def Input7_1Inn : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], Subgroup.center Y = ⊥ →
    IsPiTypeGroup p Y → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P →
      P ≤ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut Y

theorem glaPComponent_ne_bot' {p : ℕ} {X K : Subgroup G} (hK : GLAPComponent p X K) : K ≠ ⊥ := by
  rintro rfl
  have hc := hK.2.2.1
  unfold barX at hc
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot] at hc
  have hsub : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        have hx : x = 1 := Subtype.ext (by simpa using (Subgroup.mem_bot.1 x.2))
        have hy : y = 1 := Subtype.ext (by simpa using (Subgroup.mem_bot.1 y.2))
        rw [hx, hy]
  exact (not_nontrivial_iff_subsingleton.2 hsub) hc.2.2.2.toNontrivial

theorem prop95Hyp_of (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) {m p : ℕ}
    {B M E A D : Subgroup G} (h : Sec11 G m p B M E A) (hD : IsEkIn p 2 A D) :
    CFSG.LocalAnalysis.GLTheoremB.Prop95Hyp p M D := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  refine ⟨h.pre.1.1, hD.1.trans hAM, ⟨hD.2.1, hD.2.2⟩, ?_, ?_, ?_⟩
  · intro d hdD hd1
    exact (p131_pCore_le_glaPPrime hp hp2 _).trans (h111 h (hD.1 hdD) hd1)
  · intro d hdD hd1
    by_contra hc
    exact h121 (⟨h, ⟨hD.1 hdD, hd1⟩, hc⟩ : Cex121 G m p B M E A d)
  · exact (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h hD).1.trans
      (gammaStar_le_gammaD p D)

end Lemma133Setup

section Lemma133Fitting

variable {G : Type} [Group G] [Finite G]

theorem iof_ne_bot_of (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) : Iof p M D ≠ ⊥ := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : IsBOneMax p B := h.bOne
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  obtain ⟨hpc, hcent, hcomp⟩ := hP95 G m p hS M D
    (prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD)
  have hPM : gammaStar p D ≤ M := (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h.toSec11 h.hD).2
  have hTM : T ≤ M := h.hT2.trans hPM
  have hTΓ : barX p M T ≤ barX p M (gammaStar p D) := barX_mono p h.hT2
  have hTD : barX p M T ≤ barX p M (gammaD D) := barX_mono p (h.hT2.trans (gammaStar_le_gammaD p D))
  intro hbot
  have hcc : ∀ L : Subgroup G, GLAPComponent p M L →
      barX p M (gammaStar p D) ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro L hL
    by_contra hc
    have hle : L ≤ Iof p M D := le_iSup_of_le L (le_iSup_of_le ⟨hL, hc⟩ le_rfl)
    rw [hbot] at hle
    exact glaPComponent_ne_bot' hL (le_bot_iff.1 hle)
  have hQcore : GLAPPrimeCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hxfix : barX p M T ≤ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) := by
    intro x hx
    apply mem_pCore_of_centralizes hp hQcore
    · exact hcent (hTD hx)
    · intro K hK
      obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq M hK
      exact hcc L hL (hTΓ hx)
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hT2' : IsPGroup 2 ↥(barX p M T) := by
    have hsub : IsPGroup 2 ↥(T.subgroupOf M) :=
      hT2.comap_of_injective M.subtype Subtype.val_injective
    exact hsub.map _
  have hbarT : barX p M T = ⊥ := by
    have hpC : IsPGroup p ↥(CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup p
    have hI : barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ := by
      have h2 : IsPGroup 2 ↥(barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)) :=
        hT2'.to_le inf_le_left
      have hpp : IsPGroup p ↥(barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)) :=
        hpC.to_le inf_le_right
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 h2
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hpp
      have hb0 : b = 0 := by
        by_contra hb0
        have hdvd : p ∣ 2 ^ a := by
          rw [← ha, hb]
          exact dvd_pow_self p hb0
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hb, hb0, pow_zero])
    calc barX p M T = barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) :=
          (inf_eq_left.2 hxfix).symm
      _ = ⊥ := hI
  have hTp' : T ≤ GLAPPrimeCoreOf p M := by
    intro t ht
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨t, hTM ht⟩ : ↥M)) ∈ barX p M T :=
      ⟨⟨t, hTM ht⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩
    rw [hbarT, Subgroup.mem_bot] at h1
    have h2 := (QuotientGroup.eq_one_iff (⟨t, hTM ht⟩ : ↥M)).1 h1
    unfold GLAPPrimeCoreOf
    exact Subgroup.mem_map.2 ⟨⟨t, hTM ht⟩, h2, rfl⟩
  have hTΓD : T ≤ gammaD D ⊓ GLAPPrimeCoreOf p M :=
    le_inf (h.hT2.trans (gammaStar_le_gammaD p D)) hTp'
  rw [hpc] at hTΓD
  have hTeq : T = pCoreOf 2 M := le_antisymm hTΓD h.hT1
  have hM2ne : pCoreOf 2 M ≠ ⊥ := by
    intro h0
    have hcharM := hS.charTwo M h.pre.1.1
    rw [h0] at hcharM
    have hMb : M ≤ ⊥ := by
      intro x hx
      have hxc : x ∈ Subgroup.centralizer (((⊥ : Subgroup G)) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
        rw [hg, one_mul, mul_one]
      exact hcharM ⟨hx, hxc⟩
    have hBb : B = ⊥ := le_bot_iff.1 (hBM.trans hMb)
    obtain ⟨x, y, hxy⟩ := (hS.nontrivial hB).exists_pair_ne
    apply hxy
    apply Subtype.ext
    have hx : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hBb]
      exact x.2
    have hy : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hBb]
      exact y.2
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  have hIT : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hM2ne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  have hmax : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    h.pre.1.2 _ hIT (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  apply h.hN
  rw [hTeq, hmax]

end Lemma133Fitting

section Lemma133Conj

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_le_iff_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) (X : Subgroup G) :
    GLBConj g X ≤ M ↔ X ≤ M := by
  have hM : GLBConj g M = M := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hM' : GLBConj g⁻¹ M = M := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hg))
  constructor
  · intro h
    have h' := gLBConj_mono g⁻¹ h
    rwa [gLBConj_inv_gLBConj, hM'] at h'
  · intro h
    have h' := gLBConj_mono g h
    rwa [hM] at h'

theorem centralizer_singleton_conj_eq (g d : G) :
    Subgroup.centralizer ({g * d * g⁻¹} : Set G) =
      GLBConj g⁻¹ (Subgroup.centralizer ({d} : Set G)) := by
  have := centralizer_singleton_gLBConj g⁻¹ d
  rwa [inv_inv] at this

theorem prop95Hyp_gLBConj {p : ℕ} {M D : Subgroup G} (h : CFSG.LocalAnalysis.GLTheoremB.Prop95Hyp p M D)
    {g : G} (hg : g ∈ M) : CFSG.LocalAnalysis.GLTheoremB.Prop95Hyp p M (GLBConj g D) := by
  have hαM : GLBConj g⁻¹ (alphaOf p M) = alphaOf p M := by
    have h1 := sec9_alphaOf_gLBConj p g⁻¹ M
    rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hg))] at h1
    exact h1.symm
  have hαM' : GLBConj g (alphaOf p M) = alphaOf p M := by
    have h1 := sec9_alphaOf_gLBConj p g M
    rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h1
    exact h1.symm
  have hd_ne : ∀ d : G, g * d * g⁻¹ ≠ 1 → d ≠ 1 := fun d h1 h2 => h1 (by rw [h2]; group)
  refine ⟨h.twoLocal, (gLBConj_le_iff_of_mem hg D).2 h.le,
    ⟨(sec9_isElemAbelian_gLBConj g h.plane.1), (sec9_card_gLBConj g D).trans h.plane.2⟩, ?_, ?_, ?_⟩
  · intro d hd hd1
    have hd' : g * d * g⁻¹ ∈ D := mem_gLBConj.1 hd
    have hd'1 : g * d * g⁻¹ ≠ 1 := fun h' => hd1 (by
      have : d = g⁻¹ * (g * d * g⁻¹) * g := by group
      rw [this, h']; group)
    have key := h.clause_a _ hd' hd'1
    rw [centralizer_singleton_conj_eq, pCoreOf_gLBConj] at key
    exact (gLBConj_le_iff_of_mem (M.inv_mem hg) _).1 key
  · intro d hd hd1
    have hd' : g * d * g⁻¹ ∈ D := mem_gLBConj.1 hd
    have hd'1 : g * d * g⁻¹ ≠ 1 := fun h' => hd1 (by
      have : d = g⁻¹ * (g * d * g⁻¹) * g := by group
      rw [this, h']; group)
    have key := h.clause_b _ hd' hd'1
    have e1 : alphaOf p M ⊓ Subgroup.centralizer ({g * d * g⁻¹} : Set G) =
        GLBConj g⁻¹ (alphaOf p M ⊓ Subgroup.centralizer ({d} : Set G)) := by
      rw [centralizer_singleton_conj_eq, gLBConj_eq_comap, gLBConj_eq_comap, Subgroup.comap_inf]
      rw [← gLBConj_eq_comap, ← gLBConj_eq_comap, hαM]
    rw [e1, centralizer_singleton_conj_eq, pCoreOf_gLBConj, pCoreOf_gLBConj] at key
    have key2 := gLBConj_mono g key
    rwa [gLBConj_gLBConj_inv, gLBConj_gLBConj_inv] at key2
  · have hpM : GLBConj g (pCoreOf 2 M) = pCoreOf 2 M :=
      gLBConj_eq_of_mem_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg)
    have h1 : pCoreOf 2 M ≤ gammaD D := h.clause_c
    have h2 := gLBConj_mono g h1
    rw [hpM, gammaD_gLBConj] at *
    exact h2

end Lemma133Conj

section Lemma133Blocks

variable {G : Type} [Group G] [Finite G]

theorem IsPiTypeGroup.of_mulEquiv' {p : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsPiTypeGroup p Y) : IsPiTypeGroup p Y' := by
  rcases h with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hΩ, hfp⟩ | ⟨h3, ⟨f⟩⟩
  · exact Or.inl ⟨k, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, ε, hn, IsOmegaTwo.of_mulEquiv e hΩ, hfp⟩)
  · exact Or.inr (Or.inr ⟨h3, ⟨e.symm.trans f⟩⟩)

theorem isPiTypeGroup_of_prop95 {p : ℕ} {M D L : Subgroup G}
    (h : Prop95Alpha p M D L ∨ Prop95Beta p M D L ∨ Prop95Gamma p M D L) :
    IsPiTypeGroup p ↥(barX p M L) := by
  rcases h with hα | hβ | hγ
  · obtain ⟨k, -, -, e, -⟩ := hα
    exact Or.inl ⟨k, ⟨e⟩⟩
  · obtain ⟨n, hn, hβ'⟩ := hβ
    rcases hβ' with ⟨hfp, -, e, -⟩ | ⟨hfp, -, e, -⟩
    · exact Or.inr (Or.inl ⟨n, true, hn, ⟨e⟩, hfp⟩)
    · exact Or.inr (Or.inl ⟨n, false, hn, ⟨e⟩, hfp⟩)
  · obtain ⟨h3, e, -⟩ := hγ
    exact Or.inr (Or.inr ⟨h3, ⟨e⟩⟩)

theorem piGroup_of_block {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) (hT : IsPiTypeGroup p ↥(barX p M L)) :
    IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have e0 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ GLAPPrimeCore p ↥L) :=
    QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two_of_block hp hp2 hL hbl).symm
  have hZ : Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) = ⊥ :=
    center_quotient_eq_bot_of_block hp hp2 hL hbl
  have hQs : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hL.1 hL.2.1).symm hL.2.2.1.2.2
  have hO : GLAPPrimeCore p (↥L ⧸ GLAPPrimeCore p ↥L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hT' : IsPiTypeGroup p (↥L ⧸ GLAPPrimeCore p ↥L) :=
    hT.of_mulEquiv' (quotEquivBarX hp hL.1 hL.2.1).symm
  have hT'' : IsPiTypeGroup p ((↥L ⧸ GLAPPrimeCore p ↥L) ⧸ Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L)) :=
    IsPiTypeGroup.of_mulEquiv' (((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot)).symm) hT'
  have hPi : IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L) := ⟨hQs, hO, hT''⟩
  refine ⟨IsPiGroup.of_mulEquiv e0.symm hPi, ?_⟩
  intro hH
  have hzX : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    have h1 := Subgroup.map_center_eq e0.symm
    rw [hZ, Subgroup.map_bot] at h1
    exact h1.symm
  have h3 := hH.2.1
  rw [hzX, Subgroup.card_bot] at h3
  exact absurd h3 (by norm_num)

end Lemma133Blocks

theorem barX_iSup_le_iSup {G : Type} [Group G] [Finite G] {p : ℕ} {C : Subgroup G} {ι : Type}
    (X : ι → Subgroup G) (hX : ∀ i, X i ≤ C) : barX p C (⨆ i, X i) ≤ ⨆ i, barX p C (X i) := by
  have hsup : (⨆ i, X i) ≤ C := iSup_le hX
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ ⨆ i, X i := Subgroup.mem_subgroupOf.1 hk
  have key : ∀ (x : G) (hx : x ∈ ⨆ i, X i),
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x, hsup hx⟩ : ↥C) ∈ ⨆ i, barX p C (X i) := by
    intro x hx
    refine Subgroup.iSup_induction' X
      (C := fun x hx => QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x, hsup hx⟩ : ↥C) ∈
        ⨆ i, barX p C (X i)) ?_ ?_ ?_ hx
    · intro i x hx
      exact Subgroup.mem_iSup_of_mem i (⟨⟨x, hX i hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩ : _ ∈ barX p C (X i))
    · show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨1, hsup (one_mem _)⟩ : ↥C) ∈ _
      rw [show (⟨1, hsup (one_mem _)⟩ : ↥C) = 1 from rfl, map_one]
      exact one_mem _
    · intro x y hx hy hxC hyC
      show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x * y, hsup (mul_mem hx hy)⟩ : ↥C) ∈ _
      have e : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x * y, hsup (mul_mem hx hy)⟩ : ↥C) =
          QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x, hsup hx⟩ : ↥C) *
            QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨y, hsup hy⟩ : ↥C) := by
        rw [← map_mul]
        rfl
      rw [e]
      exact mul_mem hxC hyC
  exact key (k : G) hk'



section Lemma133Layer

variable {Q : Type} [Group Q] [Finite Q]

theorem isComponentOf_ne_bot' {K : Subgroup Q} (hK : IsComponentOf K ⊤) : K ≠ ⊥ := by
  rintro rfl
  have hsub : Subsingleton (↥(⊥ : Subgroup Q) ⧸ Subgroup.center ↥(⊥ : Subgroup Q)) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        have hx : x = 1 := Subtype.ext (by simpa using (Subgroup.mem_bot.1 x.2))
        have hy : y = 1 := Subtype.ext (by simpa using (Subgroup.mem_bot.1 y.2))
        rw [hx, hy]
  exact (not_nontrivial_iff_subsingleton.2 hsub) hK.2.2.2.toNontrivial

theorem layer_mem {K : Subgroup Q} (hK : IsComponentOf K ⊤) {ι : Type} {F : ι → Subgroup Q}
    (hF : ∀ i, IsComponentOf (F i) ⊤) (hle : K ≤ ⨆ i, F i) : ∃ i, F i = K := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ i, K ≤ Subgroup.centralizer (F i : Set Q) := by
    intro i
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.1
    rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open K).2 hK)
        ((CFSG.isComponent_iff_open (F i)).2 (hF i)) with h | h
    · exact absurd h.symm (hne i)
    · exact h
  have hC : (⨆ i, F i) ≤ Subgroup.centralizer (K : Set Q) := by
    refine iSup_le fun i x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := Subgroup.mem_centralizer_iff.1 (hcomm i hk) x hx
    exact h1.symm
  have hKK : K ≤ Subgroup.centralizer (K : Set Q) := hle.trans hC
  have hperf : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKK
  have hKe : ⁅K, K⁆ = K := (Subgroup.isPerfect_iff (H := K)).mp (Group.isPerfect_def.2 hK.2.2.1)
  exact isComponentOf_ne_bot' hK (hKe.symm.trans hperf)

theorem gLBConj_iSup_eq {ι : Sort*} (y : Q) (F : ι → Subgroup Q) :
    GLBConj y (⨆ i, F i) = ⨆ i, GLBConj y (F i) := by
  unfold GLBConj
  exact Subgroup.map_iSup _ _

end Lemma133Layer

section Lemma133ConjBlock

theorem le_centralizer_of_gLBConj_le {Q : Type} [Group Q] {S K : Subgroup Q} {y : Q}
    (h : GLBConj y S ≤ Subgroup.centralizer ((GLBConj y K : Subgroup Q) : Set Q)) :
    S ≤ Subgroup.centralizer (K : Set Q) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : y⁻¹ * s * y ∈ GLBConj y S := by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hs
  have h2 : y⁻¹ * k * y ∈ GLBConj y K := by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hk
  have h3 := Subgroup.mem_centralizer_iff.1 (h h1) (y⁻¹ * k * y) h2
  calc k * s = y * ((y⁻¹ * k * y) * (y⁻¹ * s * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * s * y) * (y⁻¹ * k * y)) * y⁻¹ := by rw [h3]
    _ = s * k := by group

variable {G : Type} [Group G] [Finite G]

theorem block_of_conj_iv {m p : ℕ} {M D L0 : Subgroup G} (hS : GLStanding G m p)
    (hP95 : Prop95) (hPH : CFSG.LocalAnalysis.GLTheoremB.Prop95Hyp p M D) {g : G} (hg : g ∈ M)
    (hL0 : GLAPComponent p M L0)
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L0 : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    GLAPComponent p M (GLBConj g L0) ∧ IsGLBlock M (GLBConj g L0) ∧
      IsPiTypeGroup p ↥(barX p M (GLBConj g L0)) := by
  have hLM : GLAPComponent p M (GLBConj g L0) := by
    have := glaPComponent_gLBConj hL0 g
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at this
  have hiv := ((hP95 G m p hS M (GLBConj g D) (prop95Hyp_gLBConj hPH hg)).2.2 (GLBConj g L0) hLM).2
  have hrw1 : barX p M (gammaD (GLBConj g D)) = GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)
      (barX p M (gammaD D)) := by
    rw [gammaD_gLBConj, barX_gLBConj_eq p hg]
  have hrw2 : barX p M (GLBConj g L0) = GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)
      (barX p M L0) := barX_gLBConj_eq p hg L0
  have hnc' : ¬ barX p M (gammaD (GLBConj g D)) ≤ Subgroup.centralizer
      ((barX p M (GLBConj g L0) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro hc
    apply hnc
    rw [hrw1, hrw2] at hc
    exact le_centralizer_of_gLBConj_le hc
  rcases hiv with hc | ⟨hbl, halp⟩
  · exact absurd hc hnc'
  · exact ⟨hLM, hbl, isPiTypeGroup_of_prop95 halp⟩

end Lemma133ConjBlock

section Lemma133Istar

variable {G : Type} [Group G] [Finite G]

theorem Iof_le_M (p : ℕ) (M D : Subgroup G) : Iof p M D ≤ M := by
  unfold Iof
  exact iSup₂_le fun L hL => hL.1.1

theorem conj_iSup_mem_le {M I : Subgroup G} {g : G} (hg : g ∈ M) :
    GLBConj g (⨆ h ∈ M, GLBConj h I) ≤ ⨆ h ∈ M, GLBConj h I := by
  refine (le_of_eq (gLBConj_iSup_eq g (fun h : G => ⨆ (_ : h ∈ M), GLBConj h I))).trans ?_
  refine iSup_le fun h => ?_
  refine (le_of_eq (gLBConj_iSup_eq g (fun _ : h ∈ M => GLBConj h I))).trans ?_
  refine iSup_le fun hh => ?_
  rw [gLBConj_gLBConj]
  exact le_iSup₂_of_le (h * g) (M.mul_mem hh hg) le_rfl

theorem istar_conj_le (p : ℕ) {M D : Subgroup G} {g : G} (hg : g ∈ M) :
    GLBConj g (Istar p M D) ≤ Istar p M D :=
  conj_iSup_mem_le (I := Iof p M D) hg

theorem istar_conj_eq (p : ℕ) {M D : Subgroup G} {g : G} (hg : g ∈ M) :
    GLBConj g (Istar p M D) = Istar p M D := by
  refine le_antisymm (istar_conj_le p hg) ?_
  have h1 := gLBConj_mono g (istar_conj_le (D := D) p (M.inv_mem hg))
  rw [gLBConj_gLBConj_inv] at h1
  exact h1

theorem istar_le_M (p : ℕ) (M D : Subgroup G) : Istar p M D ≤ M := by
  unfold Istar
  refine iSup₂_le fun g hg => ?_
  exact (gLBConj_le_iff_of_mem hg _).2 (Iof_le_M p M D)

theorem istar_isSubnormal (p : ℕ) (M D : Subgroup G) : IsSubnormal (Istar p M D) M := by
  refine IsSubnormal.step (istar_le_M p M D) ⟨fun n hn x => Subgroup.mem_subgroupOf.2 ?_⟩
    (IsSubnormal.refl M)
  have hn' : (n : G) ∈ Istar p M D := Subgroup.mem_subgroupOf.1 hn
  have hx : GLBConj (x : G) (Istar p M D) = Istar p M D := istar_conj_eq p x.2
  have hmem : (n : G) ∈ GLBConj (x : G) (Istar p M D) := by
    rw [hx]
    exact hn'
  exact mem_gLBConj.1 hmem

end Lemma133Istar

section Lemma133Components

variable {G : Type} [Group G] [Finite G]

def IsIComp (p : ℕ) (M D L : Subgroup G) : Prop :=
  GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤ Subgroup.centralizer
    ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))

theorem gLBConj_le_iSup_of_le {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q} {ι : Type}
    (F : ι → Subgroup Q)
    (y : Q) (h : S ≤ ⨆ i, F i) : GLBConj y S ≤ ⨆ i, GLBConj y (F i) :=
  (gLBConj_mono y h).trans (le_of_eq (gLBConj_iSup_eq y F))

theorem barX_istar_le {p : ℕ} {M I : Subgroup G} (hI : I ≤ M) :
    barX p M (⨆ j ∈ M, GLBConj j I) ≤ ⨆ y : (↥M ⧸ GLAPPrimeCore p ↥M), GLBConj y (barX p M I) := by
  have := barX_iSup_conj_le p (C := M) (Js := M) (S := I) le_rfl hI
  rw [barX_self] at this
  exact this.trans (iSup₂_le fun y _ => le_iSup_of_le y le_rfl)

theorem barX_le_iSup_conj_of {p : ℕ} {M K I : Subgroup G} {T : Type} (x : T → Subgroup G)
    (hxM : ∀ t, x t ≤ M) (hI : I = ⨆ t, x t) (hIM : I ≤ M) (hK : K ≤ ⨆ j ∈ M, GLBConj j I) :
    barX p M K ≤ ⨆ i : (↥M ⧸ GLAPPrimeCore p ↥M) × T, GLBConj i.1 (barX p M (x i.2)) := by
  have h1 : barX p M K ≤ barX p M (⨆ j ∈ M, GLBConj j I) := barX_mono p hK
  have h2 : barX p M (⨆ j ∈ M, GLBConj j I) ≤ ⨆ y : (↥M ⧸ GLAPPrimeCore p ↥M), GLBConj y (barX p M I) :=
    barX_istar_le hIM
  have h3 : barX p M I ≤ ⨆ t, barX p M (x t) := by
    rw [hI]
    exact barX_iSup_le_iSup x hxM
  refine h1.trans (h2.trans (iSup_le fun y => ?_))
  exact (gLBConj_le_iSup_of_le (fun t => barX p M (x t)) y h3).trans
    (iSup_le fun t => le_iSup_of_le (y, t) le_rfl)

theorem glaPComponent_conj_mem {p : ℕ} {M L0 : Subgroup G} (hL0 : GLAPComponent p M L0) {g : G}
    (hg : g ∈ M) : GLAPComponent p M (GLBConj g L0) := by
  have := glaPComponent_gLBConj hL0 g
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at this

theorem Iof_eq_iSup_subtype (p : ℕ) (M D : Subgroup G) :
    Iof p M D = ⨆ x : {L0 : Subgroup G // IsIComp p M D L0}, x.1 := by
  unfold Iof
  exact le_antisymm (iSup₂_le fun L0 h => le_iSup_of_le ⟨L0, h⟩ le_rfl)
    (iSup_le fun x => le_iSup₂_of_le x.1 x.2 le_rfl)

theorem istar_component {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    ∃ g ∈ M, ∃ L0 : Subgroup G, IsIComp p M D L0 ∧ L = GLBConj g L0 := by
  have hNM : Istar p M D ≤ M := istar_le_M p M D
  have hsubN : IsSubnormal (Istar p M D) M := istar_isSubnormal p M D
  have hLN : L ≤ Istar p M D := hL.1
  have hLM : L ≤ M := hLN.trans hNM
  have hsnL : IsSubnormal L M := isSubnormal_trans' hL.2.1 hsubN
  have hcompQ : IsComponentOf (barX p M L) ⊤ := by
    have e : ↥(barX p M L) ≃* ↥(barX p (Istar p M D) L) :=
      (quotEquivBarX hp hLM hsnL).symm.trans (quotEquivBarX hp hLN hL.2.1)
    refine ⟨le_top, ?_, ?_⟩
    · have := isSubnormal_barX p (C := M) hsnL
      rwa [barX_self] at this
    · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
        hL.2.2.1.2.2
  have hK_le : barX p M L ≤ ⨆ i : (↥M ⧸ GLAPPrimeCore p ↥M) × {L0 : Subgroup G // IsIComp p M D L0},
      GLBConj i.1 (barX p M (i.2 : Subgroup G)) :=
    barX_le_iSup_conj_of (fun t : {L0 : Subgroup G // IsIComp p M D L0} => t.1)
      (fun t => t.2.1.1) (Iof_eq_iSup_subtype p M D) (Iof_le_M p M D) hLN
  have hcomp0 : ∀ t : {L0 : Subgroup G // IsIComp p M D L0}, IsComponentOf (barX p M t.1) ⊤ :=
    fun t => t.2.1.2.2.1
  have hF : ∀ i : (↥M ⧸ GLAPPrimeCore p ↥M) × {L0 : Subgroup G // IsIComp p M D L0},
      IsComponentOf (GLBConj i.1 (barX p M i.2.1)) ⊤ := fun i => isComponentOf_gLBConj (hcomp0 i.2) i.1
  obtain ⟨⟨y, ⟨L0, hL0⟩⟩, hFy⟩ := layer_mem hcompQ hF hK_le
  obtain ⟨⟨g, hg⟩, hgy⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥M) y
  subst hgy
  rw [← barX_gLBConj_eq p hg L0] at hFy
  have hL0M : GLBConj g L0 ≤ Istar p M D := by
    refine le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g (Iof p M D)) g hg ?_
    exact gLBConj_mono g (le_iSup₂_of_le (f := fun L (_ : IsIComp p M D L) => L) L0 hL0 le_rfl)
  have hN2 : GLAPComponent p (Istar p M D) (GLBConj g L0) :=
    glaPComponent_of_le hp (glaPComponent_conj_mem hL0.1 hg) hL0M hNM
  have hbarN : barX p (Istar p M D) L = barX p (Istar p M D) (GLBConj g L0) := by
    have hJ : ∀ (K J : Subgroup G), K ≤ Istar p M D → J ≤ Istar p M D → K ≤ M → J ≤ M →
        barX p M K ≤ barX p M J → barX p (Istar p M D) K ≤ barX p (Istar p M D) J := by
      intro K J hKN hJN hKM hJM hle
      refine barX_le_of_forall hJN fun k hk => ?_
      obtain ⟨j, hj, hjk⟩ := exists_of_barX_le hle hk (hKM hk)
      refine ⟨j, hj, ?_⟩
      have hmem : j⁻¹ * k ∈ Istar p M D ⊓ GLAPPrimeCoreOf p M :=
        ⟨(Istar p M D).mul_mem ((Istar p M D).inv_mem (hJN hj)) (hKN hk), hjk⟩
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsubN] at hmem
      exact hmem
    have hL0M' : GLBConj g L0 ≤ M := hL0M.trans hNM
    exact le_antisymm (hJ L (GLBConj g L0) hLN hL0M hLM hL0M' hFy.symm.le)
      (hJ (GLBConj g L0) L hL0M hLN hL0M' hLM hFy.le)
  exact ⟨g, hg, L0, hL0, glaPComponent_unique hL hN2 hbarN⟩

end Lemma133Components

section Lemma133Arith

theorem pow_mul_eq_pow_mul_coprime {p α β u v : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) (hv : ¬ p ∣ v)
    (h : p ^ α * u = p ^ β * v) : α = β ∧ u = v := by
  haveI := Fact.mk hp
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero p)
  have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ dvd_zero p)
  have hp0 : p ^ α ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hp1 : p ^ β ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 := congrArg (padicValNat p) h
  rw [padicValNat.mul hp0 hu0, padicValNat.mul hp1 hv0, padicValNat.prime_pow,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu,
    padicValNat.eq_zero_of_not_dvd hv] at h1
  have hαβ : α = β := by simpa using h1
  subst hαβ
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h⟩

end Lemma133Arith

section SylowDecompCore

variable {H : Type} [Group H] [Finite H]

theorem isPGroup_inf_eq_bot_of_not_dvd {p : ℕ} (hp : p.Prime) {S N : Subgroup H} (hS : IsPGroup p S)
    (hN : ¬ p ∣ Nat.card N) : S ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgS, hgN⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨k, hk⟩ := hS ⟨g, hgS⟩
  have hk' : g ^ p ^ k = 1 := congrArg Subtype.val hk
  have hN' : g ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := N) (x := ⟨g, hgN⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  have h1 : g ^ Nat.gcd (p ^ k) (Nat.card N) = 1 := by
    rw [pow_gcd_eq_one]
    exact ⟨hk', hN'⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact Subgroup.mem_bot.2 h1

theorem sylow_pieces_commute {p : ℕ} (hp : p.Prime) {L C : Subgroup H} {S : Subgroup H}
    (hS : IsPGroup p S) (hN0 : ¬ p ∣ Nat.card (L ⊓ C : Subgroup H))
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, c * l * c⁻¹ * l⁻¹ ∈ L ⊓ C) :
    ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ C, x * y = y * x := by
  intro x hx y hy
  obtain ⟨hxS, hxL⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.1 hy
  have h1 : y * x * y⁻¹ * x⁻¹ ∈ S ⊓ (L ⊓ C) := by
    refine Subgroup.mem_inf.2 ⟨?_, hcomm x hxL y hyC⟩
    exact S.mul_mem (S.mul_mem (S.mul_mem hyS hxS) (S.inv_mem hyS)) (S.inv_mem hxS)
  have h2 : S ⊓ (L ⊓ C) = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp hS hN0
  rw [h2, Subgroup.mem_bot] at h1
  have h3 : y * x * y⁻¹ * x⁻¹ = 1 := h1
  have h4 : y * x = x * y := by
    calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
      _ = x * y := by rw [h3, one_mul]
  exact h4.symm

theorem sylow_split {p : ℕ} (hp : p.Prime) {L C : Subgroup H}
    (hCN : C ≤ Subgroup.normalizer (L : Set H)) (hLN : L ≤ Subgroup.normalizer (C : Set H))
    (hX : L ⊔ C = ⊤) (hN0 : ¬ p ∣ Nat.card (L ⊓ C : Subgroup H))
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, c * l * c⁻¹ * l⁻¹ ∈ L ⊓ C) (S : Sylow p H) :
    S.toSubgroup = (S.toSubgroup ⊓ L) ⊔ (S.toSubgroup ⊓ C) := by
  haveI := Fact.mk hp
  have hSp : IsPGroup p S.toSubgroup := S.isPGroup'
  have hNL : Subgroup.normalizer (L : Set H) = ⊤ := by
    rw [eq_top_iff, ← hX]
    exact sup_le Subgroup.le_normalizer hCN
  have hNC : Subgroup.normalizer (C : Set H) = ⊤ := by
    rw [eq_top_iff, ← hX, sup_comm]
    exact sup_le Subgroup.le_normalizer hLN
  have hcS := sylow_pieces_commute hp hSp hN0 hcomm
  have hint : (S.toSubgroup ⊓ L) ⊓ (S.toSubgroup ⊓ C) = ⊥ := by
    have e : (S.toSubgroup ⊓ L) ⊓ (S.toSubgroup ⊓ C) = S.toSubgroup ⊓ (L ⊓ C) := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [e, isPGroup_inf_eq_bot_of_not_dvd hp hSp hN0]
  have hSgpos : 0 < Nat.card S.toSubgroup := Nat.card_pos
  have hr : ¬ p ∣ S.index := Sylow.not_dvd_index S
  have hHS : Nat.card S.toSubgroup * S.index = Nat.card H := Subgroup.card_mul_index _
  have hprodL := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer
    (A := S.toSubgroup) (B := L) (by rw [hNL]; exact le_top)
  have hprodC := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer
    (A := S.toSubgroup) (B := C) (by rw [hNC]; exact le_top)
  have hprodLC := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer
    (A := C) (B := L) hCN
  have hq1 : S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * Nat.card (S.toSubgroup ⊓ (S.toSubgroup ⊔ L) : Subgroup H) =
      Nat.card (S.toSubgroup ⊔ L : Subgroup H) := Subgroup.relIndex_mul_card S.toSubgroup (S.toSubgroup ⊔ L)
  have hq2 : S.toSubgroup.relIndex (S.toSubgroup ⊔ C) * Nat.card (S.toSubgroup ⊓ (S.toSubgroup ⊔ C) : Subgroup H) =
      Nat.card (S.toSubgroup ⊔ C : Subgroup H) := Subgroup.relIndex_mul_card S.toSubgroup (S.toSubgroup ⊔ C)
  rw [inf_eq_left.2 le_sup_left] at hq1 hq2
  have hKL : Nat.card (S.toSubgroup ⊔ L : Subgroup H) * (S.toSubgroup ⊔ L).index = Nat.card H :=
    Subgroup.card_mul_index _
  have hKC : Nat.card (S.toSubgroup ⊔ C : Subgroup H) * (S.toSubgroup ⊔ C).index = Nat.card H :=
    Subgroup.card_mul_index _
  have hq1r : S.index = S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * (S.toSubgroup ⊔ L).index := by
    apply Nat.eq_of_mul_eq_mul_left hSgpos
    rw [hHS, ← hKL, ← hq1]
    ring
  have hq2r : S.index = S.toSubgroup.relIndex (S.toSubgroup ⊔ C) * (S.toSubgroup ⊔ C).index := by
    apply Nat.eq_of_mul_eq_mul_left hSgpos
    rw [hHS, ← hKC, ← hq2]
    ring
  have hnq1 : ¬ p ∣ S.toSubgroup.relIndex (S.toSubgroup ⊔ L) :=
    fun h => hr (by rw [hq1r]; exact Dvd.dvd.mul_right h _)
  have hnq2 : ¬ p ∣ S.toSubgroup.relIndex (S.toSubgroup ⊔ C) :=
    fun h => hr (by rw [hq2r]; exact Dvd.dvd.mul_right h _)
  have hL_eq : Nat.card L = S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * Nat.card (S.toSubgroup ⊓ L : Subgroup H) := by
    apply Nat.eq_of_mul_eq_mul_left hSgpos
    have h := hprodL
    rw [← hq1] at h
    rw [← h]
    ring
  have hC_eq : Nat.card C = S.toSubgroup.relIndex (S.toSubgroup ⊔ C) * Nat.card (S.toSubgroup ⊓ C : Subgroup H) := by
    apply Nat.eq_of_mul_eq_mul_left hSgpos
    have h := hprodC
    rw [← hq2] at h
    rw [← h]
    ring
  have hCL : C ⊔ L = ⊤ := by rw [sup_comm]; exact hX
  rw [hCL, Subgroup.card_top, inf_comm C L] at hprodLC
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hSp
  have hpc : IsPGroup p (S.toSubgroup ⊓ L ⊔ S.toSubgroup ⊓ C : Subgroup H) :=
    hSp.to_le (sup_le inf_le_left inf_le_left)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hpc
  have hprod12 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (S.toSubgroup ⊓ L) (S.toSubgroup ⊓ C) hcS).1
  rw [hint, Subgroup.card_bot] at hprod12
  have hs12 : Nat.card (S.toSubgroup ⊓ L : Subgroup H) * Nat.card (S.toSubgroup ⊓ C : Subgroup H) = p ^ b := by
    rw [← hb, ← hprod12, mul_one]
  have hkey : Nat.card S.toSubgroup * (S.index * Nat.card (L ⊓ C : Subgroup H)) =
      S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * S.toSubgroup.relIndex (S.toSubgroup ⊔ C) *
        (Nat.card (S.toSubgroup ⊓ L : Subgroup H) * Nat.card (S.toSubgroup ⊓ C : Subgroup H)) := by
    calc Nat.card S.toSubgroup * (S.index * Nat.card (L ⊓ C : Subgroup H))
        = Nat.card H * Nat.card (L ⊓ C : Subgroup H) := by rw [← hHS]; ring
      _ = Nat.card C * Nat.card L := hprodLC
      _ = (S.toSubgroup.relIndex (S.toSubgroup ⊔ C) * Nat.card (S.toSubgroup ⊓ C : Subgroup H)) *
            (S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * Nat.card (S.toSubgroup ⊓ L : Subgroup H)) := by
          rw [hC_eq, hL_eq]
      _ = _ := by ring
  have hEq : p ^ a * (S.index * Nat.card (L ⊓ C : Subgroup H)) =
      p ^ b * (S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * S.toSubgroup.relIndex (S.toSubgroup ⊔ C)) := by
    rw [← ha, hkey, ← hs12]
    ring
  have hu : ¬ p ∣ S.index * Nat.card (L ⊓ C : Subgroup H) :=
    fun h => (hp.dvd_mul.1 h).elim hr hN0
  have hv : ¬ p ∣ S.toSubgroup.relIndex (S.toSubgroup ⊔ L) * S.toSubgroup.relIndex (S.toSubgroup ⊔ C) :=
    fun h => (hp.dvd_mul.1 h).elim hnq1 hnq2
  obtain ⟨hab, -⟩ := pow_mul_eq_pow_mul_coprime hp hu hv hEq
  have hle : (S.toSubgroup ⊓ L ⊔ S.toSubgroup ⊓ C : Subgroup H) ≤ S.toSubgroup :=
    sup_le inf_le_left inf_le_left
  have hcard : Nat.card S.toSubgroup ≤ Nat.card (S.toSubgroup ⊓ L ⊔ S.toSubgroup ⊓ C : Subgroup H) := by
    rw [ha, hb, hab]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_mul_of_mem_sup_of_commute {s t : Subgroup H} (hc : ∀ x ∈ s, ∀ y ∈ t, x * y = y * x)
    {x : H} (hx : x ∈ s ⊔ t) : ∃ l ∈ s, ∃ c ∈ t, l * c = x := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute s t hc).2
  have hx' : x ∈ ((s ⊔ t : Subgroup H) : Set H) := hx
  rw [h] at hx'
  exact Set.mem_mul.1 hx'

theorem factor_unique {s t : Subgroup H} (hint : s ⊓ t = ⊥) {l l' c c' : H} (hl : l ∈ s)
    (hl' : l' ∈ s) (hc : c ∈ t) (hc' : c' ∈ t) (h : l * c = l' * c') : l = l' ∧ c = c' := by
  have h1 : l'⁻¹ * l = c' * c⁻¹ := by
    calc l'⁻¹ * l = l'⁻¹ * (l * c) * c⁻¹ := by group
      _ = l'⁻¹ * (l' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have hmem : l'⁻¹ * l ∈ s ⊓ t :=
    Subgroup.mem_inf.2 ⟨s.mul_mem (s.inv_mem hl') hl, h1 ▸ t.mul_mem hc' (t.inv_mem hc)⟩
  have hone : l'⁻¹ * l = 1 := by
    have h2 := hmem
    rw [hint] at h2
    exact Subgroup.mem_bot.1 h2
  have hll : l = l' := (inv_mul_eq_one.1 hone).symm
  have hcc : c = c' := by
    have h2 : c' * c⁻¹ = 1 := by rw [← h1]; exact hone
    exact (mul_inv_eq_one.1 h2).symm
  exact ⟨hll, hcc⟩

theorem isElemAbelian_of_comm_pow {p : ℕ} {E : Subgroup H} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hpow : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hpow x hx⟩
  exact Subtype.ext (hc a a.2 b b.2)

theorem decomp_core {p : ℕ} (hp : p.Prime) {L C : Subgroup H}
    (hCN : C ≤ Subgroup.normalizer (L : Set H)) (hLN : L ≤ Subgroup.normalizer (C : Set H))
    (hX : L ⊔ C = ⊤) (hN0 : ¬ p ∣ Nat.card (L ⊓ C : Subgroup H))
    (hcomm : ∀ l ∈ L, ∀ c ∈ C, c * l * c⁻¹ * l⁻¹ ∈ L ⊓ C) {m : ℕ}
    (hrank : ∀ V : Subgroup H, IsElemAbelian p V → Nat.card V ≤ p ^ m)
    (B : Subgroup H) (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ m) (S : Sylow p H)
    (hBS : B ≤ S.toSubgroup) :
    (∀ b ∈ B, ∃ l ∈ B ⊓ L, ∃ c ∈ B ⊓ C, b = l * c) ∧
      ∃ e : ℕ, Nat.card (B ⊓ (S.toSubgroup ⊓ L) : Subgroup H) = p ^ e ∧
        CFSG.Open.pRank p (S.toSubgroup ⊓ L : Subgroup H) = e := by
  haveI := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  have hNL : Subgroup.normalizer (L : Set H) = ⊤ := by
    rw [eq_top_iff, ← hX]
    exact sup_le Subgroup.le_normalizer hCN
  have hLnorm : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (L : Set H) := by rw [hNL]; exact Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  have hSdec := sylow_split hp hCN hLN hX hN0 hcomm S
  set Sg : Subgroup H := S.toSubgroup with hSgdef
  have hSp : IsPGroup p Sg := S.isPGroup'
  have hcS := sylow_pieces_commute hp hSp hN0 hcomm
  have hint : (Sg ⊓ L) ⊓ (Sg ⊓ C) = ⊥ := by
    have e : (Sg ⊓ L) ⊓ (Sg ⊓ C) = Sg ⊓ (L ⊓ C) := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [e, isPGroup_inf_eq_bot_of_not_dvd hp hSp hN0]
  have hBp : IsPGroup p B := IsPGroup.iff_card.2 ⟨m, hBcard⟩
  have hdec : ∀ x ∈ Sg, ∃ l ∈ Sg ⊓ L, ∃ c ∈ Sg ⊓ C, x = l * c := by
    intro x hx
    have hx' : x ∈ (Sg ⊓ L) ⊔ (Sg ⊓ C) := hSdec ▸ hx
    obtain ⟨l, hl, c, hc, hlc⟩ := exists_mul_of_mem_sup_of_commute hcS hx'
    exact ⟨l, hl, c, hc, hlc.symm⟩
  have hSnorm : Sg ≤ Subgroup.normalizer ((Sg ⊓ L : Subgroup H) : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hy' := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_inf.2 ⟨Sg.mul_mem (Sg.mul_mem hx hy'.1) (Sg.inv_mem hx),
        hLnorm.conj_mem y hy'.2 x⟩
    · intro hy
      have hy' := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have := Sg.mul_mem (Sg.mul_mem (Sg.inv_mem hx) hy'.1) hx
        simpa [mul_assoc] using this
      · have := hLnorm.conj_mem (x * y * x⁻¹) hy'.2 x⁻¹
        simpa [mul_assoc] using this
  have hBnorm : B ≤ Subgroup.normalizer ((Sg ⊓ L : Subgroup H) : Set H) := hBS.trans hSnorm
  set Y : Subgroup H := B ⊔ (Sg ⊓ L) with hYdef
  set T : Subgroup H := Y ⊓ (Sg ⊓ C) with hTdef
  have hTSg : T ≤ Sg := inf_le_right.trans inf_le_left
  have hTC : T ≤ Sg ⊓ C := inf_le_right
  have hTp : IsPGroup p T := hSp.to_le hTSg
  have hYT : Y = (Sg ⊓ L) ⊔ T := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_left
      intro b hb
      obtain ⟨l, hl, c, hc, hbl⟩ := hdec b (hBS hb)
      have hcb : c = l⁻¹ * b := by
        rw [hbl]
        group
      have hcY : c ∈ Y := by
        rw [hcb]
        exact Y.mul_mem (Y.inv_mem (Subgroup.mem_sup_right hl)) (Subgroup.mem_sup_left hb)
      have hcT : c ∈ T := Subgroup.mem_inf.2 ⟨hcY, hc⟩
      rw [hbl]
      exact (Sg ⊓ L ⊔ T).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hcT)
    · exact sup_le le_sup_right inf_le_left
  have hcomm2 : ∀ x ∈ Sg ⊓ L, ∀ y ∈ T, x * y = y * x := fun x hx y hy => hcS x hx y (hTC hy)
  have hST : (Sg ⊓ L) ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := Subgroup.mem_inf.1 hx
    have h2 : x ∈ (Sg ⊓ L) ⊓ (Sg ⊓ C) := Subgroup.mem_inf.2 ⟨h1.1, hTC h1.2⟩
    rw [hint] at h2
    exact h2
  have hs1pos : 0 < Nat.card (Sg ⊓ L : Subgroup H) := Nat.card_pos
  have hYB := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hBnorm
  have hYcard : Nat.card Y = Nat.card (Sg ⊓ L : Subgroup H) * Nat.card T := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Sg ⊓ L) T hcomm2).1
    rw [hST, Subgroup.card_bot, ← hYT, mul_one] at this
    exact this
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 (hBp.to_le (inf_le_left : B ⊓ (Sg ⊓ L) ≤ B))
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.1 hTp
  have hTE : Nat.card T * p ^ e = p ^ m := by
    apply Nat.eq_of_mul_eq_mul_left hs1pos
    have h1 := hYB
    rw [hYcard, he, hBcard] at h1
    calc Nat.card (Sg ⊓ L : Subgroup H) * (Nat.card T * p ^ e)
        = Nat.card (Sg ⊓ L : Subgroup H) * Nat.card T * p ^ e := by ring
      _ = p ^ m * Nat.card (Sg ⊓ L : Subgroup H) := h1
      _ = Nat.card (Sg ⊓ L : Subgroup H) * p ^ m := by ring
  have hte : t + e = m := by
    have : p ^ (t + e) = p ^ m := by rw [pow_add, ← ht, hTE]
    exact Nat.pow_right_injective hp.two_le this
  haveI := hLnorm
  have hfac : ∀ x ∈ T, ∃ b ∈ B, ∃ l ∈ Sg ⊓ L, b * l = x := by
    intro x hx
    have hxY : x ∈ B ⊔ L := sup_le_sup_left inf_le_right B (Subgroup.mem_inf.1 hx).1
    obtain ⟨b, hb, z, hz, hbz⟩ := Subgroup.mem_sup_of_normal_right.1 hxY
    have hzS : z ∈ Sg := by
      have hz' : z = b⁻¹ * x := by rw [← hbz]; group
      rw [hz']
      exact Sg.mul_mem (Sg.inv_mem (hBS hb)) (hTSg hx)
    exact ⟨b, hb, z, Subgroup.mem_inf.2 ⟨hzS, hz⟩, hbz⟩
  have hTcomm : ∀ t1 ∈ T, ∀ t2 ∈ T, t1 * t2 = t2 * t1 := by
    intro t1 ht1 t2 ht2
    obtain ⟨b1, hb1, l1, hl1, hbl1⟩ := hfac t1 ht1
    obtain ⟨b2, hb2, l2, hl2, hbl2⟩ := hfac t2 ht2
    have hcomm12 : b1 * b2 = b2 * b1 := elemAbelian_comm hB hb1 hb2
    have hb1' : b1 = t1 * l1⁻¹ := by rw [← hbl1]; group
    have hb2' : b2 = t2 * l2⁻¹ := by rw [← hbl2]; group
    have hl1i : l1⁻¹ ∈ Sg ⊓ L := (Sg ⊓ L).inv_mem hl1
    have hl2i : l2⁻¹ ∈ Sg ⊓ L := (Sg ⊓ L).inv_mem hl2
    have c1 : l1⁻¹ * t2 = t2 * l1⁻¹ := hcS _ hl1i _ (hTC ht2)
    have c2 : l2⁻¹ * t1 = t1 * l2⁻¹ := hcS _ hl2i _ (hTC ht1)
    have h1 : t1 * t2 * (l1⁻¹ * l2⁻¹) = t2 * t1 * (l2⁻¹ * l1⁻¹) := by
      have hh := hcomm12
      rw [hb1', hb2'] at hh
      calc t1 * t2 * (l1⁻¹ * l2⁻¹) = t1 * (t2 * l1⁻¹) * l2⁻¹ := by group
        _ = t1 * (l1⁻¹ * t2) * l2⁻¹ := by rw [c1]
        _ = t1 * l1⁻¹ * (t2 * l2⁻¹) := by group
        _ = t2 * l2⁻¹ * (t1 * l1⁻¹) := hh
        _ = t2 * (l2⁻¹ * t1) * l1⁻¹ := by group
        _ = t2 * (t1 * l2⁻¹) * l1⁻¹ := by rw [c2]
        _ = t2 * t1 * (l2⁻¹ * l1⁻¹) := by group
    have hu1 : (l1⁻¹ * l2⁻¹) ∈ Sg ⊓ L := (Sg ⊓ L).mul_mem hl1i hl2i
    have hu2 : (l2⁻¹ * l1⁻¹) ∈ Sg ⊓ L := (Sg ⊓ L).mul_mem hl2i hl1i
    have hv1 : (t1 * t2) ∈ Sg ⊓ C := (Sg ⊓ C).mul_mem (hTC ht1) (hTC ht2)
    have hv2 : (t2 * t1) ∈ Sg ⊓ C := (Sg ⊓ C).mul_mem (hTC ht2) (hTC ht1)
    have e1 : (l1⁻¹ * l2⁻¹) * (t1 * t2) = (t1 * t2) * (l1⁻¹ * l2⁻¹) := hcS _ hu1 _ hv1
    have e2 : (l2⁻¹ * l1⁻¹) * (t2 * t1) = (t2 * t1) * (l2⁻¹ * l1⁻¹) := hcS _ hu2 _ hv2
    have hu : (l1⁻¹ * l2⁻¹) * (t1 * t2) = (l2⁻¹ * l1⁻¹) * (t2 * t1) := by
      rw [e1, e2]
      have h1' : (t1 * t2) * (l1⁻¹ * l2⁻¹) = (t2 * t1) * (l2⁻¹ * l1⁻¹) := h1
      exact h1'
    exact (factor_unique hint hu1 hu2 hv1 hv2 hu).2
  have hTexp : ∀ t ∈ T, t ^ p = 1 := by
    intro t ht
    obtain ⟨b, hb, l, hl, hbl⟩ := hfac t ht
    have hbt : b = t * l⁻¹ := by rw [← hbl]; group
    have hcom' : Commute t l⁻¹ := (hcS _ ((Sg ⊓ L).inv_mem hl) t (hTC ht)).symm
    have hbp : b ^ p = 1 := hB.2 b hb
    rw [hbt, hcom'.mul_pow] at hbp
    have htp : t ^ p = l ^ p := by
      have h2 : t ^ p = ((l⁻¹) ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hbp
      rw [h2, inv_pow, inv_inv]
    have h1 : t ^ p ∈ (Sg ⊓ L) ⊓ (Sg ⊓ C) :=
      Subgroup.mem_inf.2 ⟨by rw [htp]; exact (Sg ⊓ L).pow_mem hl p, (Sg ⊓ C).pow_mem (hTC ht) p⟩
    rw [hint, Subgroup.mem_bot] at h1
    exact h1
  have hTel : IsElemAbelian p T := isElemAbelian_of_comm_pow hTcomm hTexp
  obtain ⟨V, hVle, hVel, hVcard⟩ := CFSG.SectionRank.exists_pRank hp1 (Sg ⊓ L : Subgroup H)
  have hcVT : ∀ v ∈ V, ∀ t' ∈ T, v * t' = t' * v := fun v hv t' ht' => hcS v (hVle hv) t' (hTC ht')
  have hVTel : IsElemAbelian p (V ⊔ T) := by
    apply isElemAbelian_of_comm_pow
    · intro x hx y hy
      obtain ⟨v1, hv1, t1, ht1, rfl⟩ := exists_mul_of_mem_sup_of_commute hcVT hx
      obtain ⟨v2, hv2, t2, ht2, rfl⟩ := exists_mul_of_mem_sup_of_commute hcVT hy
      have e1 : t1 * v2 = v2 * t1 := (hcVT v2 hv2 t1 ht1).symm
      have e2 : t2 * v1 = v1 * t2 := (hcVT v1 hv1 t2 ht2).symm
      have ev : v1 * v2 = v2 * v1 := elemAbelian_comm hVel hv1 hv2
      have et : t1 * t2 = t2 * t1 := hTcomm t1 ht1 t2 ht2
      calc v1 * t1 * (v2 * t2) = v1 * (t1 * v2) * t2 := by group
        _ = v1 * (v2 * t1) * t2 := by rw [e1]
        _ = (v1 * v2) * (t1 * t2) := by group
        _ = (v2 * v1) * (t2 * t1) := by rw [ev, et]
        _ = v2 * (v1 * t2) * t1 := by group
        _ = v2 * (t2 * v1) * t1 := by rw [e2]
        _ = v2 * t2 * (v1 * t1) := by group
    · intro x hx
      obtain ⟨v, hv, t', ht', rfl⟩ := exists_mul_of_mem_sup_of_commute hcVT hx
      rw [(show Commute v t' from hcVT v hv t' ht').mul_pow, hVel.2 v hv, hTexp t' ht', one_mul]
  have hVT_card : Nat.card (V ⊔ T : Subgroup H) = p ^ CFSG.Open.pRank p (Sg ⊓ L : Subgroup H) * p ^ t := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V T hcVT).1
    have hVTinf : V ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h2 : x ∈ (Sg ⊓ L) ⊓ (Sg ⊓ C) := Subgroup.mem_inf.2 ⟨hVle (Subgroup.mem_inf.1 hx).1, hTC (Subgroup.mem_inf.1 hx).2⟩
      rw [hint] at h2
      exact h2
    rw [hVTinf, Subgroup.card_bot, mul_one, hVcard, ht] at this
    exact this
  have hr_le : CFSG.Open.pRank p (Sg ⊓ L : Subgroup H) ≤ e := by
    have hle1 := hrank (V ⊔ T) hVTel
    rw [hVT_card, ← pow_add] at hle1
    have : CFSG.Open.pRank p (Sg ⊓ L : Subgroup H) + t ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle1
    omega
  have he_le : e ≤ CFSG.Open.pRank p (Sg ⊓ L : Subgroup H) :=
    CFSG.SectionRank.le_pRank hp1 (inf_le_right : B ⊓ (Sg ⊓ L) ≤ Sg ⊓ L) (isElemAbelian_mono hB inf_le_left) he
  have hre : CFSG.Open.pRank p (Sg ⊓ L : Subgroup H) = e := le_antisymm hr_le he_le
  refine ⟨?_, e, he, hre⟩
  intro b hb
  obtain ⟨l, hl, c, hc, hblc⟩ := hdec b (hBS hb)
  by_cases hlB : l ∈ B
  · refine ⟨l, Subgroup.mem_inf.2 ⟨hlB, (Subgroup.mem_inf.1 hl).2⟩, c,
      Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hc).2⟩, hblc⟩
    have hcb : c = l⁻¹ * b := by rw [hblc]; group
    rw [hcb]
    exact B.mul_mem (B.inv_mem hlB) hb
  · exfalso
    have hl1 : l ≠ 1 := fun h => hlB (by rw [h]; exact B.one_mem)
    have hcom_lc : Commute l c := hcS l hl c hc
    have hlp : l ^ p = 1 := by
      have hbp : (l * c) ^ p = 1 := by
        rw [← hblc]
        exact hB.2 b hb
      rw [hcom_lc.mul_pow] at hbp
      have h2 : l ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hbp
      have h3 : l ^ p ∈ (Sg ⊓ L) ⊓ (Sg ⊓ C) := by
        refine Subgroup.mem_inf.2 ⟨(Sg ⊓ L).pow_mem hl p, ?_⟩
        rw [h2]
        exact (Sg ⊓ C).inv_mem ((Sg ⊓ C).pow_mem hc p)
      rw [hint, Subgroup.mem_bot] at h3
      exact h3
    have hlo : orderOf l = p := orderOf_eq_prime hlp hl1
    have hzl_le : Subgroup.zpowers l ≤ Sg ⊓ L := Subgroup.zpowers_le.2 hl
    have hcommE : ∀ x ∈ B ⊓ (Sg ⊓ L), ∀ z ∈ Subgroup.zpowers l, x * z = z * x := by
      intro x hx z hz
      have hxl : x * l = l * x := by
        have hxb : x * (l * c) = (l * c) * x := by
          rw [← hblc]
          exact elemAbelian_comm hB (Subgroup.mem_inf.1 hx).1 hb
        have hxc : x * c = c * x := hcS x (Subgroup.mem_inf.1 hx).2 c hc
        have key : x * l * c = l * x * c := by
          calc x * l * c = x * (l * c) := by group
            _ = (l * c) * x := hxb
            _ = l * (c * x) := by group
            _ = l * (x * c) := by rw [hxc]
            _ = l * x * c := by group
        exact mul_right_cancel key
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact ((show Commute x l from hxl).zpow_right k).eq
    have hzpow : ∀ z ∈ Subgroup.zpowers l, z ^ p = 1 := by
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hlp, one_zpow]
    have hinter : (B ⊓ (Sg ⊓ L)) ⊓ Subgroup.zpowers l = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxB, hxz⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hxo : orderOf x = p := orderOf_eq_prime (hzpow x hxz) hx1
      have hzx : Subgroup.zpowers x = Subgroup.zpowers l := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxz)
        rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hlo]
      have hlx : l ∈ Subgroup.zpowers x := by
        rw [hzx]
        exact Subgroup.mem_zpowers l
      have hzxB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 (Subgroup.mem_inf.1 hxB).1
      exact hlB (hzxB hlx)
    have hE'el : IsElemAbelian p ((B ⊓ (Sg ⊓ L)) ⊔ Subgroup.zpowers l) := by
      apply isElemAbelian_of_comm_pow
      · intro x hx y hy
        obtain ⟨u1, hu1, z1, hz1, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommE hx
        obtain ⟨u2, hu2, z2, hz2, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommE hy
        have c1 : Commute u1 u2 :=
          elemAbelian_comm hB (Subgroup.mem_inf.1 hu1).1 (Subgroup.mem_inf.1 hu2).1
        have c2 : Commute u1 z2 := hcommE u1 hu1 z2 hz2
        have c3 : Commute z1 u2 := (hcommE u2 hu2 z1 hz1).symm
        have c4 : Commute z1 z2 := by
          obtain ⟨k1, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
          obtain ⟨k2, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz2
          exact ((Commute.refl l).zpow_left k1).zpow_right k2
        exact (Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)).eq
      · intro x hx
        obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommE hx
        rw [(show Commute u z from hcommE u hu z hz).mul_pow, hB.2 u (Subgroup.mem_inf.1 hu).1,
          hzpow z hz, one_mul]
    have hEcard : Nat.card ((B ⊓ (Sg ⊓ L)) ⊔ Subgroup.zpowers l : Subgroup H) = p ^ e * p := by
      have h4 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (B ⊓ (Sg ⊓ L))
        (Subgroup.zpowers l) hcommE).1
      rw [hinter, Subgroup.card_bot, mul_one, he, Nat.card_zpowers, hlo] at h4
      exact h4
    have hle2 := CFSG.SectionRank.le_pRank hp1
      (sup_le (inf_le_right : B ⊓ (Sg ⊓ L) ≤ Sg ⊓ L) hzl_le) hE'el (k := e + 1)
      (by rw [hEcard, pow_succ])
    omega

end SylowDecompCore

section Lemma133Decomp

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut innerAut)

variable {G : Type} [Group G] [Finite G]

theorem mem_centK_iff {p : ℕ} {L : Subgroup G} {x : G} :
    x ∈ (MonoidHom.ker (barAut p L)).map (Subgroup.normalizer (L : Set G)).subtype ↔
      ∃ hx : x ∈ Subgroup.normalizer (L : Set G), barAut p L ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, MonoidHom.mem_ker.1 hy⟩
  · rintro ⟨hx, h1⟩
    exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 h1, rfl⟩

theorem barAut_eq_conj_mk {p : ℕ} {L : Subgroup G} {l : G} (hl : l ∈ L)
    (hN : l ∈ Subgroup.normalizer (L : Set G)) :
    barAut p L ⟨l, hN⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

theorem mem_pPrimeCore_of_barAut_eq_one {p : ℕ} {M L : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) {l : G} (hl : l ∈ L)
    (hN : l ∈ Subgroup.normalizer (L : Set G)) (h1 : barAut p L ⟨l, hN⟩ = 1) :
    (⟨l, hl⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  haveI := Fact.mk hp
  have hZ := center_quotient_eq_bot_of_block hp hp2 hL hbl
  rw [barAut_eq_conj_mk hl hN] at h1
  have hc : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : ↥L ⧸ GLAPPrimeCore p ↥L) ∈
      Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact (QuotientGroup.eq_one_iff _).1 hc

theorem not_dvd_card_pPrimeCore {p : ℕ} (hp : p.Prime) (L : Subgroup G) :
    ¬ p ∣ Nat.card (GLAPPrimeCore p ↥L) := by
  haveI := Fact.mk hp
  have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hc

theorem isElemAbelian_map {p : ℕ} {K : Type} [Group K] (f : K →* G) {V : Subgroup K}
    (hV : IsElemAbelian p V) : IsElemAbelian p (V.map f) := by
  apply isElemAbelian_of_comm_pow
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul, elemAbelian_comm hV ha hb]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hV.2 a ha, map_one]

theorem isElemAbelian_subgroupOf {p : ℕ} {K V : Subgroup G} (hVK : V ≤ K) (hV : IsElemAbelian p V) :
    IsElemAbelian p (V.subgroupOf K) := by
  apply isElemAbelian_of_comm_pow
  · intro x hx y hy
    apply Subtype.ext
    exact elemAbelian_comm hV (Subgroup.mem_subgroupOf.1 hx) (Subgroup.mem_subgroupOf.1 hy)
  · intro x hx
    apply Subtype.ext
    simpa using hV.2 _ (Subgroup.mem_subgroupOf.1 hx)

theorem card_le_of_isTwoLocal {p m : ℕ} (hp : p.Prime)
    (hTLR : CFSG.Open.twoLocalPrimeRank p G = m) {M V : Subgroup G} (hM : CFSG.Open.IsTwoLocal M)
    (hVM : V ≤ M) (hV : IsElemAbelian p V) : Nat.card V ≤ p ^ m := by
  haveI := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  have hbdd : BddAbove {k | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H', -, rfl⟩
    obtain ⟨V', -, -, hV'card⟩ := CFSG.SectionRank.exists_pRank hp1 H'
    have h1 : Nat.card V' ≤ Nat.card G := Subgroup.card_le_card_group V'
    rw [hV'card] at h1
    exact le_trans (Nat.lt_pow_self hp1).le h1
  have hk : CFSG.Open.pRank p M ≤ CFSG.Open.twoLocalPrimeRank p G := le_csSup hbdd ⟨M, hM, rfl⟩
  obtain ⟨k, hk'⟩ : ∃ k : ℕ, Nat.card V = p ^ k :=
    exists_card_eq_pow (fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩)
  have hkM : k ≤ CFSG.Open.pRank p M := CFSG.SectionRank.le_pRank hp1 hVM hV hk'
  rw [hk']
  exact Nat.pow_le_pow_right hp.pos (hkM.trans (hk.trans hTLR.le))

theorem block_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B M L : Subgroup G}
    (hBp : IsPGroup p ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hLM : L ≤ M)
    (hsn : IsSubnormal L M) (hPi : IsPiTypeGroup p ↥(barX p M L)) (hI71 : Input7_1Inn)
    (hZ : Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) = ⊥) (b : G) (hb : b ∈ B) :
    ∃ (l : G) (hl : l ∈ L), barAut p L ⟨b, hBN hb⟩ = barAut p L ⟨l, Subgroup.le_normalizer hl⟩ := by
  haveI := Fact.mk hp
  have hY : IsPiTypeGroup p (↥L ⧸ GLAPPrimeCore p ↥L) :=
    IsPiTypeGroup.of_mulEquiv' (quotEquivBarX hp hLM hsn).symm hPi
  have hBn : IsPGroup p ↥(B.subgroupOf (Subgroup.normalizer (L : Set G))) :=
    hBp.comap_of_injective (Subgroup.normalizer (L : Set G)).subtype Subtype.val_injective
  have hPp : IsPGroup p ↥((B.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) :=
    hBn.map (barAut p L)
  have hPinn : (B.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
      innerAut (↥L ⧸ GLAPPrimeCore p ↥L) :=
    hI71 p hp hp2 _ hZ hY _ hPp
  have hmem : barAut p L ⟨b, hBN hb⟩ ∈
      (B.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 (hPinn hmem)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x, x.2, ?_⟩
  rw [barAut_eq_conj_mk x.2 (Subgroup.le_normalizer x.2)]
  exact hy.symm

theorem block_cover {p : ℕ} {B L : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ (b : G) (hb : b ∈ B), ∃ (l : G) (hl : l ∈ L),
      barAut p L ⟨b, hBN hb⟩ = barAut p L ⟨l, Subgroup.le_normalizer hl⟩) :
    ∀ y : ↥(Subgroup.normalizer (L : Set G)), y.1 ∈ L ⊔ B →
      ∃ z : ↥(Subgroup.normalizer (L : Set G)), z.1 ∈ L ∧ barAut p L y = barAut p L z := by
  set Nn := Subgroup.normalizer (L : Set G) with hNn
  let Tn : Subgroup ↥Nn := Subgroup.comap (barAut p L) ((L.subgroupOf Nn).map (barAut p L))
  have hLT : ∀ z : ↥Nn, z ∈ L.subgroupOf Nn → z ∈ Tn := by
    intro z hz
    show barAut p L z ∈ (L.subgroupOf Nn).map (barAut p L)
    exact Subgroup.mem_map_of_mem _ hz
  have hsup : L ⊔ B ≤ Tn.map Nn.subtype := by
    refine sup_le ?_ ?_
    · intro l hl
      refine Subgroup.mem_map.2 ⟨⟨l, Subgroup.le_normalizer hl⟩, hLT _ (Subgroup.mem_subgroupOf.2 hl), rfl⟩
    · intro b hb
      obtain ⟨l, hl, hbl⟩ := hinner b hb
      refine Subgroup.mem_map.2 ⟨⟨b, hBN hb⟩, ?_, rfl⟩
      show barAut p L ⟨b, hBN hb⟩ ∈ (L.subgroupOf Nn).map (barAut p L)
      rw [hbl]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hl)
  intro y hy
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 (hsup hy)
  have hw' : barAut p L w ∈ (L.subgroupOf Nn).map (barAut p L) := hw
  obtain ⟨z, hz, hzw⟩ := Subgroup.mem_map.1 hw'
  refine ⟨z, Subgroup.mem_subgroupOf.1 hz, ?_⟩
  have hyw : y = w := Subtype.ext hwy.symm
  rw [hyw]
  exact hzw.symm

theorem block_decomp {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B M L : Subgroup G}
    (hTLR : CFSG.Open.twoLocalPrimeRank p G = m) (hMtwo : CFSG.Open.IsTwoLocal M)
    (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ m) (hBM : B ≤ M)
    (hLc : GLAPComponent p M L) (hbl : IsGLBlock M L)
    (hPi : IsPiTypeGroup p ↥(barX p M L)) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hI71 : Input7_1Inn) :
    B = (B ⊓ L) ⊔ centBar p B L ∧ (B ⊓ L) ⊓ centBar p B L = ⊥ ∧
      CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L := by
  haveI := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  have hLM : L ≤ M := hbl.le
  have hBp : IsPGroup p ↥B := IsPGroup.iff_card.2 ⟨m, hBcard⟩
  have hinner : ∀ (b : G) (hb : b ∈ B), ∃ (l : G) (hl : l ∈ L),
      barAut p L ⟨b, hBN hb⟩ = barAut p L ⟨l, Subgroup.le_normalizer hl⟩ :=
    fun b hb => block_inner hp hp2 hBp hBN hLM hbl.subnormal hPi hI71
      (center_quotient_eq_bot_of_block hp hp2 hLc hbl) b hb
  have hcov := block_cover hBN hinner
  set Nn := Subgroup.normalizer (L : Set G) with hNn
  set Hs : Subgroup G := L ⊔ B with hHs
  have hHsN : Hs ≤ Nn := sup_le Subgroup.le_normalizer hBN
  have hHsM : Hs ≤ M := sup_le hLM hBM
  have hLHs : L ≤ Hs := le_sup_left
  have hBHs : B ≤ Hs := le_sup_right
  have hC0_mem : ∀ x : G, x ∈ centBar p Hs L ↔ (∃ hx : x ∈ Nn, barAut p L ⟨x, hx⟩ = 1) ∧ x ∈ Hs := by
    intro x
    unfold centBar
    rw [Subgroup.mem_inf, mem_centK_iff]
  let Lh : Subgroup ↥Hs := L.subgroupOf Hs
  let Bh : Subgroup ↥Hs := B.subgroupOf Hs
  let Ch : Subgroup ↥Hs := (centBar p Hs L).subgroupOf Hs
  have hLn : Lh.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Nn := hHsN g.2
    have := (Subgroup.mem_normalizer_iff.1 hg (n : G)).1 hn
    simpa [Subgroup.coe_mul] using this
  have hCn : Ch.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨⟨hnN, h1⟩, hnH⟩ := (hC0_mem _).1 hn
    have hgN : (g : G) ∈ Nn := hHsN g.2
    rw [hC0_mem]
    refine ⟨⟨Nn.mul_mem (Nn.mul_mem hgN hnN) (Nn.inv_mem hgN), ?_⟩, ?_⟩
    · have e1 : (⟨((g * n * g⁻¹ : ↥Hs) : G), Nn.mul_mem (Nn.mul_mem hgN hnN) (Nn.inv_mem hgN)⟩ : ↥Nn) =
          ⟨(g : G), hgN⟩ * ⟨(n : G), hnN⟩ * ⟨(g : G), hgN⟩⁻¹ :=
        Subtype.ext (by simp)
      rw [e1, map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    · exact Hs.mul_mem (Hs.mul_mem g.2 hnH) (Hs.inv_mem g.2)
  have hcomm : ∀ l ∈ Lh, ∀ c ∈ Ch, c * l * c⁻¹ * l⁻¹ ∈ Lh ⊓ Ch := by
    intro l hl c hc
    have hc' : (c : G) ∈ centBar p Hs L := Subgroup.mem_subgroupOf.1 hc
    obtain ⟨⟨hcN, h1⟩, -⟩ := (hC0_mem _).1 hc'
    have hlN : (l : G) ∈ Nn := hHsN l.2
    rw [Subgroup.mem_inf]
    refine ⟨Lh.mul_mem (hLn.conj_mem l hl c) (Lh.inv_mem hl), ?_⟩
    rw [Subgroup.mem_subgroupOf]
    show (c : G) * (l : G) * (c : G)⁻¹ * (l : G)⁻¹ ∈ centBar p Hs L
    rw [hC0_mem]
    refine ⟨⟨Nn.mul_mem (Nn.mul_mem (Nn.mul_mem hcN hlN) (Nn.inv_mem hcN)) (Nn.inv_mem hlN), ?_⟩, ?_⟩
    · have e1 : (⟨(c : G) * (l : G) * (c : G)⁻¹ * (l : G)⁻¹,
          Nn.mul_mem (Nn.mul_mem (Nn.mul_mem hcN hlN) (Nn.inv_mem hcN)) (Nn.inv_mem hlN)⟩ : ↥Nn) =
          ⟨(c : G), hcN⟩ * ⟨(l : G), hlN⟩ * ⟨(c : G), hcN⟩⁻¹ * ⟨(l : G), hlN⟩⁻¹ :=
        Subtype.ext (by simp)
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      simp
    · exact Hs.mul_mem (Hs.mul_mem (Hs.mul_mem c.2 l.2) (Hs.inv_mem c.2)) (Hs.inv_mem l.2)
  have hX : Lh ⊔ Ch = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨z, hzL, hz⟩ := hcov ⟨(h : G), hHsN h.2⟩ h.2
    have hzH : (⟨(z : G), hLHs hzL⟩ : ↥Hs) ∈ Lh := Subgroup.mem_subgroupOf.2 hzL
    have hcH : (⟨(z : G), hLHs hzL⟩ : ↥Hs)⁻¹ * h ∈ Ch := by
      rw [Subgroup.mem_subgroupOf]
      show (z : G)⁻¹ * (h : G) ∈ centBar p Hs L
      rw [hC0_mem]
      have hzN : (z : G) ∈ Nn := z.2
      have hN' : (z : G)⁻¹ * (h : G) ∈ Nn := Nn.mul_mem (Nn.inv_mem hzN) (hHsN h.2)
      refine ⟨⟨hN', ?_⟩, Hs.mul_mem (Hs.inv_mem (hLHs hzL)) h.2⟩
      have e2 : (⟨(z : G)⁻¹ * (h : G), hN'⟩ : ↥Nn) = z⁻¹ * ⟨(h : G), hHsN h.2⟩ :=
        Subtype.ext (by simp)
      rw [e2, map_mul, map_inv, ← hz, inv_mul_cancel]
    simpa using Subgroup.mul_mem_sup hzH hcH
  have hN0 : ¬ p ∣ Nat.card ↥(Lh ⊓ Ch) := by
    have hsub : (Lh ⊓ Ch).map Hs.subtype ≤ (GLAPPrimeCore p ↥L).map L.subtype := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_inf] at hy
      have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.1 hy.1
      have hyC : (y : G) ∈ centBar p Hs L := Subgroup.mem_subgroupOf.1 hy.2
      obtain ⟨⟨hyN, h1⟩, -⟩ := (hC0_mem _).1 hyC
      exact Subgroup.mem_map_of_mem _ (mem_pPrimeCore_of_barAut_eq_one hp hp2 hLc hbl hyL hyN h1)
    have hcard1 : Nat.card ↥((Lh ⊓ Ch).map Hs.subtype) = Nat.card ↥(Lh ⊓ Ch) :=
      Subgroup.card_map_of_injective (f := Hs.subtype) Subtype.val_injective
    have hcard2 : Nat.card ↥((GLAPPrimeCore p ↥L).map L.subtype) = Nat.card ↥(GLAPPrimeCore p ↥L) :=
      Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective
    intro hdiv
    have h2 : p ∣ Nat.card ↥((GLAPPrimeCore p ↥L).map L.subtype) := by
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le hsub)
      rw [hcard1]
      exact hdiv
    rw [hcard2] at h2
    exact not_dvd_card_pPrimeCore hp L h2
  have hrank : ∀ V : Subgroup ↥Hs, IsElemAbelian p V → Nat.card V ≤ p ^ m := by
    intro V hV
    have hVM : V.map Hs.subtype ≤ M := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact hHsM y.2
    have hc : Nat.card ↥(V.map Hs.subtype) = Nat.card ↥V :=
      Subgroup.card_map_of_injective (f := Hs.subtype) Subtype.val_injective
    rw [← hc]
    exact card_le_of_isTwoLocal hp hTLR hMtwo hVM (isElemAbelian_map Hs.subtype hV)
  have hBHsc : Nat.card ↥Bh = p ^ m :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBHs).toEquiv).trans hBcard
  have hBhel : IsElemAbelian p Bh := isElemAbelian_subgroupOf hBHs hBel
  have hBhp : IsPGroup p ↥Bh := IsPGroup.iff_card.2 ⟨m, hBHsc⟩
  obtain ⟨S, hBS⟩ := hBhp.exists_le_sylow
  have hCN : Ch ≤ Subgroup.normalizer (Lh : Set ↥Hs) := by
    haveI := hLn
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hLN : Lh ≤ Subgroup.normalizer (Ch : Set ↥Hs) := by
    haveI := hCn
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨hdec, e, he, hre⟩ := decomp_core hp hCN hLN hX hN0 hcomm hrank Bh hBhel hBHsc S hBS
  have hC1 : B = (B ⊓ L) ⊔ centBar p B L := by
    apply le_antisymm
    · intro b hb
      obtain ⟨l', hl', c', hc', hbc⟩ := hdec ⟨b, hBHs hb⟩ (Subgroup.mem_subgroupOf.2 hb)
      have hbc' : b = (l' : G) * (c' : G) := congrArg Subtype.val hbc
      have hl'B : (l' : G) ∈ B := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hl').1
      have hl'L : (l' : G) ∈ L := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hl').2
      have hc'B : (c' : G) ∈ B := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hc').1
      have hc'C : (c' : G) ∈ centBar p B L := by
        have hcK : (c' : G) ∈ centBar p Hs L := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hc').2
        obtain ⟨⟨hcN, h1⟩, -⟩ := (hC0_mem _).1 hcK
        unfold centBar
        exact Subgroup.mem_inf.2 ⟨mem_centK_iff.2 ⟨hcN, h1⟩, hc'B⟩
      rw [hbc']
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hl'B, hl'L⟩) hc'C
    · exact sup_le inf_le_left (by unfold centBar; exact inf_le_right)
  have hC2 : (B ⊓ L) ⊓ centBar p B L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxBL, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxB, hxL⟩ := Subgroup.mem_inf.1 hxBL
    have hxK : x ∈ (MonoidHom.ker (barAut p L)).map Nn.subtype := (Subgroup.mem_inf.1 hxC).1
    obtain ⟨hxN, h1⟩ := mem_centK_iff.1 hxK
    have hmem := mem_pPrimeCore_of_barAut_eq_one hp hp2 hLc hbl hxL hxN h1
    have hxQ : x ∈ (GLAPPrimeCore p ↥L).map L.subtype := Subgroup.mem_map_of_mem _ hmem
    have hxp : x ^ p = 1 := hBel.2 x hxB
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have hcard : orderOf x ∣ Nat.card ↥(GLAPPrimeCore p ↥L) := by
      have h3 : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥((GLAPPrimeCore p ↥L).map L.subtype) :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hxQ)
      rw [Nat.card_zpowers, Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective] at h3
      exact h3
    have hnd : ¬ p ∣ orderOf x := fun h => not_dvd_card_pPrimeCore hp L (h.trans hcard)
    rw [Subgroup.mem_bot]
    rcases (Nat.dvd_prime hp).1 hdvd with h1' | h1'
    · exact orderOf_eq_one_iff.1 h1'
    · exact absurd (h1' ▸ dvd_refl p) hnd
  have hBLHs : B ⊓ L ≤ Hs := inf_le_left.trans hBHs
  have hsubgrp : (B ⊓ L).subgroupOf Hs = Bh ⊓ (S.toSubgroup ⊓ Lh) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxB, hxL⟩
      have hxBh : x ∈ Bh := Subgroup.mem_subgroupOf.2 hxB
      have hxLh : x ∈ Lh := Subgroup.mem_subgroupOf.2 hxL
      exact Subgroup.mem_inf.2 ⟨hxBh, Subgroup.mem_inf.2 ⟨hBS hxBh, hxLh⟩⟩
    · intro hx
      have hxBh : x ∈ Bh := (Subgroup.mem_inf.1 hx).1
      have hxLh : x ∈ Lh := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).2
      exact ⟨Subgroup.mem_subgroupOf.1 hxBh, Subgroup.mem_subgroupOf.1 hxLh⟩
  have hBL : Nat.card ↥(B ⊓ L) = p ^ e := by
    have h1 : Nat.card ↥((B ⊓ L).subgroupOf Hs) = Nat.card ↥(B ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLHs).toEquiv
    rw [← h1, hsubgrp, he]
  have hBLel : IsElemAbelian p (B ⊓ L) := isElemAbelian_mono hBel inf_le_left
  have hrBL : CFSG.Open.pRank p (B ⊓ L) = e := by
    apply le_antisymm
    · obtain ⟨V, hVle, -, hVcard⟩ := CFSG.SectionRank.exists_pRank hp1 (B ⊓ L)
      have h1 : Nat.card ↥V ≤ Nat.card ↥(B ⊓ L) := Subgroup.card_le_of_le hVle
      rw [hVcard, hBL] at h1
      exact (Nat.pow_le_pow_iff_right hp1).1 h1
    · exact CFSG.SectionRank.le_pRank hp1 le_rfl hBLel hBL
  have hLe : CFSG.Open.pRank p L = e := by
    apply le_antisymm
    · obtain ⟨E, hEL, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 L
      have hEHs : E ≤ Hs := hEL.trans hLHs
      have hE'el : IsElemAbelian p (E.subgroupOf Hs) := isElemAbelian_subgroupOf hEHs hEel
      have hE'card : Nat.card ↥(E.subgroupOf Hs) = p ^ CFSG.Open.pRank p L := by
        rw [← hEcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEHs).toEquiv
      have hE'p : IsPGroup p ↥(E.subgroupOf Hs) := IsPGroup.iff_card.2 ⟨_, hE'card⟩
      obtain ⟨Q, hQ⟩ := hE'p.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Hs S Q
      set f : ↥Hs →* ↥Hs := (MulAut.conj g⁻¹ : MulAut ↥Hs).toMonoidHom with hf
      have hfinj : Function.Injective f := (MulAut.conj g⁻¹ : MulAut ↥Hs).injective
      have hEc : Nat.card ↥((E.subgroupOf Hs).map f) = p ^ CFSG.Open.pRank p L := by
        rw [Subgroup.card_map_of_injective hfinj, hE'card]
      have hEel' : IsElemAbelian p ((E.subgroupOf Hs).map f) := isElemAbelian_map f hE'el
      have hEsub : (E.subgroupOf Hs).map f ≤ S.toSubgroup ⊓ Lh := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        have hyQ : y ∈ (Q : Set ↥Hs) := hQ hy
        rw [← hg, Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem] at hyQ
        have hyL : y ∈ Lh := Subgroup.mem_subgroupOf.2 (hEL (Subgroup.mem_subgroupOf.1 hy))
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have e3 : f y = (MulAut.conj g)⁻¹ • y := by
            simp [hf, MulAut.conj_apply]
          rw [e3]
          exact hyQ
        · have e4 : f y = g⁻¹ * y * g⁻¹⁻¹ := by
            simp [hf, MulAut.conj_apply]
          rw [e4]
          exact hLn.conj_mem y hyL g⁻¹
      have hle := CFSG.SectionRank.le_pRank hp1 hEsub hEel' hEc
      rw [hre] at hle
      exact hle
    · exact CFSG.SectionRank.le_pRank hp1 (inf_le_right : B ⊓ L ≤ L) hBLel hBL
  exact ⟨hC1, hC2, hrBL.trans hLe.symm⟩

end Lemma133Decomp

theorem lemma133_of_inputs (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hI113 : Input11_3) (hI71 : Input7_1Inn) :
    Lemma133Statement := by
  intro G _ _ m p B M E A D T h
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : IsBOneMax p B := h.bOne
  have hM : IsPreUniquenessTwoLocal p B M := h.pre
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB hM
  have hMtwo : CFSG.Open.IsTwoLocal M := hM.1.1
  have hTLR : CFSG.Open.twoLocalPrimeRank p G = m := hS.rank_eq
  have hBel : IsElemAbelian p B := hB.1.1
  have hBc : Nat.card B = p ^ GLATwoLocalRank p G := hB.1.2.1
  rw [hS.rank_eq] at hBc
  refine ⟨iof_ne_bot_of h111 h1117 h121 h127 hP95 h, ?_⟩
  intro L hL
  obtain ⟨g, hg, L0, hL0, rfl⟩ := istar_component hp hL
  have hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L0 : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    fun hle => hL0.2 ((barX_mono p (gammaStar_le_gammaD p D)).trans hle)
  obtain ⟨hcomp, hbl, hpi⟩ :=
    block_of_conj_iv hS hP95 (prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD) hg hL0.1 hnc
  have hBN : B ≤ Subgroup.normalizer (GLBConj g L0 : Set G) :=
    le_normalizer_of_block hI113 hS hB hM hcomp hbl
  obtain ⟨hpg, hnh⟩ := piGroup_of_block hp hp2 hcomp hbl hpi
  obtain ⟨hdec1, hdec2, hdec3⟩ := block_decomp hp hp2 hTLR hMtwo hBel hBc hBM hcomp hbl hpi hBN hI71
  exact ⟨⟨hbl, hpg, hnh⟩, hBN, hdec1, hdec2, hdec3⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
