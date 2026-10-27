module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.Quasithin.Background.Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual
import CFSG.LocalAnalysis.RankThreeUC.TIModule
import CFSG.Quasithin.Background.B216Quotient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneCenterIn_eq_quasithinOmegaOneCenter (T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T = CFSG.Open.quasithinOmegaOneCenter T := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzT, hzc, hz2⟩ := CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz
    exact Subgroup.subset_closure ⟨⟨hzT, mem_centralizer_iff.mpr hzc⟩, hz2⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨⟨hzT, hzc⟩, hz2⟩
    exact CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
      ⟨hzT, mem_centralizer_iff.mp hzc, hz2⟩

omit [Finite G] in
theorem uCore_eq_conjClosure (M T : Subgroup G) :
    uCore M T = CFSG.Quasithin.conjClosure (CFSG.Open.quasithinOmegaOneCenter T) M := by
  rw [← omegaOneCenterIn_eq_quasithinOmegaOneCenter]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact CFSG.Quasithin.mem_conjClosure m.2 hz
  · refine CFSG.Quasithin.conjClosure_le fun h hh z hz => ?_
    exact mem_iSup_of_mem (⟨h, hh⟩ : M) ⟨z, hz, rfl⟩

private theorem pow_eq_one_of_mem_iSup {Ω : Type*} [Group Ω] (n : ℕ) (𝓕 : Finset (Subgroup Ω))
    (hn : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ n = 1)
    (hc : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) :
    ∀ x ∈ ⨆ H ∈ 𝓕, H, x ^ n = 1 := by
  classical
  induction 𝓕 using Finset.induction_on with
  | empty =>
    intro x hx
    have : (⨆ H ∈ (∅ : Finset (Subgroup Ω)), H) = ⊥ := by simp
    rw [this, Subgroup.mem_bot] at hx
    rw [hx, one_pow]
  | insert H₀ 𝓕 hH₀ ih =>
    intro x hx
    rw [Finset.iSup_insert] at hx
    have hn' : ∀ H ∈ 𝓕, ∀ x ∈ H, x ^ n = 1 := fun H hH => hn H (Finset.mem_insert_of_mem hH)
    have hc' : ∀ H ∈ 𝓕, ∀ H' ∈ 𝓕, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a :=
      fun H hH H' hH' => hc H (Finset.mem_insert_of_mem hH) H' (Finset.mem_insert_of_mem hH')
    have hK : (⨆ H ∈ 𝓕, H) ≤ centralizer (H₀ : Set Ω) := by
      refine iSup₂_le fun H hH b hb => ?_
      rw [mem_centralizer_iff]
      intro a ha
      have hne : H₀ ≠ H := fun h => hH₀ (h ▸ hH)
      exact hc H₀ (Finset.mem_insert_self _ _) H (Finset.mem_insert_of_mem hH) hne a ha b hb
    have hnorm : (⨆ H ∈ 𝓕, H) ≤ normalizer (H₀ : Set Ω) :=
      hK.trans (centralizer_le_normalizer _)
    have hx' : x ∈ ((H₀ ⊔ ⨆ H ∈ 𝓕, H : Subgroup Ω) : Set Ω) := hx
    rw [coe_mul_of_right_le_normalizer_left H₀ _ hnorm] at hx'
    obtain ⟨h, hh, k, hk, rfl⟩ := hx'
    have hcomm : Commute h k := mem_centralizer_iff.1 (hK hk) h hh
    rw [hcomm.mul_pow, hn H₀ (Finset.mem_insert_self _ _) h hh, ih hn' hc' k hk, one_mul]

private theorem pow_six_of_actsAsNaturalL2 {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hN : CFSG.Quasithin.ActsAsNaturalL2 L U) : ∀ x ∈ L, x ^ 6 = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h6 : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), g ^ 6 = 1 := by decide
  intro x hx
  have h1 : e (⟨x, hx⟩ ^ 6) = 1 := by rw [map_pow]; exact h6 _
  have h2 : (⟨x, hx⟩ : ↥L) ^ 6 = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem pow_six_mem_centralizer_of_thompsonJ {H T V : Subgroup G}
    (hF : CFSG.QuasithinUnique.CharTwo H) (hsolv : Group.IsSolvable ↥(CFSG.Quasithin.autOn H V))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T H)
    (hV : V = CFSG.Quasithin.conjClosure (CFSG.Open.quasithinOmegaOneCenter T) H) :
    ∀ x ∈ CFSG.Quasithin.thompsonJ H, x ^ 6 ∈ centralizer (V : Set G) := by
  obtain ⟨hU, hred, hcase, -⟩ := CFSG.Quasithin.B2_16_of_quot hF hsolv hT hV
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  rcases hcase with ⟨hJ, -⟩ | ⟨-, I, -, hN, hcomm, -, hnat, -⟩
  · intro x hx
    exact (centralizer (V : Set G)).pow_mem ((CFSG.Quasithin.B2_7_of_le_factor hHN hT hJ).1 hx) 6
  · intro x hx
    have hxN : x ∈ normalizer (V : Set G) := hHN (CFSG.Quasithin.thompsonJ_le_self H hx)
    have hconv := CFSG.Quasithin.convI_mem_autI hU hx hxN
    rw [hN] at hconv
    have h6 := pow_eq_one_of_mem_iSup 6 I (fun L hL => pow_six_of_actsAsNaturalL2 (hnat L hL))
      hcomm _ hconv
    have h7 : CFSG.Quasithin.convI hU ((⟨x, hxN⟩ : normalizer (V : Set G)) ^ 6) = 1 := by
      rw [map_pow]
      exact h6
    exact (CFSG.Quasithin.convI_eq_one_iff hU _).mp h7

omit [Finite G] in
private theorem mem_of_pow_mem_of_pow_eq_one {K : Subgroup G} {e : G} {m p : ℕ}
    (hmp : Nat.Coprime m p) (he : e ^ p = 1) (hm : e ^ m ∈ K) : e ∈ K := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hmp
  have h1 : e = (e ^ m) ^ a := by
    calc e = e ^ ((m : ℤ) * a + p * b) := by
          rw [show (m : ℤ) * a + p * b = 1 by linarith, zpow_one]
      _ = (e ^ m) ^ a := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, he, one_zpow, mul_one]
  rw [h1]
  exact K.zpow_mem hm a

theorem pRank_thompsonJ_le_of_pow_six {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {H V : Subgroup G}
    (h6 : ∀ x ∈ CFSG.Quasithin.thompsonJ H, x ^ 6 ∈ centralizer (V : Set G)) :
    CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ H) ≤
      CFSG.Open.pRank p (H ⊓ centralizer (V : Set G)) := by
  have hcop : Nat.Coprime 6 p :=
    Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
      ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))
  by_cases h0 : 0 < CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ H)
  · obtain ⟨E, hEJ, hE, hEc⟩ := pRank_attained p _ h0
    have hEK : E ≤ H ⊓ centralizer (V : Set G) := fun e he =>
      ⟨CFSG.Quasithin.thompsonJ_le_self H (hEJ he),
        mem_of_pow_mem_of_pow_eq_one hcop (hE.2 e he) (h6 e (hEJ he))⟩
    exact CFSG.SectionRank.le_pRank hp.one_lt hEK hE hEc
  · omega

theorem le_sup_normalizer_thompsonJ {M T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    M ≤ CFSG.Quasithin.thompsonJ M ⊔ (M ⊓ normalizer (CFSG.Quasithin.thompsonJ T : Set G)) := by
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf T M := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hLM := CFSG.Quasithin.thompsonJ_le_self M
  have hn : M ≤ normalizer (CFSG.Quasithin.thompsonJ M : Set G) :=
    le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ M)
  have hS := hT.inf_of_le_normalizer hLM hn
  have hJ : CFSG.Quasithin.thompsonJ T =
      CFSG.Quasithin.thompsonJ (T ⊓ CFSG.Quasithin.thompsonJ M) :=
    CFSG.Quasithin.thompsonJ_eq_of_le
      (le_inf (CFSG.Quasithin.thompsonJ_le_self T)
        (CFSG.Quasithin.thompsonJ_le_thompsonJ_of_isSylowTwoOf hT')) inf_le_left
  refine (le_sup_inf_normalizer_of_isSylowOf hLM hn hS).trans
    (sup_le_sup_left (inf_le_inf_left M ?_) _)
  rw [hJ]
  exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _

omit [Finite G] in
private theorem isElemAbelian_omegaOneCenterIn (T : Subgroup G) :
    IsElemAbelian 2 (CFSG.RankThree.PartOne.omegaOneCenterIn T) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx =>
    (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hx).2.2⟩
  obtain ⟨-, hbc, -⟩ := CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp b.2
  exact hbc a (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T a.2)

private theorem thompsonJ_ne_bot_of_isPGroup {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) :
    CFSG.Quasithin.thompsonJ T ≠ ⊥ := by
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian T
  have hZ1 := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hT2 hT1
  have hcard : Nat.card (CFSG.RankThree.PartOne.omegaOneCenterIn T) ≤ Nat.card A :=
    hA.2.2 _ (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T)
      (isElemAbelian_omegaOneCenterIn T)
  have h2 : 1 < Nat.card (CFSG.RankThree.PartOne.omegaOneCenterIn T) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ1
  intro h
  have hAb : A = ⊥ := le_bot_iff.mp (h ▸ le_iSup₂_of_le A hA le_rfl)
  rw [hAb, Subgroup.card_bot] at hcard
  omega

namespace IsWitnessGen

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem two_le_pRank_normalizer_thompsonJ_or (hS : StandingGen G) (hp : IsWitnessPrime p P)
    (hw : IsWitnessGen p P M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (CFSG.Quasithin.thompsonJ T : Set G)) ∨
      2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) :=
  (two_le_pRank_or_of_le_sup hp.prime hp.odd
    (CFSG.Quasithin.thompsonJ_le_self M)
    (le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ M)) inf_le_left
    (le_sup_normalizer_thompsonJ hT) (hw.three_le_pRank hp)).symm

theorem normalizer_le_of_pRank_thompsonJ_le_one (hS : StandingGen G) (hp : IsWitnessPrime p P)
    (hw : IsWitnessGen p P M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (h : CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) ≤ 1) : normalizer (T : Set G) ≤ M := by
  have hprime := hp.prime
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
  have h2 := (hw.two_le_pRank_normalizer_thompsonJ_or hS hp hT).resolve_right (by omega)
  exact hw.normalizer_le_of_two_le_pRank_normalizer hS hp hT
    (thompsonJ_ne_bot_of_isPGroup hT.isPGroup hT1) (CFSG.Quasithin.thompsonJ_le_self T)
    (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ T)
    (h2.trans (pRank_mono p hprime.one_lt inf_le_right))

theorem normalizer_le_of_thompsonJ_le_centralizer (hS : StandingGen G)
    (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJ : CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G)) :
    normalizer (T : Set G) ≤ M := by
  have hprime := hp.prime
  by_cases hK : 2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (uCore M T : Set G))
  · have hUe := (uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT).2
    exact hw.normalizer_le_of_isTI_uCore hS hT (hw.isTI_of_two_le_pRank hp.prime
      (elementary_isPGroup 2 _ hUe) (le_normalizer_uCore M T) hK)
  · have hJM := (CFSG.Quasithin.B2_7_of_le_factor (le_normalizer_uCore M T)
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hT) hJ).1
    refine hw.normalizer_le_of_pRank_thompsonJ_le_one hS hp hT ?_
    have := pRank_mono p hprime.one_lt (le_inf (CFSG.Quasithin.thompsonJ_le_self M) hJM)
    omega

theorem normalizer_le_of_solvable_quotient (hS : StandingGen G) (hp : IsWitnessPrime p P)
    (hp5 : 5 ≤ p) (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hsolv : Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) :
    normalizer (T : Set G) ≤ M := by
  by_cases hK : 2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (uCore M T : Set G))
  · have hUe := (uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT).2
    exact hw.normalizer_le_of_isTI_uCore hS hT (hw.isTI_of_two_le_pRank hp.prime
      (elementary_isPGroup 2 _ hUe) (le_normalizer_uCore M T) hK)
  · have h6 := pow_six_mem_centralizer_of_thompsonJ (hS.charTwo M hw.maxLocal.1) hsolv
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hT) (uCore_eq_conjClosure M T)
    have hJ := pRank_thompsonJ_le_of_pow_six hp.prime hp5 h6
    exact hw.normalizer_le_of_pRank_thompsonJ_le_one hS hp hT (by omega)

end IsWitnessGen

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem normalizer_le_of_pRank_thompsonJ_le_one (hS : Standing G) (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (h : CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) ≤ 1) : normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_pRank_thompsonJ_le_one hS.toGen
    (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen hT h

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
