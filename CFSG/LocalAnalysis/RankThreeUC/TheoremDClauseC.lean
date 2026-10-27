module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCBlocks
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCoprime
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCycle
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCSylow
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCWreath
import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual
import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.Background.B216Quotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_centralizer_of_convI_commute {U : Subgroup G} (hU : IsElemAbelian 2 U)
    {y x : G} (hyN : y ∈ normalizer (U : Set G)) (hxN : x ∈ normalizer (U : Set G))
    (hcomm : convI hU ⟨y, hyN⟩ * convI hU ⟨x, hxN⟩ = convI hU ⟨x, hxN⟩ * convI hU ⟨y, hyN⟩) :
    ⁅y, x⁆ ∈ centralizer (U : Set G) := by
  have hg : convI hU (⟨y, hyN⟩ * ⟨x, hxN⟩ * (⟨x, hxN⟩ * ⟨y, hyN⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, hcomm]
    exact mul_inv_cancel _
  have := (convI_eq_one_iff hU _).mp hg
  convert this using 1
  simp [commutatorElement_def, mul_assoc]

omit [Finite G] in
theorem exists_block_moved {M J U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hMN : M ≤ normalizer (U : Set G)) (hJM : J ≤ M)
    {I : Finset (Subgroup (MulAut (IntMod U hU)))} (hBD : BlockData (autI hU M) I)
    (hJI : autI hU J ≤ ⨆ L ∈ I, L) {y x : G} (hyM : y ∈ M) (hxJ : x ∈ J)
    (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) (hx3 : ∃ m : ℕ, x ^ 3 ^ m = 1)
    (hyx : ⁅y, x⁆ ∉ centralizer (U : Set G)) :
    ∃ L ∈ I, B1.conjAut (convI hU ⟨y, hMN hyM⟩) L ≠ L := by
  by_contra hcon
  push Not at hcon
  have hxN : x ∈ normalizer (U : Set G) := hMN (hJM hxJ)
  have hyN : y ∈ normalizer (U : Set G) := hMN hyM
  have hcomm := hBD.comm_of_normalizes (c := convI hU ⟨y, hyN⟩) (y := convI hU ⟨x, hxN⟩) hcon
    (by
      obtain ⟨k, hk⟩ := hy3
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : (⟨y, hyN⟩ : normalizer (U : Set G)) ^ 3 ^ k = 1 := Subtype.ext hk
      rw [this, map_one])
    (hJI (convI_mem_autI hU hxJ hxN))
    (by
      obtain ⟨m, hm⟩ := hx3
      refine ⟨m, ?_⟩
      rw [← map_pow]
      have : (⟨x, hxN⟩ : normalizer (U : Set G)) ^ 3 ^ m = 1 := Subtype.ext hm
      rw [this, map_one])
  exact hyx (commutator_mem_centralizer_of_convI_commute hU hyN hxN hcomm)

theorem false_of_clauseC_of_blocks {P : Sylow 3 G} {M U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hUM : U ≤ M) (hMN : M ≤ normalizer (U : Set G)) (hPM : (P : Subgroup G) ≤ M)
    {I : Finset (Subgroup (MulAut (IntMod U hU)))} (hBD : BlockData (autI hU M) I)
    (hJI : autI hU (thompsonJ M) ≤ ⨆ L ∈ I, L)
    (hK : NoRankTwoThree (M ⊓ centralizer (U : Set G)))
    (hcyc : CyclicMod (P : Subgroup G) ((P : Subgroup G) ⊓ thompsonJ M))
    (hc : rankThreeClauseC M (P : Subgroup G)) : False := by
  obtain ⟨-, ⟨e⟩, -, hY⟩ := hc
  have hJM : thompsonJ M ≤ M := thompsonJ_le_self M
  have hMJ : M ≤ normalizer (thompsonJ M : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_thompsonJ M)
  have hHn : ∀ p ∈ (P : Subgroup G), ∀ h ∈ (P : Subgroup G) ⊓ thompsonJ M,
      p * h * p⁻¹ ∈ (P : Subgroup G) ⊓ thompsonJ M := by
    intro p hp h hh
    exact ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hp hh.1)
      ((P : Subgroup G).inv_mem hp), (mem_normalizer_iff.mp (hMJ (hPM hp)) h).mp hh.2⟩
  have hP81 : Nat.card (P : Subgroup G) = 81 := card_eq_eighty_one_of_equiv e
  have hP3 : ∀ x ∈ (P : Subgroup G), ∃ k : ℕ, x ^ 3 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨y, hyP, hy3, x, hx, hyx⟩ := exists_three_element_nontrivial_commutator e hHn hcyc
    (C := (P : Subgroup G) ⊓ (M ⊓ centralizer (U : Set G))) (hK.mono inf_le_right)
  have hyM : y ∈ M := hPM hyP
  have hyN : y ∈ normalizer (U : Set G) := hMN hyM
  have hxP : x ∈ (P : Subgroup G) := hx.1
  have hcomP : ⁅y, x⁆ ∈ (P : Subgroup G) := by
    simp only [commutatorElement_def]
    exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hyP hxP)
      ((P : Subgroup G).inv_mem hyP)) ((P : Subgroup G).inv_mem hxP)
  have hyx' : ⁅y, x⁆ ∉ centralizer (U : Set G) := fun h => hyx ⟨hcomP, hPM hcomP, h⟩
  obtain ⟨L₀, hL₀, hmove⟩ := exists_block_moved hU hMN hJM hBD hJI hyM hx.2 (hP3 y hyP)
    (hP3 x hxP) hyx'
  have hg3 : (convI hU ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : normalizer (U : Set G)) ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one]
  obtain ⟨D, hDX, hDp, hD27, hDab⟩ := hBD.exists_abelian_three_subgroup
    (convI_mem_autI hU hyM hyN) hg3 hL₀ hmove
  let ρ : ↥M →* MulAut (IntMod U hU) := convHom hU M hMN
  let S : Sylow 3 M := P.subtype hPM
  have hDr : D ≤ ρ.range := hDX.trans (range_convHom hU M hMN).ge
  have hSρ : (S : Subgroup M).map ρ = autI hU (P : Subgroup G) :=
    (autI_eq_map_convHom hU hMN hPM).symm
  obtain ⟨hcl1, hcl2⟩ := card_le_and_commute_of_isPGroup ρ S D hDr hDp hDab
  rw [hSρ] at hcl1 hcl2
  have hxN : x ∈ normalizer (U : Set G) := hMN (hPM hxP)
  have hnotle : ¬ Nat.card (autI hU (P : Subgroup G)) ≤ Nat.card D := by
    intro hle
    have hcomm := hcl2 hle ⟨y, hyM⟩ hyP ⟨x, hMN.trans le_rfl |> fun _ => hPM hxP⟩ hxP
    exact hyx' (commutator_mem_centralizer_of_convI_commute hU hyN hxN hcomm)
  have hPN : (P : Subgroup G) ≤ normalizer (U : Set G) := hPM.trans hMN
  have hcard := card_autI_mul_card_inf hU hPN
  rw [hP81] at hcard
  have hdvd : Nat.card (autI hU (P : Subgroup G)) ∣ 3 ^ 4 := by
    have : Nat.card (autI hU (P : Subgroup G)) ∣ 81 := Dvd.intro _ hcard
    simpa using this
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hi4 : i = 4 := by
    by_contra hne
    have : i ≤ 3 := by omega
    interval_cases i <;> omega
  have hcard81 : Nat.card (autI hU (P : Subgroup G)) = 81 := by rw [hi', hi4]; norm_num
  have hPc : (P : Subgroup G) ⊓ centralizer (U : Set G) = ⊥ := by
    rw [hcard81] at hcard
    have : Nat.card ((P : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) = 1 := by omega
    exact Subgroup.card_eq_one.mp this
  obtain ⟨s, hsP, hs3, hsJ, x₂, hx₂, hsx⟩ :=
    exists_order_three_not_mem_thompsonSubgroup_commutator_ne_one e hHn hcyc
  have hs3' : s ^ 3 = 1 := by rw [← hs3]; exact pow_orderOf_eq_one s
  have hsM : s ∈ M := hPM hsP
  have hsN : s ∈ normalizer (U : Set G) := hMN hsM
  have hx₂P : x₂ ∈ (P : Subgroup G) := hx₂.1
  have hcomP₂ : ⁅s, x₂⁆ ∈ (P : Subgroup G) := by
    simp only [commutatorElement_def]
    exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hsP hx₂P)
      ((P : Subgroup G).inv_mem hsP)) ((P : Subgroup G).inv_mem hx₂P)
  have hsx' : ⁅s, x₂⁆ ∉ centralizer (U : Set G) := fun h => hsx (by
    have : ⁅s, x₂⁆ ∈ (P : Subgroup G) ⊓ centralizer (U : Set G) := ⟨hcomP₂, h⟩
    rwa [hPc, Subgroup.mem_bot] at this)
  obtain ⟨L₁, hL₁, hmove₁⟩ := exists_block_moved hU hMN hJM hBD hJI hsM hx₂.2 (hP3 s hsP)
    (hP3 x₂ hx₂P) hsx'
  have hgs3 : (convI hU ⟨s, hsN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨s, hsN⟩ : normalizer (U : Set G)) ^ 3 = 1 := Subtype.ext hs3'
    rw [this, map_one]
  obtain ⟨z₁, z₂, hz₁, hz₂, hz₁₂, hsz₁, hsz₂, hzm₁, hzm₂⟩ := hBD.exists_fixed_pair
    (convI_mem_autI hU hsM hsN) hgs3 hL₁ hmove₁
  obtain ⟨Q, hQK, hQ2, hQodd, -, m, -, hQ8⟩ := hY (zpowers s) (zpowers_le.mpr hsP)
    (by rw [Nat.card_zpowers, hs3]) (fun h => hsJ (h (mem_zpowers s)))
  obtain ⟨hNM, hMNn, hNcop⟩ := rankThreePrimeCore_spec 3 M
  have hU2 : IsPGroup 2 U := elementary_isPGroup 2 U hU
  have hUN : U ≤ rankThreePrimeCore 3 M := le_rankThreePrimeCore_of_isPGroup_two hUM hMN hU2
  have hUQ : U ≤ Q := le_of_normalized_of_not_dvd_index hUN (hNM.trans hMN) hU2 hQ2 hQodd
  have hNX : autI hU (rankThreePrimeCore 3 M) ≤ autI hU M := autI_mono hU hNM
  have hNnorm : ∀ x ∈ autI hU M, ∀ n ∈ autI hU (rankThreePrimeCore 3 M),
      x * n * x⁻¹ ∈ autI hU (rankThreePrimeCore 3 M) := by
    intro x hx n hn
    obtain ⟨m', hm', rfl⟩ := (mem_autI hU).1 hx
    obtain ⟨n', hn', rfl⟩ := (mem_autI hU).1 hn
    have hmn : (m' : G) * n' * (m' : G)⁻¹ ∈ rankThreePrimeCore 3 M :=
      (mem_normalizer_iff.mp (hMNn hm') n').mp hn'
    refine (mem_autI hU).2 ⟨m' * n' * m'⁻¹, hmn, ?_⟩
    simp
  have hNcoprime : ∀ n ∈ autI hU (rankThreePrimeCore 3 M), Nat.Coprime (orderOf n) 3 := by
    intro n hn
    obtain ⟨n', hn', rfl⟩ := (mem_autI hU).1 hn
    have h1 : orderOf (convI hU n') ∣ orderOf n' := orderOf_map_dvd _ _
    have h2 : orderOf n' ∣ Nat.card (rankThreePrimeCore 3 M) := by
      rw [← Subgroup.orderOf_coe n']
      exact Subgroup.orderOf_dvd_natCard _ hn'
    exact Nat.Coprime.coprime_dvd_left (h1.trans h2) hNcop.symm
  have hfix := hBD.fixes_commV_of_coprime hNX hNnorm hNcoprime
  have hqz : ∀ q : G, ∀ hq : q ∈ normalizer (U : Set G), q ∈ rankThreePrimeCore 3 M →
      ∀ z ∈ ⨆ L ∈ I, commV L, convI hU ⟨q, hq⟩ z = z := by
    intro q hq hqN z hz
    have hle : (⨆ L ∈ I, commV L) ≤
        MonoidHom.eqLocus (convI hU ⟨q, hq⟩).toMonoidHom (MonoidHom.id _) := by
      refine iSup₂_le fun L hL v hv => ?_
      exact hfix _ (convI_mem_autI hU hqN hq) L hL v hv
    exact hle hz
  have hcomm_of : ∀ (q : G) (hq : q ∈ normalizer (U : Set G)) (z : IntMod U hU),
      convI hU ⟨q, hq⟩ z = z → q * z.val = z.val * q := by
    intro q hq z h
    have := congrArg IntMod.val h
    rw [convI_apply_val] at this
    calc q * z.val = q * z.val * q⁻¹ * q := by group
      _ = z.val * q := by rw [this]
  have hzsq : ∀ z : IntMod U hU, z.val ^ 2 = 1 := fun z => by
    have h := congrArg IntMod.val (IntMod.sq_eq_one z)
    simpa [pow_two] using h
  have hz1 : ∀ z : IntMod U hU, z ≠ 1 → z.val ≠ 1 := fun z hz h =>
    hz (IntMod.val_injective (by simpa using h))
  have hmem : ∀ z : IntMod U hU, convI hU ⟨s, hsN⟩ z = z → z ∈ ⨆ L ∈ I, commV L →
      z.val ∈ Q ⊓ centralizer ((zpowers s : Subgroup G) : Set G) ∧
        ∀ h ∈ Q ⊓ centralizer ((zpowers s : Subgroup G) : Set G), h * z.val = z.val * h := by
    intro z hzs hz
    refine ⟨⟨hUQ z.val_mem, ?_⟩, fun h hh => ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact ((show Commute s z.val from hcomm_of s hsN z hzs).zpow_left k).eq
    · have hhN : h ∈ normalizer (U : Set G) := hMN (hNM (hQK hh.1))
      exact hcomm_of h hhN z (hqz h hhN (hQK hh.1) z hz)
  obtain ⟨hz₁Q, hz₁c⟩ := hmem z₁ hsz₁ hzm₁
  obtain ⟨hz₂Q, hz₂c⟩ := hmem z₂ hsz₂ hzm₂
  exact false_of_two_central_involutions hQ8 hz₁Q hz₂Q hz₁c hz₂c (hz1 z₁ hz₁) (hz1 z₂ hz₂)
    (fun h => hz₁₂ (IntMod.val_injective h)) (hzsq z₁) (hzsq z₂)

theorem IsWitnessGen.not_clauseC_of_solvable_quotient (hS : StandingGen G)
    {P : Sylow 3 G} {M : Subgroup G} (hp : IsWitnessPrime 3 P) (hw : IsWitnessGen 3 P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hC : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank 3 (normalizer (C : Set G)) ≤ 1)
    (hsolv : Group.IsSolvable ↥(autOn M (uCore M T))) :
    ¬ rankThreeClauseC M (P : Subgroup G) := by
  intro hc
  have hPM : (P : Subgroup G) ≤ M := hw.sylow_le hp
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
  obtain ⟨hU, hred, hcase, -⟩ := B2_16_of_quot (hS.charTwo M hw.maxLocal.1) hsolv
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hT) (uCore_eq_conjClosure M T)
  rcases hcase with ⟨hJ, -⟩ | ⟨-, I, -, hN, hcomm, hindep, hnat, -, -, hvindep, hperm⟩
  · exact hJe hJ
  have hZ : CFSG.Open.quasithinOmegaOneCenter T ≠ ⊥ := by
    rw [← omegaOneCenterIn_eq_quasithinOmegaOneCenter]
    exact CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hT.isPGroup hT1
  have hZT : CFSG.Open.quasithinOmegaOneCenter T ≤ T := by
    rw [← omegaOneCenterIn_eq_quasithinOmegaOneCenter]
    exact CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T
  have hZU : CFSG.Open.quasithinOmegaOneCenter T ≤ uCore M T := by
    rw [← omegaOneCenterIn_eq_quasithinOmegaOneCenter]
    exact omegaOneCenterIn_le_uCore M T
  have hrank := hC _ hZ hZT (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T)
  have hKle : M ⊓ centralizer (uCore M T : Set G) ≤
      normalizer ((CFSG.Open.quasithinOmegaOneCenter T : Subgroup G) : Set G) := fun g hg =>
    centralizer_le_normalizer _ (Subgroup.centralizer_le (fun z hz => hZU hz) hg.2)
  have hK := noRankTwoThree_of_pRank_le_one
    ((pRank_mono 3 (by norm_num) hKle).trans hrank)
  have hJM : thompsonJ M ≤ M := thompsonJ_le_self M
  have hMJ : M ≤ normalizer (thompsonJ M : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_thompsonJ M)
  have hrankJ := hC _ (S1414.thompsonJ_ne_bot hT.isPGroup hT1) (thompsonJ_le_self T)
    (S1414.characteristic_thompsonJ T)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup G) M :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPM, P.isPGroup', fun h =>
      P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  have hcyc := cyclicMod_of_le_sup hJM hMJ inf_le_left (le_sup_normalizer_thompsonJ hT)
    ((pRank_mono 3 (by norm_num) inf_le_right).trans hrankJ) hSyl
  have hBD : BlockData (autI hU M) I := ⟨hcomm, hindep, hnat, hvindep, hperm, by
    rw [← hN]
    exact autI_mono hU hJM⟩
  exact false_of_clauseC_of_blocks hU hred.1 hred.2.1 hPM hBD hN.le
    (by simpa using hK) hcyc hc

end CFSG.LocalAnalysis.RankThreeUC
