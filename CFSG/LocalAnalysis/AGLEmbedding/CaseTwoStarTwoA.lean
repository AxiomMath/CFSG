module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarNF
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarCore
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarProj
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataBase
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.inf_X0_facts (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) :
    Group.IsSolvable ((d1X0 p M H).comap L.subtype) ∧
      ∀ k : L, (∀ y ∈ (d1X0 p M H).comap L.subtype, k * y * k⁻¹ ∈ (d1X0 p M H).comap L.subtype) →
        k ∈ (d1X0 p M H).comap L.subtype :=
  hd.toBase.inf_X0_facts hAut hS hKL hL hLX

theorem D1CaseTwoDataAt.coprime_card_of_perfect_of_forall (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H)
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hred := hd.cfg.red
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set Ub := (U.subgroupOf H).map π with hUbdef
  have hUH : U ≤ H := hU.trans inf_le_left
  have hUb : ⁅Ub, Ub⁆ = Ub := by
    have h1 : ⁅U.subgroupOf H, U.subgroupOf H⁆ = U.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH, hUp]
    rw [hUbdef, ← Subgroup.map_commutator, h1]
  have hUbX : Ub ≤ d1X0 p M H := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    (hU (Subgroup.mem_subgroupOf.mp hu))
  have hUbC : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      Ub ≤ Subgroup.centralizer (L : Set _) := by
    intro L hL
    have hLX := hall L hL
    obtain ⟨hsolv, hself⟩ := D1CaseTwoDataAt.inf_X0_facts hAut hS hKL hd hL hLX
    obtain ⟨hsimple, hnonab, hcat, -⟩ := hred.isSimpleGroup_of_isCyclic hd.cfg.catalog hL
      (hd.cyclic L hL)
    have hZ := hred.center_eq_bot_of_isCyclic hL (hd.cyclic L hL)
    have hUbN : Ub ≤ Subgroup.normalizer (L : Set _) :=
      le_normalizer_of_perfect (fun L₁ L₂ L₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ =>
        hred.false_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃) hUb hL
    have hUbK : Ub ≤ L ⊔ Subgroup.centralizer (L : Set _) :=
      perfect_le_sup_centralizer_of_outer (hSch L hsimple hnonab hcat) hUb hUbN
    obtain ⟨ρ, hρ⟩ := exists_proj hZ hUbK
    have hρX : ∀ u : Ub, ρ u ∈ (d1X0 p M H).comap L.subtype := by
      intro u
      apply hself
      intro y hy
      set a : H ⧸ primeComplementCore (G := H) p :=
        ((ρ u : L) : H ⧸ primeComplementCore (G := H) p) with ha
      set b : H ⧸ primeComplementCore (G := H) p := (u : H ⧸ primeComplementCore (G := H) p)
        with hb
      have hc : a⁻¹ * b ∈ Subgroup.centralizer (L : Set _) := hρ u
      have hconj : a * (y : H ⧸ primeComplementCore (G := H) p) * a⁻¹ = b * y * b⁻¹ := by
        have h1 : (y : H ⧸ primeComplementCore (G := H) p) * (a⁻¹ * b) = (a⁻¹ * b) * y :=
          Subgroup.mem_centralizer_iff.mp hc (y : _) y.2
        calc a * (y : H ⧸ primeComplementCore (G := H) p) * a⁻¹
            = a * ((y : H ⧸ primeComplementCore (G := H) p) * (a⁻¹ * b)) * b⁻¹ := by group
          _ = a * ((a⁻¹ * b) * y) * b⁻¹ := by rw [h1]
          _ = b * y * b⁻¹ := by group
      show ((ρ u * y * (ρ u)⁻¹ : L) : H ⧸ primeComplementCore (G := H) p) ∈ d1X0 p M H
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← ha, hconj]
      exact (d1X0 p M H).mul_mem ((d1X0 p M H).mul_mem (hUbX u.2) hy) ((d1X0 p M H).inv_mem
        (hUbX u.2))
    have hρrange : ρ.range = ⊥ := by
      have hle : ρ.range ≤ (d1X0 p M H).comap L.subtype := by
        rintro _ ⟨u, rfl⟩
        exact hρX u
      have hsol : Group.IsSolvable ρ.range := Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective hle)
      have hper : ⁅ρ.range, ρ.range⁆ = ρ.range := by
        have h1 : ⁅(⊤ : Subgroup Ub), (⊤ : Subgroup Ub)⁆ = ⊤ := by
          have : Group.IsPerfect Ub := Subgroup.isPerfect_iff.mpr hUb
          exact Group.IsPerfect.commutator_eq_top
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
      have : Group.IsPerfect ρ.range := Subgroup.isPerfect_iff.mpr hper
      obtain ⟨n, hn⟩ := hsol.solvable
      rw [Group.IsPerfect.derivedSeries_eq_top] at hn
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx⟩ : ρ.range) ∈ (⊤ : Subgroup ρ.range) := Subgroup.mem_top _
      rw [hn, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)
    intro u hu
    have h1 : ρ ⟨u, hu⟩ = 1 := by
      have : ρ ⟨u, hu⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hρrange, Subgroup.mem_bot] at this
      exact this
    have := hρ ⟨u, hu⟩
    rwa [h1, Subgroup.coe_one, inv_one, one_mul] at this
  obtain ⟨K₀, hK₀⟩ := hd.cfg.exists_isComponentOf
  have hUbO : Ub ≤ Subgroup.centralizer (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :
      Set _) := by
    have : (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)).Normal := CFSG.pCore_normal
    exact le_centralizer_of_perfect_of_isCyclic (hred.isCyclic_pCore_of_component hK₀) hUb
  have hUb1 : Ub = ⊥ := by
    have hcomm : ∀ a ∈ Ub, ∀ b ∈ Ub, a * b = b * a := fun a ha b hb =>
      (commute_of_mem_centralizer_fstar hred.core_eq_bot (hUbO ha) (fun L hL => hUbC L hL ha)
        (hUbO hb) (fun L hL => hUbC L hL hb)).eq
    rw [← hUb, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a ha b hb
  have hUN : U ≤ GLBPrimeCore p H := by
    intro u hu
    have h1 : π ⟨u, hUH hu⟩ ∈ Ub := ⟨⟨u, hUH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hUb1, Subgroup.mem_bot] at h1
    exact (mk'_primeComplementCore_eq_one_iff p _).mp h1
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hUN) (glbPrimeCore_coprime p H)

theorem D1CaseTwoData.coprime_card_of_perfect_of_forall (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (hd : D1CaseTwoData p P M H R Rbar)
    (hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H)
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) :=
  D1CaseTwoDataAt.coprime_card_of_perfect_of_forall (hAut := (kFactCycAut_of_kFactBeta hβ))
    (hS := hS) (hKL := hKL) (hSch := hSch) (hd := hd.toAt) (hall := hall) (hU := hU) (hUp := hUp)

@[expose] def D1CaseTwoNormalFormTwoA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      (p = 3 ∨ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
        L ≤ d1X0 p M H) → False

theorem D1CaseTwoDataAt.false_of_nf_five {G : Type} [Group G] [Finite G] (hAut : KFactCycAut)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hInn : KFactBlockAutPrimeInner) {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd :
        D1CaseTwoDataAt p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z)
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H) (hp3 : p ≠ 3)
    (hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M
        H)
    (hrk3 : 3 < p → Open.pRank 3 (H ⊓ M) ≤ 3) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    omega
  obtain ⟨-, -, -, hzR, hzp, -, -⟩ := hz
  exact (hd.toPhaseThree hAut hS hKL).false_of_centralizer_le_five_of_pRank (hrk3 (by omega))
    h84 h85 h86 h93 hD2 hKP hC3 hK5 hK2 hC3' hK5' hInn hp5
    (fun U hU hUp => hd.coprime_card_of_perfect_of_forall hAut hS hKL hSch hall hU hUp)
    ⟨hd.cfg.ext.le_H hzR, hd.cfg.ext.le_M hzR⟩ hzp (centralizer_le_of_normalizer_vz_le hNH)

theorem d1CaseTwoNormalForm_of_twoA (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hInn : KFactBlockAutPrimeInner) (h : D1CaseTwoNormalFormTwoA) : D1CaseTwoNormalForm := by
  intro G _ _ p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hK hNH
  by_cases hrest : p = 3 ∨ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p),
      IsComponentOf L ⊤ ∧ L ≤ d1X0 p M H
  · exact h G p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hK hNH hrest
  push Not at hrest
  obtain ⟨hp3, hall⟩ := hrest
  refine hd.toAt.false_of_nf_five (kFactCycAut_of_kFactBeta hβ) hS hKL hSch h84 h85 h86 h93 hD2
    hKP hC3 hK5 hK2 hC3' hK5' hInn hz hNH hp3 hall fun hp => ?_
  by_contra hc
  exact (hd.toPhaseThree hβ hS hKL).false_of_four_le_pRank' hd.cfg.ind Nat.prime_three
    (by decide) hp (by omega)

end CFSG.AGLEmbedding
