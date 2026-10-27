module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Gen
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import CFSG.ClassicalInvolution.RouteD.TwinTenNodes
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.MilestoneAssemblyCore
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainAssembly
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate110
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups commutatorElement
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

section ChainSign

variable {p : ℕ} [Fact p.Prime]

theorem chainSign_of_lifts_norm {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hcls : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p e) {X : Type} [Group X]
    (φ : (modelUniv t n p e Fact.out).K →* X) (hker : φ.ker ≤ Subgroup.center _)
    {R₁ R₂ R₃ : Subgroup (modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (h₃ : R₃ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) {a₁ a₂ a₃ : X}
    (ha₁ : IsUniqueInvolution (R₁.map φ) a₁) (ha₂ : IsUniqueInvolution (R₂.map φ) a₂)
    (ha₃ : IsUniqueInvolution (R₃.map φ) a₃) (hnorm₁ : conjSub a₂ (R₁.map φ) = R₁.map φ)
    (hnorm₃ : conjSub a₂ (R₃.map φ) = R₃.map φ) (hR₁₃ : Commutes (R₁.map φ) (R₃.map φ))
    (hne₁₂ : R₁.map φ ≠ R₂.map φ) (hne₃₂ : R₃.map φ ≠ R₂.map φ)
    (hnc₁₂ : ¬ Commutes (R₁.map φ) (R₂.map φ)) (hnc₃₂ : ¬ Commutes (R₃.map φ) (R₂.map φ)) :
    ((∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₂.map φ) (R₃.map φ)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₂.map φ) (R₃.map φ)) := by
  have hG2 : t ≠ .G2 := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hfund : IsFundTag t := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by omega
  have hSL2 : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField p e)) := fun R hR =>
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund
      hadm hG2 hD4 hR
  have hlong : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      R ∈ CFSG.ClassicalInvolution.ModelFacts.longestFundamental
        (modelUniv t n p e Fact.out).D := fun R hR =>
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR
  obtain ⟨c₁, hc₁, ho₁, hu₁, ha₁', -, hperf₁⟩ :=
    ConnectedA2.exists_lift_central_involution hodd h4 φ hker (hSL2 R₁ h₁).some ha₁
  obtain ⟨c₂, hc₂, ho₂, -, ha₂', -, -⟩ :=
    ConnectedA2.exists_lift_central_involution hodd h4 φ hker (hSL2 R₂ h₂).some ha₂
  obtain ⟨c₃, hc₃, ho₃, hu₃, ha₃', -, hperf₃⟩ :=
    ConnectedA2.exists_lift_central_involution hodd h4 φ hker (hSL2 R₃ h₃).some ha₃
  have hqs := CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv t n p e Fact.out hfund
    hadm
  have : Group.IsPerfect (modelUniv t n p e Fact.out).K := ⟨hqs.1⟩
  have hperf₁' : ⁅R₁, R₁⁆ = R₁ :=
    le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hperf₁
  have hR₁₃' : Commutes R₁ R₃ := commutes_of_map_commutes hker hperf₁' hR₁₃
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := hR₁₃' c₁ hc₁ c₃ hc₃
  have h₂₁ : c₂ * c₁ = c₁ * c₂ :=
    ConnectedA2.commute_of_conjSub_map hker hperf₁ hc₁ ho₁ hu₁ (by rw [← ha₂']; exact hnorm₁)
  have h₂₃ : c₂ * c₃ = c₃ * c₂ :=
    ConnectedA2.commute_of_conjSub_map hker hperf₃ hc₃ ho₃ hu₃ (by rw [← ha₂']; exact hnorm₃)
  exact CFSG.ClassicalInvolution.ModelFacts.StandardPairChainSign.map_of_commute
    (CFSG.ClassicalInvolution.ModelFacts.standardPairChainSign_of_classical hcls hadm) hfund hadm
    hp2 hq φ hker (hlong R₁ h₁) (hlong R₂ h₂) (hlong R₃ h₃) hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₂₁.symm
    h₂₃.symm h₁₃ hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

end ChainSign

section Model

variable {p f : ℕ} [hp : Fact p.Prime]

theorem exists_commuting_fund_sl4 (hq : 4 ≤ p ^ f)
    {R : Subgroup (modelUniv .PSL 4 p f hp.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D) :
    ∃ R' ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D, Commutes R R' := by
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hf, by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hsc := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSL 4 p f hp.out trivial
    hadm (by decide) (by decide)
  have hl := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .PSL 4 p f hp.out trivial
    hadm
  set D := (modelUniv .PSL 4 p f hp.out).D with hD
  have hB : ∀ i : Fin 3, rankOne D.rootGroup i ∈
      fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D := fun i =>
    rankOne_mem_fundamental D (hl i trivial)
  obtain ⟨g, hg⟩ := hsc _ (hB 0) R hR
  have hB2 := CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups (hB 2) g
  have h02 : Commutes (rankOne D.rootGroup (0 : Fin 3)) (rankOne D.rootGroup (2 : Fin 3)) :=
    sl_nodes_comm (GaloisField p f) 0 2 (by decide)
  refine ⟨conjSub g (rankOne D.rootGroup (2 : Fin 3)), hB2, ?_⟩
  rw [hg]
  exact (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff g).mpr h02

end Model

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem layer_le_sup_of_chain {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : LocalShapeT p f 2 .PSL 4 (conjClass K) z) {β : Subgroup G}
    (hβ : β ∈ conjClass K) {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {j₁ j₂ T : Subgroup G}
    (hj₁ : j₁ ∈ conjClass K) (hj₂ : j₂ ∈ conjClass K) (hT : T ∈ conjClass K)
    (hKj₁ : Commutes K j₁) (hKj₂ : Commutes K j₂) (hKT : Commutes K T)
    (hβj₁ : Commutes β j₁) (hβj₂ : Commutes β j₂) (hj₁₂ : Commutes j₁ j₂)
    (hTj₁ : Commutes T j₁) (hTj₂ : T ≠ j₂)
    {x₀ : G} (hx₀ : IsClassicalMember p f j₁ x₀) {M : Subgroup G} (hM : M ∈ conjClass K)
    (hMj₁ : Commutes j₁ M) (hMj₂ : M ≠ j₂) : M ≤ K ⊔ β ⊔ T := by
  classical
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    have hf : f ≠ 0 := by
      have := S.five
      rintro rfl
      simp at this
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two S.odd).pow
  obtain ⟨c⟩ := TCtx.nonempty_A3 S.odd S.five hΩ hex hKΩ S.cls S.p1 hshape
  obtain ⟨cx⟩ := Gaps.exists_ctx_member c hsingle hshape hj₁ hx₀
  obtain ⟨W, hW⟩ := hKβ
  have hnc : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hKΩ hx₀.mem hKj₁
  have hβx : β ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hβ hx₀.mem hβj₁
  have hj₂x : j₂ ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hj₂ hx₀.mem hj₁₂.symm
  have hTx : T ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hT hx₀.mem hTj₁
  have hMx : M ∈ centralizingMembers (conjClass K) {x₀} :=
    mem_centralizingMembers_of_commutes hM hx₀.mem hMj₁.symm
  have hne : ∀ {A B : Subgroup G}, A ∈ conjClass K → Commutes A B → A ≠ B := by
    intro A B hA hAB hAeq
    subst hAeq
    exact not_commutes_self_of_mem hΩ hA hAB
  have hKj₁ne : K ≠ j₁ := hne hKΩ hKj₁
  have hKj₂ne : K ≠ j₂ := hne hKΩ hKj₂
  have hβj₁ne : β ≠ j₁ := hne hβ hβj₁
  have hTj₁ne : T ≠ j₁ := hne hT hTj₁
  have hj₂j₁ne : j₂ ≠ j₁ := (hne hj₁ hj₁₂).symm
  have hβK : β ≠ K := hKβne.symm
  have hKQ : ¬ locImg (conjClass K) x₀ K ≤ cx.d.Q₁ := fun hQ =>
    hnc (cx.commutes_T_of_ne hKx hQ hβx hβK)
  obtain ⟨R_K, hR_K, hKR⟩ := cx.exists_fund_of_ne hKx hKj₁ne hKQ
  have hβQ : ¬ locImg (conjClass K) x₀ β ≤ cx.d.Q₁ := fun hQ =>
    hnc (cx.commutes_T_of_ne hβx hQ hKx hKβne).symm
  obtain ⟨R_β, hR_β, hβR⟩ := cx.exists_fund_of_ne hβx hβj₁ne hβQ
  have hj₂Q : locImg (conjClass K) x₀ j₂ ≤ cx.d.Q₁ := by
    by_contra hQ
    obtain ⟨R₂, hR₂, hj₂R⟩ := cx.exists_fund_of_ne hj₂x hj₂j₁ne hQ
    have c₁ : Commutes R₂ R_K :=
      (cx.commutes_iff_fund hj₂x hKx hR₂ hj₂R hKR).mp hKj₂.symm
    have c₂ : Commutes R₂ R_β :=
      (cx.commutes_iff_fund hj₂x hβx hR₂ hj₂R hβR).mp hβj₂.symm
    have hne₁ : R_K ≠ R₂ := fun h =>
      hKj₂ne (cx.eq_of_locImg_eq hKx hj₂x (by rw [hKR, hj₂R, h]))
    have hne₂ : R_β ≠ R₂ := fun h =>
      (hne hβ hβj₂) (cx.eq_of_locImg_eq hβx hj₂x (by rw [hβR, hj₂R, h]))
    have := fund_sl4_eq_of_commutes S.odd hR₂ hR_K hR_β hne₁ hne₂ c₁ c₂
    exact hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, this]))
  have hTQ : ¬ locImg (conjClass K) x₀ T ≤ cx.d.Q₁ := fun hQ =>
    hTj₂ (cx.eq_of_locImg_le_Q₁ hTx hj₂x hQ hj₂Q)
  obtain ⟨R_T, hR_T, hTR⟩ := cx.exists_fund_of_ne hTx hTj₁ne hTQ
  have hKTne : K ≠ T := hne hKΩ hKT
  have hTβne : T ≠ β := fun h => hnc (h ▸ hKT)
  have hKR_T : Commutes R_K R_T := (cx.commutes_iff_fund hKx hTx hR_K hKR hTR).mp hKT
  have hTβnc : ¬ Commutes T β := by
    intro hTβ
    have c₂ : Commutes R_T R_β := (cx.commutes_iff_fund hTx hβx hR_T hTR hβR).mp hTβ
    have hne₁ : R_K ≠ R_T := fun h =>
      hKTne (cx.eq_of_locImg_eq hKx hTx (by rw [hKR, hTR, h]))
    have hne₂ : R_β ≠ R_T := fun h =>
      hTβne (cx.eq_of_locImg_eq hTx hβx (by rw [hTR, hβR, h]))
    have := fund_sl4_eq_of_commutes S.odd hR_T hR_K hR_β hne₁ hne₂ hKR_T.symm c₂
    exact hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, this]))
  have htx : t * x₀ * t⁻¹ = x₀ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hβj₁ t ht.mem x₀ hx₀.mem
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hj₁t : conjSub t j₁ = j₁ := conjSub_eq_of_mem_of_commutes ht.mem hβj₁
  have hj₂t : conjSub t j₂ = j₂ := conjSub_eq_of_mem_of_commutes ht.mem hβj₂
  have hTt : conjSub t T = T := by
    have hmem : conjSub t T ∈ centralizingMembers (conjClass K) {x₀} := by
      have := centralizingMembers_conj hΩ.conjInvariant t x₀
      rw [htx] at this
      rw [this]
      exact ⟨T, hTx, rfl⟩
    have hne1 : conjSub t T ≠ j₁ := fun h =>
      hTj₁ne (conjSub_injective t (h.trans hj₁t.symm))
    have hne2 : conjSub t T ≠ j₂ := fun h => hTj₂ (conjSub_injective t (h.trans hj₂t.symm))
    have hQ : ¬ locImg (conjClass K) x₀ (conjSub t T) ≤ cx.d.Q₁ := fun hQ =>
      hne2 (cx.eq_of_locImg_le_Q₁ hmem hj₂x hQ hj₂Q)
    obtain ⟨R', hR', hR'img⟩ := cx.exists_fund_of_ne hmem hne1 hQ
    have hKT' : Commutes K (conjSub t T) := by
      have := (commutes_conjSub_iff (K := K) (L := T) t).mpr hKT
      rwa [hKt] at this
    have c₁ : Commutes R_K R' := (cx.commutes_iff_fund hKx hmem hR_K hKR hR'img).mp hKT'
    have hne₁ : R' ≠ R_K := fun h =>
      (hne hKΩ hKT') (cx.eq_of_locImg_eq hKx hmem (by rw [hKR, hR'img, h]))
    have hne₂ : R_T ≠ R_K := fun h =>
      hKTne (cx.eq_of_locImg_eq hKx hTx (by rw [hKR, hTR, h]))
    have := fund_sl4_eq_of_commutes S.odd hR_K hR' hR_T hne₁ hne₂ c₁ hKR_T
    exact cx.eq_of_locImg_eq hmem hTx (by rw [hR'img, hTR, this])
  obtain ⟨zT, hzT⟩ := hΩ.classical T hT
  have hu₁ := ConnectedA2.isUniqueInvolution_locImg hex hKx
    (isUniqueInvolution_of_exact hodd (hex K hKΩ) S.cls)
  have hu₂ := ConnectedA2.isUniqueInvolution_locImg hex hβx
    (isUniqueInvolution_of_exact hodd (hex β hβ) ht)
  have hu₃ := ConnectedA2.isUniqueInvolution_locImg hex hTx
    (isUniqueInvolution_of_exact hodd (hex T hT) hzT)
  rw [hKR] at hu₁
  rw [hβR] at hu₂
  rw [hTR] at hu₃
  have htY : t ∈ locLayer (conjClass K) x₀ := le_centralizingLayer hβx ht.mem
  have hnorm : ∀ {N : Subgroup G} {R : Subgroup (modelUniv .PSL 4 p f Fact.out).K},
      conjSub t N = N → locImg (conjClass K) x₀ N = R.map cx.d.ψ →
      conjSub (locMk (conjClass K) x₀ ⟨t, htY⟩) (R.map cx.d.ψ) = R.map cx.d.ψ := by
    intro N R hN hNR
    have h := locImg_conjSub_layer (Ω := conjClass K) (x := x₀) N ⟨t, htY⟩
    rw [show ((⟨t, htY⟩ : ↥(locLayer (conjClass K) x₀)) : G) = t from rfl, hN] at h
    rw [← hNR]
    exact h.symm
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr (by
      have := S.five
      rintro rfl
      simp at this), by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hs := chainSign_of_lifts_norm S.odd S.five (Or.inl rfl) hadm cx.d.ψ cx.d.ker_le hR_K hR_β
    hR_T hu₁ hu₂ hu₃ (hnorm hKt hKR) (hnorm hTt hTR)
    (by rw [← hKR, ← hTR]; exact commutes_locImg_of_commutes hKT)
    (fun h => hKβne (cx.eq_of_locImg_eq hKx hβx (by rw [hKR, hβR, h])))
    (fun h => hTβne (cx.eq_of_locImg_eq hTx hβx (by rw [hTR, hβR, h])))
    (fun h => hnc ((commutes_iff_locImg hΩ cx.hP1 hKx hβx).mpr (by rw [hKR, hβR]; exact h)))
    (fun h => hTβnc ((commutes_iff_locImg hΩ cx.hP1 hTx hβx).mpr (by rw [hTR, hβR]; exact h)))
  rw [← hKR, ← hβR, ← hTR] at hs
  have hβT : ∃ W, LinearBlockStandardPair (GaloisField p f) W β T :=
    linear_of_chainSign_images S.odd S.five hΩ cx.hP1 hKx hβx hTx hs ⟨W, hW⟩
  have hMj₁ne : M ≠ j₁ := (hne hj₁ hMj₁).symm
  have hMQ : ¬ locImg (conjClass K) x₀ M ≤ cx.d.Q₁ := fun hQ =>
    hMj₂ (cx.eq_of_locImg_le_Q₁ hMx hj₂x hQ hj₂Q)
  have hgen := cx.le_iSup_of_chain (L := ![K, β, T])
    (fun k => by fin_cases k <;> simp [hKx, hβx, hTx])
    (fun k => by fin_cases k <;> simp [hKj₁ne, hβj₁ne, hTj₁ne])
    (fun k => by fin_cases k <;> simp [hKQ, hβQ, hTQ])
    (by simpa using hKT) (by simpa using ⟨W, hW⟩) (by simpa using hβT) hMx hMj₁ne hMQ
  refine hgen.trans (iSup_le fun k => ?_)
  fin_cases k
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

end Layer

end CFSG.ClassicalInvolution.RouteD
