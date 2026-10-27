module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Close
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem klingenSocleData_of (hk : KFactKlingenLocal) {p : ℕ} [Fact p.Prime] {T : Type} [Group T]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsKlingenIndex p d) (eT : T ≃* CatGroup d)
    {P : Sylow p G} {M H R X : Subgroup G} (h : D1SocleConfig T p P M H R R) (hXR : X ≤ R)
    (hXel : IsElemAbelian p X) (hXc : Nat.card X = p ^ 3) : D1SurvivorData p P M H R X := by
  have hp : p.Prime := Fact.out
  obtain ⟨K, hKn, ⟨eK⟩, hC, -⟩ := h.socle
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.toD1Escape.reducedNongeneration
  have hXp : IsPGroup p X := h.ext.isPGroup.to_le hXR
  have hXH : X ≤ H := hXR.trans h.ext.le_H
  have hXp' : IsPGroup p (X.subgroupOf H) := hXp.comap_subtype
  have hcard : Nat.card ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) = p ^ 3 := by
    rw [card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hXp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hXRb : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hRbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hXR)
  have hXe : IsElemAbelian p ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) := by
    refine elementary_abelian_map p ?_ _
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := (isMulCommutative_iff.mp hXel.1) ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hXel.2 _ (Subgroup.mem_subgroupOf.mp hx))
  have hS := hk.inSitu p h.ext.ne_two d hd _ K hKn ⟨eK.trans eT⟩ hC Rbar _ _ hXRb hXe hcard
    hred.weakCore_le hred.ne_top
  have hX1 : X ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card (⊥ : Subgroup G) = p ^ 3 := hXc
    rw [Subgroup.card_bot] at h1
    have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hp.one_lt
    omega
  refine h.ext.survivorData_of_map h.glob hXR hX1 (fun W hW hWn hWc => ?_)
    hS.normal_dichotomy (hS.centralizer_le.trans ?_)
  · exact hS.primeCore W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) hWc
  · rw [hRbar]

theorem d1CaseThreeKlingen3_of_residue3 (hmod : StmtKlingenModel) (hk : KFactKlingenLocal)
    (hβ : KFactBetaRank2) (h1s : D1CaseOneSmall3 G) (h2 : D1CaseTwo3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (h : D1KlingenResidue3 G) : D1CaseThreeKlingen3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD
  by_cases hsp : IsKlingenComponent p K
  swap
  · exact h.other p P M H R Rbar hcfg K hK huniq hnc hcent hKD hsp
  have hp : p.Prime := Fact.out
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hsp
  have hZ : Subgroup.center K = ⊥ :=
    hmod.center K p d hcfg.loc.ne_two hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK₀ : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have eK : K ≃* CatGroup d := eK₀.trans e₁
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hC := hcfg.centralizer_eq_bot hK huniq hcent hZ
  have hOut := hk.outer p hcfg.loc.ne_two d hd K ⟨eK⟩
  obtain ⟨hKs, hKnab⟩ := simple_nonabelian_of_center_eq_bot hK hZ
  have hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K := by
    have : Finite (MulAut K) := MulEquiv.finite_left
    intro x hx
    rw [← hcfg.rbar] at hx
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem := mem_sup_centralizer_of_pow hp hOut hxk
    rwa [hC, sup_bot_eq] at hmem
  have hS0 : D1SocleConfig (↥K) p P M H R R :=
    ⟨hcfg.ext, hcfg.glob.toU.toAGLGlobal, le_rfl, K, hKn, ⟨MulEquiv.refl _⟩, hC,
      (inf_eq_left.mpr hRK).symm⟩
  have hRH : R ≤ H := hcfg.ext.le_H
  have hRp : IsPGroup p R := hcfg.ext.isPGroup
  obtain ⟨E, hER, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p)
    (H := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) (k := 3)
    hcfg.red.three_le_pRank
  obtain ⟨X, hXH, hXR, hXmap, -, ψ, -⟩ := exists_lift_of_le_map hp hRH hRp
    (primeComplementCore (G := H) p) (primeComplementCore_coprime p) (hER.trans hcfg.rbar.le)
  have hXel : IsElemAbelian p X := isElemAbelian_of_mulEquiv ψ hE
  have hXc : Nat.card X = p ^ 3 := (Nat.card_congr ψ.toEquiv).trans hEc
  have hX1 : X ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card (⊥ : Subgroup G) = p ^ 3 := hXc
    rw [Subgroup.card_bot] at h1
    have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hp.one_lt
    omega
  have hcompR : D1JCompetitorsOn (fun H' => D1KlingenSocle p P M R H') R R :=
    competitorsOn_klingen3 hmod hk hβ h1s h2 h3 h.other hcfg.glob hcfg.loc hcfg.ind
  have hS1 : D1KlingenSocle p P M R H := ⟨↥K, inferInstance, hKs, hKnab,
    ⟨d, hd, ⟨eK⟩⟩, hS0⟩
  have hsurv : ∀ H' : Subgroup G, D1KlingenSocle p P M R H' → D1SurvivorData p P M H' R X := by
    rintro H' ⟨T, _, -, -, ⟨d', hd', ⟨eT⟩⟩, h'⟩
    exact klingenSocleData_of hk hd' eT h' hXR hXel hXc
  have hO := h.mSide p P M H R Rbar hcfg K hK huniq hnc hcent hKD ⟨d, hd, ⟨e₁⟩⟩ X
    (hsurv H hS1) hXel hXc
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1KlingenSocle p P M R H') hsurv hO
    (competitorsOn_of_le_klingen hcompR hXR hX1) hS1

end CFSG.LocalAnalysis.RankThreeTheoremC
