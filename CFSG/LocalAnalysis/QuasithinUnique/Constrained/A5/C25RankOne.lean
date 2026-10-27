module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Core
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Sporadic.J1
public import Certificates.Certificate43
public import Certificates.Certificate3119
public import CFSG.Foundations
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
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
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

section Bender

variable {X : Type} [Group X] [Finite X]

theorem normalizer_le_of_stronglyEmbedded {T : Sylow 2 X}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup X) : Set X)))
    {P : Subgroup X} (hP1 : P ≠ ⊥) (hPT : P ≤ (T : Subgroup X)) :
    Subgroup.normalizer (P : Set X) ≤ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
  set B := Subgroup.normalizer ((T : Subgroup X) : Set X) with hB
  have hTB : (T : Subgroup X) ≤ B := Subgroup.le_normalizer
  have hP2 : IsPGroup 2 P := T.isPGroup'.to_le hPT
  intro g hg
  by_contra hgB
  have hgodd := hSE.2.2 g hgB
  have hUle : P ≤ B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro u hu
    refine ⟨hTB (hPT hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, ?_, ?_⟩⟩
    · exact hTB (hPT ((Subgroup.mem_normalizer_iff.mp hg u).mp hu))
    · simp [mul_assoc]
  have hne : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  obtain ⟨n, hn, hcard⟩ := hP2.nontrivial_iff_card.mp hne
  have hdvd : 2 ∣ Nat.card (B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) :=
    (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
  exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)

theorem isSolvable_normalizer_of_borelSetup {T : Sylow 2 X} {D : Subgroup X}
    (h : Goldschmidt.G3a.BorelSetup T D) :
    Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup X) : Set X)) := by
  set B := Subgroup.normalizer ((T : Subgroup X) : Set X) with hB
  have hTB : (T : Subgroup X) ≤ B := Subgroup.le_normalizer
  have hN : ((T : Subgroup X).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).2 le_rfl
  have hT2 : IsPGroup 2 ↥((T : Subgroup X).subgroupOf B) :=
    T.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hTB).symm
  have : Group.IsSolvable ↥((T : Subgroup X).subgroupOf B) := by
    have : Group.IsNilpotent ↥((T : Subgroup X).subgroupOf B) := hT2.isNilpotent
    infer_instance
  let ψ : ↥D →* ↥B ⧸ ((T : Subgroup X).subgroupOf B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion h.le)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul hg
    refine ⟨⟨d, hd⟩, ?_⟩
    change (QuotientGroup.mk (⟨d, h.le hd⟩ : B) : ↥B ⧸ ((T : Subgroup X).subgroupOf B)) =
      QuotientGroup.mk ⟨t * d, hg⟩
    rw [QuotientGroup.eq]
    have hd' : d⁻¹ ∈ B := B.inv_mem (h.le hd)
    have := (Subgroup.mem_normalizer_iff.mp hd' t).mp ht
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using this
  have : IsCyclic ↥D := h.cyc
  have : IsCyclic (↥B ⧸ ((T : Subgroup X).subgroupOf B)) := isCyclic_of_surjective ψ hψ
  have : Group.IsSolvable (↥B ⧸ ((T : Subgroup X).subgroupOf B)) := inferInstance
  exact Group.isSolvable_of_ker_le_range ((T : Subgroup X).subgroupOf B).subtype
    (QuotientGroup.mk' ((T : Subgroup X).subgroupOf B)) (by
      intro x hx
      exact ⟨⟨x, (QuotientGroup.eq_one_iff x).1 hx⟩, rfl⟩)

theorem solvable_of_bender
    (hX : fusionIsBenderGroup X) {P Λ : Subgroup X} (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) (hΛ : Λ ≤ Subgroup.normalizer (P : Set X)) : Group.IsSolvable ↥Λ := by
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨D, h⟩ := Goldschmidt.G3a.exists_borelSetup hX T
  have hNP := normalizer_le_of_stronglyEmbedded h.se hP1 hPT
  have := isSolvable_normalizer_of_borelSetup h
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion (hΛ.trans hNP) : ↥Λ →* _))
    (Subgroup.inclusion_injective (hΛ.trans hNP))

end Bender

section Models

open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels CFSG.ShultStronglyClosedTI

theorem fusionIsBenderGroup_of_isPSL {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    fusionIsBenderGroup X := by
  obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := h
  have hn1 : 1 ≤ n := hadm.2.1
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact hadm.2.2.2.1 (by simp)
  left
  exact ⟨n, hn2, ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (projectiveSpecialLinearFieldEquiv (finiteFieldEquivGaloisField K 2 n (by omega) hcard)
      (Fin 2)))⟩⟩

theorem fusionIsBenderGroup_of_isSz {n : ℕ} {X : Type} [Group X] (h : IsSz n X) :
    fusionIsBenderGroup X := by
  obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := h
  subst hn
  right
  right
  exact ⟨a, ha, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (glaSzEquivNative a ha hcard))⟩⟩

end Models

theorem rankOneLocalSolvable :
    RankOneLocalSolvable := by
  intro X _ _ hX P Λ hP h16 hΛ
  have hP2 : IsPGroup 2 ↥P := fun x => ⟨1, Subtype.ext (by simpa using hP.2 x x.2)⟩
  have hP1 : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h16
    omega
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hn⟩
  · exact solvable_of_bender (fusionIsBenderGroup_of_isPSL hn) hP2 hP1 hΛ
  · exact solvable_of_bender (fusionIsBenderGroup_of_isSz hn) hP2 hP1 hΛ
  · exfalso
    obtain ⟨e⟩ := hJ
    have hdvd : Nat.card P ∣ Nat.card X := Subgroup.card_subgroup_dvd_card P
    rw [Nat.card_congr e.toEquiv] at hdvd
    change Nat.card P ∣ Nat.card NativeSporadic.J1 at hdvd
    rw [CFSG.Sporadic.J1.card_J1, hk] at hdvd
    have h16' : 2 ^ 4 ∣ 175560 := (pow_dvd_pow 2 hk4).trans hdvd
    omega
  · exfalso
    have hle := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp
      (by omega) hn
    have := CFSG.SectionRank.le_pRank Nat.one_lt_two (le_top : P ≤ ⊤) hP hk
    change k ≤ twoRank X at this
    omega

end CFSG.QuasithinUnique.A5.C25
