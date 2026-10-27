module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardComp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDiag
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardStep
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm3Cover

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit
open CFSG.ASVolI.ChIJK (IsComponentIn)

theorem false_of_diag_balanced (hH : Harris82Theorem1KProper)
    (hL : CFSG.StandardType.GGLBalanceInput)
    (hbr : Assembly.CatalogImp Blueprint.Catalog Assembly.InCatalog) (hKR : T1.KnownRowThree)
    (hC2 : POmegaPlusCentreExpTwo) (hC3 : LinUnitInvolutionComponents)
    (hC4 : POmegaPlusNotLinUnit) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {w t : G} (hw2 : orderOf w = 2) (ht2 : orderOf t = 2) (htM : t ∈ centralizer {w})
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer {w} ⊓ centralizer {t}))
    {n : ℕ} (hn : n = 4 ∨ n = 6)
    (hmJ : Blueprint.LieModel (↥J ⧸ Open.fusionZStar ↥J) .POmegaPlus n 3 1) (hwJ : w ∈ J)
    {K₀ K₁ : Subgroup ↥(centralizer ({w} : Set G))} (hK₀ : IsTwoComponent K₀)
    (hK₁ : K₁ = K₀.map (MulAut.conj (⟨t, htM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom)
    (hne : K₁ ≠ K₀)
    (hLeq : J.subgroupOf (centralizer {w}) = centralizerResidual (K₀ ⊔ K₁)
      (⟨t, htM⟩ : ↥(centralizer ({w} : Set G)))) : False := by
  subst hK₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥(centralizer ({w} : Set G)) := ⟨t, htM⟩ with ht'def
  set z : ↥(centralizer ({w} : Set G)) := ⟨w, mem_centralizer_singleton_iff.mpr rfl⟩ with hzdef
  have hO : pPrimeCore 2 ↥(centralizer ({w} : Set G)) = ⊥ :=
    pPrimeCore_eq_bot_of_oddCore (hbal w hw2)
  have hK₀c : CFSG.IsComponent K₀ := (isTwoComponent_iff_isComponent hO K₀).mp hK₀
  have hK₁c : CFSG.IsComponent (K₀.map (MulAut.conj t').toMonoidHom) :=
    (isTwoComponent_iff_isComponent hO _).mp (L219.isTwoComponent_map_conj hK₀ t')
  have hcomm : K₀ ≤ centralizer ((K₀.map (MulAut.conj t').toMonoidHom : Subgroup _) : Set _) := by
    rcases LocalCores.distinct_components_commute hK₀c hK₁c with h | h
    · exact absurd h.symm hne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have ht'2 : orderOf t' = 2 := by rw [ht'def, Subgroup.orderOf_mk]; exact ht2
  have ht'sq : t' ^ 2 = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [ht'2] at this
  have hRJ := centralizerResidual_sup_eq_range K₀ ht'sq hcomm hK₀c.1.1
  rw [hRJ] at hLeq
  have hRq : CFSG.IsQuasisimple ↥(swapDiag K₀ t' hcomm).range :=
    isQuasisimple_range_swapDiag hcomm hK₀c.1
  have hJM : J ≤ centralizer ({w} : Set G) := hJ.1.trans inf_le_left
  let e : ↥J ≃* ↥(swapDiag K₀ t' hcomm).range :=
    (Subgroup.subgroupOfEquivOfLe hJM).symm.trans (MulEquiv.subgroupCongr hLeq)
  have hJq : CFSG.IsQuasisimple ↥J := LocalCores.isQuasisimple_of_mulEquiv e.symm hRq
  have hZJ : Open.fusionZStar ↥J = center ↥J :=
    fusionZStar_eq_center_of_involution hJq (y := ⟨w, hwJ⟩) ((Subgroup.orderOf_mk w hwJ).trans hw2)
  have hmJ' : Blueprint.LieModel (↥J ⧸ center ↥J) .POmegaPlus n 3 1 :=
    Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZJ) hmJ
  have hmR : Blueprint.LieModel (↥(swapDiag K₀ t' hcomm).range ⧸
      center ↥(swapDiag K₀ t' hcomm).range) .POmegaPlus n 3 1 :=
    lieModel_quotCenter_of_mulEquiv e hmJ'
  obtain ⟨eKR⟩ := nonempty_quotCenter_equiv_swapDiag hcomm hK₀c.1
  have hmK₀ : Blueprint.LieModel (↥K₀ ⧸ center ↥K₀) .POmegaPlus n 3 1 :=
    Blueprint.LieModel.of_mulEquiv eKR.symm hmR
  have hzJ : z ∈ (swapDiag K₀ t' hcomm).range := by
    have hzJ' : z ∈ J.subgroupOf (centralizer ({w} : Set G)) := hwJ
    rwa [hLeq] at hzJ'
  have hzc : z ∈ center ↥(centralizer ({w} : Set G)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  obtain ⟨ν, hνc, hνz⟩ := exists_center_swapDiag hcomm hK₀c.1 hzJ fun y _ =>
    Subgroup.mem_center_iff.mp hzc y
  have hz1 : z ≠ 1 := fun h => by
    have hw1 : w = 1 := congrArg Subtype.val h
    rw [hw1, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hν1 : ν ≠ 1 := fun h => hz1 (by rw [← hνz, h, map_one])
  have hνν : ν * ν = 1 := hC2 ↥K₀ hK₀c.1 n hn hmK₀ ν hνc
  have hν2 : orderOf ν = 2 := orderOf_eq_prime (by rw [sq]; exact hνν) hν1
  have hν₁2 : orderOf (((ν : ↥(centralizer ({w} : Set G))) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hν2
  have hν₂2 : orderOf (((MulAut.conj t' (ν : ↥(centralizer ({w} : Set G))) :
      ↥(centralizer ({w} : Set G))) : G)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_injective (MulAut.conj t').toMonoidHom (MulAut.conj t').injective
      (ν : ↥(centralizer ({w} : Set G)))).trans ((Subgroup.orderOf_coe ν).trans hν2)
  have hν₂K₁ : MulAut.conj t' (ν : ↥(centralizer ({w} : Set G))) ∈
      K₀.map (MulAut.conj t').toMonoidHom := ⟨ν, ν.2, rfl⟩
  have hνν₂ : (MulAut.conj t' (ν : ↥(centralizer ({w} : Set G)))) * ν =
      (ν : ↥(centralizer ({w} : Set G))) * MulAut.conj t' (ν : ↥(centralizer ({w} : Set G))) :=
    Subgroup.mem_centralizer_iff.mp (hcomm ν.2) _ hν₂K₁
  have hw : w = ((ν : ↥(centralizer ({w} : Set G))) : G) *
      ((MulAut.conj t' (ν : ↥(centralizer ({w} : Set G))) : ↥(centralizer ({w} : Set G))) : G) :=
    (congrArg Subtype.val (show (ν : ↥(centralizer ({w} : Set G))) *
      MulAut.conj t' (ν : ↥(centralizer ({w} : Set G))) = z from hνz)).symm
  have hA : IsComponentIn (K₀.map (centralizer ({w} : Set G)).subtype) (centralizer {w}) :=
    isComponentIn_map_subtype hK₀c
  have hB : IsComponentIn ((K₀.map (MulAut.conj t').toMonoidHom).map
      (centralizer ({w} : Set G)).subtype) (centralizer {w}) :=
    isComponentIn_map_subtype hK₁c
  have hAB : K₀.map (centralizer ({w} : Set G)).subtype ≤
      centralizer (((K₀.map (MulAut.conj t').toMonoidHom).map
        (centralizer ({w} : Set G)).subtype : Subgroup G) : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcomm hk) m hm)
  have hν₁A : ((ν : ↥(centralizer ({w} : Set G))) : G) ∈
      K₀.map (centralizer ({w} : Set G)).subtype := ⟨ν, ν.2, rfl⟩
  have hAν₁ : K₀.map (centralizer ({w} : Set G)).subtype ≤
      centralizer ({((ν : ↥(centralizer ({w} : Set G))) : G)} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg (fun x : ↥K₀ => (((x : ↥(centralizer ({w} : Set G))) : G)))
      (Subgroup.mem_center_iff.mp hνc ⟨k, hk⟩)
  have hν₂B : ((MulAut.conj t' (ν : ↥(centralizer ({w} : Set G))) :
      ↥(centralizer ({w} : Set G))) : G) ∈ (K₀.map (MulAut.conj t').toMonoidHom).map
        (centralizer ({w} : Set G)).subtype := ⟨_, hν₂K₁, rfl⟩
  have hmA : Blueprint.LieModel (↥(K₀.map (centralizer ({w} : Set G)).subtype) ⧸
      center ↥(K₀.map (centralizer ({w} : Set G)).subtype)) .POmegaPlus n 3 1 :=
    lieModel_quotCenter_of_mulEquiv
      (K₀.equivMapOfInjective _ (centralizer ({w} : Set G)).subtype_injective) hmK₀
  have hmB : Blueprint.LieModel (↥((K₀.map (MulAut.conj t').toMonoidHom).map
      (centralizer ({w} : Set G)).subtype) ⧸ center ↥((K₀.map (MulAut.conj t').toMonoidHom).map
        (centralizer ({w} : Set G)).subtype)) .POmegaPlus n 3 1 :=
    lieModel_quotCenter_of_mulEquiv
      ((K₀.equivMapOfInjective _ (MulAut.conj t').injective).trans
        ((K₀.map (MulAut.conj t').toMonoidHom).equivMapOfInjective _
          (centralizer ({w} : Set G)).subtype_injective)) hmK₀
  exact false_of_ambient hH hL hbr hKR hC3 hC4 hnab hK hcat hbal hν₁2 hν₂2
    (congrArg Subtype.val hνν₂.symm) hw hw2 hA hB hAB hν₁A hAν₁ hν₂B hn hmA hmB

theorem hardBranchBalanced (hH : Harris82Theorem1KProper) (hLB : CFSG.Open.LBalanceStatement)
    (hbr : Assembly.CatalogImp Blueprint.Catalog Assembly.InCatalog) (hKR : T1.KnownRowThree)
    (hC2 : POmegaPlusCentreExpTwo) (hC3 : LinUnitInvolutionComponents)
    (hC4 : POmegaPlusNotLinUnit) : HardBranchBalanced := by
  intro G _ _ _ hnab hK hcat hbal W hW2 hW4 J hJ n hn hmJ w hw hw1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hwJ, hwW⟩ := mem_inf.mp hw
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 w hwW) hw1
  obtain ⟨t, htW, htw⟩ : ∃ t ∈ W, t ∉ zpowers w := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show W ≤ zpowers w from fun x hx => h x hx)
    rw [hW4, Nat.card_zpowers, hw2] at hle
    omega
  obtain ⟨-, ht2, htM, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hwW hw1 htW htw
  have hJ' : IsTwoComponentIn J (centralizer {w} ⊓ centralizer {t}) := hCW ▸ hJ
  obtain ⟨K₀, hK₀, hKeq, hcases⟩ := T23.exists_pumpup ht2 htM hJ'
  rcases hcases with ⟨hfix, -⟩ | ⟨hne, hLeq⟩
  ·
    rw [hKeq, hfix, sup_idem]
    exact T23.isTwoComponentIn_map_subtype hK₀
  · exact (false_of_diag_balanced hH (CFSG.StandardType.ggLBalanceInput_of_milestone hLB) hbr
      hKR hC2 hC3 hC4 hnab hK hcat hbal hw2 ht2 htM hJ' hn hmJ hwJ hK₀ rfl hne hLeq).elim

end CFSG.OddStandard.HigherRank.F3
