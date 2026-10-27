module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Block
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.EvenSporadicStandard.Induction.ThmU
  (universal_rank_two_component_eq_of_commutator_eq_bot_of_ne_top)

theorem heldKDiagonalCentralStep_of_component
    (hKMc : HeldKDiagonalComponentStep) : HeldKDiagonalCentralStep := by
  intro X _ _ L hset a u M ha hLa hLc hu hMu hMp hne hfix hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHS, -, -, ⟨e⟩, -⟩ := id hset
  obtain ⟨hsimp, hnab, -, -, -, -, ⟨e₀⟩⟩ := id hHS
  haveI := hsimp
  set Cu := centralizer ({u} : Set X) with hCu
  set N := conjugate M a with hN
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hu2 : orderOf u = 2 := hu.2.1
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    norm_num at hu2
  have haCu : a ∈ Cu := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hMc : IsComponent (M.subgroupOf Cu) := HeUC.isComponent_of_central hMu hMp hc
  have hNc : IsComponent (N.subgroupOf Cu) := HeKP.isComponent_conjugate hMc haCu
  have hNu : N ≤ Cu := by
    intro x hx
    rw [hN, HeKP.mem_conjugate] at hx
    have h := mul_mem (mul_mem (inv_mem haCu) (hMu hx)) haCu
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h
  have hMN := HeKP.commute_of_components hMu hNu hMc hNc (Ne.symm hne)
  have hNM : ∀ x ∈ N, ∀ y ∈ M, x * y = y * x := fun x hx y hy => (hMN y hy x hx).symm
  have hMq : IsQuasisimple ↥M :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMu) hMc.1
  have hNq : IsQuasisimple ↥N :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hNu) hNc.1
  have haM : ∀ y ∈ M, a * y * a⁻¹ ∈ N := fun y hy => by
    rw [hN, HeKP.mem_conjugate,
      show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, haa]
    simpa using hy
  have haN : ∀ x ∈ N, a * x * a⁻¹ ∈ M := fun x hx => HeKP.mem_conjugate.mp hx
  set K := gsFixedLayer L u with hKdef
  have hKL : K ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hKau : K ≤ centralizer ({a} : Set X) ⊓ Cu :=
    le_inf (hKL.trans hLa) ((gsFixedLayer_le_inf L u).trans inf_le_right)
  obtain ⟨B₈, hBK, hBe, hB8, V, hVB, hV4, hVZ⟩ := HeDE.exists_eight_le_center hLa e₀ hu.1 huu
    hu1 hKL hKau (HeDG.isPComponent_gsFixedLayer_inf e hLa hLc hu)
  have hfix' : gsFixedLayer (N ⊔ M) a = K := by rw [sup_comm]; exact hfix
  obtain ⟨E, hEe, hE8, hEM, -, -⟩ := HeDG.exists_elem_eight haa hNM haN haM hNq
    (by rw [hfix']; exact hBK) hBe hB8 hVB hV4 (by rw [hfix']; exact hVZ)
  have hrank : 3 ≤ pRank 2 ↥M := three_le_pRank_of_le hEe hE8 hEM
  have hMq' : CFSG.Assembly.IsQuasisimple M :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥M).2 hMq
  have hrank2 : 2 ≤ CFSG.Assembly.pRank 2 M := by
    rw [← CFSG.SectionRank.pRank_coe_eq_assemblyPRank 2 M]
    omega
  have hJ : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent M := by
    intro t ht ht2
    have hMt : M ≤ centralizer ({t} : Set X) := by
      intro m hm
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 ht) m hm
    have hp := hKMc X L hset a u M ha hLa hLc hu hMu hMp hne hfix hc t ht2 hMt
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hMt).2
      (HeUC.isComponent_of_central hMt hp hc)
  have hNfs : CFSG.EvenSporadicStandard.Induction.FStarSimple (⊤ : Subgroup X) :=
    CFSG.EvenSporadicStandard.Induction.fStarSimple_top X hnab
  have heven : Even (Nat.card M) :=
    CFSG.LocalAnalysis.ComponentInitial.even_card_of_two_le_pRank hrank2
  have huCent : u ∈ centralizer (M : Set X) := by
    rw [mem_centralizer_iff]
    intro m hm
    exact mem_centralizer_singleton_iff.mp (hMu hm)
  have hCeven : Even (Nat.card (centralizer (M : Set X))) := by
    refine even_iff_two_dvd.2 ?_
    have h3 := orderOf_dvd_natCard (⟨u, huCent⟩ : centralizer (M : Set X))
    have h4 : orderOf (⟨u, huCent⟩ : centralizer (M : Set X)) = 2 := by
      rw [Subgroup.orderOf_mk, hu.2.1]
    rwa [h4] at h3
  have hH := CFSG.EvenSporadicStandard.Induction.ThmU.normalizer_blockGroup_ne_top_of_fStarSimple
    hNfs hMq' hJ heven le_top hCeven
  have hc_eq : CFSG.LocalAnalysis.ComponentInitial.conjSub a⁻¹ M = conjugate M a := rfl
  have hbot : ⁅M, CFSG.LocalAnalysis.ComponentInitial.conjSub a⁻¹ M⁆ = ⊥ := by
    rw [hc_eq, commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (hMN x hx y hy).symm
  have hEq :=
    universal_rank_two_component_eq_of_commutator_eq_bot_of_ne_top
      hMq' hrank2 hJ hH a⁻¹ hbot
  rw [hc_eq] at hEq
  exact hne hEq

end CFSG.ComponentClassification.GrSLit
