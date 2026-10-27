module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.SubnormalClosure

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C311

open CFSG Subgroup

section Main


variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_le_center_of_catalog (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hS : IsSimpleGroup ↥(Open.genFittingFStar G))
    (hnab : ∃ a b : ↥(Open.genFittingFStar G), a * b ≠ b * a)
    (hcat : Blueprint.Catalog ↥(Open.genFittingFStar G)) {J : Subgroup G}
    (hJ : IsInvolutionTwoComponent J) : pPrimeCore 2 ↥J ≤ center ↥J := by
  classical
  obtain ⟨a, ha, hJa⟩ := hJ
  set S := Open.genFittingFStar G with hSdef
  have : S.Normal := ClassicalInvolution.genFittingFStar_normal G
  have : IsSimpleGroup ↥S := hS
  have hC : centralizer (S : Set G) = ⊥ :=
    CatalogueRelativeB.simple_self_centralizing_centralizer_eq_bot S hnab
      (Adapters.generalized_fitting_self_centralizing G)
  by_cases hO : CFSG.oddCore ↥(centralizer ({a} : Set G)) = ⊥
  ·
    have hO' : pPrimeCore 2 ↥(centralizer ({a} : Set G)) = ⊥ := by
      rw [← oddCore_eq_pPrimeCore_two]
      exact hO
    have h1 := pPrimeCore_eq_bot_of_isSubnormal hO' hJa.2.1
    have h2 := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hJa.1)
    rw [h1, Subgroup.map_bot] at h2
    rw [← h2]
    exact bot_le
  have hU := hU G hS hnab hcat ⟨a, ha, hO⟩
  have hout : Group.IsSolvable (OuterAutomorphisms.Outer ↥S) := hSch ↥S hnab hcat
  have : Group.IsPerfect ↥J := hJa.2.2.1
  have hJS : J ≤ S := le_of_isPerfect hC
  apply pPrimeCore_le_center_of_isQuasisimple hJa.2.2
  have hα2 : MulAut.conjNormal (H := S) a * MulAut.conjNormal (H := S) a = 1 := by
    rw [← map_mul, ← pow_two, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : MulAut.conjNormal (H := S) a ≠ 1 := by
    intro h1
    have haC : a ∈ centralizer (S : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h3 := congrArg (fun φ : MulAut S => ((φ ⟨x, hx⟩ : S) : G)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc x * a = a * x * a⁻¹ * a := by rw [h3]
        _ = a * x := by group
    rw [hC, mem_bot] at haC
    rw [haC, orderOf_one] at ha
    omega
  have hαo : orderOf (MulAut.conjNormal (H := S) a) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
  have hP2 : ∀ {X : Type} [Group X] {x : X}, orderOf x = 2 → IsPGroup 2 (zpowers x) :=
    fun hx => IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  rcases hU with hodd | ⟨n, -, hn7, ⟨θ⟩, -⟩ | ⟨hm | hHe, -⟩
  ·
    exact isQuasisimple_of_fixed hJS hJa fun L hL =>
      CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hnab hodd _ hα2 hα1 L hL
  ·
    have : IsSimpleGroup ↥(GeneralizedFitting.subgroup G) := hS
    exact isQuasisimple_of_bad ha hJa
      (CatalogueBAlternating.generalizedFitting_normalizer_badSubgroup_eq_bot hnab (Or.inr hn7)
        θ _ (hP2 ha))
  ·
    set H : Subgroup G := S ⊔ zpowers a with hH
    have haH : a ∈ H := mem_sup_right (mem_zpowers a)
    have hSH : S ≤ H := le_sup_left
    have : (S.subgroupOf H).Normal := Subgroup.normal_subgroupOf
    let eSH : ↥(S.subgroupOf H) ≃* ↥S := subgroupOfEquivOfLe hSH
    have : IsSimpleGroup ↥(S.subgroupOf H) := eSH.isSimpleGroup
    have hmH : Blueprint.LieModel ↥(S.subgroupOf H) .PSL 3 2 2 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eSH.symm hm
    have hidx : (S.subgroupOf H).index ≤ 2 := by
      have h1 : (S.subgroupOf H).index = S.relIndex (zpowers a) :=
        Subgroup.relIndex_sup_left (zpowers a) S
      rw [h1]
      have h2 : S.relIndex (zpowers a) ∣ Nat.card ↥(zpowers a) :=
        Subgroup.relIndex_dvd_card S (zpowers a)
      rw [Nat.card_zpowers, ha] at h2
      exact Nat.le_of_dvd (by norm_num) h2
    obtain ⟨-, hbadH⟩ := PSL3Four.index_two_local_B (S.subgroupOf H) hmH hidx
    have ha' : orderOf (⟨a, haH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
    have hT : zpowers (⟨a, haH⟩ : H) ≠ ⊥ := by
      intro h0
      rw [zpowers_eq_bot] at h0
      rw [h0, orderOf_one] at ha'
      omega
    have hq := isQuasisimple_of_bad ha' (isTwoComponentIn_subgroupOf haH (hJS.trans hSH) hJa)
      (hbadH _ hT (hP2 ha'))
    exact LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hJS.trans hSH)) hq
  ·
    exact isQuasisimple_of_fixed hJS hJa fun L hL =>
      Sporadic.HeldB.ctbh_all_involution_automorphism_fixed_p_components hHe _ hαo L hL

theorem pPrimeCore_le_center_of_harrisF (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) {p : ℕ}
    (hS : IsSimpleGroup ↥(Open.genFittingFStar G)) (hF : HarrisF p ↥(Open.genFittingFStar G))
    {J : Subgroup G} (hJ : IsInvolutionTwoComponent J) : pPrimeCore 2 ↥J ≤ center ↥J :=
  pPrimeCore_le_center_of_catalog hU hSch hS (nonabelian_of_harrisF hF) (catalog_of_harrisF hF)
    hJ

theorem harris311PSL2_of (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
      IsSimpleGroup ↥(Open.genFittingFStar G) → HarrisF p ↥(Open.genFittingFStar G) →
      ∀ J : Subgroup G, IsInvolutionTwoComponent J →
        (∃ p' f' : ℕ, Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p' f') →
          pPrimeCore 2 ↥J ≤ center ↥J :=
  fun _ _ _ _ _ _ hS hF _ hJ _ => pPrimeCore_le_center_of_harrisF hU hSch hS hF hJ

end Main

end CFSG.ComponentClassification.HarrisLit.C311
