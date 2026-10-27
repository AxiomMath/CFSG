module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporWit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporW

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf

theorem isComponentOf_map_subtype {M : Type*} [Group M] {K : Subgroup M} {B : Subgroup ↥K}
    (hB : IsComponent B) : Assembly.IsComponentOf (B.map K.subtype) K := by
  refine (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (Subgroup.map_subtype_le B)).mpr ?_
  have h : (B.map K.subtype).subgroupOf K = B :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective B
  rw [h]
  exact hB

theorem false_of_inner_class
    {X : Type*} [Group X] {L : Subgroup X} (hcomp : IsComponent L) (hL60 : Nat.card L = 60)
    {τ : Equiv.Perm (Fin 3850)} (hτP : τ ∈ hsP) (hτ : orderOf τ = 2)
    (E : X ≃* ↥(hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))))) : False := by
  have hB := LocalCores.isComponent_map_mulEquiv E hcomp
  have hB' := isComponentOf_map_subtype hB
  obtain ⟨-, -, h360⟩ := hsP_local_components hτP hτ hB'
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Subgroup.card_map_of_injective E.injective, hL60] at h360
  omega

theorem fiveSpor_HS :
    FiveSporClauseFor .HS := by
  intro S _ _ _ hna ⟨e⟩ σ P h hex ⟨eP⟩
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have eP' : Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hex.symm).trans eP⟩
  let θ : S ≃* hsP := e.trans hsPermEquiv
  obtain ⟨eR, heR, -⟩ := hs_full_automorphism_model
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, ⟨E⟩⟩ := exists_fixed_equiv eR heR hcover θ hσσ hσ1
  have hrowr := hrows r hr
  have hcardC : Nat.card (fixedSubgroup σ) = r.centOrder := by
    rw [Nat.card_congr E.toEquiv]
    exact hrowr.2.2.2.2.1
  have hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥ :=
    oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_HS hna e) hσ2
  obtain ⟨hcomp, ⟨eL⟩⟩ := exact_component_of_oddCore h hcore hex
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hL60 : Nat.card L = 60 := by
    rw [Nat.card_congr (eL.trans eP).toEquiv]
    exact Even.card_alt_five (MulEquiv.refl _)
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h0 | h1 | h2 | h3
  ·
    have hout : r.outer = false := by rw [h0]
    refine false_of_inner_class hcomp hL60 (τ := tp 3850 r.rep) ?_ hrowr.2.1 E
    by_contra hn
    have := hrowr.2.2.1.2 hn
    rw [hout] at this
    exact Bool.false_ne_true this
  ·
    have hout : r.outer = false := by rw [h1]
    refine false_of_inner_class hcomp hL60 (τ := tp 3850 r.rep) ?_ hrowr.2.1 E
    by_contra hn
    have := hrowr.2.2.1.2 hn
    rw [hout] at this
    exact Bool.false_ne_true this
  ·
    have hrep : r.rep = hsCentTbl 21 := by rw [h2]
    have hO : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) =
        QuasithinUnique.Id2519.HSAut.outerC := by
      rw [hrep]
      rfl
    let E' : ↥(fixedSubgroup σ) ≃* ↥QuasithinUnique.Id2519.HSAut.outerC :=
      E.trans (MulEquiv.subgroupCongr hO)
    have hB := LocalCores.isComponent_map_mulEquiv E' hcomp
    have eB : ↥(L.map E'.toMonoidHom) ≃* alternatingGroup (Fin 5) :=
      (L.equivMapOfInjective _ E'.injective).symm.trans (eL.trans eP)
    have : IsSimpleGroup ↥(commutator ↥QuasithinUnique.Id2519.HSAut.outerC) :=
      QuasithinUnique.Id2519.HSAut.commutator_simple'
    have hBle := QuasithinUnique.Id2519.le_commutator_of_isQuasisimple hB.1
    have htop := QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup
      (CFSG.LocalCores.component_overgroup hB hBle)
    have hBeq : L.map E'.toMonoidHom = commutator ↥QuasithinUnique.Id2519.HSAut.outerC :=
      le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
    have hc := Even.card_alt_five eB
    rw [hBeq, QuasithinUnique.Id2519.HSAut.card_commutator'] at hc
    omega
  ·
    have h1920 : r.centOrder = 1920 := by rw [h3]
    have hrep : r.rep = hsCentTbl 34 := by rw [h3]
    obtain ⟨x, hx, hx5, y, hy, hxy⟩ := hs_witness34
    rw [← hrep] at hx hy
    exact false_of_five_witness_of_equiv h.2.1 h.2.2.1 eP' (k := 5)
      (by rw [hcardC, h1920]; norm_num) E hx hy hx5 hxy

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
