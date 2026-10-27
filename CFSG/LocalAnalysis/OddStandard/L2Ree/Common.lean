module

public import CFSG.LocalAnalysis.OddStandard.Glue
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitReduction

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem isComponent_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    L ≤ centralizer ({t} : Set G) ∧
      IsComponent (L.subgroupOf (centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLT, hnorm, -, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL ht ht2
  refine ⟨hLT, ?_⟩
  set C := centralizer ({t} : Set G) with hC
  have e : (L.subgroupOf C) ≃* L := Subgroup.subgroupOfEquivOfLe hLT
  have hq : IsQuasisimple (L.subgroupOf C) :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      (ComponentClassification.Components.quasisimple_of_equiv e hL.1)
  exact ⟨hq, hnorm.isSubnormal⟩

theorem nonempty_quotient_center_subgroupOf {G : Type*} [Group G] {C L : Subgroup G}
    (hLC : L ≤ C) :
    Nonempty (↥(L.subgroupOf C) ⧸ center ↥(L.subgroupOf C) ≃* ↥L ⧸ center ↥L) :=
  let e : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem config_of_standard_psl_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hev : 2 ∣ Nat.card L) {p f : ℕ} (hp2 : p ≠ 2)
    (hodd : Odd (Nat.card (center L))) (hm : LieModel (L ⧸ center L) .PSL 2 p f)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) :
    ComponentClassification.HarrisLit.Config t L p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hL.1
  have hpc : pPrimeCore 2 L = center L := pPrimeCore_eq_center_of_odd_center hq hodd hev
  obtain ⟨hLt, hcomp⟩ := isPComponent_two_of_standard hL ht ht2 hev
  have hmBar : LieModel (ComponentClassification.HarrisLit.Bar L) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpc.symm) hm
  obtain ⟨hp, hf, -, -, h3⟩ := hm.admissible
  have hpodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h3p : 3 ≤ p ^ f := by
    have := hp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have h5 : 5 ≤ p ^ f := by
    have h3' : p ^ f ≠ 3 := fun h => h3 (by rw [h])
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hcycK := isCyclic_sylow_coreActionKernel hq.1 hpc.le S hS
  exact ⟨ht2, hLt, hcomp, hp, hp2, hf, h5, hmBar,
    fun P => ComponentClassification.HarrisLit.isCyclic_sylow_of_le inf_le_right hcycK P⟩

theorem orderOf_mulAut_conj_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {t : S} (ht : orderOf t = 2) :
    orderOf (MulAut.conj t : MulAut S) = 2 :=
  (orderOf_injective _ (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna)
    t).trans ht

theorem exists_fixed_component_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    ∃ D : Subgroup ↥(fixedSubgroup (MulAut.conj t)), IsComponent D ∧
      Nonempty (↥D ⧸ center ↥D ≃* ↥L ⧸ center ↥L) := by
  obtain ⟨hLt, hcomp⟩ := isComponent_of_standard hL ht ht2
  have hfix : fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set G) :=
    AltStdSec.lookup_fixedSubgroup_conj t
  let φ : ↥(centralizer ({t} : Set G)) ≃* ↥(fixedSubgroup (MulAut.conj t)) :=
    MulEquiv.subgroupCongr hfix.symm
  let e1 := (L.subgroupOf (centralizer ({t} : Set G))).equivMapOfInjective φ.toMonoidHom
    φ.injective
  obtain ⟨e2⟩ := nonempty_quotient_center_subgroupOf hLt
  exact ⟨(L.subgroupOf (centralizer ({t} : Set G))).map φ.toMonoidHom,
    LocalCores.isComponent_map_mulEquiv φ hcomp,
    ⟨(QuotientGroup.congr _ _ e1.symm (Subgroup.map_center_eq e1.symm)).trans e2⟩⟩

end CFSG.OddStandard.L2Ree
