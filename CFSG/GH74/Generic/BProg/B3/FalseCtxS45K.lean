module

public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.GLS.Classes
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.C3.Layer1.Th2Dih
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.Walter.W67.Section5.Lemma57
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.BProg.B3.FalseCtxS45K

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ComponentClassification Subgroup

section Abstract

variable {W Kt : Type} [Group W] [Finite W] [Group Kt] [Finite Kt]

theorem map_eq_derived_of_isPComponent (C : Subgroup Kt) (ρ : W →* Kt)
    (hρC : ∀ w, ρ w ∈ C) (hsurj : ∀ c ∈ C, ∃ w, ρ w = c) (hker : ¬ 2 ∣ Nat.card ρ.ker)
    (hS : IsSimpleGroup ↥⁅C, C⁆) {H : Subgroup W} (hH : IsPComponent 2 H) :
    H.map ρ = ⁅C, C⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ' : W →* ↥C := ρ.codRestrict C hρC with hρ'
  have hρ's : Function.Surjective ρ' := by
    rintro ⟨c, hc⟩
    obtain ⟨w, hw⟩ := hsurj c hc
    exact ⟨w, Subtype.ext hw⟩
  have hk' : ¬ 2 ∣ Nat.card ρ'.ker := by
    rwa [hρ', MonoidHom.ker_codRestrict]
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection ρ' hρ's hk'
  have hM : IsPComponent 2 (H.map ρ') := hbij.mapsTo hH
  set M : Subgroup ↥C := H.map ρ' with hMdef
  have hMperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hM)
  have hMsub : M.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hM
    exact h
  have hMne : M ≠ ⊥ := by
    intro h0
    obtain ⟨Kc, hKc, -, hmap, -⟩ := hM
    have h1 : Kc = ⊥ := by rw [← hmap, h0, Subgroup.map_bot]
    have hnt : Nontrivial ↥Kc := CFSG.LocalCores.isQuasisimple_nontrivial hKc.1
    exact (Subgroup.nontrivial_iff_ne_bot Kc).mp hnt h1
  set M₁ : Subgroup Kt := M.map C.subtype with hM₁
  have hM₁eq : M₁ = H.map ρ := by
    rw [hM₁, hMdef, Subgroup.map_map]
    congr 1
  have hM₁C : M₁ ≤ C := Subgroup.map_subtype_le M
  have hM₁le : M₁ ≤ ⁅C, C⁆ := by
    have h1 : ⁅M₁, M₁⁆ = M₁ := by rw [hM₁, ← Subgroup.map_commutator, hMperf]
    calc M₁ = ⁅M₁, M₁⁆ := h1.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hM₁C hM₁C
  have hSC : ⁅C, C⁆ ≤ C :=
    Subgroup.commutator_le.mpr fun g hg h hh => by
      simp only [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  have hsubC : (M₁.subgroupOf C).IsSubnormal := by
    have h1 : M₁.subgroupOf C = M := Subgroup.comap_map_eq_self_of_injective C.subtype_injective M
    rw [h1]
    exact hMsub
  have hsubS : (M₁.subgroupOf ⁅C, C⁆).IsSubnormal := by
    have h1 := B1.isSubnormal_subgroupOf_inf (S := ⁅C, C⁆) hsubC
    rwa [inf_of_le_left hM₁le, inf_of_le_right hSC] at h1
  rw [← hM₁eq]
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hS hsubS with h0 | h0
  · exfalso
    have h1 : M₁ = ⊥ := by
      have := (Subgroup.subgroupOf_eq_bot).1 h0
      rw [disjoint_iff, inf_of_le_left hM₁le] at this
      exact this
    apply hMne
    exact (Subgroup.map_eq_bot_iff_of_injective M C.subtype_injective).1 h1
  · exact le_antisymm hM₁le ((Subgroup.subgroupOf_eq_top).1 h0)

end Abstract

section Glevel

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev cent (K : Subgroup G) (e : G) (heK : e ∈ K) :
    Subgroup (↥K ⧸ pPrimeCore 2 ↥K) :=
  centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨e, heK⟩} : Set (↥K ⧸ pPrimeCore 2 ↥K))

theorem map_eq_derived {K : Subgroup G} {e : G} (heK : e ∈ K) (he2 : orderOf e = 2)
    (hS : IsSimpleGroup ↥⁅cent K e heK, cent K e heK⁆) {H : Subgroup G}
    (hH : IsPCompIn 2 (K ⊓ centralizer ({e} : Set G)) H) :
    (H.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) = ⁅cent K e heK, cent K e heK⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥K := pPrimeCore 2 ↥K with hN
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set ψ : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N with hψ
  set W : Subgroup G := K ⊓ centralizer ({e} : Set G) with hW
  have hWK : W ≤ K := inf_le_left
  set eK : ↥K := ⟨e, heK⟩ with heKdef
  have hordK : orderOf eK = 2 := by rw [heKdef, Subgroup.orderOf_mk]; exact he2
  set ρ : ↥W →* ↥K ⧸ N := ψ.comp (Subgroup.inclusion hWK) with hρ
  have hρC : ∀ w : ↥W, ρ w ∈ cent K e heK := by
    intro w
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw : (w : G) * e = e * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 w.2.2
    show ψ (Subgroup.inclusion hWK w) * ψ eK = ψ eK * ψ (Subgroup.inclusion hWK w)
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hw)
  have hsurj : ∀ c ∈ cent K e heK, ∃ w : ↥W, ρ w = c := by
    intro c hc
    have hy' : ∀ a ∈ zpowers eK, ψ a * c = c * ψ a := by
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hcy : Commute (ψ eK) c := (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
      rw [map_zpow]
      exact (Commute.zpow_left hcy k).eq
    obtain ⟨g, hgψ, hgc⟩ := B1.centralizer_quotient_of_pGroup N hNodd
      (B1.isPGroup_two_zpowers_of_orderOf hordK) hy'
    have hge : eK * g = g * eK := hgc _ (mem_zpowers _)
    have hgW : (g : G) ∈ W := ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val hge).symm⟩
    exact ⟨⟨g, hgW⟩, hgψ⟩
  have hker : ¬ 2 ∣ Nat.card ρ.ker :=
    B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hWK) (Subgroup.inclusion_injective hWK) N hNodd
  have hmain := map_eq_derived_of_isPComponent (cent K e heK) ρ hρC hsurj hker hS hH.2
  rw [← hmain]
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hkH : (k : G) ∈ H := Subgroup.mem_subgroupOf.mp hk
    exact ⟨⟨k, hH.1 hkH⟩, Subgroup.mem_subgroupOf.mpr hkH, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwH : (w : G) ∈ H := Subgroup.mem_subgroupOf.mp hw
    exact ⟨⟨w, hWK w.2⟩, Subgroup.mem_subgroupOf.mpr hwH, rfl⟩

end Glevel

end CFSG.GH74.Generic.BProg.B3.FalseCtxS45K
