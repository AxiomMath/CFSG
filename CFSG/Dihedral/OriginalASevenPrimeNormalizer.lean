module

public import CFSG.Dihedral.OriginalPrimeNormalizerBasics
public import CFSG.Dihedral.OriginalCyclicKernel
public import CFSG.Dihedral.PrimeNormalizerQuotientAlternatives
public import CFSG.Dihedral.FourgroupActionTransport
public import CFSG.Dihedral.GorensteinWalter.ASevenFourgroupFullAction
public import CFSG.Dihedral.GorensteinWalter.ASevenCentralizerFourgroup
import all CFSG.Dihedral.BlueprintDefs
import Mathlib.Tactic
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate112
public import CFSG.Dihedral.OriginalPrimeStationarity
public import CFSG.Dihedral.OriginalProjectiveExclusion
public import CFSG.Dihedral.OriginalCosetSetup
public import CFSG.Dihedral.GorensteinWalter.ASevenFourgroupFullActionInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Free

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem isKleinFour_of_isFourGroup (V : Subgroup G) (hV : IsFourGroup V) : IsKleinFour V := by
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV.1]; decide)
  refine ⟨hV.1, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro v hv
  apply orderOf_eq_prime
  · exact Subtype.ext (hV.2 v v.property)
  · exact hv

omit [Finite G] in
theorem isFourGroup_of_isKleinFour (V : Subgroup G) (hV : IsKleinFour V) : IsFourGroup V := by
  refine ⟨hV.card_four, ?_⟩
  intro v hv
  have h := congrArg Subtype.val (hV.mul_self (⟨v, hv⟩ : V))
  change v * v = 1 at h
  simpa only [pow_two] using h

namespace OriginalData

variable (d : OriginalData G)

theorem prime_sylow_eq_R_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) : P = d.R := by
  have hR : d.R ≠ ⊥ := by
    intro h
    have hd := hp.2
    rw [h, Subgroup.card_bot] at hd
    exact hp.1.not_dvd_one hd
  have hRcard := d.R_card_of_aSeven_model hR e
  have hp3 : p = 3 := by
    have hd := hp.2
    rw [hRcard] at hd
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hp.1.ne_one
  exact isSylowIn_eq_of_card_prime p hp.1 P d.R hP (hRcard.trans hp3.symm)

theorem HP_eq_N_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    d.HP P = d.N := by
  rw [d.prime_sylow_eq_R_of_aSeven_model e p hp P hP]
  let : IsCyclic d.R := d.R_isCyclic_of_aSeven_model e
  change Subgroup.normalizer ((Subgroup.center d.R).map d.R.subtype : Set G) =
    Subgroup.normalizer (d.R : Set G)
  rw [Subgroup.center_eq_top, Subgroup.map_top, Subgroup.range_subtype]

theorem JP_eq_R_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    d.JP P = d.R := by
  have hR : d.R ≠ ⊥ := by
    intro h
    have hd := hp.2
    rw [h, Subgroup.card_bot] at hd
    exact hp.1.not_dvd_one hd
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  change oddCoreOf (d.HP P) = d.R
  rw [d.HP_eq_N_of_aSeven_model e p hp P hP]
  exact d.N_oddCore_of_aligned_aSeven_model hR f ht

theorem HP_quotient_card_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    Nat.card (d.HP P ⧸ Assembly.oddCore (d.HP P)) = 24 := by
  rw [d.HP_eq_N_of_aSeven_model e p hp P hP]
  have hR : d.R ≠ ⊥ := by
    intro h
    have hd := hp.2
    rw [h, Subgroup.card_bot] at hd
    exact hp.1.not_dvd_one hd
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  exact d.N_quotient_card_of_aligned_aSeven_model hR f ht

theorem prime_normalizer_fullAction_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R)
    (V : Subgroup G) (hV : IsFourGroup V) (hcent : P ≤ Subgroup.centralizer (V : Set G)) :
    FullAutomorphismImage (Subgroup.normalizer (P : Set G) ⊓
      Subgroup.normalizer (V : Set G)) V ∧ Cycles (d.HP P) V := by
  have hPeq := d.prime_sylow_eq_R_of_aSeven_model e p hp P hP
  have hR : d.R ≠ ⊥ := hPeq ▸ d.prime_sylow_ne_bot p hp P hP
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  have hPmap : P.map f.toMonoidHom = a7U := by
    rw [hPeq]
    exact d.R_map_eq_a7U hR f ht
  have hVmapped := isKleinFour_map_mulEquiv_cross V (isKleinFour_of_isFourGroup V hV) f
  have hVcent : V.map f.toMonoidHom ≤ Subgroup.centralizer (a7U : Set (alternatingGroup (Fin 7))) := by
    rw [← hPmap]
    exact centralizer_map_le_of_mulEquiv f P V (Subgroup.le_centralizer_iff.mp hcent)
  refine ⟨?_, ?_⟩
  · apply fullAutomorphismImage_normalizer_inf_of_map_equiv f P V
    rw [hPmap]
    exact a7U_fourgroup_fullAutomorphismImage _ hVmapped hVcent
  · have hcycle : Cycles (Subgroup.normalizer (P : Set G)) V := by
      apply cycles_normalizer_of_map_equiv f P V
      rw [hPmap]
      exact a7U_fourgroup_cycles _ hVmapped hVcent
    obtain ⟨x, hx, hxV, hmove⟩ := hcycle
    exact ⟨x, d.normalizer_le_HP P hx, hxV, hmove⟩

theorem exists_prime_fixed_fourgroup_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7))
    (p : ℕ) (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    ∃ V : Subgroup G, IsFourGroup V ∧ V ≤ (d.S : Subgroup G) ∧
      P ≤ Subgroup.centralizer (V : Set G) := by
  have hPeq := d.prime_sylow_eq_R_of_aSeven_model e p hp P hP
  have hR : d.R ≠ ⊥ := hPeq ▸ d.prime_sylow_ne_bot p hp P hP
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  have hf : Function.Surjective f.toMonoidHom := f.surjective
  let T := d.S.mapSurjective hf
  have hTC : (T : Subgroup (alternatingGroup (Fin 7))) ≤
      Subgroup.centralizer ({a7t} : Set (alternatingGroup (Fin 7))) := by
    dsimp only [T]
    rw [Sylow.coe_mapSurjective]
    rw [← ht, ← centralizer_singleton_map]
    exact Subgroup.map_mono (by simpa only [d.centralizer, t] using d.sylow_le_centralizer)
  have hVT := a7V_le_sylow_of_le_t_centralizer T hTC
  let V := a7V.map f.symm.toMonoidHom
  have hVS : V ≤ (d.S : Subgroup G) := by
    have h := Subgroup.map_mono (f := f.symm.toMonoidHom) hVT
    dsimp only [T] at h
    rw [Sylow.coe_mapSurjective,
      ← Subgroup.comap_equiv_eq_map_symm' f ((d.S : Subgroup G).map f.toMonoidHom),
      Subgroup.comap_map_eq_self_of_injective f.injective] at h
    exact h
  have hVK : IsKleinFour V := isKleinFour_map_mulEquiv_cross a7V
    aSeven_structure_fact_1_8_ii_centralizer.2.2.2 f.symm
  have hVcentU : a7V ≤ Subgroup.centralizer (a7U : Set (alternatingGroup (Fin 7))) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
    change u = 1 ∨ u = a7a ∨ u = a7a ^ 2 at hu
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;> decide
  have hVcent : V ≤ Subgroup.centralizer (d.R : Set G) := by
    have h := centralizer_map_le_of_mulEquiv f.symm a7U a7V hVcentU
    rw [← d.R_map_eq_a7U hR f ht,
      ← Subgroup.comap_equiv_eq_map_symm' f (d.R.map f.toMonoidHom),
      Subgroup.comap_map_eq_self_of_injective f.injective] at h
    exact h
  refine ⟨V, isFourGroup_of_isKleinFour V hVK, hVS, ?_⟩
  rw [hPeq]
  exact Subgroup.le_centralizer_iff.mp hVcent

end OriginalData

end CFSG.DihedralBlueprint
