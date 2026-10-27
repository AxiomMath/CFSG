module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Notation54
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_central_unbalancing
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hconj : ∀ v ∈ L34UnbalancingSet L t S, ∃ l ∈ L, l⁻¹ * v * l ∈ S ∧
      ∀ s ∈ S, s * (l⁻¹ * v * l) = l⁻¹ * v * l * s) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) :
    ∃ u' ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u' = u' * s) ∧
      ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u'} : Set G)) := by
  obtain ⟨-, hLt, -⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, -, -, -, htS, -, -⟩ := hset'
  obtain ⟨l, hlL, hlS, hlc⟩ := hconj u hu
  obtain ⟨huS₀, hu2, hun⟩ := hu
  have hlN : l ∈ normalizer (oddIn L : Set G) :=
    normalizer_le_normalizer_oddIn L (le_normalizer hlL)
  have hCX : conjugate (oddIn L ⊓ centralizer ({u} : Set G)) l =
      oddIn L ⊓ centralizer ({l⁻¹ * u * l} : Set G) := by
    rw [show conjugate (oddIn L ⊓ centralizer ({u} : Set G)) l =
        conjugate (oddIn L) l ⊓ conjugate (centralizer ({u} : Set G)) l from
      Subgroup.map_inf_eq _ _ _ (MulAut.conj l⁻¹).injective, conjugate_eq_self hlN,
      conjugate_centralizer_singleton]
  have hcard : Nat.card ↥(oddIn L ⊓ centralizer ({l⁻¹ * u * l} : Set G)) =
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G)) := by
    rw [← hCX]
    exact card_map_of_injective (MulAut.conj l⁻¹).injective
  have hn' : ¬ oddIn L ⊓ centralizer ({l⁻¹ * u * l} : Set G) ≤
      oddIn (centralizer ({l⁻¹ * u * l} : Set G)) := by
    have hO' : oddIn (centralizer ({l⁻¹ * u * l} : Set G)) =
        conjugate (oddIn (centralizer ({u} : Set G))) l :=
      (UnbalancedCorr.conjugate_map_pPrimeCore_centralizer u l).symm
    rw [← hCX, hO']
    intro h
    exact hun ((Subgroup.map_le_map_iff_of_injective (MulAut.conj l⁻¹).injective).mp h)
  have htc : ∀ y ∈ S ⊓ L, t * y = y * t := fun y hy => (hZS y (mem_inf.mp hy).1).symm
  rw [sup_comm] at huS₀
  obtain ⟨i, h, hh, hu_eq⟩ := mem_zpowers_sup htc huS₀
  have hlt : Commute l t := mem_centralizer_singleton_iff.mp (hLt hlL)
  have hu'eq : l⁻¹ * u * l = t ^ i * (l⁻¹ * h * l) := by
    rw [hu_eq]
    have hc : Commute l⁻¹ (t ^ i) := (hlt.zpow_right i).inv_left
    calc l⁻¹ * (t ^ i * h) * l = (l⁻¹ * t ^ i) * h * l := by group
      _ = (t ^ i * l⁻¹) * h * l := by rw [hc.eq]
      _ = t ^ i * (l⁻¹ * h * l) := by group
  have hhl : l⁻¹ * h * l ∈ S ⊓ L := by
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (inv_mem hlL) (mem_inf.mp hh).2) hlL⟩
    have h1 : l⁻¹ * h * l = (t ^ i)⁻¹ * (l⁻¹ * u * l) := by rw [hu'eq]; group
    rw [h1]
    exact mul_mem (inv_mem (zpow_mem htS i)) hlS
  have hu'S₀ : l⁻¹ * u * l ∈ S ⊓ L ⊔ zpowers t := by
    rw [sup_comm, hu'eq]
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers t) i)) (mem_sup_right hhl)
  have hu'2 : orderOf (l⁻¹ * u * l) = 2 := by
    rw [show l⁻¹ * u * l = MulAut.conj l⁻¹ u by simp, MulEquiv.orderOf_eq, hu2]
  exact ⟨l⁻¹ * u * l, ⟨hu'S₀, hu'2, hn'⟩, hlc, fun v hv => (hmax v hv).trans hcard.ge⟩

end CFSG.ComponentClassification.GrSLit.GrS5
