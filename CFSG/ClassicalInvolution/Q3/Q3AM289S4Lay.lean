module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Glue
public import CFSG.ClassicalInvolution.Q3.Q3AM289Nbr
public import CFSG.ClassicalInvolution.Q3.Q3AM289Pair
public import CFSG.ClassicalInvolution.Q3.Q3AMTriT00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Lay

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerFam_conjInvariant [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t) :
    ConjInvariant (layerFam Ω K z) := by
  classical
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  intro n A hA
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective
    (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) n
  obtain ⟨N, hN, rfl⟩ := exists_of_mem_layerFam hA
  have hyY : (y' : G) ∈ nbrLayer Ω K z := y'.2
  have hyC : (y' : G) ∈ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z hyY
  have hyz : (y' : G) * z * (y' : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [this]
    group
  have hyK : conjSub (y' : G) K = K := mem_normalizer_iff_conjSub_eq.mp (hNC ▸ hyC)
  have hN' : conjSub (y' : G) N ∈ omegaNbr Ω K := conjSub_mem_omegaNbr_of_conjSub_eq hΩ hyK hN
  have hcore : exactCore3 z (conjSub (y' : G) N) = conjSub (y' : G) (exactCore3 z N) := by
    have := exactCore3_conjSub (y' : G) z N
    rwa [hyz] at this
  have himg : modOddIn (nbrLayer Ω K z) (exactCore3 z (conjSub (y' : G) N)) =
      conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) y')
        (modOddIn (nbrLayer Ω K z) (exactCore3 z N)) := by
    rw [hcore]
    exact modOddIn_conj hyY
  rw [← himg]
  exact modOddIn_mem_layerFam hN'

theorem isUniqueInvolution_layerImage [IsSimpleGroup G]
    (h : BadStd8 Ω K J S R T W z t) {N : Subgroup G} (hN : N ∈ omegaNbr Ω K) {r : G}
    (hr : IsUniqueInvolution N r) :
    ∃ hrY : r ∈ nbrLayer Ω K z, IsUniqueInvolution (layerImage Ω K z N)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨r, hrY⟩) := by
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  have hzr : z * r = r * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ h.std.hz hN hr
  have hrE : r ∈ exactCore3 z N :=
    ⟨hr.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzr.symm⟩
  have hrY : r ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hN hrE
  exact ⟨hrY, isUniqueInvolution_modOddIn (exactCore3_le_left z N) hr hrE hrY⟩

theorem exists_nbr_of_image_involution [IsSimpleGroup G]
    (h : BadStd8 Ω K J S R T W z t) {r : G} (hrY : r ∈ nbrLayer Ω K z) (hr2 : r * r = 1)
    {C : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))}
    (hC : C ∈ layerFam Ω K z)
    (hrC : IsUniqueInvolution C
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨r, hrY⟩)) :
    ∃ N₂ ∈ omegaNbr Ω K, IsUniqueInvolution N₂ r := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  obtain ⟨N₀, hN₀, rfl⟩ := exists_of_mem_layerFam hC
  obtain ⟨r₀, hr₀⟩ := hΩ.exists_uniqueInvolution hN₀.1
  obtain ⟨hr₀Y, hu₀⟩ := isUniqueInvolution_layerImage h hN₀ hr₀
  have heq := hu₀.eq hrC
  have hYC : nbrLayer Ω K z ≤ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z
  have hzr₀ : z * r₀ = r₀ * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hYC hr₀Y)).symm
  have hzr : z * r = r * z := (Subgroup.mem_centralizer_singleton_iff.mp (hYC hrY)).symm
  have hzX : ∀ x ∈ nbrLayer Ω K z, ⁅x, z⁆ ∈ oddCoreOf (nbrLayer Ω K z) := by
    intro x hx
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hYC hx)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hxz]
    exact (oddCoreOf _).one_mem
  obtain ⟨y, hyY, hyz, hyr⟩ := exists_conj_lift_involutions'
    (h.centralizer_le_normalizer_nbrLayer hstd.stand.mem hstd.hz)
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hstd.hz.sq hzX hr₀Y hrY hr₀.sq hr2
    hzr₀ hzr
    ⟨1, by rw [one_mul, inv_one, mul_one]; exact heq⟩
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := hYC hyY
  have hyK : conjSub y K = K := mem_normalizer_iff_conjSub_eq.mp (hNC ▸ hyC)
  refine ⟨conjSub y N₀, conjSub_mem_omegaNbr_of_conjSub_eq hΩ hyK hN₀, ?_⟩
  have := hr₀.conj y
  rwa [hyr] at this

end Lay

end CFSG.ClassicalInvolution.Q3.Q3AM
