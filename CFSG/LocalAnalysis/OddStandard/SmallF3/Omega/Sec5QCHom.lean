module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem sec5qc_ker_conj {φ : ↥L →* omegaGroup hQ} (hker : φ.ker = CFSG.oddCore ↥L) {x : G}
    (hx : x ∈ normalizer (L : Set G)) {l : ↥L} (hl : sec5cdPhi φ l = 1) :
    sec5cdPhi φ (L.normalizerMonoidHom ⟨x, hx⟩ l) = 1 := by
  have hl1 : φ l = 1 := Subtype.ext (by simpa [sec5cdPhi_apply] using hl)
  have hlk : l ∈ CFSG.oddCore ↥L := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hl1
  have hlO : (l : G) ∈ oddCoreIn L := by
    rw [oddCoreIn, CFSG.inSubgroup]
    exact Subgroup.mem_map_of_mem L.subtype hlk
  have hconj : x * (l : G) * x⁻¹ ∈ oddCoreIn L := conj_mem_oddCoreIn hx hlO
  have hcoe : ((L.normalizerMonoidHom ⟨x, hx⟩ l : ↥L) : G) = x * (l : G) * x⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ l
  have hmem : L.normalizerMonoidHom ⟨x, hx⟩ l ∈ CFSG.oddCore ↥L := by
    rw [oddCoreIn, CFSG.inSubgroup] at hconj
    rw [← hcoe] at hconj
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp hconj
  have hone : φ (L.normalizerMonoidHom ⟨x, hx⟩ l) = 1 := by
    rw [← hker] at hmem
    exact MonoidHom.mem_ker.mp hmem
  simpa [sec5cdPhi_apply] using congrArg Subtype.val hone

theorem sec5qc_comm_mem_oddCoreIn {φ : ↥L →* omegaGroup hQ} (hker : φ.ker = CFSG.oddCore ↥L)
    {x : G} (hx : x ∈ normalizer (L : Set G)) {l : ↥L}
    (h : sec5cdPhi φ (L.normalizerMonoidHom ⟨x, hx⟩ l) = sec5cdPhi φ l) :
    x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ oddCoreIn L := by
  have hφ : φ (L.normalizerMonoidHom ⟨x, hx⟩ l) = φ l :=
    Subtype.ext (by simpa [sec5cdPhi_apply] using h)
  have h1 : φ (L.normalizerMonoidHom ⟨x, hx⟩ l * l⁻¹) = 1 := by
    rw [map_mul, map_inv, hφ, mul_inv_cancel]
  have hmem : (L.normalizerMonoidHom ⟨x, hx⟩ l * l⁻¹ : ↥L) ∈ CFSG.oddCore ↥L := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr h1
  have hcoe : ((L.normalizerMonoidHom ⟨x, hx⟩ l * l⁻¹ : ↥L) : G) =
      x * (l : G) * x⁻¹ * (l : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ l]
  show x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ oddCoreIn L
  rw [← hcoe, oddCoreIn, CFSG.inSubgroup]
  exact Subgroup.mem_map_of_mem L.subtype hmem

theorem sec5qc_twoRes_lift {Δ : Type*} [Group Δ] {z : G} (hzL : z ∈ L) (f f' : ↥L →* Δ)
    (h : ∀ g : ↥L, Odd (orderOf g) → g * ⟨z, hzL⟩ = ⟨z, hzL⟩ * g → f' g = f g) :
    ∀ n ∈ twoRes (L ⊓ centralizer ({z} : Set G)), ∃ l : ↥L, (l : G) = n ∧ f' l = f l := by
  intro n hn
  have hle : twoRes (L ⊓ centralizer ({z} : Set G)) ≤
      (MonoidHom.eqLocus f f').map L.subtype := by
    rw [twoRes]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hodd⟩
    obtain ⟨hgL, hgz⟩ := Subgroup.mem_inf.mp hg
    have hcomm : (⟨g, hgL⟩ : ↥L) * ⟨z, hzL⟩ = ⟨z, hzL⟩ * ⟨g, hgL⟩ := by
      apply Subtype.ext
      simpa using Subgroup.mem_centralizer_singleton_iff.mp hgz
    have hoddL : Odd (orderOf (⟨g, hgL⟩ : ↥L)) := by
      rw [← Subgroup.orderOf_coe (⟨g, hgL⟩ : ↥L)]
      simpa using hodd
    have hgen : (⟨g, hgL⟩ : ↥L) ∈ MonoidHom.eqLocus f f' := by
      change f (⟨g, hgL⟩ : ↥L) = f' ⟨g, hgL⟩
      exact (h ⟨g, hgL⟩ hoddL hcomm).symm
    simpa using Subgroup.mem_map_of_mem L.subtype hgen
  obtain ⟨l, hl, hln⟩ := Subgroup.mem_map.mp (hle hn)
  change f l = f' l at hl
  exact ⟨l, hln, hl.symm⟩

end CFSG.OddStandard.SmallF3.Omega
