module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05
public import CFSG.ClassicalInvolution.Asc77.AscT7L4

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem ne_conj_z {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J) {zJ : G}
    (hzJ : IsUniqueInvolution J zJ) {t : G} (htT : T ≤ Subgroup.centralizer ({t} : Set G))
    (ht : t ≠ zJ) (g : G) : g * z * g⁻¹ ≠ t := by
  intro hg
  have hΩ := C.hyp
  have hJ' : conjSub g K ∈ Ω := hΩ.conjInvariant g K C.mem
  have hzJ' : IsUniqueInvolution (conjSub g K) t := hg ▸ C.hzK.conj g
  by_cases hJJ : J = conjSub g K
  · subst hJJ
    exact ht (hzJ'.eq hzJ)
  · have hTR : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hT
    have h8 := hΩ.eight_le_of_mem_RSet hTR
    have hTN := hΩ.le_normalizer_of_le_centralizer hJ' hJ (Ne.symm hJJ) hzJ'
      hT.1 hT.2.1 (by omega) htT
    have hnbr : J ∈ omegaNbr Ω (conjSub g K) := ⟨hJ, hJJ, T, hTR, hT.1, hTN⟩
    have hperp : J ∈ KPerp Ω (conjSub g K) := Set.mem_insert_of_mem _ hnbr
    rw [T7L.kPerp_conj_pair hΩ.conjInvariant C.perp g] at hperp
    rcases hperp with h | h
    · exact hJJ h
    · have h2 : IsUniqueInvolution J (g * z * g⁻¹) := h ▸ C.hzK'.conj g
      exact ht (hg ▸ (h2.eq hzJ))

include C in
theorem le_centralizer_z : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := C.hzK.conj y
  have h2 : y * z * y⁻¹ = z := by
    rcases C.conjSub_K_mem hy with h | h
    · rw [h] at h1; exact (C.hzK.eq h1).symm
    · rw [h] at h1; exact (C.hzK'.eq h1).symm
  calc y * z = y * z * y⁻¹ * y := by group
    _ = z * y := by rw [h2]

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
