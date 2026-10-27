module

public import CFSG.ClassicalInvolution.Q3.TL3DichThmA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  {T : Sylow 2 G}

theorem TightSylowStd.inf_core_eq (h : TightSylowStd R S t T) :
    (T : Subgroup G) ⊓ tightCore R = (S : Subgroup R).map R.subtype := by
  have hsyl : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := h.datum.sylow_core
  rw [inf_comm]
  exact hsyl.2.2 _ inf_le_left (T.isPGroup'.to_le inf_le_right) (le_inf hsyl.1 h.hST)

theorem TightSylowStd.comm_of_mem_normalizer_inf_core (h : TightSylowStd R S t T) {n : G}
    (hn : n ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ tightCore R : Subgroup G) : Set G)) :
    n * t = t * n := by
  have htI : t ∈ (T : Subgroup G) ⊓ tightCore R := ⟨h.hST h.datum.mem, h.isUniqueInvolution.mem⟩
  have h1 : n * t * n⁻¹ ∈ (T : Subgroup G) ⊓ tightCore R :=
    (Subgroup.mem_normalizer_iff.mp hn t).mp htI
  have h2 : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    rw [show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, t_mul_t h.datum]
    group
  rcases h.isUniqueInvolution.unique _ h1.2 h2 with h3 | h3
  · exfalso
    apply h.isUniqueInvolution.ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h3]; group
  · calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h3]

end CFSG.ClassicalInvolution.Q3
