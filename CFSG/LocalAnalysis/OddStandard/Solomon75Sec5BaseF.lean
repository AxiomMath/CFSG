module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Core

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

namespace Sec5Data

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem K0_le_centralizer_Z (h : Sec5Data X n z Z S) :
    K0 X n (normalizer (Z : Set X)) ≤ centralizer (Z : Set X) := by
  rw [K0_eq_sSup_sec5Comp]
  refine sSup_le fun A hA => ?_
  obtain ⟨⟨u, hu⟩, -⟩ := hA
  exact le_centralizer_of_isPCompIn_of_normal_pgroup hu.2.2.1 (Subgroup.le_normalizer)
    le_rfl h.isPGroup_Z

theorem Z_le_center_K0 (h : Sec5Data X n z Z S) {x : X} (hx : x ∈ Z) {k : X}
    (hk : k ∈ K0 X n (normalizer (Z : Set X))) : x * k = k * x :=
  Subgroup.mem_centralizer_iff.1 (h.K0_le_centralizer_Z hk) x hx

theorem Z_comm (h : Sec5Data X n z Z S) {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) : x * y = y * x :=
  h.Z_le_center_K0 hx (h.Z_le_K0 hy)

theorem comm_mem_pPrimeCoreOf (h : Sec5Data X n z Z S) {u : X} (hu : u ∈ Z) :
    ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, u⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X))) := fun k hk => by
  have : ⁅k, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (h.Z_le_center_K0 hu hk).symm
  rw [this]
  exact one_mem _

theorem cen_eq_odd_sup (h : Sec5Data X n z Z S) {u : X} (hu : u ∈ Z) (hu2 : orderOf u = 2) :
    centralizer ({u} : Set X) = oddCoreOf (centralizer ({u} : Set X)) ⊔
      (normalizer (Z : Set X) ⊓ centralizer ({u} : Set X)) :=
  h.l52.b u (Subgroup.le_normalizer hu) hu2 (h.comm_mem_pPrimeCoreOf hu)

end Sec5Data

end CFSG.OddStandard.Solomon75
