module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPfLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.TL3T1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section E4

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem centralizes_of_map (c : CentQuotGen Φ N) {L : Subgroup G} (hL : L ∈ Φ) {a : G}
    (hLc : L.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N a} : Set (G ⧸ N))) :
    L ≤ Subgroup.centralizer ({a} : Set G) := by
  have h1 : QuotientGroup.mk' N a ∈ Subgroup.centralizer
      ((L.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp (hLc hy) (QuotientGroup.mk' N a) rfl
    exact this.symm
  have h2 : a ∈ Subgroup.normalizer (L : Set G) :=
    c.normalizer_of_map L hL a (Subgroup.centralizer_le_normalizer _ h1)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have h3 : a * x * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp h2 x).mp hx
  have h4 : QuotientGroup.mk' N (a * x * a⁻¹) = QuotientGroup.mk' N x := by
    have := Subgroup.mem_centralizer_iff.mp (hLc (Subgroup.mem_map_of_mem _ hx))
      (QuotientGroup.mk' N a) rfl
    rw [map_mul, map_mul, map_inv, this, mul_inv_cancel_right]
  have h5 : x⁻¹ * (a * x * a⁻¹) ∈ L ⊓ N := by
    refine ⟨L.mul_mem (L.inv_mem hx) h3, ?_⟩
    have h6 : QuotientGroup.mk' N (x⁻¹ * (a * x * a⁻¹)) = 1 := by
      rw [map_mul, map_inv, h4, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h6
  rw [c.meet L hL, Subgroup.mem_bot] at h5
  have h7 : a * x * a⁻¹ = x := (inv_mul_eq_one.mp h5).symm
  calc a * x = (a * x * a⁻¹) * a := by group
    _ = x * a := by rw [h7]

end E4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
