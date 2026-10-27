module

public import CFSG.LargeExtraspecial.S14W4DWInv
public import CFSG.LargeExtraspecial.S14C8Cases
public import CFSG.LargeExtraspecial.S14W4LocLeaf
public import CFSG.LargeExtraspecial.S14W4DWRes
public import CFSG.LargeExtraspecial.S14W4LocInst

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {c : Config}

namespace W4Hyp

theorem psl_of_cent [IsSimpleGroup G] (hD : DW.DempwolffLn2Input) (hNQ : NQIrredStmt)
    (hNQ6 : NQPlus6Stmt) (h : W4Hyp S g t c) (hp : c = .omegaPlus6)
    (hcent : ∀ k ∈ (Mbar0 S).map S.Mbar.subtype, k * t = t * k →
      ∃ r ∈ Rbar S g t, ∀ v ∈ Vt S g t, ((r⁻¹ * k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    Nonempty (↥(Mbar0 S) ≃* PSL(6, ZMod 2)) := by
  have : IsSimpleGroup ↥(Mbar0 S) := h.simple
  obtain ⟨W₁, W₂, h1, h2, h12, hc1, hc2, hall⟩ := h.lattice hNQ6 hp
  have hl : W4DW.Lat4 h.S₀ h.R₀ W₁ W₂ := ⟨h1, h2, h12, hc1, hc2, hall⟩
  have hc' : ∀ k : ↥(h.S₀.M), ∃ r : ↥(h.S₀.M), (r : ↥(Mbar0 S)) ∈ h.R₀ ∧
      h.π (r⁻¹ * k) = 1 := fun k =>
    (hcent (ι S k) (ι_mem_map S k) (h.mem_S₀_M.mp k.2)).elim fun _ hr =>
      h.exists_R₀_ker hr.1 hr.2
  have hsimp : IsSimpleGroup ((h.R₀.subgroupOf h.S₀.M).map h.π) := by
    rw [h.π_R₀]
    exact isSimpleGroup_RmodN_of_occurs h.occ
  have hcardR : Nat.card ((h.R₀.subgroupOf h.S₀.M).map h.π) = 20160 ∨
      Nat.card ((h.R₀.subgroupOf h.S₀.M).map h.π) = 25920 := by
    rw [h.πR_eq]
    exact O62.card_omegaGroup h.finrank_Vt h.qf_nondeg
  obtain ⟨H, hsurj⟩ := hl.hyp h.act h.card_Qt (h.lat hNQ hNQ6) hc' hsimp hcardR h.width_S₀
  obtain ⟨e⟩ := H.nonempty_centralizer_mulEquiv hsurj (h.exists_isRank2Inv_res H)
  exact hD.nonempty_mulEquiv_psl (w := 4) le_rfl ↥(Mbar0 S) h.S₀.z h.S₀.orderOf_z ⟨e⟩

end W4Hyp

end CFSG.LargeExtraspecial.S14
