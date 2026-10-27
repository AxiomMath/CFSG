module

public import CFSG.GF2Type.Aschbacher1976Full.WidthBounds
public import CFSG.GF2Type.Aschbacher1976Full.WidthStruct

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Card

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

section Bound

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem center_Fz_eq (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2) :
    center ↥(Fz z) = Z.subgroupOf (Fz z) := by
  ext x
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    refine Width.mem_Z_of_comm hD hz x.2 fun b hb => ?_
    have hbF : b ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_right hb
    exact (congrArg Subtype.val (hx ⟨b, hbF⟩)).symm
  · intro hx g
    exact Subtype.ext (Width.Z_comm_F hD hx g.2).symm

theorem center_Fz_card (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2) :
    IsCyclic ↥(center ↥(Fz z)) ∧ Nat.card ↥(center ↥(Fz z)) = 4 := by
  have hZF : Z ≤ Fz z := hD.sup_eq ▸ le_sup_left
  haveI := hD.cyc
  have e := Subgroup.subgroupOfEquivOfLe hZF
  rw [center_Fz_eq hD hz]
  exact ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans hD.card_Z⟩

theorem card_elemAbelian_le (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2) {U : Subgroup G}
    (hUF : U ≤ Fz z) (hU : CFSG.Open.IsElemAbelian 2 U) : Nat.card U ≤ 2 ^ (w + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Width.CData z (Fz z) :=
    { zF := hD.sup_eq ▸ Subgroup.mem_sup_left hD.mem_z
      zc := fun f hf => Width.Z_comm_F hD hD.mem_z hf
      z2 := Width.z_sq hz
      z1 := fun h => by simp [h] at hz
      comm := fun f hf g hg => Width.comm_F hD hz hf hg
      sq := fun f hf => Width.sq_F hD hz hf }
  have hcen := center_Fz_card hD hz
  exact (Width.bounds_F hF w (Width.card_Fz hD hz) Z
    (fun x => by rw [center_Fz_eq hD hz, Subgroup.mem_subgroupOf]) hcen.1 hcen.2).1 U hUF hU

end Bound

end CFSG.GF2Type.Aschbacher1976Full.HS.Card
