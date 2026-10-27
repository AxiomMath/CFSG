module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs
public import CFSG.GF2Type.Aschbacher1976Full.WidthStruct
public import CFSG.Quasithin.H13.L32NZ4Q8Q8
public import CFSG.Quasithin.EmptyFaithful.S14113bFStar

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem quasithinGenFitting_Hz (z : G) : CFSG.Open.quasithinGenFitting (Hz z) = Fz z := by
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype,
    ← CFSG.generalizedFitting_eq_componentClassification]
  rfl

theorem isZ4Q8Q8_Fz {z : G} (hz : orderOf z = 2) (hZ : IsZ4Star z 2) :
    CFSG.Quasithin.HSType.IsZ4Q8Q8 ↥(Fz z) := by
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ
  haveI := hD.cyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Z)
  have hgZ : (g : G) ∈ Z := g.2
  have hgF : (g : G) ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_left hgZ
  have hzF : z ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_left hD.mem_z
  have hordg : orderOf (g : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hD.card_Z]
  have hg4 : (g : G) ^ 4 = 1 := by
    simpa [hordg] using pow_orderOf_eq_one (g : G)
  have hg2 : (g : G) ^ 2 = z := by
    refine Width.involution_eq hD hz (Z.pow_mem hgZ 2) ?_ ?_
    · rw [← pow_mul]
      exact hg4
    · exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hordg]; norm_num)
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact Width.z_sq hz
  have hS : CFSG.Quasithin.H13.Q8Pow.CommPair z (Fz z) :=
    { z_mem := hzF
      z_ne := fun h => by simp [h] at hz
      z_sq := hzz
      z_comm := fun u hu => (Width.Z_comm_F hD hD.mem_z hu).symm
      comm := fun a ha b hb => Width.comm_F hD hz ha hb
      sq := fun u hu => by simpa only [pow_two] using Width.sq_F hD hz hu }
  refine CFSG.Quasithin.H13.Q8Pow.nonempty_mulEquiv_z4Q8Q8 hS hgF
    (by rw [← pow_two]; exact hg2) (fun u hu => Width.Z_comm_F hD hgZ hu) ?_
    ((Width.card_Fz hD hz).trans (by norm_num))
  intro u hu hcomm
  have huZ : u ∈ Z := Width.mem_Z_of_comm hD hz hu fun b hb =>
    hcomm b (hD.sup_eq ▸ Subgroup.mem_sup_right hb)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨u, huZ⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem hsOne_of_S5 {z : G} (hset : HSSetting G z) (hS5 : HSS5 z) :
    CFSG.Quasithin.HSType.HSOne z := by
  have hbr := quasithinGenFitting_Hz z
  refine ⟨?_, ?_⟩
  · rw [hbr]
    exact isZ4Q8Q8_Fz hset.1.2.2.1 hset.2
  · rw [hbr]
    exact hS5

end CFSG.GF2Type.Aschbacher1976Full.HS
