module

public import CFSG.ClassicalInvolution.Asc77.AscExactDTwin
public import CFSG.ClassicalInvolution.Asc77.AscT7K1
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T7Z

open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem twin_commutes (hs : Hyp23Setting p f Ω K K' z) (hex : ExactMembers Ω) :
    Commutes K K' := by
  have hst := hs.stand
  have d := ExactD.TwinPair.of_twinSet hst.odd hst.five hst.hyp hst.mem hs.hz hs.hK' hs.hne.symm
  have h := d.comm_le
  rw [oddCoreOf_eq_bot_of_exact hex hst.mem, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem g_comm_e (hd : Hyp23bData Ω K K' W z u e g) : g * e = e * g :=
  T7K.comm_e hd (T7K.g_mem_normalizer hd)

theorem conjSub_le_centralizer_e (hd : Hyp23bData Ω K K' W z u e g) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({e} : Set G)) :
    conjSub g L ≤ Subgroup.centralizer ({e} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (g⁻¹ * x * g) * e = e * (g⁻¹ * x * g) := Subgroup.mem_centralizer_singleton_iff.mp
    (hL hx)
  have h2 := g_comm_e hd
  calc x * e = g * ((g⁻¹ * x * g) * e) * g⁻¹ := by
        have : g * ((g⁻¹ * x * g) * e) * g⁻¹ = x * (g * e * g⁻¹) := by group
        rw [this, h2]; group
    _ = g * (e * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = e * x := by
        have : g * (e * (g⁻¹ * x * g)) * g⁻¹ = (g * e * g⁻¹) * x := by group
        rw [this, h2]; group

theorem t_sq (hd : Hyp23bData Ω K K' W z u e g) (hs : Hyp23Setting p f Ω K K' z) :
    (u * e) * (u * e) = 1 := by
  rw [← hd.hgt]
  exact (hs.hz.conj g).sq

theorem u_eq_t_mul_e (hd : Hyp23bData Ω K K' W z u e g) : u = (u * e) * e := by
  have : e * e = 1 := hd.he2
  calc u = u * (e * e) := by rw [this, mul_one]
    _ = (u * e) * e := by group

theorem t_ne_z (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    u * e ≠ z := by
  intro h
  apply T7K.e_not_mem_sup hs hd
  have he : e = u * z := by
    calc e = u * (u * e) := by
          have := hd.hu2
          calc e = (u * u) * e := by rw [this, one_mul]
            _ = u * (u * e) := by group
      _ = u * z := by rw [h]
  rw [he]
  exact Subgroup.mul_mem _ hd.hu (Subgroup.mem_sup_left hs.hz.mem)

end T7Z

end CFSG.ClassicalInvolution.Asc77
