module

public import CFSG.ClassicalInvolution.Asc77.AscT7K1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Std

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Y1

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem hs_of_cfg (hc : P23Cfg n Y R S t K' W u e g) :
    CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  exact ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
    hc.std.hne, hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)⟩

theorem comm_ut (hc : P23Cfg n Y R S t K' W u e g) : u * t = t * u := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hle : tightCore R ⊔ K' ≤ Subgroup.centralizer ({t} : Set Y) :=
    sup_le (le_centralizer_of_unique hz) (le_centralizer_of_unique hz')
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hc.data.hu)

theorem comm_gen (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ a ∈ ({u * e, u, t} : Set Y), ∀ b ∈ ({u * e, u, t} : Set Y), a * b = b * a := by
  have hd := hc.data
  have c1 : Commute u e := T7K.comm_e_of_mem_W hd hd.huW
  have c2 : Commute u t := comm_ut hc
  have c3 : Commute t e := T7K.comm_e_of_mem_W hd hd.hzW
  have c4 : Commute (u * e) u := Commute.mul_left (Commute.refl u) c1.symm
  have c5 : Commute (u * e) t := Commute.mul_left c2 c3.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (Commute.refl _).eq
  · exact c4.eq
  · exact c5.eq
  · exact c4.symm.eq
  · exact (Commute.refl _).eq
  · exact c2.eq
  · exact c5.symm.eq
  · exact c2.symm.eq
  · exact (Commute.refl _).eq

theorem B_isElemAbelian (hc : P23Cfg n Y R S t K' W u e g) :
    IsElemAbelian 2 (Subgroup.closure ({u * e, u, t} : Set Y)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hcomm := T7A.commutes_closure (comm_gen hc)
  have hue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hsq : ∀ a ∈ ({u * e, u, t} : Set Y), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · calc u * e * (u * e) = u * (e * u) * e := by group
        _ = u * (u * e) * e := by rw [← hue]
        _ = (u * u) * (e * e) := by group
        _ = 1 := by rw [hd.hu2, hd.he2]; group
    · exact hd.hu2
    · exact hz.sq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq (comm_gen hc) x hx

end Y1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
