module

import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8UE
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZO2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7N0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section ZDataAE5


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_zdata_of_ae5 (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e) (hA5 : SecAE R u 5)
    (hA6 : SecAE R e 6) :
    ∃ Z : Subgroup Y, P23ZData t u e Z := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have huC : u ∈ C := hWt hd.huW
  have ht2 : t * t = 1 := (Inner.isUniqueInvolution_core hC.datum).sq
  obtain ⟨-, -, -, -, -, -, -, heA, heB, b₁, b', hub, hb₁, hb', -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm := p23_twin_perm hc hCdef
  have hPhi := p23E8PhiAE_of_comm p23E8UEComm_proved hcit hP Y R S t K' W u e g hc hno hA5 hA6
  have hmemA : ∀ γ : ↥C ⧸ classicalInvolutionOddCore ↥C,
      γ * F7I.piC C ⟨e, heC⟩ * γ⁻¹ ∈ p23ABar t 1 e := by
    intro γ
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) γ
    refine Subgroup.subset_closure ⟨c * ⟨e, heC⟩ * c⁻¹, ⟨c, c.2, by simp⟩, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rfl
  have hcc : ∀ γ δ : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (γ * F7I.piC C ⟨e, heC⟩ * γ⁻¹) * (δ * F7I.piC C ⟨e, heC⟩ * δ⁻¹) =
        (δ * F7I.piC C ⟨e, heC⟩ * δ⁻¹) * (γ * F7I.piC C ⟨e, heC⟩ * γ⁻¹) :=
    fun γ δ => hPhi _ (hmemA γ) _ (hmemA δ)
  have hcAB := F7N.conj_cent_of_perm hperm heA heB
  set π := F7I.piC C with hπ
  set eb := π ⟨e, heC⟩ with hebdef
  set tb := π ⟨t, htC⟩ with htbdef
  have htcen : ∀ x : ↥C ⧸ classicalInvolutionOddCore ↥C, tb * x = x * tb := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) x
    have hct : (c : Y) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have h : (⟨t, htC⟩ : ↥C) * c = c * ⟨t, htC⟩ := Subtype.ext hct.symm
    change π _ * π c = π c * π _
    rw [← map_mul, ← map_mul, h]
  have he2' : (⟨e, heC⟩ : ↥C) * ⟨e, heC⟩ = 1 := Subtype.ext hd.he2
  have ht2' : (⟨t, htC⟩ : ↥C) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
  have hu2' : (⟨u, huC⟩ : ↥C) * ⟨u, huC⟩ = 1 := Subtype.ext hd.hu2
  have heb2 : eb * eb = 1 := by rw [hebdef, ← map_mul, he2', map_one]
  have htb2 : tb * tb = 1 := by rw [htbdef, ← map_mul, ht2', map_one]
  obtain ⟨Sb, hSb⟩ : ∃ Sb : Set (↥C ⧸ classicalInvolutionOddCore ↥C),
      Sb = {x | ∃ c : ↥C, ((c : Y) = t ∨ ∃ d ∈ C, (c : Y) = d * e * d⁻¹) ∧ π c = x} := ⟨_, rfl⟩
  have hgen : ∀ x ∈ Sb, x = tb ∨ ∃ γ, x = γ * eb * γ⁻¹ := by
    intro x hx
    rw [hSb] at hx
    obtain ⟨c, hcX, rfl⟩ := hx
    rcases hcX with hct | ⟨d, hdC, hcd⟩
    · left
      have h : c = ⟨t, htC⟩ := Subtype.ext hct
      rw [h]
    · right
      refine ⟨π ⟨d, hdC⟩, ?_⟩
      have h : c = ⟨d, hdC⟩ * ⟨e, heC⟩ * (⟨d, hdC⟩ : ↥C)⁻¹ := Subtype.ext hcd
      rw [h, map_mul, map_mul, map_inv]
  have hSinv : ∀ q x, x ∈ Sb → q * x * q⁻¹ ∈ Sb := by
    intro q x hx
    rw [hSb] at hx ⊢
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    obtain ⟨c, hcX, rfl⟩ := hx
    refine ⟨d * c * d⁻¹, ?_, ?_⟩
    · have hdt : (d : Y) * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp d.2
      show (d : Y) * c * (d : Y)⁻¹ = t ∨ ∃ d' ∈ C, (d : Y) * c * (d : Y)⁻¹ = d' * e * d'⁻¹
      rcases hcX with hct | ⟨d', hd'C, hcd⟩
      · left
        rw [hct, hdt, mul_inv_cancel_right]
      · right
        refine ⟨d * d', C.mul_mem d.2 hd'C, ?_⟩
        rw [hcd]
        group
    · change π (d * c * d⁻¹) = π d * π c * (π d)⁻¹
      rw [map_mul, map_mul, map_inv]
  have hScomm : ∀ x ∈ Sb, ∀ y ∈ Sb, x * y = y * x := by
    intro x hx y hy
    rcases hgen x hx with rfl | ⟨γ, rfl⟩
    · exact htcen y
    · rcases hgen y hy with rfl | ⟨δ, rfl⟩
      · exact (htcen _).symm
      · exact hcc γ δ
  have hS2 : ∀ x ∈ Sb, x * x = 1 := by
    intro x hx
    rcases hgen x hx with rfl | ⟨γ, rfl⟩
    · exact htb2
    · calc γ * eb * γ⁻¹ * (γ * eb * γ⁻¹) = γ * (eb * eb) * γ⁻¹ := by group
        _ = 1 := by rw [heb2, mul_one, mul_inv_cancel]
  set Pb := Subgroup.closure Sb with hPbdef
  have hPn : Pb.Normal := F7N.normal_closure_of_conj hSinv
  have hPc : ∀ a ∈ Pb, ∀ b ∈ Pb, a * b = b * a := F7I.closure_comm hScomm
  have hP2 : ∀ a ∈ Pb, a * a = 1 := F7N.sq_eq_one_of_mem_closure hScomm hS2
  have hu' : (⟨u, huC⟩ : ↥C) = b₁ * b' := Subtype.ext hub.symm
  have huS : ∀ x ∈ Sb, x * π ⟨u, huC⟩ = π ⟨u, huC⟩ * x := by
    intro x hx
    rcases hgen x hx with rfl | ⟨γ, rfl⟩
    · exact htcen _
    · rw [hu', map_mul]
      have h1 := (hcAB γ).1 _ hb₁
      have h2 := (hcAB γ).2 _ hb'
      calc γ * eb * γ⁻¹ * (π b₁ * π b') = (γ * eb * γ⁻¹ * π b₁) * π b' := by group
        _ = π b₁ * (γ * eb * γ⁻¹ * π b') := by rw [h1]; group
        _ = π b₁ * (π b' * (γ * eb * γ⁻¹)) := by rw [h2]
        _ = π b₁ * π b' * (γ * eb * γ⁻¹) := by group
  have huP : ∀ a ∈ Pb, π ⟨u, huC⟩ * a = a * π ⟨u, huC⟩ := by
    have hle : Pb ≤ Subgroup.centralizer ({π ⟨u, huC⟩} : Set _) := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (huS x hx)
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
  have heP : eb ∈ Pb := by
    refine Subgroup.subset_closure ?_
    rw [hSb]
    exact ⟨⟨e, heC⟩, Or.inr ⟨1, C.one_mem, by group⟩, rfl⟩
  have htP : tb ∈ Pb := by
    refine Subgroup.subset_closure ?_
    rw [hSb]
    exact ⟨⟨t, htC⟩, Or.inl rfl, rfl⟩
  have het : (⟨e, heC⟩ : ↥C) * ⟨t, htC⟩ = ⟨t, htC⟩ * ⟨e, heC⟩ :=
    Subtype.ext (hWab e heW t hd.hzW)
  have heu : (⟨e, heC⟩ : ↥C) * ⟨u, huC⟩ = ⟨u, huC⟩ * ⟨e, heC⟩ :=
    Subtype.ext (hWab e heW u hd.huW)
  have htu : (⟨t, htC⟩ : ↥C) * ⟨u, huC⟩ = ⟨u, huC⟩ * ⟨t, htC⟩ :=
    Subtype.ext (hWab t hd.hzW u hd.huW)
  obtain ⟨Z, hab, hsq, heZ, htZ, hZC, hZu, hfr, himg⟩ :=
    F7N.exists_zdata C Pb hPn hPc hP2 ⟨e, heC⟩ ⟨t, htC⟩ ⟨u, huC⟩ heP htP huP he2' ht2' hu2' het
      heu htu
  set Q := Subgroup.closure (({t} : Set Y) ∪ {f | ∃ c ∈ C, f = c * e * c⁻¹}) with hQdef
  have hPbQ : Pb ≤ (Q.subgroupOf C).map π := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rw [hSb] at hx
    obtain ⟨c, hcX, rfl⟩ := hx
    refine ⟨c, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ?_), rfl⟩
    rcases hcX with h | ⟨d, hdC, h⟩
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ ⟨d, hdC, h⟩
  refine ⟨Z, ⟨hab, hsq, heZ, htZ, hZC, hZu, hfr, ?_⟩⟩
  intro a ha
  obtain ⟨haC, hπa⟩ := himg a ha
  obtain ⟨q, hq, hqa⟩ := hPbQ hπa
  have ho : ((q⁻¹ * ⟨a, haC⟩ : ↥C) : Y) ∈ oddCoreOf C := (F7I.piC_eq_iff q ⟨a, haC⟩).mp hqa
  have hqQ : (q : Y) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have h : a = (q : Y) * ((q⁻¹ * ⟨a, haC⟩ : ↥C) : Y) := by
    show a = (q : Y) * ((q : Y)⁻¹ * a)
    group
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hqQ) (Subgroup.mem_sup_left ho)

end ZDataAE5

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
