module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfTwo
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEApply
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Two

variable {n : ℕ}

@[expose] def P23FuseN (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R e →
      ∀ L ∈ twinSet (Om R) (tightCore R), ∀ L' ∈ twinSet (Om R) (tightCore R), L' ≠ L →
        ∀ R₁ R₂ : Subgroup Y, IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ →
          ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
            ∃ c ∈ Subgroup.centralizer ({t} : Set Y), c * u * c⁻¹ = x * y

theorem p23TwoN_of_fuseN (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hf : P23FuseN n) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
      (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R e →
        Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ := by
  intro Y _ _ R S t K' W u e g hc hno
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  have hfuse := hf Y R S t K' W u e g hc hno
  have hd := hc.data
  have htrans := trans_of_fuse hs hc.std.hW hc.std.htW hd.hu hd.huW hd.hu1 hd.huz hd.hu2 hfuse
  have hstd : StdCent (Om R) (tightCore R)
      (Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y)) t := by
    refine ⟨le_sup_right, ?_, ?_⟩
    · intro L hL J hJ z' hz' hzz
      exfalso
      have hJp : J ∈ KPerp (Om R) L := Set.mem_insert_of_mem _ hJ
      rw [A7T22.kPerp_eq_of_twin hΩ hK hL, hperp] at hJp
      rcases hJp with rfl | rfl
      · exact hzz (hz'.eq hz)
      · exact hzz (hz'.eq (isUniqueInvolution_of_mem_twinSet hz hs.hK'))
    · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hcm x hx y hy ox oy a ha
      obtain ⟨c, hcz, hcu⟩ := hfuse L hL L' hL' hne R₁ R₂ hR₁ hR₂ hcm x hx y hy ox oy
      have ha' : a * (x * y) = (x * y) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hu' : u = c⁻¹ * (x * y) * c := by rw [← hcu]; group
      have hcomm : (c⁻¹ * a * c) * u = u * (c⁻¹ * a * c) := by
        have e1 : c⁻¹ * (a * (x * y)) * c = c⁻¹ * ((x * y) * a) * c := by rw [ha']
        calc (c⁻¹ * a * c) * u = c⁻¹ * (a * (x * y)) * c := by rw [hu']; group
          _ = c⁻¹ * ((x * y) * a) * c := e1
          _ = u * (c⁻¹ * a * c) := by rw [hu']; group
      have hcH : c ∈ Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) :=
        Subgroup.mem_sup_right hcz
      have ha'H : c⁻¹ * a * c ∈
          Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) :=
        Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH ha'H) (Subgroup.inv_mem _ hcH)
  exact TwinDisc.thmE_apply (hE hcit hP) hc.std.perp.core.toHyp hK hz hstd htrans

end Two

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
