module

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


section Mem

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem normalizer_le_centralizer_e (hd : Hyp23bData (Om R) (tightCore R) K' W t u e g) :
    Subgroup.normalizer (W : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) := by
  have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) := by
    rw [← hd.he]; exact Subgroup.subset_closure rfl
  obtain ⟨a, ha, rfl⟩ := (Subgroup.mem_inf.mp he).2
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := Subgroup.mem_center_iff.mp ha ⟨y, hy⟩
  exact congrArg Subtype.val this

end Mem

theorem p23Members (n : ℕ) : P23Members n := by
  intro Y _ _ R S t K' W u e g hc
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  obtain ⟨S₀, R₀, R', hWS, hR₀, -, hRS, -⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hc.std.hW hc.std.htW
  have hRD : R₀ ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK hR₀) hRS
  have hRN : R₀ ≤ Subgroup.normalizer (W : Set Y) := hRD.2
  have hNe := normalizer_le_centralizer_e hc.data
  have hRe : R₀ ≤ Subgroup.centralizer ({e} : Set Y) := hRN.trans hNe
  have hKt : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hz
  refine ⟨?_, ?_⟩
  · have hKe : tightCore R ∈ tqMembers3 (Om R) e :=
      ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₀, hR₀, hRe⟩⟩
    exact ⟨_, secImg_mem_secFam hKe⟩
  · have hgN : g ∈ Subgroup.normalizer (W : Set Y) := by
      have : (⨆ X ∈ DSet (Om R) W, X) ≤ Subgroup.normalizer (W : Set Y) :=
        iSup₂_le fun X hX => hX.2
      exact this hc.data.hg
    have hJ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
    have hRu : conjSub g R₀ ≤ Subgroup.centralizer ({u} : Set Y) := by
      rintro _ ⟨x, hx, rfl⟩
      have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
      rw [e1, Subgroup.mem_centralizer_singleton_iff]
      have hxN : x ∈ Subgroup.normalizer (W : Set Y) := hRN hx
      have hyN : g * x * g⁻¹ ∈ Subgroup.normalizer (W : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hxN) (Subgroup.inv_mem _ hgN)
      have hye : (g * x * g⁻¹) * e = e * (g * x * g⁻¹) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hNe hyN))
      have hxt : x * t = t * x :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hKt (hR₀.1 hx)))
      have hyt : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
        calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
          _ = g * (t * x) * g⁻¹ := by rw [hxt]
          _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
      have hu : u = (g * t * g⁻¹) * e := by
        rw [hc.data.hgt, mul_assoc, hc.data.he2, mul_one]
      have key : (g * x * g⁻¹) * u = u * (g * x * g⁻¹) := by
        rw [hu]
        calc (g * x * g⁻¹) * ((g * t * g⁻¹) * e)
            = ((g * x * g⁻¹) * (g * t * g⁻¹)) * e := by group
          _ = ((g * t * g⁻¹) * (g * x * g⁻¹)) * e := by rw [hyt]
          _ = (g * t * g⁻¹) * ((g * x * g⁻¹) * e) := by group
          _ = (g * t * g⁻¹) * (e * (g * x * g⁻¹)) := by rw [hye]
          _ = ((g * t * g⁻¹) * e) * (g * x * g⁻¹) := by group
      exact key
    have hJu : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
      ⟨hJ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ ⟨conjSub g R₀, hR₀.conj g, hRu⟩⟩
    exact ⟨_, secImg_mem_secFam hJu⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
