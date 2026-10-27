module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Twin

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem exists_sylow_cent_twins (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z)
    (hVZ : V ≤ Z) :
    (∃ P : Subgroup Y, IsSylow2In P (tightCore R) ∧ P ≤ Subgroup.centralizer (V : Set Y)) ∧
      ∃ P : Subgroup Y, IsSylow2In P K' ∧ P ≤ Subgroup.centralizer (V : Set Y) := by
  have hV2 : IsPGroup 2 ↥V := (P23ZData.isPGroup hZ).to_le hVZ
  have key : ∀ {J : Subgroup Y}, (∀ a ∈ Z, CentMod J a) →
      ∃ P : Subgroup Y, IsSylow2In P J ∧ P ≤ Subgroup.centralizer (V : Set Y) := by
    intro J hJ
    have hVN : V ≤ Subgroup.normalizer (J : Set Y) := fun v hv =>
      F7E.mem_normalizer_of_centMod (hJ v (hVZ hv)) (hZ.sq v (hVZ hv))
    obtain ⟨P, hP, hPc⟩ := F7E.exists_sylow_comm hV2 hVN (X := (V : Set Y)) (fun x hx => hx)
      (fun x hx => hJ x (hVZ hx))
    refine ⟨P, hP, fun r hr => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hPc x hx r hr).symm
  exact ⟨key fun a ha => (hZ.centMod hc ha).1, key fun a ha => (hZ.centMod hc ha).2⟩

theorem p23_twin_pair (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (hL1 : SecCoresTwoGroup (Om R) V) :
    ∃ P₀ P₀' : Subgroup Y, IsSylow2In P₀ (tightCore R) ∧ IsSylow2In P₀' K' ∧
      P₀ ≤ Subgroup.centralizer (V : Set Y) ∧ P₀' ≤ Subgroup.centralizer (V : Set Y) ∧
      secImage (rLayerSub (Om R) V) P₀ ∈ p23SecFamV R V ∧
      secImage (rLayerSub (Om R) V) P₀' ∈ p23SecFamV R V ∧
      secImage (rLayerSub (Om R) V) P₀' ≠ secImage (rLayerSub (Om R) V) P₀ ∧
      (∃ zb : SecQuot (rLayerSub (Om R) V),
        IsUniqueInvolution (secImage (rLayerSub (Om R) V) P₀) zb ∧
          IsUniqueInvolution (secImage (rLayerSub (Om R) V) P₀') zb) ∧
      (∀ J ∈ p23SecFamV R V, J ≠ secImage (rLayerSub (Om R) V) P₀ →
        J ≤ Subgroup.normalizer ((secImage (rLayerSub (Om R) V) P₀ :
          Subgroup (SecQuot (rLayerSub (Om R) V))) : Set (SecQuot (rLayerSub (Om R) V))) →
          J = secImage (rLayerSub (Om R) V) P₀') ∧
      (∀ J ∈ p23SecFamV R V, J ≠ secImage (rLayerSub (Om R) V) P₀' →
        J ≤ Subgroup.normalizer ((secImage (rLayerSub (Om R) V) P₀' :
          Subgroup (SecQuot (rLayerSub (Om R) V))) : Set (SecQuot (rLayerSub (Om R) V))) →
          J = secImage (rLayerSub (Om R) V) P₀) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  obtain ⟨⟨P₀, hP₀, hP₀C⟩, ⟨P₀', hP₀', hP₀'C⟩⟩ := exists_sylow_cent_twins hc hZ hVZ
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hP₀X : P₀ ≤ rLayerSub (Om R) V :=
    le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK₀ hP₀) hP₀C
  have hP₀'X : P₀' ≤ rLayerSub (Om R) V :=
    le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK'Ω hP₀') hP₀'C
  have htX : t ∈ rLayerSub (Om R) V := hP₀X (mem_sylow_of_isUniqueInvolution hΩ hK₀ hP₀ hz)
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hperp' : KPerp (Om R) K' = {K', tightCore R} := by
    rw [A7T22.kPerp_eq_of_twin hΩ hK₀ hc.std.hK', hperp, Set.pair_comm]
  refine ⟨P₀, P₀', hP₀, hP₀', hP₀C, hP₀'C, ⟨P₀, mem_RSet_of_isSylow2In hK₀ hP₀, hP₀C, rfl⟩,
    ⟨P₀', mem_RSet_of_isSylow2In hK'Ω hP₀', hP₀'C, rfl⟩, ?_,
    ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨t, htX⟩,
      isUniqueInvolution_secImage hΩ hK₀ hP₀ hP₀X hz htX,
      isUniqueInvolution_secImage hΩ hK'Ω hP₀' hP₀'X hz' htX⟩,
    perp_lift hΩ hL1 hK₀ hK'Ω hP₀ hP₀' hP₀C hP₀'C hperp,
    perp_lift hΩ hL1 hK'Ω hK₀ hP₀' hP₀ hP₀'C hP₀C hperp'⟩
  exact secImage_ne_of_twin hΩ hK₀ hK'Ω hP₀ hP₀' hP₀X hP₀'X hz hz' hc.std.hne
    (fun c hodd hcC => (hc.conjSub_eq_of_odd hcC hodd).1)

end Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
