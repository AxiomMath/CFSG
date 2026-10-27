module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Twin

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem p23_twin_pair_of_sylow (hc : P23Cfg n Y R S t K' W u e g) (hL1 : SecCoresTwoGroup (Om R) V)
    {P₀ P₀' : Subgroup Y} (hP₀ : IsSylow2In P₀ (tightCore R)) (hP₀' : IsSylow2In P₀' K')
    (hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y)) (hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y)) :
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
  refine ⟨⟨P₀, mem_RSet_of_isSylow2In hK₀ hP₀, hP₀C, rfl⟩,
    ⟨P₀', mem_RSet_of_isSylow2In hK'Ω hP₀', hP₀'C, rfl⟩, ?_,
    ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨t, htX⟩,
      isUniqueInvolution_secImage hΩ hK₀ hP₀ hP₀X hz htX,
      isUniqueInvolution_secImage hΩ hK'Ω hP₀' hP₀'X hz' htX⟩,
    perp_lift hΩ hL1 hK₀ hK'Ω hP₀ hP₀' hP₀C hP₀'C hperp,
    perp_lift hΩ hL1 hK'Ω hK₀ hP₀' hP₀ hP₀'C hP₀C hperp'⟩
  exact secImage_ne_of_twin hΩ hK₀ hK'Ω hP₀ hP₀' hP₀X hP₀'X hz hz' hc.std.hne
    (fun c hodd hcC => (hc.conjSub_eq_of_odd hcC hodd).1)

end Twin

section Pullback

variable {Y : Type} [Group Y] [Finite Y]

theorem comm_mem_oddCoreOf_of_comm {X : Subgroup Y} (w x : ↥X)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) w *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) w) :
    (w : Y) * (x : Y) * (w : Y)⁻¹ * (x : Y)⁻¹ ∈ oddCoreOf X := by
  refine mem_oddCoreOf_iff.mpr ⟨(w * x * w⁻¹ * x⁻¹ : ↥X).2, ?_⟩
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (w * x * w⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem conj_mem_oddCoreOf_of_eq {X : Subgroup Y} (w a b : ↥X)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) w *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) a *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) w)⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) b) :
    ((w : Y) * (a : Y) * (w : Y)⁻¹)⁻¹ * (b : Y) ∈ oddCoreOf X := by
  refine mem_oddCoreOf_iff.mpr ⟨((w * a * w⁻¹)⁻¹ * b : ↥X).2, ?_⟩
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ((w * a * w⁻¹)⁻¹ * b) = 1 := by
    simp only [map_mul, map_inv, h, inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem mk_mem_secImage {X Q : Subgroup Y} {x : Y} (hx : x ∈ Q) (hxX : x ∈ X) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨x, hxX⟩ ∈ secImage X Q :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)

theorem mk_comm_secImage {X Q : Subgroup Y} {c : Y} (hcX : c ∈ X) (hcQ : ∀ x ∈ Q, c * x = x * c) :
    ∀ x ∈ secImage X Q, QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ * x =
      x * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcQ y (Subgroup.mem_subgroupOf.mp hy))

end Pullback

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
