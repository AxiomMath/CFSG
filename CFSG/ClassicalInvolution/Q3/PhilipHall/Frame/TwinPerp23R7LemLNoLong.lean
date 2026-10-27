module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLNoSplit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Split
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTrans

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem p23_twin_pair_of_sylow' (hc : P23Cfg n Y R S t K' W u e g) (hL1 : SecCoresTwoGroup (Om R) V)
    {P₀ P₀' : Subgroup Y} (hP₀ : IsSylow2In P₀ (tightCore R)) (hP₀' : IsSylow2In P₀' K')
    (hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y))
    (hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y)) :
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


theorem lemLNoLong_of_coreTwo (hT : Thm4RTwinBelow 3 n) (hL1 : LemLCoreTwo n) : LemLNoLong n := by
  intro hcit hP Y _ _ R S t K' W u e g Z V f₁ f₂ ctx K hK τ hτ hlong
  have hc := ctx.cfg
  have hZd := ctx.zdata
  have hVZ := ctx.vz
  have hL := hL1 hcit hP Y R S t K' W u e g Z V f₁ f₂ ctx
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hf₁Z : f₁ ∈ Z := hZd.orb_le ctx.hf₁
  have hVf : V ⊔ Subgroup.zpowers f₁ ≤ Z := sup_le hVZ (Subgroup.zpowers_le.mpr hf₁Z)
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, ⟨P₀', hP₀', hP₀'C'⟩⟩ := exists_sylow_cent_twins hc hZd hVf
  have hVle : ((V : Subgroup Y) : Set Y) ⊆ ((V ⊔ Subgroup.zpowers f₁ : Subgroup Y) : Set Y) :=
    SetLike.coe_subset_coe.mpr le_sup_left
  have hfle : ({f₁} : Set Y) ⊆ ((V ⊔ Subgroup.zpowers f₁ : Subgroup Y) : Set Y) :=
    Set.singleton_subset_iff.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers f₁))
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le hVle)
  have hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀'C'.trans (Subgroup.centralizer_le hVle)
  have hP₀f : P₀ ≤ Subgroup.centralizer ({f₁} : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le hfle)
  have hP₀'f : P₀' ≤ Subgroup.centralizer ({f₁} : Set Y) :=
    hP₀'C'.trans (Subgroup.centralizer_le hfle)
  obtain ⟨hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, hperp'⟩ :=
    p23_twin_pair_of_sylow' hc hL hP₀ hP₀' hP₀C hP₀'C
  have hlt := card_secQuot_lt hc ctx.v1
  have hY1 : ModS3O ↥(rLayer (Om R) e) := modS3O_rLayer hc ctx.ecase
  obtain ⟨hfX, ha⟩ := p23_type237 hc hZd hVZ hY1 ctx.hf₁ ctx.h₁
  have hΦΩ := p23SecFamV_hypOmegaGen hc hZd hVZ hL
  have F : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) :=
    { hyp := hΦΩ
      two := p23SecFamV_isPGroup hL
      q8 := p23SecFamV_q8 hc hL
      aEmpty := p23SecFamV_aEmpty hc hZd hVZ hL
      gen := p23SecFamV_pSpan R V
      trans := trans_of_twin hT hlt hΦΩ (p23SecFamV_isPGroup hL) (p23SecFamV_q8 hc hL)
        (p23SecFamV_aEmpty hc hZd hVZ hL)
        (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V)) hKb
        ⟨hKb', zb, hzb, hzb'⟩ hne' hperp hperp' ha
      oddFree := CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V) }
  obtain ⟨-, -, -, hcov⟩ := p23_cover_V hc hZd hVZ ctx.hf₁ ctx.h₁
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  obtain ⟨w, hwf, hwodd, hwP, ⟨x, hx, hwx⟩, -⟩ :=
    L7.exists_split_of_longFund_core hΩ F (mem_RSet_of_isSylow2In hK₀ hP₀)
      (mem_RSet_of_isSylow2In hc.std.hK'.1 hP₀') hP₀C hP₀'C hne' hzb hzb'
      (hZd.sq f₁ hf₁Z) hfX hP₀f hP₀'f hcov hK hτ hlong
  exact hwx (centralizes_of_odd_normalizes_orb hc ctx.ecase ctx.hf₁ (Or.inl rfl) hP₀ hP₀f hwf
    hwodd hwP x hx)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
