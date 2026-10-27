module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueOrth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueCover
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTwin
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1
local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frame

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}

theorem frame_perp_eq_suppPerp (fr : OFrame Q) :
    fr.perp = suppPerp Q fr.span := by
  have hreg := fr.polarNondegOn_span
  have hle : fr.perp ≤ suppPerp Q fr.span := fun y hy =>
    mem_suppPerp.mpr fun x hx => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.polar_eq_zero_of_mem_perp hx hy
  refine le_antisymm hle fun x hx => ?_
  obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.mp
    (by rw [(fr.isCompl_span_perp).sup_eq_top]; trivial : x ∈ fr.span ⊔ fr.perp)
  have hwp : w ∈ suppPerp Q fr.span := by
    have := (suppPerp Q fr.span).sub_mem hx (hle hp)
    simpa using this
  have hw0 : w = 0 := by
    have hc := (isCompl_suppPerp hreg).disjoint
    exact Submodule.disjoint_def.mp hc w hw hwp
  rw [hw0, zero_add]
  exact hp

end Frame

section Main

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}

theorem model1520_of_spinCtx3 {𝓕 : Set (Subgroup (spinGroup Q))} (ctx : SpinCtx3 Q 𝓕)
    [Finite (spinGroup Q)] (hperf : Group.IsPerfect (spinGroup Q))
    (hOD : orthDerived Q = elementaryGroup Q)
    (hind : ∀ α : MulAut (ProjOrthDerived Q),
      CFSG.RankThree.PartOne.KCOrthogonalAut.InducedBySemilinear Q α)
    {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : spinGroup Q →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (spinGroup Q))
    {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) (e₂ : R ≃* SL(2, 𝔽₃)) :
    Model1520 X ((ψ (sl2Inv e₂) : ↥X) : G) := by
  classical
  have h3 : Nat.card 𝔽₃ = 3 := natCard_galoisField_three
  have hodd := odd_natCard_galoisField_three
  obtain ⟨fr, hfr⟩ := ctx.hframe R hR
  have hθ : spinAction Q (sl2Inv e₂) = fr.La (-1) := theta_sl2Inv e₂ hfr
  have hQ := ctx.hQ
  have hmem : ∀ k, spinAction Q k ∈ orthDerived Q := fun k => by
    rw [hOD, ← ctx.hrange]
    exact ⟨k, rfl⟩
  let θ' : spinGroup Q →* orthDerived Q := (spinAction Q).codRestrict _ hmem
  let π : spinGroup Q →* ProjOrthDerived Q := (QuotientGroup.mk' _).comp θ'
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : (g : _ ≃ₗ[𝔽₃] _) ∈ (spinAction Q).range := by
      rw [ctx.hrange, ← hOD]
      exact g.2
    obtain ⟨k, hk⟩ := hg
    exact ⟨k, congrArg QuotientGroup.mk (Subtype.ext hk)⟩
  have hπker : π.ker = Subgroup.center (spinGroup Q) := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      refine mem_center_of_commutators_central hperf fun y => ker_spinAction_le_center Q ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc := commute_of_mem_scalars (show spinAction Q k ∈ scalars 𝔽₃ _ from hk)
        (spinAction Q y)
      calc spinAction Q k * spinAction Q y * (spinAction Q k)⁻¹ * (spinAction Q y)⁻¹
          = (spinAction Q y * spinAction Q k) * (spinAction Q k)⁻¹ * (spinAction Q y)⁻¹ := by
            rw [hc]
        _ = 1 := by group
    · intro hk
      have hz : (⟨spinAction Q k, by rw [← ctx.hrange]; exact ⟨k, rfl⟩⟩ : elementaryGroup Q) ∈
          Subgroup.center (elementaryGroup Q) := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨g, hg⟩
        rw [← ctx.hrange] at hg
        obtain ⟨y, rfl⟩ := hg
        apply Subtype.ext
        change spinAction Q y * spinAction Q k = spinAction Q k * spinAction Q y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk y]
      exact Subgroup.mem_subgroupOf.mp (ctx.hZ hz)
  obtain ⟨e, he⟩ := exists_equiv_of_covers hperf ψ hψ hker π hπ hπker
  have hP : Group.IsPerfect (ProjOrthDerived Q) := Group.IsPerfect.ofSurjective hπ
  have hreg := fr.polarNondegOn_span
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_suppPerp hreg)
  have hspan := fr.finrank_span
  have hdim := ctx.hdim
  have hhmem : fr.La (-1) ∈ orthDerived Q := hθ ▸ hmem _
  have hsq : ((ψ (sl2Inv e₂) : ↥X) : G) * ((ψ (sl2Inv e₂) : ↥X) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, sl2Inv_mul_self hodd e₂, map_one, Subgroup.coe_one]
  refine model1520_of_orth_abs (X := X) (t := ((ψ (sl2Inv e₂) : ↥X) : G)) (ψ (sl2Inv e₂)).2 hsq h3 Q
    hQ hind hP e fr.span (nondegenerate_polarBilin_restrict hreg) (by omega) (by omega)
    (fr.La (-1)) hhmem (-1) 1 ?_ ?_ ?_
  · intro w hw
    rw [fr.La_neg_one_apply, ← (fr.mem_span_iff.mp hw)]
    module
  · intro w hw
    rw [← frame_perp_eq_suppPerp, fr.mem_perp_iff] at hw
    rw [fr.La_neg_one_apply, hw]
    simp
  · have := he (sl2Inv e₂)
    rw [this]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    exact hθ

end Main


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
