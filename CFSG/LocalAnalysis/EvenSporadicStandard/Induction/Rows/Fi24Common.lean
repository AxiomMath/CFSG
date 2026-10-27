module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverMore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCoreBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowFinal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24 (R JR)
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (fi24_equiv_P fi24_autModel)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem fi24AutOddCore_native : AutOddCoreTrivial ↥(JR : Subgroup R) := by
  refine autOddCoreTrivial_of_oddCore fun ν hν1 hνν => ?_
  have h := fi24_autModel
  set τ : R := h.elt ν with hτ
  have hspec : ∀ p : ↥(JR : Subgroup R), ((ν p : ↥(JR : Subgroup R)) : R) = τ * p * τ⁻¹ :=
    h.elt_spec ν
  have hττ : τ * τ = 1 := by
    refine h.inj (τ * τ) (Subgroup.mem_top _) fun p hp => ?_
    have h1 := hspec ⟨p, hp⟩
    have h2 := hspec (ν ⟨p, hp⟩)
    have h3 : ((ν (ν ⟨p, hp⟩) : ↥(JR : Subgroup R)) : R) = p := by
      have : ν (ν ⟨p, hp⟩) = ⟨p, hp⟩ := by
        have := congrArg (fun a : MulAut ↥(JR : Subgroup R) => a ⟨p, hp⟩) hνν
        simpa using this
      rw [this]
    rw [h3, h1] at h2
    calc τ * τ * p = (τ * τ * p * (τ * τ)⁻¹) * (τ * τ) := by group
      _ = p * (τ * τ) := by
        have : τ * τ * p * (τ * τ)⁻¹ = p := by
          have h2' : p = τ * (τ * p * τ⁻¹) * τ⁻¹ := h2
          calc τ * τ * p * (τ * τ)⁻¹ = τ * (τ * p * τ⁻¹) * τ⁻¹ := by group
            _ = p := h2'.symm
        rw [this]
  have hτ1 : τ ≠ 1 := fun h1 => hν1 (MulEquiv.ext fun p => Subtype.ext (by
    rw [hspec p, h1]
    simp))
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hττ) hτ1
  have hB := (CTUC_Fi24_all_extension_involution_centralizers_odd_core_trivial τ hτ2).2
  refine oddCore_eq_bot_of_equiv ?_ hB
  have hfix : (fixSubgroup ν : Subgroup ↥(JR : Subgroup R)).map (JR : Subgroup R).subtype =
      (JR : Subgroup R) ⊓ Subgroup.centralizer {τ} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : ν p = p := hp
      have h2 := hspec p
      rw [h1] at h2
      calc (p : R) * τ = (τ * p * τ⁻¹) * τ := by rw [← h2]
        _ = τ * p := by group
    · rintro ⟨hxP, hxc⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      show ν ⟨x, hxP⟩ = ⟨x, hxP⟩
      apply Subtype.ext
      rw [hspec]
      have := mem_centralizer_singleton_iff.1 hxc
      calc τ * x * τ⁻¹ = (x * τ) * τ⁻¹ := by rw [this]
        _ = x := by group
  exact (Subgroup.equivMapOfInjective (fixSubgroup ν : Subgroup ↥(JR : Subgroup R))
    (JR : Subgroup R).subtype (JR : Subgroup R).subtype_injective).trans
    (MulEquiv.subgroupCongr hfix)

theorem fi24AutOddCore {Y : Type} [Group Y] (h : IsSporadic Y .Fi24Prime) :
    AutOddCoreTrivial Y := by
  obtain ⟨e⟩ := fi24_equiv_P h
  have hP := fi24AutOddCore_native
  exact @AutOddCoreTrivial.of_mulEquiv Y ↥(JR : Subgroup R) _ _ e hP

theorem fi24FusionData : FusionRowData .Fi24Prime noExc :=
  ⟨fun _ _ h => (fi24_autCenterCond h).toExc, fun _ _ h => fi24_umovesCond h,
    fun _ _ h => fi24AutOddCore h⟩

end CFSG.EvenSporadicStandard.Induction
