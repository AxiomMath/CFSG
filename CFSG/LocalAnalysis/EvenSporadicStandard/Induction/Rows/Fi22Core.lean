module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCoreBridge
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverMore

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.Schreier CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.M12Cover
  CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.Fi22

theorem fi22AutOddCore_native : AutOddCoreTrivial ↥fi22P := by
  refine autOddCoreTrivial_of_oddCore fun ν hν1 hνν => ?_
  have h := fi22_autModel
  set τ : Equiv.Perm (Fin 3510) := h.elt ν with hτ
  have hτR : τ ∈ fi22R := h.elt_mem ν
  have hspec : ∀ p : ↥fi22P, ((ν p : ↥fi22P) : Equiv.Perm (Fin 3510)) = τ * p * τ⁻¹ :=
    h.elt_spec ν
  have hττ : τ * τ = 1 := by
    refine h.inj (τ * τ) (fi22R.mul_mem hτR hτR) fun p hp => ?_
    have h1 := hspec ⟨p, hp⟩
    have h2 := hspec (ν ⟨p, hp⟩)
    have h3 : ((ν (ν ⟨p, hp⟩) : ↥fi22P) : Equiv.Perm (Fin 3510)) = p := by
      have : ν (ν ⟨p, hp⟩) = ⟨p, hp⟩ := by
        have := congrArg (fun a : MulAut ↥fi22P => a ⟨p, hp⟩) hνν
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
  have hB := CTUC_Fi22_all_involution_fixed_subgroups_odd_core_trivial τ hτR hτ2
  refine oddCore_eq_bot_of_equiv ?_ hB
  have hfix : (fixSubgroup ν : Subgroup ↥fi22P).map fi22P.subtype =
      fi22P ⊓ Subgroup.centralizer {τ} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : ν p = p := hp
      have h2 := hspec p
      rw [h1] at h2
      calc (p : Equiv.Perm (Fin 3510)) * τ = (τ * p * τ⁻¹) * τ := by rw [← h2]
        _ = τ * p := by group
    · rintro ⟨hxP, hxc⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      show ν ⟨x, hxP⟩ = ⟨x, hxP⟩
      apply Subtype.ext
      rw [hspec]
      have := mem_centralizer_singleton_iff.1 hxc
      calc τ * x * τ⁻¹ = (x * τ) * τ⁻¹ := by rw [this]
        _ = x := by group
  exact (Subgroup.equivMapOfInjective (fixSubgroup ν : Subgroup ↥fi22P) fi22P.subtype
    fi22P.subtype_injective).trans (MulEquiv.subgroupCongr hfix)

theorem fi22AutOddCore {Y : Type} [Group Y] (h : IsSporadic Y .Fi22) : AutOddCoreTrivial Y := by
  obtain ⟨e⟩ := h
  exact AutOddCoreTrivial.of_mulEquiv (e.trans fi22PermEquiv) fi22AutOddCore_native

end CFSG.EvenSporadicStandard.Induction
