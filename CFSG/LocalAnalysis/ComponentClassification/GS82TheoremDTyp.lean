module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP5Basic
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDefs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup

@[expose] def TwoAltTyp (n : ℕ) (K : Type) [Group K] : Prop :=
  ∃ m : ℕ, n ≤ m ∧ GH74.GLS.IsDoubleCoverOfAlt (K ⧸ pPrimeCore 2 K) m

theorem isDoubleCoverOfAlt_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {m : ℕ}
    (h : GH74.GLS.IsDoubleCoverOfAlt K m) : GH74.GLS.IsDoubleCoverOfAlt L m := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ⟨(Sol78.centerQuotCongr e).symm.trans f⟩⟩
  rw [← Sol78.map_center_eq_of_mulEquiv e, Subgroup.card_map_of_injective e.injective]
  exact hc

theorem diagonalTransfer_twoAltTyp (q₀ : ℕ) {n : ℕ} (hn : 5 ≤ n) :
    DiagonalTransfer q₀ (TwoAltTyp n) := by
  intro A B _ _ _ _ _ hBq ⟨m, hm, hA⟩ ⟨e⟩ _ _ _ c hc _ _ hcZ
  obtain ⟨-, -, ⟨eA⟩⟩ := hA
  set Bb := B ⧸ pPrimeCore 2 B with hBb
  let eB : Bb ⧸ center Bb ≃* alternatingGroup (Fin m) :=
    (Sol78.coreQuotientCenterEquiv B).trans
      (e.symm.trans ((Sol78.coreQuotientCenterEquiv A).symm.trans eA))
  have hBbq : IsQuasisimple Bb := hBq.2
  have : Group.IsPerfect Bb := hBbq.1
  have h2 : IsPGroup 2 (center Bb) :=
    Sol78.center_isPGroup_two (GH74.GLS.pPrimeCore_quotient_eq_bot B)
  obtain ⟨hcc, hc1⟩ := mk_mem_center_ne_one hcZ hc
  let η : Bb →* alternatingGroup (Fin m) := eB.toMonoidHom.comp (QuotientGroup.mk' (center Bb))
  have hη : Function.Surjective η := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Bb := by
    ext x
    rw [MonoidHom.mem_ker]
    change eB (QuotientGroup.mk' (center Bb) x) = 1 ↔ x ∈ center Bb
    rw [map_eq_one_iff eB eB.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hle :=
    LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      (hn.trans hm) η hη hker.le (hker ▸ h2)
  rw [hker] at hle
  have hlt : 1 < Nat.card (center Bb) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    rw [h, mem_bot] at hcc
    exact hc1 hcc
  have hcard : Nat.card (center Bb) = 2 := by omega
  exact ⟨m, hm, hBbq, hcard, ⟨eB⟩⟩

end CFSG.ComponentClassification.GS82PumpInputs
