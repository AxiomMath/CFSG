module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypes
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesSym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon.Coordinator

theorem false_of_sym {X : Type} [Group X] {N : Subgroup X}
    (hNc : N = ⁅(⊤ : Subgroup X), ⊤⁆) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (ψ : X →* LinearMap.GeneralLinearGroup (ZMod 2) U)
    (hinj : Function.Injective ψ) (hd : 5 ≤ finrank (ZMod 2) U)
    (hsym : Even (finrank (ZMod 2) U) ∧
      ((∃ β : U ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) U + 1),
          ψ.range.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
            (sumZeroRep (finrank (ZMod 2) U + 1)).range) ∨
        ∃ β : U ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) U + 2) ⧸
            onesLine (finrank (ZMod 2) U + 2),
          ψ.range.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
            (heartRep (finrank (ZMod 2) U + 2)).range))
    (hnotAlt : ∀ n : ℕ, 7 ≤ n → ¬ Nonempty (↥N ≃* alternatingGroup (Fin n))) : False := by
  have key : ∃ m : ℕ, 7 ≤ m ∧ Nonempty (X ≃* Equiv.Perm (Fin m)) := by
    obtain ⟨hev, hs | hs⟩ := hsym
    · obtain ⟨β, hβ⟩ := hs
      obtain ⟨eH⟩ := mclt_nonempty_equiv_perm β (mclt_sumZeroRep_injective (by omega)) hβ
      obtain ⟨k, hk⟩ := hev
      exact ⟨_, by omega, ⟨(MonoidHom.ofInjective hinj).trans eH⟩⟩
    · obtain ⟨β, hβ⟩ := hs
      obtain ⟨eH⟩ := mclt_nonempty_equiv_perm β (mclt_heartRep_injective (by omega)) hβ
      obtain ⟨k, hk⟩ := hev
      exact ⟨_, by omega, ⟨(MonoidHom.ofInjective hinj).trans eH⟩⟩
  obtain ⟨m, hm7, ⟨e⟩⟩ := key
  have h5 : 5 ≤ Nat.card (Fin m) := by simpa using (by omega : 5 ≤ m)
  have hmap : N.map e.toMonoidHom = alternatingGroup (Fin m) := by
    rw [hNc, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    have := alternatingGroup.commutator_perm_eq h5
    rwa [commutator_def] at this
  exact hnotAlt m hm7 ⟨(N.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
