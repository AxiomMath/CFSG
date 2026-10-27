module

public import CFSG.LocalAnalysis.GLTheoremB.AltAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB

namespace S7

theorem exists_invariant_two_subgroup {K : Type*} [Group K] (e : K ≃* ↥Alt7)
    (R : Subgroup (MulAut K)) (hR : IsPGroup 3 ↥R) :
    ∃ W : Subgroup K, W ≠ ⊥ ∧ IsPGroup 2 ↥W ∧ ∀ φ ∈ R, W.map φ.toMonoidHom ≤ W := by
  obtain ⟨N, hNA, hNb, hN2, hRN⟩ := exists_normalizes (R := R.map (permOfAut e)) (hR.map _)
  refine ⟨(N.subgroupOf Alt7).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro h
    apply hNb
    have h1 := (Subgroup.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) _
      e.symm.injective).1 h
    rw [← Subgroup.map_subgroupOf_eq_of_le hNA, h1, Subgroup.map_bot]
  · exact (hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNA).symm).map _
  · rintro φ hφ _ ⟨w, hw, rfl⟩
    obtain ⟨n', hn', rfl⟩ := hw
    have hσ : permOfAut e φ ∈ Subgroup.normalizer (N : Set S) := hRN ⟨φ, hφ, rfl⟩
    refine ⟨e (φ (e.symm n')), ?_, by simp⟩
    show ((e (φ (e.symm n')) : ↥Alt7) : S) ∈ N
    rw [permOfAut_spec e φ (e.symm n')]
    have hwN : ((e (e.symm n') : ↥Alt7) : S) ∈ N := by
      rw [MulEquiv.apply_symm_apply]
      exact hn'
    exact (Subgroup.mem_normalizer_iff.1 hσ _).1 hwN

end S7

end CFSG.LocalAnalysis.GLTheoremB
