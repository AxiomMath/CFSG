module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E7Six

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem map_hyperClosure_le_of_injective {φ : G →* G'} (hφ : Function.Injective φ) {p : ℕ}
    (E : Subgroup G) :
    (hyperClosure p ⊤ E).map φ ≤ hyperClosure p ⊤ (E.map φ) := by
  rw [hyperClosure, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, ⟨-, F, hFE, hF, hcomm⟩, rfl⟩
  refine ⟨Subgroup.mem_top _, F.map φ, Subgroup.map_mono hFE, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective F E hφ]
    exact hF
  · rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, hcomm f hf]

end Transport

@[expose] def E7SixStep3Adj : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r] (p : ℕ), p.Prime →
    orderOf ((Nat.card K : ℕ) : ZMod p) = 6 →
    ∃ E E₁ : Subgroup ↥(adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      E₁ ≤ E ∧ E₁ ≠ ⊥ ∧
      (∃ R : Subgroup ↥(adjointGroup Tag.E7 K), R ≠ ⊥ ∧ IsPGroup r R ∧
        ∀ x ∈ E₁, R.map (MulAut.conj x).toMonoidHom = R) ∧
      ∀ B : Subgroup ↥(adjointGroup Tag.E7 K), B ≤ E₁ → B.relIndex E₁ = p →
        ∀ k, (∀ f ∈ B, f * k = k * f) → k ∈ hyperClosure p ⊤ E


theorem e7SixPlane_of_step3Adj (h : E7SixStep3Adj) :
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E7SixPlane := by
  intro q hv p hp _ _ hord
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [hK]; exact hord
  obtain ⟨E, E₁, hE, hEc, hE₁E, hE₁, ⟨R, hR1, hRp, hRn⟩, hlines⟩ := h K q.p p hp hordK
  set φ := e.symm.toMonoidHom with hφ
  have hinj : Function.Injective φ := e.symm.injective
  refine ⟨E.map φ, E₁.map φ, ?_, ?_, Subgroup.map_mono hE₁E, ?_, ?_, ?_⟩
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE φ
  · rw [Subgroup.card_map_of_injective hinj]
    exact hEc
  · exact fun h0 => hE₁ ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h0)
  · refine ⟨R.map φ, fun h0 => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h0), ?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.characteristic_E7]
      exact hRp.map φ
    · rintro _ ⟨x, hx, rfl⟩
      calc (R.map φ).map (MulAut.conj (φ x)).toMonoidHom
          = (R.map (MulAut.conj x).toMonoidHom).map φ := by
            rw [Subgroup.map_map, Subgroup.map_map]
            congr 1
            ext y
            simp [φ, MulAut.conj_apply]
        _ = R.map φ := by rw [hRn x hx]
  · intro B hB hBi k hk
    have hBm : B.map e.toMonoidHom ≤ E₁ := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨x, hx, hxb⟩ := hB hb
      rw [← hxb]
      simpa [φ] using hx
    have hBi' : (B.map e.toMonoidHom).relIndex E₁ = p := by
      have hE₁' : E₁ = (E₁.map φ).map e.toMonoidHom := by
        rw [Subgroup.map_map]
        ext y
        simp [φ]
      rw [hE₁', Subgroup.relIndex_map_map_of_injective _ _ e.injective]
      exact hBi
    have hk' : e k ∈ hyperClosure p ⊤ E := by
      refine hlines _ hBm hBi' (e k) ?_
      rintro _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hk b hb]
    have : k = φ (e k) := by simp [φ]
    rw [this]
    exact map_hyperClosure_le_of_injective hinj E ⟨e k, hk', rfl⟩

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
