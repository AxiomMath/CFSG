module

public import CFSG.LieType.ChevTwo.OppositeFixedExcBase
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LieType.BorelTits

@[expose] def OppositeFixedInner (K : Type) [Group K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K), IsPGroup p R →
    R ≤ (MulAut.conj : K →* MulAut K).range →
    ∀ Q : Subgroup K, Q ≠ ⊥ → IsPGroup 2 Q →
      pCoreOf 2 (Subgroup.normalizer (Q : Set K)) = Q → Subgroup.normalizer (Q : Set K) ≠ ⊤ →
        (∀ α ∈ R, Q.map α.toMonoidHom = Q) →
          autCentralizer R ≤ Subgroup.normalizer (Q : Set K) → autCentralizer R ⊓ Q = ⊥

private theorem map_congr_le_range_conj {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {R : Subgroup (MulAut K)} (hR : R ≤ (MulAut.conj : K →* MulAut K).range) :
    R.map (MulAut.congr e).toMonoidHom ≤ (MulAut.conj : K' →* MulAut K').range := by
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨k, rfl⟩ := hR hα
  refine ⟨e k, ?_⟩
  ext x'
  simp [MulAut.congr_apply]

theorem oppositeFixedInner_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : OppositeFixedInner K') : OppositeFixedInner K :=
  fun p hp hp2 R hR hRinn Q =>
    oppositeFixedAt_of_map_congr e
      (h p hp hp2 _ (hR.map _) (map_congr_le_range_conj e hRinn) (Q.map e.toMonoidHom))

end CFSG.LieType.ChevTwo
