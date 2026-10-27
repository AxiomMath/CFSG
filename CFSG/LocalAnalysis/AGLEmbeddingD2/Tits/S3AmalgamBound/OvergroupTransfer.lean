module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer

@[expose] def OvergroupEqTop (K : Type) [Group K] : Prop :=
  (∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) →
    ∀ A W : Subgroup K, Nat.card A = 3 → Subgroup.normalizer (A : Set K) ≤ W →
      ¬ CFSG.HallHigman.IsPSolvable 3 W → W = ⊤

theorem eqTop_of_map_eq {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {A W : Subgroup K}
    {A' : Subgroup K'} (hA : A.map e.toMonoidHom = A')
    (hNW : Subgroup.normalizer (A : Set K) ≤ W) (hW : ¬ CFSG.HallHigman.IsPSolvable 3 W)
    (h : ∀ W' : Subgroup K', Subgroup.normalizer (A' : Set K') ≤ W' →
      ¬ CFSG.HallHigman.IsPSolvable 3 W' → W' = ⊤) : W = ⊤ := by
  subst hA
  have hN' : Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup K') : Set K') ≤
      W.map e.toMonoidHom := by
    intro y' hy'
    obtain ⟨y, rfl⟩ := e.surjective y'
    refine ⟨y, hNW ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hy' ⊢
    have hmem : ∀ b : K, e b ∈ A.map e.toMonoidHom ↔ b ∈ A := fun b => by
      constructor
      · rintro ⟨b0, hb0, h⟩
        exact (e.injective h) ▸ hb0
      · intro hb
        exact ⟨b, hb, rfl⟩
    intro a
    rw [← hmem a, ← hmem (y * a * y⁻¹)]
    simpa only [← map_inv, ← map_mul] using hy' (e a)
  have hW' : ¬ CFSG.HallHigman.IsPSolvable 3 (W.map e.toMonoidHom) := by
    intro hs
    apply hW
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective W e.toMonoidHom e.injective).symm hs
  have htop := h _ hN' hW'
  rw [eq_top_iff]
  intro k _
  have hk : e k ∈ W.map e.toMonoidHom := by rw [htop]; trivial
  obtain ⟨w, hw, hwk⟩ := hk
  have : w = k := e.injective hwk
  exact this ▸ hw

theorem overgroupEqTop_of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : OvergroupEqTop K') : OvergroupEqTop K := by
  intro hcyc A W hA hNW hW
  have hcyc' : ∀ X' : Subgroup K', IsPGroup 3 X' → IsCyclic X' := by
    intro X' hX'
    have hX : IsPGroup 3 (X'.comap e.toMonoidHom) :=
      hX'.comap_of_injective e.toMonoidHom e.injective
    have hc := hcyc _ hX
    have hmap : (X'.comap e.toMonoidHom).map e.toMonoidHom = X' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective X'
    rw [← hmap]
    exact isCyclic_of_surjective ((e.toMonoidHom).subgroupMap (X'.comap e.toMonoidHom))
      (MonoidHom.subgroupMap_surjective _ _)
  have hA' : Nat.card (A.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hA]
  exact eqTop_of_map_eq e rfl hNW hW fun W' hN' hW' => h hcyc' _ W' hA' hN' hW'

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
