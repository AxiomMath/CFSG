module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

@[expose] def OrbitTrans (p : ℕ) (K : Type) [Group K] (T : Sylow p K) : Prop :=
  ∀ x ∈ (T : Subgroup K), x ≠ 1 → ∀ y ∈ (T : Subgroup K), y ≠ 1 →
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n * x * n⁻¹ = y

section Transport

variable {K K' : Type} [Group K] [Group K'] {p : ℕ}

theorem OrbitTrans.of_equiv (e : K ≃* K') {T : Sylow p K} {T' : Sylow p K'}
    (hT : (T : Subgroup K).map e.toMonoidHom = (T' : Subgroup K')) (D : OrbitTrans p K' T') :
    OrbitTrans p K T := by
  have hTmem : ∀ x : K, x ∈ (T : Subgroup K) ↔ e x ∈ (T' : Subgroup K') := by
    intro x
    rw [← hT, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hN : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map e.toMonoidHom =
      Subgroup.normalizer ((T' : Subgroup K') : Set K') := by
    rw [Subgroup.map_equiv_normalizer_eq, hT]
  have hNmem : ∀ x : K, x ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) ↔
      e x ∈ Subgroup.normalizer ((T' : Subgroup K') : Set K') := by
    intro x
    rw [← hN, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  intro x hx hx1 y hy hy1
  obtain ⟨n', hn', hn'xy⟩ := D (e x) ((hTmem x).1 hx)
    (fun h => hx1 (e.injective (by simpa using h))) (e y) ((hTmem y).1 hy)
    (fun h => hy1 (e.injective (by simpa using h)))
  refine ⟨e.symm n', (hNmem _).2 (by simpa using hn'), e.injective ?_⟩
  simpa using hn'xy

variable [Finite K]

theorem OrbitTrans.of_sylow (hp : p.Prime) {T₀ : Sylow p K} (D : OrbitTrans p K T₀)
    (T : Sylow p K) : OrbitTrans p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  refine OrbitTrans.of_equiv (MulAut.conj g⁻¹) (T' := T₀) ?_ D
  have h1 : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact coe_smul_sylow_eq_map T₀ g
  rw [h1, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (T₀ : Subgroup K)]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.id_apply]
  group

theorem OrbitTrans.of_equiv_all [Finite K'] (hp : p.Prime) (e : K ≃* K')
    (hD : ∃ T₀ : Sylow p K', OrbitTrans p K' T₀) (T : Sylow p K) : OrbitTrans p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₀, D⟩ := hD
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  have D' := D.of_sylow hp (Sylow.mapSurjective hf T)
  exact OrbitTrans.of_equiv e (T' := Sylow.mapSurjective hf T) rfl D'

end Transport

section Orbits

variable {K : Type} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem orbits_of_orbitTrans {T : Sylow p K} (hcard : Nat.card (T : Subgroup K) = p ^ 2)
    (D : OrbitTrans p K T) (O : Set K) (hO : O ⊆ (T : Set K) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) :
    O.ncard = 0 ∨ O.ncard = p ^ 2 - 1 := by
  by_cases hne : O.Nonempty
  · right
    obtain ⟨x, hx⟩ := hne
    have hxT : x ∈ (T : Subgroup K) := (hO hx).1
    have hx1 : x ≠ 1 := fun h => (hO hx).2 h
    have hOeq : O = (T : Set K) \ {1} := by
      refine Set.Subset.antisymm hO fun y hy => ?_
      obtain ⟨n, hn, hnxy⟩ := D x hxT hx1 y hy.1 hy.2
      rw [← hnxy]
      exact hinv n hn x hx
    have h1 : (1 : K) ∈ (T : Set K) := (T : Subgroup K).one_mem
    have h2 : (T : Set K).ncard = Nat.card (T : Subgroup K) := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [hOeq, Set.ncard_sdiff_singleton_of_mem h1, h2, hcard]
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty]

end Orbits

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
