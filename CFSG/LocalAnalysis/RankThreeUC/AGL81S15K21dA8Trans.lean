module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dA8Proof

@[expose] def K21dHyp {S : Type} [Group S] [Finite S] (U D E : Subgroup S) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧ U ≤ D ∧ Group.IsSolvable ↥D ∧ E ≤ D ∧
    CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
    ∃ u ∈ U ⊓ Subgroup.normalizer (E : Set S), ∀ e ∈ E, u * e * u⁻¹ = e⁻¹

@[expose] def K21dConcl {S : Type} [Group S] [Finite S] (U E : Subgroup S) : Prop :=
  ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧
    Nat.card ↥(U ⊓ Subgroup.normalizer (E : Set S) ⊓ Subgroup.centralizer ({x} : Set S)) ≠
      Nat.card ↥(U ⊓ Subgroup.normalizer (E : Set S) ⊓ Subgroup.centralizer ({y} : Set S))

theorem k21dGeomAt_iff (S : Type) [Group S] [Finite S] :
    K21dGeomAt S ↔ ∀ U D E : Subgroup S, K21dHyp U D E → K21dConcl U E := by
  constructor
  · intro h U D E ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact h U D E h1 h2 h3 h4 h5 h6 h7
  · intro h U D E h1 h2 h3 h4 h5 h6 h7
    exact h U D E ⟨h1, h2, h3, h4, h5, h6, h7⟩

section Transport

variable {S S' : Type} [Group S] [Group S']

theorem map_mem_iff (φ : S ≃* S') (E : Subgroup S) (x : S) :
    φ x ∈ E.map φ.toMonoidHom ↔ x ∈ E :=
  Subgroup.mem_map_iff_mem φ.injective

theorem map_mem_normalizer_iff (φ : S ≃* S') (E : Subgroup S) (g : S) :
    φ g ∈ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup S') : Set S') ↔
      g ∈ Subgroup.normalizer (E : Set S) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have hx := h (φ x)
    rwa [← map_inv, ← map_mul, ← map_mul, map_mem_iff, map_mem_iff] at hx
  · intro h x'
    obtain ⟨x, rfl⟩ := φ.surjective x'
    rw [← map_inv, ← map_mul, ← map_mul, map_mem_iff, map_mem_iff]
    exact h x

theorem card_triple_map (φ : S ≃* S') (U E : Subgroup S) (x : S) :
    Nat.card ↥(U.map φ.toMonoidHom ⊓ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup S') :
        Set S') ⊓ Subgroup.centralizer ({φ.toMonoidHom x} : Set S')) =
      Nat.card ↥(U ⊓ Subgroup.normalizer (E : Set S) ⊓ Subgroup.centralizer ({x} : Set S)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv ?_)).symm
  intro g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, map_mem_iff, map_mem_normalizer_iff, MulEquiv.coe_toMonoidHom, ← map_mul,
    EmbeddingLike.apply_eq_iff_eq]

theorem K21dConcl.of_map [Finite S] [Finite S'] (φ : S ≃* S') {U E : Subgroup S}
    (h : K21dConcl (U.map φ.toMonoidHom) (E.map φ.toMonoidHom)) : K21dConcl U E := by
  obtain ⟨x', hx', y', hy', hx1, hy1, hne⟩ := h
  obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.1 hx'
  obtain ⟨y, hyE, rfl⟩ := Subgroup.mem_map.1 hy'
  refine ⟨x, hxE, y, hyE, fun h => hx1 ?_, fun h => hy1 ?_, ?_⟩
  · simp [h]
  · simp [h]
  · rwa [card_triple_map, card_triple_map] at hne

theorem isSylowOf_map [Finite S] [Finite S'] (φ : S ≃* S') {U : Subgroup S}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (U.map φ.toMonoidHom) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨-, hp, hdvd⟩ := h
  refine ⟨le_top, hp.of_equiv (U.equivMapOfInjective φ.toMonoidHom φ.injective), ?_⟩
  rw [Subgroup.relIndex_top_right, Subgroup.index_map_of_bijective φ.bijective]
  rwa [Subgroup.relIndex_top_right] at hdvd

theorem isSolvable_map (φ : S ≃* S') {D : Subgroup S} (h : Group.IsSolvable ↥D) :
    Group.IsSolvable ↥(D.map φ.toMonoidHom) :=
  haveI := h
  solvable_of_surjective (f := (D.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom)
    (D.equivMapOfInjective φ.toMonoidHom φ.injective).surjective

theorem isElemAbelian_map (φ : S ≃* S') {E : Subgroup S} (h : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (E.map φ.toMonoidHom) := by
  obtain ⟨hc, h3⟩ := h
  refine ⟨Subgroup.map_isMulCommutative E φ.toMonoidHom, ?_⟩
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hx'
  rw [← map_pow, h3 x hx, map_one]

theorem K21dHyp.map [Finite S] [Finite S'] (φ : S ≃* S') {U D E : Subgroup S}
    (h : K21dHyp U D E) :
    K21dHyp (U.map φ.toMonoidHom) (D.map φ.toMonoidHom) (E.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, u, hu, hinv⟩ := h
  refine ⟨isSylowOf_map φ h1, Subgroup.map_mono h2, isSolvable_map φ h3, Subgroup.map_mono h4,
    isElemAbelian_map φ h5, ?_, φ u, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact h6
  · rw [Subgroup.mem_inf] at hu ⊢
    exact ⟨(map_mem_iff φ U u).2 hu.1, (map_mem_normalizer_iff φ E u).2 hu.2⟩
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 he'
    rw [MulEquiv.coe_toMonoidHom, ← map_inv, ← map_mul, ← map_mul, hinv e he, map_inv]

end Transport

theorem k21dGeomAt_of_mulEquiv {S S' : Type} [Group S] [Finite S] [Group S'] [Finite S']
    (φ : S ≃* S') (h : K21dGeomAt S') : K21dGeomAt S := by
  rw [k21dGeomAt_iff] at h ⊢
  intro U D E hUDE
  exact K21dConcl.of_map φ (h _ _ _ (K21dHyp.map φ hUDE))

end K21dA8Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
