module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

variable {G : Type} [Group G]

theorem isGomiAtom_iff_isMinOverBorel (L U A : Subgroup G) :
    IsGomiAtom L U A ↔ IsMinOverBorel L U A := by
  constructor
  · rintro ⟨hlt, hle, hmin⟩
    refine ⟨hle, hlt, fun Q hBQ hQA => ?_⟩
    rcases eq_or_lt_of_le hBQ with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hmin Q h hQA)
  · rintro ⟨hle, hlt, hmin⟩
    refine ⟨hlt, hle, fun Q hBQ hQA => ?_⟩
    rcases hmin Q hBQ.le hQA with h | h
    · exact absurd h.symm (ne_of_lt hBQ)
    · exact h

theorem isGomiAtom_iff_covBy (L U A : Subgroup G) :
    IsGomiAtom L U A ↔ L ⊓ normalizer (U : Set G) ⋖ A ∧ A ≤ L := by
  constructor
  · rintro ⟨hlt, hle, hmin⟩
    refine ⟨?_, hle⟩
    rw [covBy_iff_lt_and_eq_or_eq]
    refine ⟨hlt, fun c hBc hcA => ?_⟩
    rcases eq_or_lt_of_le hBc with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hmin c h hcA)
  · rintro ⟨hcov, hle⟩
    rw [covBy_iff_lt_and_eq_or_eq] at hcov
    obtain ⟨hlt, hmin⟩ := hcov
    refine ⟨hlt, hle, fun Q hBQ hQA => ?_⟩
    rcases hmin Q hBQ.le hQA with h | h
    · exact absurd h.symm (ne_of_lt hBQ)
    · exact h

theorem isGomiAtom_top_iff_covBy (U A : Subgroup G) :
    IsGomiAtom ⊤ U A ↔ normalizer (U : Set G) ⋖ A := by
  rw [isGomiAtom_iff_covBy, top_inf_eq, and_iff_left le_top]

theorem IsGomiAtom.center_le {U A : Subgroup G} (h : IsGomiAtom ⊤ U A) : center G ≤ A :=
  (le_inf le_top (Subgroup.center_le_normalizer (U : Set G))).trans h.1.le

theorem inf_normalizer_eq_map_normalizer_subgroupOf {L U : Subgroup G} (hU : U ≤ L) :
    L ⊓ normalizer (U : Set G) = (normalizer (U.subgroupOf L : Set ↥L)).map L.subtype := by
  rw [← Subgroup.subgroupOf_normalizer_eq hU, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem isGomiAtom_map_subtype_iff (L : Subgroup G) (U A : Subgroup ↥L) :
    IsGomiAtom L (U.map L.subtype) (A.map L.subtype) ↔ IsGomiAtom ⊤ U A := by
  have hB : L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G) =
      (normalizer (U : Set ↥L)).map L.subtype := by
    rw [inf_normalizer_eq_map_normalizer_subgroupOf (Subgroup.map_subtype_le U),
      Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective U]
  let f : Subgroup ↥L ↪o Subgroup G := OrderEmbedding.ofMapLEIff
    (fun H => H.map L.subtype) (fun _ _ => Subgroup.map_subtype_le_map_subtype)
  have hrange : Set.range f = Set.Iic L := by
    ext H
    constructor
    · rintro ⟨H', rfl⟩
      exact Subgroup.map_subtype_le H'
    · intro hH
      exact ⟨H.subgroupOf L, Subgroup.map_subgroupOf_eq_of_le hH⟩
  have h1 : IsGomiAtom L (U.map L.subtype) (A.map L.subtype) ↔
      (L ⊓ normalizer ((U.map L.subtype : Subgroup G) : Set G)) ⋖ A.map L.subtype ∧
        A.map L.subtype ≤ L := isGomiAtom_iff_covBy _ _ _
  have h2 : IsGomiAtom ⊤ U A ↔ (⊤ ⊓ normalizer (U : Set ↥L)) ⋖ A ∧ A ≤ ⊤ :=
    isGomiAtom_iff_covBy _ _ _
  rw [h1, h2, hB, top_inf_eq, and_iff_left (Subgroup.map_subtype_le A), and_iff_left le_top]
  exact Set.OrdConnected.apply_covBy_apply_iff f (hrange ▸ Set.ordConnected_Iic)
    (a := normalizer (U : Set ↥L)) (b := A)

theorem isGomiAtom_iff_subgroupOf {L U A : Subgroup G} (hU : U ≤ L) (hA : A ≤ L) :
    IsGomiAtom L U A ↔ IsGomiAtom ⊤ (U.subgroupOf L) (A.subgroupOf L) := by
  have h := isGomiAtom_map_subtype_iff L (U.subgroupOf L) (A.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hU, Subgroup.map_subgroupOf_eq_of_le hA] at h
  exact h

theorem isSylowOf_top_subgroupOf_iff [Finite G] {p : ℕ} [Fact p.Prime] {L U : Subgroup G}
    (hU : U ≤ L) : IsSylowOf p (U.subgroupOf L) ⊤ ↔ IsSylowOf p U L := by
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← L.subtype.range_eq_map, Subgroup.range_subtype]
  have h := isSylowOf_map_subtype_iff (p := p) L (A := U.subgroupOf L) (B := ⊤)
  rw [Subgroup.map_subgroupOf_eq_of_le hU, htop] at h
  exact h.symm

theorem isGomiAtom_map_mulEquiv_iff {G' : Type} [Group G'] (e : G ≃* G') (L U A : Subgroup G) :
    IsGomiAtom (L.map e.toMonoidHom) (U.map e.toMonoidHom) (A.map e.toMonoidHom) ↔
      IsGomiAtom L U A := by
  have hB : L.map e.toMonoidHom ⊓ normalizer ((U.map e.toMonoidHom : Subgroup G') : Set G') =
      (L ⊓ normalizer (U : Set G)).map e.toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq U e,
      ← Subgroup.map_inf_eq L (normalizer (U : Set G)) e.toMonoidHom e.injective]
  have h1 : IsGomiAtom (L.map e.toMonoidHom) (U.map e.toMonoidHom) (A.map e.toMonoidHom) ↔
      (L.map e.toMonoidHom ⊓
        normalizer ((U.map e.toMonoidHom : Subgroup G') : Set G')) ⋖ A.map e.toMonoidHom ∧
        A.map e.toMonoidHom ≤ L.map e.toMonoidHom := isGomiAtom_iff_covBy _ _ _
  have h2 : IsGomiAtom L U A ↔ (L ⊓ normalizer (U : Set G)) ⋖ A ∧ A ≤ L :=
    isGomiAtom_iff_covBy _ _ _
  rw [h1, h2, hB, Subgroup.map_le_map_iff_of_injective e.injective]
  exact and_congr (apply_covBy_apply_iff (MulEquiv.mapSubgroup e)) Iff.rfl

theorem isGomiAtom_top_map_mulEquiv_iff {G' : Type} [Group G'] (e : G ≃* G')
    (U A : Subgroup G) :
    IsGomiAtom ⊤ (U.map e.toMonoidHom) (A.map e.toMonoidHom) ↔ IsGomiAtom ⊤ U A := by
  have h1 : IsGomiAtom ⊤ (U.map e.toMonoidHom) (A.map e.toMonoidHom) ↔
      normalizer ((U.map e.toMonoidHom : Subgroup G') : Set G') ⋖ A.map e.toMonoidHom :=
    isGomiAtom_top_iff_covBy _ _
  have h2 : IsGomiAtom ⊤ U A ↔ normalizer (U : Set G) ⋖ A := isGomiAtom_top_iff_covBy _ _
  rw [h1, h2, ← Subgroup.map_equiv_normalizer_eq U e]
  exact apply_covBy_apply_iff (MulEquiv.mapSubgroup e)

theorem IsGomiAtom.map_conj {L U A : Subgroup G} (h : IsGomiAtom L U A) {g : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgU : g ∈ normalizer (U : Set G)) :
    IsGomiAtom L U (A.map (MulAut.conj g).toMonoidHom) := by
  have hL : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgL
  have hU : U.map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgU
  have hh := (isGomiAtom_map_mulEquiv_iff (MulAut.conj g) L U A).mpr h
  rwa [hL, hU] at hh

end CFSG.GroupTheory
