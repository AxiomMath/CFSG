module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoNative
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoTorus

public noncomputable section

open scoped MatrixGroups

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  TauCeti CFSG.Open

section Assembly


variable {K : Type} [Field K]

@[expose] def PlaneCoverOf {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (ψ : H →* G), ¬ p ∣ Nat.card ψ.ker ∧
    (∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤) ∧ X ≤ ψ.range

@[expose] def frameTorusGroup (σ : K →+* K) : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  (⨆ i, (frameHom σ i).range) ⊔ (torusG σ).range

@[expose] def leviRootGroups (σ : K →+* K) : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  (orbitRankOneGroup TwistTag.E6 K σ ⟨0, by decide⟩ ⊔
    orbitRankOneGroup TwistTag.E6 K σ ⟨1, by decide⟩ ⊔
    orbitRankOneGroup TwistTag.E6 K σ ⟨2, by decide⟩).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)

@[expose] def centerRootGroup (σ : K →+* K) : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  (orbitRankOneGroup TwistTag.E6 K σ ⟨3, by decide⟩).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)

@[expose] def TwE6SU6Cover : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ), ℓ.Prime → 1 ≤ f →
    Nat.card K = (ℓ ^ f) ^ 2 → (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → p ∣ ℓ ^ f + 1 →
      PlaneCoverOf p (frameTorusGroup σ.toRingHom ⊔ leviRootGroups σ.toRingHom)

@[expose] def TwE6D4Cover : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ), ℓ.Prime → 1 ≤ f →
    Nat.card K = (ℓ ^ f) ^ 2 → (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → p ∣ ℓ ^ f + 1 →
      PlaneCoverOf p (frameTorusGroup σ.toRingHom ⊔ centerRootGroup σ.toRingHom)

theorem eq_top_of_orbitRankOneGroup_le {σ : K ≃+* K}
    (M : Subgroup ↥(twistedE6RootGroup K σ))
    (hM : ∀ a : Fin TwistTag.E6.foldedTag.rank,
      orbitRankOneGroup TwistTag.E6 K σ.toRingHom a ≤ M.map (twistedE6RootGroup K σ).subtype) :
    M = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : ModGL TwistTag.E6.tag K) ∈ ⨆ a, orbitRankOneGroup TwistTag.E6 K σ.toRingHom a := by
    rw [← graphFixedRootGroup_eq_iSup_orbitRankOneGroup σ.surjective]
    exact g.2
  obtain ⟨m, hm, hmg⟩ := (iSup_le hM) hg
  have : m = g := Subtype.ext hmg
  exact this ▸ hm

theorem orbitRankOneGroup_le_graphFixedRootGroup' (σ : K →+* K)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitRankOneGroup TwistTag.E6 K σ a ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  (Subgroup.closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (orbitX_mem_graphFixedPosUnipotent _ σ a _)
    · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ K σ
        (orbitY_mem_graphFixedNegUnipotent _ σ a _))

theorem le_map_subtype_of_mem {σ : K →+* K} {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    {M : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hY : Y ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (h : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ), (y : ModGL TwistTag.E6.tag K) ∈ Y →
      y ∈ M) :
    Y ≤ M.map (graphFixedRootGroup TwistTag.E6 K σ).subtype := fun y hy =>
  ⟨⟨y, hY hy⟩, h _ hy, rfl⟩

theorem twE6TwoNative_ge_seven (h1 : TwE6SU6Cover) (h2 : TwE6D4Cover) :
    TwE6TwoNative (fun p => 7 ≤ p) := by
  refine twE6TwoNative_of_covers fun K _ _ σ ℓ f hℓ hf hK hσ p hpF hp5 hp7 hpq => ?_
  obtain ⟨H₁, _, _, ψ₁, hk₁, hH₁, hX₁⟩ := h1 K σ ℓ f hℓ hf hK hσ p hp7 hpq
  obtain ⟨H₂, _, _, ψ₂, hk₂, hH₂, hX₂⟩ := h2 K σ ℓ f hℓ hf hK hσ p hp7 hpq
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  have hpq' : p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) + 1 := by
    rw [hkcard]; exact hpq
  have hX₁' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      y ∈ leviRootGroups σ.toRingHom → y ∈ ψ₁.range := fun y hy =>
    hX₁ (Subgroup.mem_sup_right hy)
  have hX₂' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      y ∈ centerRootGroup σ.toRingHom → y ∈ ψ₂.range := fun y hy =>
    hX₂ (Subgroup.mem_sup_right hy)
  have hclose : ∀ M : Subgroup ↥(twistedE6RootGroup K σ), ψ₁.range ≤ M → ψ₂.range ≤ M →
      M = ⊤ := by
    intro M hM₁ hM₂
    refine eq_top_of_orbitRankOneGroup_le M fun a => ?_
    refine le_map_subtype_of_mem (orbitRankOneGroup_le_graphFixedRootGroup' _ _) fun y hy => ?_
    match a, hy with
    | ⟨0, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))))
    | ⟨1, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))))
    | ⟨2, _⟩, hy =>
      exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hy)))
    | ⟨3, _⟩, hy => exact hM₂ (hX₂' y (Subgroup.mem_subgroupOf.2 hy))
    | ⟨n + 4, h⟩, _ => exact absurd h (by change ¬ n + 4 < 4; omega)
  refine hasTwoCovers_of_frame hp5 hpq' (frameHom σ.toRingHom) (frameHom_injective σ.toRingHom)
    (fun i j hij A B => frameHom_commute σ.toRingHom hij A B) (torusG σ.toRingHom).range
    (fun a ha i y => ?_) (factorization_card_le_frame_torusG hℓ hf K hK σ hσ hpF.out hp7 hpq)
    H₁ H₂ ψ₁ ψ₂ hk₁ hk₂ hH₁ hH₂ hclose (le_trans le_sup_left hX₁)
    (le_trans le_sup_left hX₂) _
  obtain ⟨t, rfl⟩ := ha
  exact torusG_commute_frame _ (frameHom_mem_rootPair σ.toRingHom) t i y

end Assembly

section Final


theorem seitzExcHighTwE6TwoGeSeven_of_covers (h1 : TwE6SU6Cover) (h2 : TwE6D4Cover) :
    SeitzExcHighTwE6TwoGeSeven :=
  seitzExcHighTwE6Two_of_native_for (twE6TwoNative_ge_seven h1 h2)

end Final

end CFSG.LieType.SeitzGeneration.ExcHigh
