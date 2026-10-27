module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.Chevalley.BruhatCellFactorization

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

theorem rootSubgroup_le_posUnipotent_of_height_pos {R : Type*} [CommRing R] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hpos : 0 < height α) : rootSubgroup τ R α ≤ posUnipotent τ R :=
  le_iSup₂_of_le α ⟨hα, hpos⟩ le_rfl

theorem borelGroup_le_adjointGroup_of_field {K : Type*} [Field K] :
    borelGroup τ K ≤ adjointGroup τ K :=
  ((triangular_borel_structure τ K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem exists_map_conj_canonicalRep_sup_le_posUnipotent
    {K : Type} [Field K] {s : Fin τ.rank → ℤ} (hs : IsRoot τ s) (hne : s ≠ -highRoot τ) :
    ∃ v : WeylGroup τ, (rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K s).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).toMonoidHom ≤ posUnipotent τ K := by
  obtain ⟨v, h1, h2⟩ := exists_height_smul_highRoot_pos hs hne
  refine ⟨v, ?_⟩
  rw [Subgroup.map_sup, (canonical_weyl_root_transport τ K).2.1 v _ (isRoot_highRoot τ),
    (canonical_weyl_root_transport τ K).2.1 v _ hs]
  exact sup_le
    (rootSubgroup_le_posUnipotent_of_height_pos (IsRoot.smul (isRoot_highRoot τ) v) h1)
    (rootSubgroup_le_posUnipotent_of_height_pos (IsRoot.smul hs v) h2)

section RootCommutators


theorem commute_pinnedX_highRoot (R : Type) [CommRing R] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβp : 0 < height β) (a b : R) :
    Commute (pinnedX τ R β a) (pinnedX τ R (highRoot τ) b) := by
  by_cases hβr : β = highRoot τ
  · subst hβr
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hc := commutator_rootSubgroup_le R hβ (isRoot_highRoot τ) hβp (height_highRoot_pos τ)
      hβr
    have hbot : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • β + b • highRoot τ), rootSubgroup τ R γ) = ⊥ := by
      refine iSup₂_eq_bot.2 ?_
      rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
      exact absurd hγ (not_isRoot_nsmul_add_nsmul_highRoot hβp ha hb)
    rw [hbot] at hc
    have hmem := hc (Subgroup.commutator_mem_commutator (mem_rootSubgroup.2 ⟨a, rfl⟩)
      (mem_rootSubgroup.2 ⟨b, rfl⟩))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem posUnipotent_le_centralizer_highRoot (R : Type) [CommRing R] :
    posUnipotent τ R ≤ Subgroup.centralizer
      (rootSubgroup τ R (highRoot τ) : Set (Module.End R (RootModule τ R))ˣ) := by
  refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hh
  exact (commute_pinnedX_highRoot R hβ.1 hβ.2 a b).eq.symm

theorem borelGroup_le_normalizer_highRoot (R : Type) [CommRing R] :
    borelGroup τ R ≤ Subgroup.normalizer
      (rootSubgroup τ R (highRoot τ) : Set (Module.End R (RootModule τ R))ˣ) := by
  refine sup_le ((Subgroup.closure_le _).2 ?_)
    ((posUnipotent_le_centralizer_highRoot R).trans (Subgroup.centralizer_le_normalizer _))
  rintro _ ⟨⟨i, t⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_conj_torusElt_rootSubgroup i t (isRoot_highRoot τ)

theorem map_conj_highRoot_of_mem_borelGroup {R : Type} [CommRing R]
    {b : (Module.End R (RootModule τ R))ˣ} (hb : b ∈ borelGroup τ R) :
    (rootSubgroup τ R (highRoot τ)).map (MulAut.conj b).toMonoidHom =
      rootSubgroup τ R (highRoot τ) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (borelGroup_le_normalizer_highRoot R hb)

variable {K : Type} [Field K]

theorem highRoot_pair_of_mem_bruhatCell {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ bruhatCell τ K w) :
    ∃ b ∈ borelGroup τ K,
      rootSubgroup τ K (highRoot τ) ⊔
          (rootSubgroup τ K (highRoot τ)).map (MulAut.conj g).toMonoidHom =
        (rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K (w • highRoot τ)).map
          (MulAut.conj b).toMonoidHom ∧
      (w • highRoot τ ≠ -highRoot τ → ∃ v : WeylGroup τ,
        (rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K (w • highRoot τ)).map
          (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).toMonoidHom ≤ posUnipotent τ K) := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hg
  refine ⟨b, hb, ?_, fun hne => ?_⟩
  · rw [Subgroup.map_sup, map_conj_mul, map_conj_mul, map_conj_highRoot_of_mem_borelGroup hb',
      (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_highRoot τ),
      map_conj_highRoot_of_mem_borelGroup hb]
  · exact exists_map_conj_canonicalRep_sup_le_posUnipotent (IsRoot.smul (isRoot_highRoot τ) w) hne

section Bruhat


theorem exists_mem_bruhatCell_of_mem_adjointGroup {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    ∃ w : WeylGroup τ, g ∈ bruhatCell τ K w := by
  have h : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
  rw [adjointGroup_eq_iUnion_bruhatCell] at h
  exact Set.mem_iUnion.1 h

theorem highRoot_pair_le_conj_posUnipotent_or_eq_conj {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K) :
    (∃ c ∈ adjointGroup τ K,
      rootSubgroup τ K (highRoot τ) ⊔
          (rootSubgroup τ K (highRoot τ)).map (MulAut.conj g).toMonoidHom ≤
        (posUnipotent τ K).map (MulAut.conj c).toMonoidHom) ∨
    ∃ c ∈ borelGroup τ K,
      rootSubgroup τ K (highRoot τ) ⊔
          (rootSubgroup τ K (highRoot τ)).map (MulAut.conj g).toMonoidHom =
        (rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K (-highRoot τ)).map
          (MulAut.conj c).toMonoidHom := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hg
  obtain ⟨b, hb, heq, hpos⟩ := highRoot_pair_of_mem_bruhatCell hw
  by_cases hne : w • highRoot τ = -highRoot τ
  · rw [hne] at heq
    exact Or.inr ⟨b, hb, heq⟩
  · have hbC : b ∈ adjointGroup τ K := borelGroup_le_adjointGroup_of_field hb
    obtain ⟨v, hv⟩ := hpos hne
    set n := canonicalRep (coxeterSystem τ) K v
    refine Or.inl ⟨b * n⁻¹, mul_mem hbC (inv_mem (canonicalRep_mem_adjointGroup _ K v)), ?_⟩
    rw [heq, map_conj_mul]
    refine Subgroup.map_mono ?_
    have h := Subgroup.map_mono (f := (MulAut.conj n⁻¹).toMonoidHom) hv
    rwa [← map_conj_mul, inv_mul_cancel, map_conj_one] at h

theorem isPGroup_posUnipotent_of_charP [Finite K] (p : ℕ) [CharP K p] :
    IsPGroup p (posUnipotent τ K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K p
  refine IsPGroup.of_card
    (n := (n : ℕ) * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) ?_
  rw [card_posUnipotent, Nat.card_eq_fintype_card, hcard, ← pow_mul]

theorem isPGroup_or_eq_conj_highRoot_pair [Finite K] (p : ℕ) [CharP K p] {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K) :
    IsPGroup p ↥(rootSubgroup τ K (highRoot τ) ⊔
        (rootSubgroup τ K (highRoot τ)).map (MulAut.conj g).toMonoidHom) ∨
    ∃ c ∈ adjointGroup τ K,
      rootSubgroup τ K (highRoot τ) ⊔
          (rootSubgroup τ K (highRoot τ)).map (MulAut.conj g).toMonoidHom =
        (rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K (-highRoot τ)).map
          (MulAut.conj c).toMonoidHom := by
  rcases highRoot_pair_le_conj_posUnipotent_or_eq_conj hg with ⟨c, -, hc⟩ | ⟨c, hc, h⟩
  · exact Or.inl (((isPGroup_posUnipotent_of_charP p).map _).to_le hc)
  · exact Or.inr ⟨c, borelGroup_le_adjointGroup_of_field hc, h⟩

theorem isPGroup_or_eq_conj_of_conj_highRoot [Finite K] (p : ℕ) [CharP K p]
    {x y : ModGL τ K} (hx : x ∈ adjointGroup τ K) (hy : y ∈ adjointGroup τ K) :
    IsPGroup p ↥((rootSubgroup τ K (highRoot τ)).map (MulAut.conj x).toMonoidHom ⊔
        (rootSubgroup τ K (highRoot τ)).map (MulAut.conj y).toMonoidHom) ∨
    ∃ c ∈ adjointGroup τ K,
      (rootSubgroup τ K (highRoot τ)).map (MulAut.conj x).toMonoidHom ⊔
          (rootSubgroup τ K (highRoot τ)).map (MulAut.conj y).toMonoidHom =
        (rootSubgroup τ K (highRoot τ) ⊔ rootSubgroup τ K (-highRoot τ)).map
          (MulAut.conj c).toMonoidHom := by
  have e : (rootSubgroup τ K (highRoot τ)).map (MulAut.conj x).toMonoidHom ⊔
      (rootSubgroup τ K (highRoot τ)).map (MulAut.conj y).toMonoidHom =
      (rootSubgroup τ K (highRoot τ) ⊔
        (rootSubgroup τ K (highRoot τ)).map (MulAut.conj (x⁻¹ * y)).toMonoidHom).map
          (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.map_sup, ← map_conj_mul, mul_inv_cancel_left]
  rw [e]
  rcases isPGroup_or_eq_conj_highRoot_pair p (mul_mem (inv_mem hx) hy) with h | ⟨c, hc, h⟩
  · exact Or.inl (h.map _)
  · refine Or.inr ⟨x * c, mul_mem hx hc, ?_⟩
    rw [h, map_conj_mul]

theorem isPGroup_or_eq_conj_highRoot_pair_subgroupOf [Finite K] (p : ℕ) [CharP K p]
    (g : adjointGroup τ K) :
    IsPGroup p ↥((rootSubgroup τ K (highRoot τ)).subgroupOf (adjointGroup τ K) ⊔
        ((rootSubgroup τ K (highRoot τ)).subgroupOf (adjointGroup τ K)).map
          (MulAut.conj g).toMonoidHom) ∨
    ∃ c : adjointGroup τ K,
      (rootSubgroup τ K (highRoot τ)).subgroupOf (adjointGroup τ K) ⊔
          ((rootSubgroup τ K (highRoot τ)).subgroupOf (adjointGroup τ K)).map
            (MulAut.conj g).toMonoidHom =
        ((rootSubgroup τ K (highRoot τ)).subgroupOf (adjointGroup τ K) ⊔
          (rootSubgroup τ K (-highRoot τ)).subgroupOf (adjointGroup τ K)).map
            (MulAut.conj c).toMonoidHom := by
  have hinj : Function.Injective (Subgroup.map (adjointGroup τ K).subtype) :=
    Subgroup.map_injective (adjointGroup τ K).subtype_injective
  have hsub : ∀ α, ((rootSubgroup τ K α).subgroupOf (adjointGroup τ K)).map
      (adjointGroup τ K).subtype = rootSubgroup τ K α := fun α => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (rootSubgroup_le_adjointGroup α)]
  have hconj : ∀ (H : Subgroup (adjointGroup τ K)) (x : adjointGroup τ K),
      (H.map (MulAut.conj x).toMonoidHom).map (adjointGroup τ K).subtype =
        (H.map (adjointGroup τ K).subtype).map (MulAut.conj (x : ModGL τ K)).toMonoidHom :=
    fun H x => by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
  rcases isPGroup_or_eq_conj_highRoot_pair p g.2 with h | ⟨c, hc, h⟩
  · left
    rw [← hsub (highRoot τ), ← hconj, ← Subgroup.map_sup] at h
    exact h.of_equiv (Subgroup.equivMapOfInjective _ _ (adjointGroup τ K).subtype_injective).symm
  · right
    refine ⟨⟨c, hc⟩, hinj ?_⟩
    rw [Subgroup.map_sup, hconj, hconj, Subgroup.map_sup, hsub, hsub]
    exact h

end Bruhat

end RootCommutators

end CFSG.SeitzReduction
