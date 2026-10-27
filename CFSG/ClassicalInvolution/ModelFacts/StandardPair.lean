module

public import CFSG.ClassicalInvolution.ModelFacts.Partner
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

section Transport

variable {F : Type} [Field F] {X : Type} [Group X]

theorem linearBlockStandardPair_map_conj {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) (g : X) :
    LinearBlockStandardPair F (W.map (MulAut.conj g).toMonoidHom)
      (U.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  refine ⟨(MulAut.conj g).toMonoidHom.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hW]
  · rw [MonoidHom.ker_comp_of_injective θ (g := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    exact hker
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

end Transport

section Levi

variable {F : Type} [Field F] {K : Type} [Group K]

theorem map_Bs_eq_closure (s : Fin 2) (emb : SL(3, F) →* K) {a b : F → K}
    (ha : ∀ c, emb (blk F s (tv 0 1 c)) = a c) (hb : ∀ c, emb (blk F s (tv 1 0 c)) = b c) :
    (Bs F s).map emb = Subgroup.closure (Set.range a ∪ Set.range b) := by
  rw [map_Bs, MonoidHom.range_eq_map, ← closure_tv_two (F := F), MonoidHom.map_closure]
  congr 1
  ext k
  constructor
  · rintro ⟨y, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · exact Or.inl ⟨c, (ha c).symm⟩
    · exact Or.inr ⟨c, (hb c).symm⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨tv 0 1 c, Or.inl ⟨c, rfl⟩, ha c⟩
    · exact ⟨tv 1 0 c, Or.inr ⟨c, rfl⟩, hb c⟩

omit [Field F] in
theorem closure_range_eq_sup {A B : Subgroup K} {a b : F → K} (hA : (A : Set K) = Set.range a)
    (hB : (B : Set K) = Set.range b) : Subgroup.closure (Set.range a ∪ Set.range b) = A ⊔ B := by
  rw [← hA, ← hB, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]

theorem linearBlockStandardPair_sup {A B A' B' : Subgroup K} {a b a' b' : F → K}
    (hA : (A : Set K) = Set.range a) (hB : (B : Set K) = Set.range b)
    (hA' : (A' : Set K) = Set.range a') (hB' : (B' : Set K) = Set.range b')
    (emb : SL(3, F) →* K) (hker : emb.ker ≤ Subgroup.center SL(3, F))
    (h : ∀ c, emb (tv 0 1 c) = a c ∧ emb (tv 1 0 c) = b c ∧ emb (tv 1 2 c) = a' c ∧
      emb (tv 2 1 c) = b' c) :
    LinearBlockStandardPair F emb.range (A ⊔ B) (A' ⊔ B') := by
  have hU : (B12 F).map emb = A ⊔ B := by
    have := map_Bs_eq_closure (F := F) 0 emb (a := a) (b := b)
      (fun c => by rw [blk_zero_tv01]; exact (h c).1)
      (fun c => by rw [blk_zero_tv10]; exact (h c).2.1)
    exact this.trans (closure_range_eq_sup hA hB)
  have hV : (B23 F).map emb = A' ⊔ B' := by
    have := map_Bs_eq_closure (F := F) 1 emb (a := a') (b := b')
      (fun c => by rw [blk_one_tv01]; exact (h c).2.2.1)
      (fun c => by rw [blk_one_tv10]; exact (h c).2.2.2)
    exact this.trans (closure_range_eq_sup hA' hB')
  have hc : ∀ S : Subgroup SL(3, F), S.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = S := by
    intro S
    have : (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = MonoidHom.id _ := by ext; simp
    rw [this, Subgroup.map_id]
  exact ⟨emb, 1, rfl, hker, Or.inl ⟨by rw [hc]; exact hU, by rw [hc]; exact hV⟩⟩

theorem linearBlockStandardPair_rankOne {r : ℕ} (X : (Fin r → ℤ) → Subgroup K)
    (x : (Fin r → ℤ) → F → K) {i j : Fin r}
    (hXi : (X (Pi.single i 1) : Set K) = Set.range (x (Pi.single i 1)))
    (hXi' : (X (-Pi.single i 1) : Set K) = Set.range (x (-Pi.single i 1)))
    (hXj : (X (Pi.single j 1) : Set K) = Set.range (x (Pi.single j 1)))
    (hXj' : (X (-Pi.single j 1) : Set K) = Set.range (x (-Pi.single j 1)))
    (emb : SL(3, F) →* K) (hker : emb.ker ≤ Subgroup.center SL(3, F))
    (h : ∀ c, emb (tv 0 1 c) = x (Pi.single i 1) c ∧ emb (tv 1 0 c) = x (-Pi.single i 1) c ∧
      emb (tv 1 2 c) = x (Pi.single j 1) c ∧ emb (tv 2 1 c) = x (-Pi.single j 1) c) :
    LinearBlockStandardPair F emb.range (rankOne X i) (rankOne X j) :=
  linearBlockStandardPair_sup hXi hXi' hXj hXj' emb hker h

end Levi

section Group

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {F : Type} [Field F]

theorem exists_standardPair_partner
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {γ₀ δ₀ : Fin D.rank → ℤ} (hγ₀ : IsLongestRoot D γ₀) (hδ₀ : IsLongestRoot D δ₀)
    (hp : IsPartner D.isFiniteType γ₀ δ₀)
    (h₀ : ∃ W, LinearBlockStandardPair F W (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀))
      (D.rootGroup δ₀ ⊔ D.rootGroup (-δ₀)))
    {γ : Fin D.rank → ℤ} (hγ : IsLongestRoot D γ) :
    ∃ δ : Fin D.rank → ℤ, IsLongestRoot D δ ∧ IsPartner D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair F W (D.rootGroup γ ⊔ D.rootGroup (-γ))
        (D.rootGroup δ ⊔ D.rootGroup (-δ)) := by
  refine exists_forall_longest_partner hct hirr hD hγ₀ hδ₀ hp
    (fun U V => ∃ W, LinearBlockStandardPair F W U V) ?_ h₀ hγ
  rintro g U V ⟨W, hW⟩
  exact ⟨_, linearBlockStandardPair_map_conj hW g⟩

end Group

end CFSG.ClassicalInvolution.ModelFacts
