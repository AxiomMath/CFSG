module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def StmtLemmaBRel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L Y Z : Subgroup G) (p r : ℕ) (t : G),
    Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → p.Prime → p ≠ 2 →
    (∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y', Y'⁆ = Y' →
      p.Coprime (Nat.card Y')) →
    Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → Y ≤ Subgroup.normalizer (L : Set G) →
    IsPGroup p Y → ⁅Y, Y⁆ = Z → Z ≤ Subgroup.centralizer (Y : Set G) →
    (∀ y ∈ Y, y ^ p ∈ Z) → p ^ 3 ≤ Z.relIndex Y →
    t ∈ M ⊓ Subgroup.normalizer (S : Set G) → t ∈ Subgroup.normalizer (L : Set G) →
    t ∈ Subgroup.normalizer (Y : Set G) →
    r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p → ¬ r ∣ p - 1 →
    (∀ y ∈ Y, t ^ r * y * (t ^ r)⁻¹ * y⁻¹ ∈ Z) → (∃ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∉ Z) →
    (∀ V : Subgroup G, Z ≤ V → V ≤ Y → t ∈ Subgroup.normalizer (V : Set G) → V = Z ∨ V = Y) →
    barM M Y ≤ Subgroup.centralizer (barM M L : Set _)

theorem stmtLemmaB_of_rel (h : StmtLemmaBRel) : StmtLemmaB := by
  intro G _ _ M S L X p r t hK hA hL hX1 hS hp hp2 hcop hXK hXL hXel hXcard htK htL htX hr hr2
    hr3 hrp hrp1 htr htnt hirr
  have hXp : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using hXel.2 x x.2)⟩
  have hcomm : ⁅X, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hXel.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  refine h G M S L X ⊥ p r t hK hA hL hX1 hS hp hp2 hcop hXK hXL hXp hcomm bot_le
    (fun y hy => by rw [hXel.2 y hy]; exact Subgroup.one_mem _)
    (by rw [Subgroup.relIndex_bot_left]; exact hXcard) htK htL htX hr hr2 hr3 hrp hrp1
    (fun y hy => by rw [htr y hy, mul_inv_cancel]; exact Subgroup.one_mem _) ?_
    (fun V _ hVX hV => hirr V hVX hV)
  obtain ⟨x, hx, hne⟩ := htnt
  refine ⟨x, hx, fun hmem => hne ?_⟩
  rw [Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

end CFSG.AGLEmbedding
