module

public import CFSG.CharacterTheory.PSL2Table.Blocks
public import CFSG.CharacterTheory.PSL2Table.DirectProduct

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.DirectProduct

theorem centralChar_outerProduct {Z L : Type} [Group Z] [Fintype Z] [Group L] [Fintype L]
    {ε : Z → ℂ} (hε1 : ε 1 = 1) (θ : L → ℂ) (z : Z × L → ℂ) :
    BlocksCentralChar (outerProductCharacter ε θ) z =
      ∑ a, ε a * BlocksCentralChar θ (fun x => z (a, x)) := by
  unfold BlocksCentralChar
  simp only [finsum_eq_sum_of_fintype, Fintype.sum_prod_type, outerProductCharacter,
    Prod.fst_one, Prod.snd_one, hε1, one_mul, Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

theorem centralChar_outerProduct_lift {Z L : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    [Group L] [Fintype L] {ε : Z → ℂ} (hε1 : ε 1 = 1) (θ : L → ℂ) (zL : L → ℂ) :
    BlocksCentralChar (outerProductCharacter ε θ) (fun p => if p.1 = 1 then zL p.2 else 0) =
      BlocksCentralChar θ zL := by
  rw [centralChar_outerProduct hε1, Finset.sum_eq_single 1]
  · simp [hε1]
  · intro a _ ha
    simp [ha, BlocksCentralChar]
  · simp

variable (m : Ideal BlocksAlgInt)

theorem isCentralR_slice {Z L : Type} [Group Z] [Group L] {z : Z × L → ℂ}
    (hz : BlocksIsCentralR m z) (a : Z) : BlocksIsCentralR m (fun x => z (a, x)) := by
  refine ⟨fun x => hz.1 _, fun x y => ?_⟩
  have := hz.2 (a, x) (1, y)
  simpa using this

theorem isCentralR_lift (hm : m.IsMaximal) {Z L : Type} [Group Z] [DecidableEq Z] [Group L]
    {zL : L → ℂ} (hz : BlocksIsCentralR m zL) :
    BlocksIsCentralR m (fun p : Z × L => if p.1 = 1 then zL p.2 else 0) := by
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · dsimp only
    split_ifs
    · exact hz.1 _
    · exact localRing_zero m hm
  · obtain ⟨a, x⟩ := p
    obtain ⟨b, y⟩ := q
    simp only [Prod.mk_mul_mk, Prod.inv_mk, conj_eq_one_iff, hz.2 x y]

section OrderTwo

variable {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]

omit [Fintype Z] in
theorem sign_values {ε : Z → ℂ} (hε : ε ∈ ({1, signChar Z} : Set (Z → ℂ))) :
    ε 1 = 1 ∧ ∀ a, ε a = 1 ∨ ε a = -1 := by
  rcases hε with rfl | rfl
  · exact ⟨rfl, fun _ => Or.inl rfl⟩
  · refine ⟨by simp [signChar], fun a => ?_⟩
    simp only [signChar]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem blockOf_prod_card_two (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    (hZ : Nat.card Z = 2) {L : Type} [Group L] [Fintype L] {ε : Z → ℂ}
    (hε : ε ∈ ({1, signChar Z} : Set (Z → ℂ))) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    BlocksBlockOf m (Z × L) (outerProductCharacter ε θ) =
      {χ | ∃ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)), ∃ θ' ∈ BlocksBlockOf m L θ,
        χ = outerProductCharacter ε' θ'} := by
  obtain ⟨hIrr, -⟩ := blocksIrr_prod_card_two hZ L
  have hmem : ∀ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ θ' ∈ BlocksIrr L,
      outerProductCharacter ε' θ' ∈ BlocksIrr (Z × L) := by
    intro ε' hε' θ' hθ'
    rw [hIrr]
    rcases hε' with rfl | rfl
    · exact ⟨θ', hθ', Or.inl rfl⟩
    · exact ⟨θ', hθ', Or.inr rfl⟩
  have hχ := hmem ε hε θ hθ
  obtain ⟨hε1, hεv⟩ := sign_values hε
  ext χ
  constructor
  · intro hχ'
    have hχIrr := hχ'.1
    rw [hIrr] at hχIrr
    obtain ⟨θ', hθ', hχeq⟩ := hχIrr
    have key : ∀ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)), χ = outerProductCharacter ε' θ' →
        θ' ∈ BlocksBlockOf m L θ := by
      rintro ε' hε' rfl
      obtain ⟨hε'1, -⟩ := sign_values hε'
      apply mem_blockOf_of_centralChar_congr m hm L hθ hθ'
      intro zL hzL
      have := sameBlock_centralChar_congr m hm (Z × L) hχ hχ' (isCentralR_lift m hm hzL)
      rwa [centralChar_outerProduct_lift hε'1, centralChar_outerProduct_lift hε1] at this
    rcases hχeq with h | h
    · exact ⟨1, Or.inl rfl, θ', key 1 (Or.inl rfl) h, h⟩
    · exact ⟨signChar Z, Or.inr rfl, θ', key _ (Or.inr rfl) h, h⟩
  · rintro ⟨ε', hε', θ', hθ', rfl⟩
    obtain ⟨hε'1, hε'v⟩ := sign_values hε'
    apply mem_blockOf_of_centralChar_congr m hm (Z × L) hχ (hmem ε' hε' θ' hθ'.1)
    intro z hz
    rw [centralChar_outerProduct hε'1, centralChar_outerProduct hε1, ← Finset.sum_sub_distrib]
    apply localMaxIdeal_sum m hm
    intro a _
    have hR := centralChar_localRing m hm hθ (isCentralR_slice m hz a)
    have hM := sameBlock_centralChar_congr m hm L hθ hθ' (isCentralR_slice m hz a)
    have hsplit : ε' a * BlocksCentralChar θ' (fun x => z (a, x)) -
        ε a * BlocksCentralChar θ (fun x => z (a, x)) =
        (BlocksCentralChar θ' (fun x => z (a, x)) - BlocksCentralChar θ (fun x => z (a, x))) *
          ε' a + (ε' a - ε a) * BlocksCentralChar θ (fun x => z (a, x)) := by
      ring
    rw [hsplit]
    refine localMaxIdeal_add m hm (localMaxIdeal_mul_localRing m hm hM ?_)
      (localMaxIdeal_mul_localRing m hm ?_ hR)
    · rcases hε'v a with h | h <;> rw [h]
      · exact localRing_one m hm
      · exact localRing_neg m (localRing_one m hm)
    · rcases hε'v a with h | h <;> rcases hεv a with h' | h' <;> rw [h, h']
      · simpa using localMaxIdeal_zero m hm
      · exact mem_localMaxIdeal_of_eq_two_mul m hm h2 (localRing_one m hm) (by ring)
      · exact mem_localMaxIdeal_of_eq_two_mul m hm h2 (localRing_neg m (localRing_one m hm))
          (by ring)
      · simpa using localMaxIdeal_zero m hm

theorem principalBlock_prod_card_two (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    (hZ : Nat.card Z = 2) (L : Type) [Group L] [Fintype L] :
    BlocksPrincipalBlock m (Z × L) =
      {χ | ∃ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)), ∃ θ' ∈ BlocksPrincipalBlock m L,
        χ = outerProductCharacter ε' θ'} := by
  have h1 : (fun _ => (1 : ℂ)) = outerProductCharacter (1 : Z → ℂ) (fun _ : L => (1 : ℂ)) := by
    funext p
    simp [outerProductCharacter]
  rw [BlocksPrincipalBlock, h1, blockOf_prod_card_two m hm h2 hZ (Or.inl rfl) (trivial_mem_irr L)]
  rfl

theorem blocks_prod_card_two (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    (hZ : Nat.card Z = 2) (L : Type) [Group L] [Fintype L] :
    {B | BlocksIsBlock m (Z × L) B} =
      (fun B : Set (L → ℂ) => {χ | ∃ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∃ θ ∈ B,
        χ = outerProductCharacter ε θ}) '' {B | BlocksIsBlock m L B} := by
  obtain ⟨hIrr, -⟩ := blocksIrr_prod_card_two hZ L
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    rw [hIrr] at hχ
    obtain ⟨θ, hθ, h | h⟩ := hχ
    · exact ⟨_, ⟨θ, hθ, rfl⟩, by rw [h, blockOf_prod_card_two m hm h2 hZ (Or.inl rfl) hθ]⟩
    · exact ⟨_, ⟨θ, hθ, rfl⟩, by rw [h, blockOf_prod_card_two m hm h2 hZ (Or.inr rfl) hθ]⟩
  · rintro ⟨B', ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨outerProductCharacter 1 θ, ?_, (blockOf_prod_card_two m hm h2 hZ (Or.inl rfl) hθ).symm⟩
    rw [hIrr]
    exact ⟨θ, hθ, Or.inl rfl⟩

end OrderTwo

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem prod_psl2_blocks_of_mod_eight_eq_three (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (h8 : Fintype.card F % 8 = 3) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ : Nat.card Z = 2) :
    BlocksPrincipalBlock m (Z × PSL(2, F)) = {χ | ∃ ε ∈ ({1, signChar Z} : Set (Z → ℂ)),
      ∃ θ ∈ ({1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} : Set (PSL(2, F) → ℂ)),
        χ = outerProductCharacter ε θ} ∧
    (∀ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      BlocksBlockOf m (Z × PSL(2, F)) (outerProductCharacter ε (principal α)) =
        {outerProductCharacter 1 (principal α),
          outerProductCharacter (signChar Z) (principal α)}) ∧
    (∀ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      BlocksBlockOf m (Z × PSL(2, F)) (outerProductCharacter ε (discrete β)) =
        {χ | ∃ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)),
          ∃ θ ∈ ({discrete β, discrete (β * nonsplitQuadChar ν)} : Set (PSL(2, F) → ℂ)),
            χ = outerProductCharacter ε' θ}) := by
  obtain ⟨hP, hR, hD⟩ := psl2_blocks_of_mod_eight_eq_three hF hq hν hψ h8 m hm h2
  refine ⟨?_, fun ε hε α hα => ?_, fun ε hε β hβ => ?_⟩
  · rw [principalBlock_prod_card_two m hm h2 hZ, hP]
  · rw [blockOf_prod_card_two m hm h2 hZ hε (principal_mem_blocksIrr hF hq hν hα), hR α hα]
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      exists_eq_left]
    constructor
    · rintro ⟨ε', hε' | hε', rfl⟩ <;> subst hε'
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, Or.inl rfl, rfl⟩
      · exact ⟨signChar Z, Or.inr rfl, rfl⟩
  · rw [blockOf_prod_card_two m hm h2 hZ hε (discrete_mem_blocksIrr hF hq hν hβ),
      (hD β hβ).2.2]

theorem prod_psl2_blocks_of_mod_eight_eq_five (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (h8 : Fintype.card F % 8 = 5) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) {Z : Type} [Group Z] [Fintype Z] [DecidableEq Z]
    (hZ : Nat.card Z = 2) :
    BlocksPrincipalBlock m (Z × PSL(2, F)) = {χ | ∃ ε ∈ ({1, signChar Z} : Set (Z → ℂ)),
      ∃ θ ∈ ({1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} : Set (PSL(2, F) → ℂ)),
        χ = outerProductCharacter ε θ} ∧
    (∀ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      BlocksBlockOf m (Z × PSL(2, F)) (outerProductCharacter ε (discrete β)) =
        {outerProductCharacter 1 (discrete β),
          outerProductCharacter (signChar Z) (discrete β)}) ∧
    (∀ ε ∈ ({1, signChar Z} : Set (Z → ℂ)), ∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      BlocksBlockOf m (Z × PSL(2, F)) (outerProductCharacter ε (principal α)) =
        {χ | ∃ ε' ∈ ({1, signChar Z} : Set (Z → ℂ)),
          ∃ θ ∈ ({principal α, principal (α * splitQuadChar F)} : Set (PSL(2, F) → ℂ)),
            χ = outerProductCharacter ε' θ}) := by
  obtain ⟨hP, hD, hR⟩ := psl2_blocks_of_mod_eight_eq_five hF hq hν hψ h8 m hm h2
  refine ⟨?_, fun ε hε β hβ => ?_, fun ε hε α hα => ?_⟩
  · rw [principalBlock_prod_card_two m hm h2 hZ, hP]
  · rw [blockOf_prod_card_two m hm h2 hZ hε (discrete_mem_blocksIrr hF hq hν hβ), hD β hβ]
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      exists_eq_left]
    constructor
    · rintro ⟨ε', hε' | hε', rfl⟩ <;> subst hε'
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, Or.inl rfl, rfl⟩
      · exact ⟨signChar Z, Or.inr rfl, rfl⟩
  · rw [blockOf_prod_card_two m hm h2 hZ hε (principal_mem_blocksIrr hF hq hν hα),
      (hR α hα).2.2]

end CFSG.PSL2Table
