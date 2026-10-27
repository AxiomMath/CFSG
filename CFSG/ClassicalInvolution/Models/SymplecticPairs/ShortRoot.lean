module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat blockHom coe_blockHom blockHom_injective blockHom_upper
  blockHom_lower mem_closure_sl2 x x_eq)
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E
  elt_difference_eq_leviHom mat_equiv_leviHom ne_succ' stdVec_shortPos_eq stdVec_shortNeg_eq
  stdVec_positiveLong_eq stdVec_negativeLong_eq)
open scoped MatrixGroups

variable {K : Type} [Field K] {m n : ℕ}

section Short

variable {i j : Fin n}

variable (K) in
@[expose] noncomputable def shortBlock (hij : i ≠ j) : SL(2, K) →* StatedSp n K :=
  (equivStatedSp n K).toMonoidHom.comp
    ((TauCeti.GLSymplecticFin.leviHom (m := n) (R := K)).comp (blockHom K hij))

theorem mat_shortBlock (hij : i ≠ j) (A : SL(2, K)) :
    mat n K (shortBlock K hij A) =
      fromBlocks (blockMat i j (A : Matrix (Fin 2) (Fin 2) K)) 0 0
        (blockMat i j ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))ᵀ := by
  have h := mat_equiv_leviHom (blockHom K hij A)
  rw [← map_inv, coe_blockHom] at h
  exact h

theorem shortBlock_injective (hij : i ≠ j) : Function.Injective (shortBlock K hij) :=
  (equivStatedSp n K).injective.comp
    (TauCeti.GLSymplecticFin.leviHom_injective.comp (blockHom_injective hij))

theorem shortBlock_sl2Upper (hij : i ≠ j) (c : K) :
    shortBlock K hij (sl2Upper c) = elt (.difference i j hij) c := by
  rw [elt_difference_eq_leviHom, shortBlock, MonoidHom.comp_apply, MonoidHom.comp_apply,
    blockHom_upper]
  rfl

theorem shortBlock_sl2Lower (hij : i ≠ j) (c : K) :
    shortBlock K hij (sl2Lower c) = elt (.difference j i hij.symm) c := by
  rw [elt_difference_eq_leviHom, shortBlock, MonoidHom.comp_apply, MonoidHom.comp_apply,
    blockHom_lower]
  rfl

theorem inl_mem_union_iff {i j a : Fin n} :
    (Sum.inl a : Fin n ⊕ Fin n) ∈ coords i ∪ coords j ↔ a = i ∨ a = j := by
  simp [coords, or_comm]

theorem inr_mem_union_iff {i j a : Fin n} :
    (Sum.inr a : Fin n ⊕ Fin n) ∈ coords i ∪ coords j ↔ a = i ∨ a = j := by
  simp [coords, or_comm]

theorem isSupp_shortBlock (hij : i ≠ j) (A : SL(2, K)) :
    IsSupp (coords i ∪ coords j) (mat n K (shortBlock K hij A)) := by
  rw [mat_shortBlock]
  intro r t hrt
  rcases r with a | a <;> rcases t with b | b
  · rw [Matrix.fromBlocks_apply₁₁]
    have h : ¬((a = i ∨ a = j) ∧ (b = i ∨ b = j)) := fun h =>
      hrt ⟨inl_mem_union_iff.2 h.1, inl_mem_union_iff.2 h.2⟩
    rw [blockMat_apply_of_not hij _ h]
    simp [Matrix.one_apply]
  · simp [Matrix.fromBlocks_apply₁₂]
  · simp [Matrix.fromBlocks_apply₂₁]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    have h : ¬((b = i ∨ b = j) ∧ (a = i ∨ a = j)) := fun h =>
      hrt ⟨inr_mem_union_iff.2 h.2, inr_mem_union_iff.2 h.1⟩
    rw [blockMat_apply_of_not hij _ h]
    simp [Matrix.one_apply, eq_comm]

theorem commute_shortBlock_longBlock (hij : i ≠ j) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j)
    (A B : SL(2, K)) : Commute (shortBlock K hij A) (longBlock K n k B) := by
  have hsub : coords k ⊆ (coords i ∪ coords j)ᶜ := by
    intro a ha hmem
    rcases mem_coords.1 ha with rfl | rfl
    · rcases inl_mem_union_iff.1 hmem with h | h
      · exact hki h
      · exact hkj h
    · rcases inr_mem_union_iff.1 hmem with h | h
      · exact hki h
      · exact hkj h
  refine commute_suppGroup_compl (isSupp_shortBlock hij A) ?_
  exact suppGroup_mono hsub (by rw [← longRootSp2_eq_suppGroup]; exact ⟨B, rfl⟩)

theorem commute_shortBlock_shortBlock {k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (A B : SL(2, K)) :
    Commute (shortBlock K hij A) (shortBlock K hkl B) := by
  have hsub : coords k ∪ coords l ⊆ (coords i ∪ coords j)ᶜ := by
    intro a ha hmem
    rcases ha with ha | ha
    · rcases mem_coords.1 ha with rfl | rfl
      · rcases inl_mem_union_iff.1 hmem with h | h
        · exact hik h.symm
        · exact hjk h.symm
      · rcases inr_mem_union_iff.1 hmem with h | h
        · exact hik h.symm
        · exact hjk h.symm
    · rcases mem_coords.1 ha with rfl | rfl
      · rcases inl_mem_union_iff.1 hmem with h | h
        · exact hil h.symm
        · exact hjl h.symm
      · rcases inr_mem_union_iff.1 hmem with h | h
        · exact hil h.symm
        · exact hjl h.symm
  exact commute_suppGroup_compl (isSupp_shortBlock hij A)
    (suppGroup_mono hsub (isSupp_shortBlock hkl B))

theorem shortBlock_mulVec_inl_left (hij : i ≠ j) (A : SL(2, K)) :
    mat n K (shortBlock K hij A) *ᵥ Pi.single (Sum.inl i) 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 • (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → K) +
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 • (Pi.single (Sum.inl j) 1 : Fin n ⊕ Fin n → K) := by
  funext r
  rw [mulVec_single_one_apply, mat_shortBlock]
  rcases r with a | a
  · rw [Matrix.fromBlocks_apply₁₁]
    by_cases ha : a = i
    · subst ha
      simp [blockMat, hij]
    · by_cases hb : a = j
      · subst hb
        simp [blockMat, hij.symm]
      · simp [blockMat, ha, hb, Matrix.one_apply]
  · simp [Matrix.fromBlocks_apply₂₁]

theorem shortBlock_mulVec_inl_right (hij : i ≠ j) (A : SL(2, K)) :
    mat n K (shortBlock K hij A) *ᵥ Pi.single (Sum.inl j) 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 • (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → K) +
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 • (Pi.single (Sum.inl j) 1 : Fin n ⊕ Fin n → K) := by
  funext r
  rw [mulVec_single_one_apply, mat_shortBlock]
  rcases r with a | a
  · rw [Matrix.fromBlocks_apply₁₁]
    by_cases ha : a = i
    · subst ha
      simp [blockMat, hij.symm]
    · by_cases hb : a = j
      · subst hb
        simp [blockMat, hij.symm]
      · simp [blockMat, ha, hb, Matrix.one_apply]
  · simp [Matrix.fromBlocks_apply₂₁]

theorem shortBlock_mulVec_inr_left (hij : i ≠ j) (A : SL(2, K)) :
    mat n K (shortBlock K hij A) *ᵥ Pi.single (Sum.inr i) 1 =
      ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 •
          (Pi.single (Sum.inr i) 1 : Fin n ⊕ Fin n → K) +
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 •
          (Pi.single (Sum.inr j) 1 : Fin n ⊕ Fin n → K) := by
  funext r
  rw [mulVec_single_one_apply, mat_shortBlock]
  rcases r with a | a
  · simp [Matrix.fromBlocks_apply₁₂]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    by_cases ha : a = i
    · subst ha
      simp [blockMat, hij]
    · by_cases hb : a = j
      · subst hb
        simp [blockMat, hij.symm]
      · simp [blockMat, ha, hb, Matrix.one_apply]

theorem shortBlock_mulVec_inr_right (hij : i ≠ j) (A : SL(2, K)) :
    mat n K (shortBlock K hij A) *ᵥ Pi.single (Sum.inr j) 1 =
      ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 •
          (Pi.single (Sum.inr i) 1 : Fin n ⊕ Fin n → K) +
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 •
          (Pi.single (Sum.inr j) 1 : Fin n ⊕ Fin n → K) := by
  funext r
  rw [mulVec_single_one_apply, mat_shortBlock]
  rcases r with a | a
  · simp [Matrix.fromBlocks_apply₁₂]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    by_cases ha : a = i
    · subst ha
      simp [blockMat, hij.symm]
    · by_cases hb : a = j
      · subst hb
        simp [blockMat, hij.symm]
      · simp [blockMat, ha, hb, Matrix.one_apply]

theorem blockMat_neg_one (hij : i ≠ j) :
    blockMat i j (-1 : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun a : Fin n => if a = i ∨ a = j then (-1 : K) else 1) := by
  ext a b
  simp only [blockMat, Matrix.of_apply, Matrix.diagonal_apply, Matrix.neg_apply,
    Matrix.one_apply]
  split_ifs <;> simp_all

theorem shortBlock_neg_one (hij : i ≠ j) :
    shortBlock K hij (-1) = longInv K n i * longInv K n j := by
  refine mat_injective ?_
  rw [map_mul, mat_longInv, mat_longInv, mat_shortBlock, Matrix.diagonal_mul_diagonal,
    inv_neg_one]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  rw [blockMat_neg_one hij, Matrix.diagonal_transpose]
  ext r t
  rcases r with a | a <;> rcases t with b | b <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, coords]
  all_goals (split_ifs <;> simp_all)

end Short

section Nodes

theorem shortBlock_sl2Upper_eq_x {k : Fin n} (hk : k.val + 1 < n) (c : K) :
    shortBlock K (ne_succ' hk) (sl2Upper c) = x n K (Pi.single k 1) c := by
  rw [x_eq (stdVec_shortPos_eq hk), shortBlock_sl2Upper]

theorem shortBlock_sl2Lower_eq_x {k : Fin n} (hk : k.val + 1 < n) (c : K) :
    shortBlock K (ne_succ' hk) (sl2Lower c) = x n K (-Pi.single k 1) c := by
  rw [x_eq (stdVec_shortNeg_eq hk), shortBlock_sl2Lower]

theorem longBlock_sl2Upper_eq_x {k : Fin n} (hk : ¬k.val + 1 < n) (c : K) :
    longBlock K n k (sl2Upper c) = x n K (Pi.single k 1) c := by
  rw [x_eq (stdVec_positiveLong_eq hk), longBlock_sl2Upper]

theorem longBlock_sl2Lower_eq_x {k : Fin n} (hk : ¬k.val + 1 < n) (c : K) :
    longBlock K n k (sl2Lower c) = x n K (-Pi.single k 1) c := by
  rw [x_eq (stdVec_negativeLong_eq hk), longBlock_sl2Lower]

theorem longBlock_eq_of_eq_x {k : Fin n} (hk : ¬k.val + 1 < n) (φ : SL(2, K) →* StatedSp n K)
    (hU : ∀ c, φ (sl2Upper c) = x n K (Pi.single k 1) c)
    (hL : ∀ c, φ (sl2Lower c) = x n K (-Pi.single k 1) c) : φ = longBlock K n k := by
  refine MonoidHom.ext fun A => ?_
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus φ (longBlock K n k) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (hU c).trans (longBlock_sl2Upper_eq_x hk c).symm
    · exact (hL c).trans (longBlock_sl2Lower_eq_x hk c).symm
  exact hle (mem_closure_sl2 A)

theorem shortBlock_eq_of_eq_x {k : Fin n} (hk : k.val + 1 < n) (φ : SL(2, K) →* StatedSp n K)
    (hU : ∀ c, φ (sl2Upper c) = x n K (Pi.single k 1) c)
    (hL : ∀ c, φ (sl2Lower c) = x n K (-Pi.single k 1) c) :
    φ = shortBlock K (ne_succ' hk) := by
  refine MonoidHom.ext fun A => ?_
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus φ (shortBlock K (ne_succ' hk)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (hU c).trans (shortBlock_sl2Upper_eq_x hk c).symm
    · exact (hL c).trans (shortBlock_sl2Lower_eq_x hk c).symm
  exact hle (mem_closure_sl2 A)

end Nodes

section Pair

variable {i j : Fin n}

@[expose] def pairMap (i j : Fin n) : Fin 2 → Fin n := ![i, j]

@[simp] theorem pairMap_zero : pairMap i j 0 = i := rfl

@[simp] theorem pairMap_one : pairMap i j 1 = j := rfl

theorem pairMap_injective (hij : i ≠ j) : Function.Injective (pairMap i j) := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd h hij
  · exact absurd h.symm hij
  · rfl

theorem spEmbed_elt_difference {σ : Fin m → Fin n} (hσ : Function.Injective σ) {a b : Fin m}
    (hab : a ≠ b) (c : K) :
    spEmbed σ hσ (elt (.difference a b hab) c) =
      elt (.difference (σ a) (σ b) (fun h => hab (hσ h))) c := by
  refine mat_injective ?_
  rw [mat_spEmbed, mat_elt, mat_elt]
  have e : (1 + c • E K (.difference a b hab) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 =
      c • E K (.difference a b hab) := add_sub_cancel_left _ _
  rw [spEmbedMat, e]
  simp only [E, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    spIncl_mul_single_mul_transpose, Sum.map_inl, Sum.map_inr]

theorem spEmbed_comp_shortBlock (hij : i ≠ j) :
    (spEmbed (pairMap i j) (pairMap_injective hij)).comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)) = shortBlock K hij := by
  refine MonoidHom.ext fun A => ?_
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus ((spEmbed (pairMap i j) (pairMap_injective hij)).comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1))) (shortBlock K hij) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show (spEmbed (pairMap i j) (pairMap_injective hij)).comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)) (sl2Upper c) =
          shortBlock K hij (sl2Upper c)
      rw [MonoidHom.comp_apply, shortBlock_sl2Upper, shortBlock_sl2Upper, spEmbed_elt_difference]
      rfl
    · show (spEmbed (pairMap i j) (pairMap_injective hij)).comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)) (sl2Lower c) =
          shortBlock K hij (sl2Lower c)
      rw [MonoidHom.comp_apply, shortBlock_sl2Lower, shortBlock_sl2Lower, spEmbed_elt_difference]
      rfl
  exact hle (mem_closure_sl2 A)

theorem spEmbed_comp_longBlock (hij : i ≠ j) :
    (spEmbed (pairMap i j) (pairMap_injective hij)).comp (longBlock K 2 1) =
      longBlock K n j :=
  MonoidHom.ext fun A => spEmbed_longBlock (pairMap_injective hij) 1 A

end Pair

section Generation

variable (K)


theorem shortBlock_sup_longBlock_eq_top :
    (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range ⊔ (longBlock K 2 1).range = ⊤ := by
  set H' : Subgroup (StatedSp 2 K) :=
    (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range ⊔ (longBlock K 2 1).range with hH'
  have hS : ∀ c : K, elt (.difference 0 1 zero_ne_one) c ∈ H' := fun c =>
    Subgroup.mem_sup_left ⟨sl2Upper c, shortBlock_sl2Upper _ c⟩
  have hS' : ∀ c : K, elt (.difference 1 0 zero_ne_one.symm) c ∈ H' := fun c =>
    Subgroup.mem_sup_left ⟨sl2Lower c, shortBlock_sl2Lower _ c⟩
  have hL : ∀ c : K, elt (.positiveLong 1) c ∈ H' := fun c =>
    Subgroup.mem_sup_right ⟨sl2Upper c, longBlock_sl2Upper 1 c⟩
  have hL' : ∀ c : K, elt (.negativeLong 1) c ∈ H' := fun c =>
    Subgroup.mem_sup_right ⟨sl2Lower c, longBlock_sl2Lower 1 c⟩
  let H : Subgroup (TauCeti.GLSymplecticFin 2 K) := H'.comap (equivStatedSp 2 K).toMonoidHom
  have hH : H = ⊤ := by
    refine TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long H 1 ?_ ?_ ?_
    · intro i j hij c hadj
      have key : equivStatedSp 2 K (TauCeti.GLSymplecticFin.differenceShortRootUnit hij c) =
          elt (.difference i j hij) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_difference,
          TauCeti.GLSymplecticFin.differenceShortRootHom_apply, toAdd_ofAdd]
      change equivStatedSp 2 K _ ∈ H'
      rw [key]
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hcase : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
        rcases hadj with h | h
        · exact Or.inl ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
        · exact Or.inr ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hS c
      · exact hS' c
    · intro c
      have key : equivStatedSp 2 K (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit 1 c) =
          elt (.positiveLong 1) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
          TauCeti.GLSymplecticFin.positiveLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp 2 K _ ∈ H'
      rw [key]
      exact hL c
    · intro c
      have key : equivStatedSp 2 K (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit 1 c) =
          elt (.negativeLong 1) c := by
        simp only [elt, TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
          TauCeti.GLSymplecticFin.negativeLongRootTransvectionHom_apply, toAdd_ofAdd]
      change equivStatedSp 2 K _ ∈ H'
      rw [key]
      exact hL' c
  rw [eq_top_iff]
  intro x _
  have : (equivStatedSp 2 K).symm x ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using this

end Generation

section StandardPair

variable {i j : Fin n}

theorem shortBlock_sup_longBlock (hij : i ≠ j) :
    (shortBlock K hij).range ⊔ (longBlock K n j).range =
      (spEmbed (pairMap i j) (pairMap_injective hij)).range := by
  rw [← spEmbed_comp_shortBlock hij, ← spEmbed_comp_longBlock hij, MonoidHom.range_comp,
    MonoidHom.range_comp, ← Subgroup.map_sup, shortBlock_sup_longBlock_eq_top,
    MonoidHom.range_eq_map]

theorem range_pairMap : Set.range (Sum.map (pairMap i j) (pairMap i j)) = coords i ∪ coords j := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    rcases x with l | l <;> fin_cases l
    · exact Or.inl (inl_mem_coords i)
    · exact Or.inr (inl_mem_coords j)
    · exact Or.inl (inr_mem_coords i)
    · exact Or.inr (inr_mem_coords j)
  · rintro (ha | ha)
    · rcases mem_coords.1 ha with rfl | rfl
      · exact ⟨Sum.inl 0, rfl⟩
      · exact ⟨Sum.inr 0, rfl⟩
    · rcases mem_coords.1 ha with rfl | rfl
      · exact ⟨Sum.inl 1, rfl⟩
      · exact ⟨Sum.inr 1, rfl⟩

theorem shortBlock_sup_longBlock_eq_suppGroup (hij : i ≠ j) :
    (shortBlock K hij).range ⊔ (longBlock K n j).range = suppGroup (coords i ∪ coords j) := by
  rw [shortBlock_sup_longBlock hij, range_spEmbed (pairMap_injective hij), range_pairMap]

variable (K) in
@[expose] def SymplecticBlockStandardPair {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  ∃ (θ : StatedSp 2 K →* X) (c : StatedSp 2 K), θ.range = W ∧
    θ.ker ≤ Subgroup.center (StatedSp 2 K) ∧
    Function.Injective (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (longBlock K 2 1))) ∧
    Function.Injective (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp
      (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)))) ∧
    ((longBlock K 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ = U ∧
      ((shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
        (MulAut.conj c⁻¹).toMonoidHom).map θ = V

theorem map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = H := by
  ext x
  simp

theorem symplecticBlockStandardPair_longShort (hij : i ≠ j) :
    SymplecticBlockStandardPair K ((longBlock K n j).range ⊔ (shortBlock K hij).range)
      (longBlock K n j).range (shortBlock K hij).range := by
  have hθ := spEmbed_injective (K := K) (pairMap_injective hij)
  refine ⟨spEmbed (pairMap i j) (pairMap_injective hij), 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sup_comm, shortBlock_sup_longBlock hij]
  · rw [(MonoidHom.ker_eq_bot_iff _).2 hθ]
    exact bot_le
  · exact hθ.comp ((MulAut.conj (1 : StatedSp 2 K)⁻¹).injective.comp
      (longBlock_injective (K := K) (n := 2) 1))
  · exact hθ.comp ((MulAut.conj (1 : StatedSp 2 K)⁻¹).injective.comp
      (shortBlock_injective (K := K) (zero_ne_one : (0 : Fin 2) ≠ 1)))
  · rw [map_conj_one, ← MonoidHom.range_comp, spEmbed_comp_longBlock hij]
  · rw [map_conj_one, ← MonoidHom.range_comp, spEmbed_comp_shortBlock hij]

theorem symplecticBlockStandardPair_map {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : SymplecticBlockStandardPair K W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    SymplecticBlockStandardPair K (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, hinjL, hinjS, hU, hV⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · exact hφ.comp hinjL
  · exact hφ.comp hinjS
  · rw [← Subgroup.map_map, hU]
  · rw [← Subgroup.map_map, hV]

theorem symplecticBlockStandardPair_conj (hij : i ≠ j) (g : StatedSp n K) :
    SymplecticBlockStandardPair K
      (((longBlock K n j).range ⊔ (shortBlock K hij).range).map (MulAut.conj g).toMonoidHom)
      ((longBlock K n j).range.map (MulAut.conj g).toMonoidHom)
      ((shortBlock K hij).range.map (MulAut.conj g).toMonoidHom) :=
  symplecticBlockStandardPair_map (symplecticBlockStandardPair_longShort hij) _
    (MulAut.conj g).injective

end StandardPair

end CFSG.ClassicalInvolution.Models.SymplecticPairs
