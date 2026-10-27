module

public import CFSG.GH74.BNPair.Cells

public noncomputable section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

namespace RankTwoSystem

variable {X X' : Type u} [Group X] [Group X'] {n : ℕ}

structure Transfer (D : RankTwoSystem X n) (D' : RankTwoSystem X' n) where
  φ : D.U ≃* D'.U
  hφ : ∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : D.U, (x : X) ∈ D.root i ↔ ((φ x : D'.U) : X') ∈ D'.root i
  ι : D.Weyl ≃ D'.Weyl
  ι_alt₁ : ∀ t : ℕ, t ≤ n → ι (altWord D.w₁ D.w₂ t) = altWord D'.w₁ D'.w₂ t
  ι_alt₂ : ∀ t : ℕ, t ≤ n → ι (altWord D.w₂ D.w₁ t) = altWord D'.w₂ D'.w₁ t
  ι_mul₁ : ∀ w, ι (D.w₁ * w) = D'.w₁ * ι w
  ι_mul₂ : ∀ w, ι (D.w₂ * w) = D'.w₂ * ι w

variable {D : RankTwoSystem X n} {D' : RankTwoSystem X' n}

namespace Transfer

@[expose] def symm (T : Transfer D D') : Transfer D' D where
  φ := T.φ.symm
  hφ i hi hin y := by
    rw [T.hφ i hi hin (T.φ.symm y), MulEquiv.apply_symm_apply]
  ι := T.ι.symm
  ι_alt₁ t ht := by
    rw [← T.ι_alt₁ t ht, Equiv.symm_apply_apply]
  ι_alt₂ t ht := by
    rw [← T.ι_alt₂ t ht, Equiv.symm_apply_apply]
  ι_mul₁ w := T.ι.injective (by rw [Equiv.apply_symm_apply, T.ι_mul₁, Equiv.apply_symm_apply])
  ι_mul₂ w := T.ι.injective (by rw [Equiv.apply_symm_apply, T.ι_mul₂, Equiv.apply_symm_apply])

theorem ι_gen (T : Transfer D D') (i : Bool) (w : D.Weyl) :
    T.ι (gen D.w₁ D.w₂ i * w) = gen D'.w₁ D'.w₂ i * T.ι w := by
  cases i
  · exact T.ι_mul₂ w
  · exact T.ι_mul₁ w

theorem chain_iff (T : Transfer D D') :
    ∀ l : List ℤ, (∀ k ∈ l, 1 ≤ k ∧ k ≤ (n : ℤ)) → ∀ x : D.U,
      ((x : X) ∈ chainProd D.root l ↔ ((T.φ x : D'.U) : X') ∈ chainProd D'.root l)
  | [], _, x => by
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one]
    constructor
    · intro h
      have : x = 1 := Subtype.ext h
      rw [this]
      simp
    · intro h
      have h1 : T.φ x = 1 := Subtype.ext h
      have : x = 1 := T.φ.injective (h1.trans (map_one T.φ).symm)
      rw [this]
      rfl
  | k :: l, hl, x => by
    have hk := hl k List.mem_cons_self
    have hl' : ∀ k' ∈ l, 1 ≤ k' ∧ k' ≤ (n : ℤ) := fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')
    have hsub : chainProd D.root l ⊆ D.U :=
      chainProd_subset D.root D.U l fun k' hk' => D.root_le_U (hl' k' hk').1 (hl' k' hk').2
    have hsub' : chainProd D'.root l ⊆ D'.U :=
      chainProd_subset D'.root D'.U l fun k' hk' => D'.root_le_U (hl' k' hk').1 (hl' k' hk').2
    rw [chainProd_cons, chainProd_cons]
    constructor
    · intro hx
      obtain ⟨a, ha, r, hr, hxe⟩ := Set.mem_mul.1 hx
      have haU : a ∈ D.U := D.root_le_U hk.1 hk.2 ha
      have hrU : r ∈ D.U := hsub hr
      have hx' : x = ⟨a, haU⟩ * ⟨r, hrU⟩ := Subtype.ext hxe.symm
      rw [hx', map_mul]
      refine Set.mem_mul.2 ⟨_, ?_, _, ?_, rfl⟩
      · exact (T.hφ k hk.1 hk.2 ⟨a, haU⟩).1 ha
      · exact (chain_iff T l hl' ⟨r, hrU⟩).1 hr
    · intro hx
      obtain ⟨a', ha', r', hr', hxe⟩ := Set.mem_mul.1 hx
      have ha'U : a' ∈ D'.U := D'.root_le_U hk.1 hk.2 ha'
      have hr'U : r' ∈ D'.U := hsub' hr'
      set a₀ : D.U := T.φ.symm ⟨a', ha'U⟩ with ha₀
      set r₀ : D.U := T.φ.symm ⟨r', hr'U⟩ with hr₀
      have hφa : T.φ a₀ = ⟨a', ha'U⟩ := by rw [ha₀, MulEquiv.apply_symm_apply]
      have hφr : T.φ r₀ = ⟨r', hr'U⟩ := by rw [hr₀, MulEquiv.apply_symm_apply]
      have hxx : x = a₀ * r₀ := by
        apply T.φ.injective
        rw [map_mul, hφa, hφr]
        exact Subtype.ext hxe.symm
      rw [hxx]
      refine Set.mem_mul.2 ⟨(a₀ : X), ?_, (r₀ : X), ?_, rfl⟩
      · exact (T.hφ k hk.1 hk.2 a₀).2 (by rw [hφa]; exact ha')
      · exact (chain_iff T l hl' r₀).2 (by rw [hφr]; exact hr')

theorem root_mem_Icc_of_mem_intList {a b k : ℤ} (hk : k ∈ intList a b) (ha : 1 ≤ a) (hb : b ≤ n) :
    1 ≤ k ∧ k ≤ (n : ℤ) := by
  obtain ⟨h1, h2⟩ := mem_intList_iff.1 hk
  omega

theorem UwMinus_iff (T : Transfer D D') (w : D.Weyl) (x : D.U) :
    (x : X) ∈ D.UwMinus (D.lift w) ↔ ((T.φ x : D'.U) : X') ∈ D'.UwMinus (D'.lift (T.ι w)) := by
  have hn := D.three_le
  obtain ⟨t, ht, hw | hw⟩ := D.rank2.dih.exists_altWord w
  · obtain ⟨h1, -⟩ := D.eq30_5_A ht (D.lift w) (by rw [D.lift_mk]; exact hw)
    obtain ⟨h1', -⟩ := D'.eq30_5_A ht (D'.lift (T.ι w)) (by
      rw [D'.lift_mk, hw]
      exact T.ι_alt₁ t ht)
    rw [h1, h1']
    exact T.chain_iff _ (fun k hk => root_mem_Icc_of_mem_intList hk le_rfl (by omega)) x
  · obtain ⟨h1, -⟩ := D.eq30_5_B ht (D.lift w) (by rw [D.lift_mk]; exact hw)
    obtain ⟨h1', -⟩ := D'.eq30_5_B ht (D'.lift (T.ι w)) (by
      rw [D'.lift_mk, hw]
      exact T.ι_alt₂ t ht)
    rw [h1, h1']
    exact T.chain_iff _ (fun k hk => root_mem_Icc_of_mem_intList (List.mem_reverse.1 hk)
      (by omega) le_rfl) x

theorem UwPlus_iff (T : Transfer D D') (w : D.Weyl) (x : D.U) :
    (x : X) ∈ D.UwPlus (D.lift w) ↔ ((T.φ x : D'.U) : X') ∈ D'.UwPlus (D'.lift (T.ι w)) := by
  have hn := D.three_le
  obtain ⟨t, ht, hw | hw⟩ := D.rank2.dih.exists_altWord w
  · obtain ⟨-, h1⟩ := D.eq30_5_A ht (D.lift w) (by rw [D.lift_mk]; exact hw)
    obtain ⟨-, h1'⟩ := D'.eq30_5_A ht (D'.lift (T.ι w)) (by
      rw [D'.lift_mk, hw]
      exact T.ι_alt₁ t ht)
    rw [h1, h1']
    exact T.chain_iff _ (fun k hk => root_mem_Icc_of_mem_intList hk (by omega) le_rfl) x
  · obtain ⟨-, h1⟩ := D.eq30_5_B ht (D.lift w) (by rw [D.lift_mk]; exact hw)
    obtain ⟨-, h1'⟩ := D'.eq30_5_B ht (D'.lift (T.ι w)) (by
      rw [D'.lift_mk, hw]
      exact T.ι_alt₂ t ht)
    rw [h1, h1']
    exact T.chain_iff _ (fun k hk => root_mem_Icc_of_mem_intList (List.mem_reverse.1 hk)
      le_rfl (by omega)) x

end Transfer

end RankTwoSystem

end CFSG.GH74.BNPair
