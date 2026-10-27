module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl MatrixExtension

variable {n : ℕ}

abbrev spMatrixOf (g : StatedSp n (ZMod 2)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  ((g : GL (Fin n ⊕ Fin n) (ZMod 2)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2))

theorem spMatrixOf_mul (g h : StatedSp n (ZMod 2)) :
    spMatrixOf (g * h) = spMatrixOf g * spMatrixOf h := by
  rw [spMatrixOf, Subgroup.coe_mul, Units.val_mul]

theorem spMatrixOf_inv_mul (g : StatedSp n (ZMod 2)) : spMatrixOf g⁻¹ * spMatrixOf g = 1 := by
  rw [← spMatrixOf_mul, inv_mul_cancel]
  rfl

theorem spMatrixOf_mul_inv (g : StatedSp n (ZMod 2)) : spMatrixOf g * spMatrixOf g⁻¹ = 1 := by
  rw [← spMatrixOf_mul, mul_inv_cancel]
  rfl

theorem spMatrixOf_tauSym (B : Multiplicative (binarySymMatrices n)) :
    spMatrixOf (tauSym n B) = fromBlocks 1 (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) 0 1 :=
  coe_tauSym B

variable (n) in
abbrev lagrangianZero : Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) := isoFlag n (ZMod 2) n

theorem mem_lagrangianZero {v : Fin n ⊕ Fin n → ZMod 2} :
    v ∈ lagrangianZero n ↔ ∀ j, v (Sum.inr j) = 0 := by
  rw [mem_isoFlag]
  exact ⟨fun h => h.1, fun h => ⟨h, fun j hj => absurd j.2 (not_lt.2 hj)⟩⟩

theorem single_inl_mem_lagrangianZero (j : Fin n) :
    (Pi.single (Sum.inl j) 1 : Fin n ⊕ Fin n → ZMod 2) ∈ lagrangianZero n :=
  mem_lagrangianZero.2 fun i => by simp

theorem fixes_lagrangianZero_iff (g : StatedSp n (ZMod 2)) :
    (∀ v ∈ lagrangianZero n, spMatrixOf g *ᵥ v = v) ↔
      (spMatrixOf g).toBlocks₁₁ = 1 ∧ (spMatrixOf g).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    have hcol : ∀ j, spMatrixOf g *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1 :=
      fun j => h _ (single_inl_mem_lagrangianZero j)
    refine ⟨?_, ?_⟩
    · ext i j
      have := congrFun (hcol j) (Sum.inl i)
      rw [mulVec_single_one, col_apply] at this
      rw [toBlocks₁₁, of_apply, this, one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    · ext i j
      have := congrFun (hcol j) (Sum.inr i)
      rw [mulVec_single_one, col_apply] at this
      rw [toBlocks₂₁, of_apply, this]
      simp
  · rintro ⟨h₁, h₂⟩ v hv
    have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
      funext x
      rcases x with i | j
      · rfl
      · exact mem_lagrangianZero.1 hv j
    rw [← fromBlocks_toBlocks (spMatrixOf g), h₁, h₂, hv', fromBlocks_mulVec]
    simp

theorem mem_range_tauSym_iff (g : StatedSp n (ZMod 2)) :
    g ∈ (tauSym n).range ↔ ∀ v ∈ lagrangianZero n, spMatrixOf g *ᵥ v = v := by
  rw [fixes_lagrangianZero_iff]
  constructor
  · rintro ⟨B, rfl⟩
    rw [spMatrixOf_tauSym]
    exact ⟨toBlocks_fromBlocks₁₁ _ _ _ _, toBlocks_fromBlocks₂₁ _ _ _ _⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨-, C, hC, hg⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h₂
    refine ⟨Multiplicative.ofAdd ⟨C, hC⟩, statedSp_ext ?_⟩
    change spMatrixOf (tauSym n (Multiplicative.ofAdd ⟨C, hC⟩)) = spMatrixOf g
    rw [spMatrixOf_tauSym, spMatrixOf, hg]
    change _ = blockMat (spMatrixOf g).toBlocks₁₁ C
    rw [h₁, blockMat, Matrix.one_mul, inv_one, transpose_one]
    rfl

theorem mem_lagrangianZero_of_forall {v : Fin n ⊕ Fin n → ZMod 2}
    (h : ∀ B, spMatrixOf (tauSym n B) *ᵥ v = v) : v ∈ lagrangianZero n := by
  rw [mem_lagrangianZero]
  intro j
  have h1 := congrFun (h (Multiplicative.ofAdd ⟨single j j 1, single_mem_binarySymMatrices j⟩))
    (Sum.inl j)
  rw [spMatrixOf_tauSym, fromBlocks_mulVec] at h1
  simp only [Sum.elim_inl, Pi.add_apply, one_mulVec, toAdd_ofAdd, Function.comp_apply] at h1
  have h2 : (single j j (1 : ZMod 2) *ᵥ (v ∘ Sum.inr)) j = v (Sum.inr j) := by
    simp [mulVec, dotProduct, single_apply]
  rw [h2] at h1
  simpa using h1

theorem mulVec_mem_of_mem_stabilizer {g : StatedSp n (ZMod 2)}
    (hg : g ∈ stabilizer n (ZMod 2) (lagrangianZero n)) {v : Fin n ⊕ Fin n → ZMod 2}
    (hv : v ∈ lagrangianZero n) : spMatrixOf g *ᵥ v ∈ lagrangianZero n := by
  have h : spMatrixOf g *ᵥ v ∈ (lagrangianZero n).map (mulVecLin (spMatrixOf g)) :=
    ⟨v, hv, rfl⟩
  rwa [mem_stabilizer.1 hg] at h

theorem toBlocks₂₁_eq_zero_of_mem_stabilizer {g : StatedSp n (ZMod 2)}
    (hg : g ∈ stabilizer n (ZMod 2) (lagrangianZero n)) : (spMatrixOf g).toBlocks₂₁ = 0 := by
  ext i j
  have h := mem_lagrangianZero.1
    (mulVec_mem_of_mem_stabilizer hg (single_inl_mem_lagrangianZero j)) i
  rw [mulVec_single_one, col_apply] at h
  rw [toBlocks₂₁, of_apply, h]
  rfl

theorem leviSp_mem_stabilizer (A : GL (Fin n) (ZMod 2)) :
    leviSp A ∈ stabilizer n (ZMod 2) (lagrangianZero n) := by
  have key : ∀ A : GL (Fin n) (ZMod 2), ∀ v ∈ lagrangianZero n,
      spMatrixOf (leviSp A) *ᵥ v ∈ lagrangianZero n := by
    intro A v hv
    have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
      funext x
      rcases x with i | j
      · rfl
      · exact mem_lagrangianZero.1 hv j
    rw [mem_lagrangianZero]
    intro j
    rw [spMatrixOf, coe_leviSp, hv', fromBlocks_mulVec]
    simp
  refine mem_stabilizer_of_mulVec_mem (key A) ?_
  rw [← map_inv]
  exact key A⁻¹

theorem normalizer_range_tauSym :
    Subgroup.normalizer ((tauSym n).range : Set (StatedSp n (ZMod 2))) =
      stabilizer n (ZMod 2) (lagrangianZero n) := by
  apply le_antisymm
  · have key : ∀ h ∈ Subgroup.normalizer ((tauSym n).range : Set (StatedSp n (ZMod 2))),
        ∀ v ∈ lagrangianZero n, spMatrixOf h *ᵥ v ∈ lagrangianZero n := by
      intro h hh v hv
      refine mem_lagrangianZero_of_forall fun B => ?_
      have hx : h⁻¹ * tauSym n B * h ∈ (tauSym n).range := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hh) (tauSym n B)).1 ⟨B, rfl⟩
        rwa [inv_inv] at this
      have hfix := (mem_range_tauSym_iff _).1 hx v hv
      have hm : spMatrixOf h * spMatrixOf (h⁻¹ * tauSym n B * h) =
          spMatrixOf (tauSym n B) * spMatrixOf h := by
        rw [← spMatrixOf_mul, ← spMatrixOf_mul]
        congr 1
        group
      calc spMatrixOf (tauSym n B) *ᵥ (spMatrixOf h *ᵥ v)
          = spMatrixOf h *ᵥ (spMatrixOf (h⁻¹ * tauSym n B * h) *ᵥ v) := by
            rw [mulVec_mulVec, mulVec_mulVec, hm]
        _ = spMatrixOf h *ᵥ v := by rw [hfix]
    intro g hg
    exact mem_stabilizer_of_mulVec_mem (key g hg) (key g⁻¹ (inv_mem hg))
  · have key : ∀ h ∈ stabilizer n (ZMod 2) (lagrangianZero n), ∀ y ∈ (tauSym n).range,
        h * y * h⁻¹ ∈ (tauSym n).range := by
      intro h hh y hy
      refine (mem_range_tauSym_iff _).2 fun w hw => ?_
      have hw' := mulVec_mem_of_mem_stabilizer (inv_mem hh) hw
      rw [spMatrixOf_mul, spMatrixOf_mul, ← mulVec_mulVec, ← mulVec_mulVec,
        (mem_range_tauSym_iff y).1 hy _ hw', mulVec_mulVec, spMatrixOf_mul_inv, one_mulVec]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)}
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, hN, fromBlocks_multiply]
  rw [toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero]

theorem toBlocks₁₁_one_sum :
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)).toBlocks₁₁ = 1 := by
  ext i j
  simp [toBlocks₁₁, one_apply]

variable (n) in
@[expose] def lagrangianLevi : stabilizer n (ZMod 2) (lagrangianZero n) →* GL (Fin n) (ZMod 2)
    where
  toFun g :=
    { val := (spMatrixOf (g : StatedSp n (ZMod 2))).toBlocks₁₁
      inv := (spMatrixOf ((g : StatedSp n (ZMod 2))⁻¹)).toBlocks₁₁
      val_inv := by
        rw [← toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero
          (toBlocks₂₁_eq_zero_of_mem_stabilizer (inv_mem g.2)), spMatrixOf_mul_inv]
        exact toBlocks₁₁_one_sum
      inv_val := by
        rw [← toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (toBlocks₂₁_eq_zero_of_mem_stabilizer g.2),
          spMatrixOf_inv_mul]
        exact toBlocks₁₁_one_sum }
  map_one' := Units.ext (by
    change (spMatrixOf (1 : StatedSp n (ZMod 2))).toBlocks₁₁ = 1
    exact toBlocks₁₁_one_sum)
  map_mul' g h := Units.ext (by
    change (spMatrixOf ((g : StatedSp n (ZMod 2)) * (h : StatedSp n (ZMod 2)))).toBlocks₁₁ =
      (spMatrixOf (g : StatedSp n (ZMod 2))).toBlocks₁₁ *
        (spMatrixOf (h : StatedSp n (ZMod 2))).toBlocks₁₁
    rw [spMatrixOf_mul, toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero
      (toBlocks₂₁_eq_zero_of_mem_stabilizer h.2)])

theorem coe_lagrangianLevi (g : stabilizer n (ZMod 2) (lagrangianZero n)) :
    ((lagrangianLevi n g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (spMatrixOf (g : StatedSp n (ZMod 2))).toBlocks₁₁ :=
  rfl

theorem lagrangianLevi_leviSp (A : GL (Fin n) (ZMod 2)) :
    lagrangianLevi n ⟨leviSp A, leviSp_mem_stabilizer A⟩ = A := by
  refine Units.ext ?_
  rw [coe_lagrangianLevi]
  change (spMatrixOf (leviSp A)).toBlocks₁₁ = _
  rw [spMatrixOf, coe_leviSp, toBlocks_fromBlocks₁₁]

theorem lagrangianLevi_surjective : Function.Surjective (lagrangianLevi n) :=
  fun A => ⟨⟨leviSp A, leviSp_mem_stabilizer A⟩, lagrangianLevi_leviSp A⟩

theorem ker_lagrangianLevi :
    (lagrangianLevi n).ker = (tauSym n).range.subgroupOf (stabilizer n (ZMod 2) (lagrangianZero n))
    := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_range_tauSym_iff, fixes_lagrangianZero_iff]
  constructor
  · intro h
    refine ⟨?_, toBlocks₂₁_eq_zero_of_mem_stabilizer g.2⟩
    have := congrArg (fun A : GL (Fin n) (ZMod 2) => (A : Matrix (Fin n) (Fin n) (ZMod 2))) h
    simpa [coe_lagrangianLevi] using this
  · rintro ⟨h₁, -⟩
    refine Units.ext ?_
    rw [coe_lagrangianLevi, h₁]
    rfl

theorem exists_eq_leviSp_mul_tauSym_of_mem_stabilizer {g : StatedSp n (ZMod 2)}
    (hg : g ∈ stabilizer n (ZMod 2) (lagrangianZero n)) :
    ∃ C : Multiplicative (binarySymMatrices n),
      g = leviSp (lagrangianLevi n ⟨g, hg⟩) * tauSym n C := by
  obtain ⟨-, C, hC, hgC⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero
    (toBlocks₂₁_eq_zero_of_mem_stabilizer hg)
  set A := lagrangianLevi n ⟨g, hg⟩ with hA
  have hAm : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = (spMatrixOf g).toBlocks₁₁ :=
    coe_lagrangianLevi ⟨g, hg⟩
  refine ⟨Multiplicative.ofAdd ⟨C, mem_binarySymMatrices.2 hC⟩, statedSp_ext ?_⟩
  change spMatrixOf g = spMatrixOf (leviSp A) *
    spMatrixOf (tauSym n (Multiplicative.ofAdd ⟨C, mem_binarySymMatrices.2 hC⟩))
  have hL : spMatrixOf (leviSp A) =
      fromBlocks (A : Matrix (Fin n) (Fin n) (ZMod 2)) 0 0
        ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := coe_leviSp A
  have hg' : spMatrixOf g = blockMat (spMatrixOf g).toBlocks₁₁ C := hgC
  rw [hL, spMatrixOf_tauSym, coe_units_inv, hAm]
  conv_lhs => rw [hg', blockMat_eq_mul]
  rfl

theorem conj_tauSym_of_mem_stabilizer {g : StatedSp n (ZMod 2)}
    (hg : g ∈ stabilizer n (ZMod 2) (lagrangianZero n)) (B : Multiplicative (binarySymMatrices n)) :
    g * tauSym n B * g⁻¹ = tauSym n (Multiplicative.ofAdd
      ⟨(lagrangianLevi n ⟨g, hg⟩ : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (lagrangianLevi n ⟨g, hg⟩ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
        congr_mem_binarySymMatrices _ _⟩) := by
  obtain ⟨C, hC⟩ := exists_eq_leviSp_mul_tauSym_of_mem_stabilizer hg
  set A := lagrangianLevi n ⟨g, hg⟩
  have hcomm : tauSym n C * tauSym n B = tauSym n B * tauSym n C := by
    rw [← map_mul, ← map_mul, mul_comm]
  calc g * tauSym n B * g⁻¹ = leviSp A * (tauSym n C * tauSym n B * (tauSym n C)⁻¹) *
      (leviSp A)⁻¹ := by
        conv_lhs => rw [hC]
        group
    _ = leviSp A * tauSym n B * (leviSp A)⁻¹ := by
        rw [hcomm, mul_inv_cancel_right]
    _ = _ := leviSp_mul_tauSym_mul_inv A B

theorem zmod_two_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

theorem eq_one_of_forall_congr {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hA : ∀ B ∈ binarySymMatrices n, A * B * Aᵀ = B) : A = 1 := by
  ext i k
  have h := congrFun (congrFun (hA (single k k 1) (single_mem_binarySymMatrices k)) i) i
  have h1 : (A * single k k (1 : ZMod 2) * Aᵀ) i i = A i k * A i k := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [mul_single_apply_same, mul_one, transpose_apply]
    · intro j _ hjk
      rw [mul_single_apply_of_ne (hbj := hjk), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [h1, zmod_two_mul_self, single_apply] at h
  rw [h, one_apply]
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik, Ne.symm hik]

theorem centralizer_range_tauSym :
    Subgroup.centralizer ((tauSym n).range : Set (StatedSp n (ZMod 2))) = (tauSym n).range := by
  apply le_antisymm
  · intro g hg
    have hgN : g ∈ stabilizer n (ZMod 2) (lagrangianZero n) := by
      rw [← normalizer_range_tauSym]
      exact Subgroup.centralizer_le_normalizer _ hg
    have hA : ∀ B ∈ binarySymMatrices n,
        (lagrangianLevi n ⟨g, hgN⟩ : Matrix (Fin n) (Fin n) (ZMod 2)) * B *
          (lagrangianLevi n ⟨g, hgN⟩ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = B := by
      intro B hB
      have h1 := conj_tauSym_of_mem_stabilizer hgN (Multiplicative.ofAdd ⟨B, hB⟩)
      have h2 : g * tauSym n (Multiplicative.ofAdd ⟨B, hB⟩) * g⁻¹ =
          tauSym n (Multiplicative.ofAdd ⟨B, hB⟩) := by
        rw [(Subgroup.mem_centralizer_iff.1 hg _ ⟨_, rfl⟩).symm, mul_inv_cancel_right]
      rw [h2] at h1
      have h3 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauSym_injective h1))
      exact h3.symm
    have hA1 := eq_one_of_forall_congr hA
    refine (mem_range_tauSym_iff g).2 ((fixes_lagrangianZero_iff g).2
      ⟨?_, toBlocks₂₁_eq_zero_of_mem_stabilizer hgN⟩)
    rw [← coe_lagrangianLevi ⟨g, hgN⟩]
    exact hA1
  · rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨C, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
