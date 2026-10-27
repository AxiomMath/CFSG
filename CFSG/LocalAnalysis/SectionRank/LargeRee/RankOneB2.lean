module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneBlock
public import CFSG.LieType.Chevalley.OrbitGroups
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Blocks
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section Basis

@[expose] def vRoot : Fin 4 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 2, 1]]

@[expose] def vIdx : Fin 4 → ℕ :=
  ![3, 10, 17, 25]

theorem vIdx_lt (j : Fin 4) : vIdx j < ReeTag.F4.tag.rootCertificate.roots.length := by
  revert j
  decide

theorem root_vIdx (j : Fin 4) : ReeTag.F4.tag.rootCertificate.root (vIdx j) = vRoot j := by
  revert j
  decide

theorem isRoot_vRoot (j : Fin 4) : IsRoot ReeTag.F4.tag (vRoot j) :=
  root_vIdx j ▸ RootCertificate.isRoot_root ReeTag.F4.tag.rootCertificate_check _ (vIdx_lt j)

@[expose] def vLabel (j : Fin 4) : Label ReeTag.F4.tag :=
  .inr ⟨vRoot j, isRoot_vRoot j⟩

theorem vLabel_injective : Function.Injective vLabel := by
  intro i j h
  simp only [vLabel, Sum.inr.injEq, Subtype.mk.injEq] at h
  revert i j
  decide

variable {K : Type} [Field K]

theorem rootVec_vRoot (j : Fin 4) :
    rootVec ReeTag.F4.tag K (vRoot j) = Finsupp.single (vLabel j) 1 :=
  rootVec_eq_single_of_isRoot (isRoot_vRoot j)

theorem vRoot_ne (j : Fin 4) {i : Fin ReeTag.F4.tag.rank} (hi : i = fi 1 ∨ i = fi 2) :
    vRoot j ≠ Pi.single i 1 ∧ vRoot j ≠ -Pi.single i 1 := by
  rcases hi with rfl | rfl <;> revert j <;> decide

theorem strings_vRoot
    (j : Fin 4) {i : Fin ReeTag.F4.tag.rank} (hi : i = fi 1 ∨ i = fi 2) :
    stringUp ReeTag.F4.tag i (vRoot j) = ReeTag.F4.tag.stringData.up (vIdx j) i ∧
      stringDown ReeTag.F4.tag i (vRoot j) = ReeTag.F4.tag.stringData.down (vIdx j) i :=
  stringUp_stringDown_of_root_eq (vIdx_lt j) (root_vIdx j) i (vRoot_ne j hi).1 (vRoot_ne j hi).2

end Basis

section Ops

variable {K : Type} [Field K]

theorem xOp_vRoot_fixed
    {i : Fin ReeTag.F4.tag.rank} (hi : i = fi 1 ∨ i = fi 2) (j : Fin 4)
    (hup : ReeTag.F4.tag.stringData.up (vIdx j) i = 0) (c : K) :
    xOp ReeTag.F4.tag K i c (rootVec ReeTag.F4.tag K (vRoot j)) =
      rootVec ReeTag.F4.tag K (vRoot j) :=
  xOp_rootVec_of_stringUp_eq_zero c (isRoot_vRoot j) (vRoot_ne j hi).1 (vRoot_ne j hi).2
    ((strings_vRoot j hi).1.trans hup)

theorem xOp_vRoot_step
    {i : Fin ReeTag.F4.tag.rank} (hi : i = fi 1 ∨ i = fi 2) (j j' : Fin 4)
    (hup : ReeTag.F4.tag.stringData.up (vIdx j) i = 1)
    (hdown : ReeTag.F4.tag.stringData.down (vIdx j) i = 0) (hj : vRoot j + Pi.single i 1 = vRoot j')
    (c : K) :
    xOp ReeTag.F4.tag K i c (rootVec ReeTag.F4.tag K (vRoot j)) =
      rootVec ReeTag.F4.tag K (vRoot j) + c • rootVec ReeTag.F4.tag K (vRoot j') := by
  rw [xOp_rootVec_of_stringUp_eq_one c (isRoot_vRoot j) (vRoot_ne j hi).1 (vRoot_ne j hi).2
    ((strings_vRoot j hi).1.trans hup) ((strings_vRoot j hi).2.trans hdown), hj]

theorem yOp_vRoot_fixed
    {i : Fin ReeTag.F4.tag.rank} (hi : i = fi 1 ∨ i = fi 2) (j : Fin 4)
    (hdown : ReeTag.F4.tag.stringData.down (vIdx j) i = 0) (c : K) :
    yOp ReeTag.F4.tag K i c (rootVec ReeTag.F4.tag K (vRoot j)) =
      rootVec ReeTag.F4.tag K (vRoot j) :=
  yOp_rootVec_of_stringDown_eq_zero c (isRoot_vRoot j) (vRoot_ne j hi).1 (vRoot_ne j hi).2
    ((strings_vRoot j hi).2.trans hdown)

theorem yOp_vRoot_step
    {i : Fin ReeTag.F4.tag.rank} (hi : i = fi 1 ∨ i = fi 2) (j j' : Fin 4)
    (hdown : ReeTag.F4.tag.stringData.down (vIdx j) i = 1)
    (hup : ReeTag.F4.tag.stringData.up (vIdx j) i = 0) (hj : vRoot j - Pi.single i 1 = vRoot j')
    (c : K) :
    yOp ReeTag.F4.tag K i c (rootVec ReeTag.F4.tag K (vRoot j)) =
      rootVec ReeTag.F4.tag K (vRoot j) + c • rootVec ReeTag.F4.tag K (vRoot j') := by
  rw [yOp_rootVec_of_stringDown_eq_one c (isRoot_vRoot j) (vRoot_ne j hi).1 (vRoot_ne j hi).2
    ((strings_vRoot j hi).2.trans hdown) ((strings_vRoot j hi).1.trans hup), hj]

@[expose] def mX1 (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, c, 1, 0; 0, 0, 0, 1]

@[expose] def mX2 (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; c, 1, 0, 0; 0, 0, 1, 0; 0, 0, c, 1]

@[expose] def mY1 (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, c, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mY2 (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, c, 0, 0; 0, 1, 0, 0; 0, 0, 1, c; 0, 0, 0, 1]

theorem presBlock_xOp_one (c : K) :
    PresBlock vLabel (xOp ReeTag.F4.tag K (fi 1) c) ∧
      blockMat vLabel (xOp ReeTag.F4.tag K (fi 1) c) = mX1 c := by
  have h0 : xOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 0) 1) =
      ∑ i, mX1 c i 0 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_fixed (.inl rfl) 0 (by decide)]
    simp [Fin.sum_univ_four, mX1, rootVec_vRoot]
  have h1 : xOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 1) 1) =
      ∑ i, mX1 c i 1 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_step (.inl rfl) 1 2 (by decide) (by decide) (by decide)]
    simp [Fin.sum_univ_four, mX1, rootVec_vRoot]
  have h2 : xOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 2) 1) =
      ∑ i, mX1 c i 2 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_fixed (.inl rfl) 2 (by decide)]
    simp [Fin.sum_univ_four, mX1, rootVec_vRoot]
  have h3 : xOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 3) 1) =
      ∑ i, mX1 c i 3 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_fixed (.inl rfl) 3 (by decide)]
    simp [Fin.sum_univ_four, mX1, rootVec_vRoot]
  refine presBlock_of vLabel_injective _ fun j => ?_
  fin_cases j
  exacts [h0, h1, h2, h3]

theorem presBlock_xOp_two (c : K) :
    PresBlock vLabel (xOp ReeTag.F4.tag K (fi 2) c) ∧
      blockMat vLabel (xOp ReeTag.F4.tag K (fi 2) c) = mX2 c := by
  have h0 : xOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 0) 1) =
      ∑ i, mX2 c i 0 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_step (.inr rfl) 0 1 (by decide) (by decide) (by decide)]
    simp [Fin.sum_univ_four, mX2, rootVec_vRoot]
  have h1 : xOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 1) 1) =
      ∑ i, mX2 c i 1 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_fixed (.inr rfl) 1 (by decide)]
    simp [Fin.sum_univ_four, mX2, rootVec_vRoot]
  have h2 : xOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 2) 1) =
      ∑ i, mX2 c i 2 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_step (.inr rfl) 2 3 (by decide) (by decide) (by decide)]
    simp [Fin.sum_univ_four, mX2, rootVec_vRoot]
  have h3 : xOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 3) 1) =
      ∑ i, mX2 c i 3 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, xOp_vRoot_fixed (.inr rfl) 3 (by decide)]
    simp [Fin.sum_univ_four, mX2, rootVec_vRoot]
  refine presBlock_of vLabel_injective _ fun j => ?_
  fin_cases j
  exacts [h0, h1, h2, h3]

theorem presBlock_yOp_one (c : K) :
    PresBlock vLabel (yOp ReeTag.F4.tag K (fi 1) c) ∧
      blockMat vLabel (yOp ReeTag.F4.tag K (fi 1) c) = mY1 c := by
  have h0 : yOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 0) 1) =
      ∑ i, mY1 c i 0 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_fixed (.inl rfl) 0 (by decide)]
    simp [Fin.sum_univ_four, mY1, rootVec_vRoot]
  have h1 : yOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 1) 1) =
      ∑ i, mY1 c i 1 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_fixed (.inl rfl) 1 (by decide)]
    simp [Fin.sum_univ_four, mY1, rootVec_vRoot]
  have h2 : yOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 2) 1) =
      ∑ i, mY1 c i 2 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_step (.inl rfl) 2 1 (by decide) (by decide) (by decide)]
    simp [Fin.sum_univ_four, mY1, rootVec_vRoot, add_comm]
  have h3 : yOp ReeTag.F4.tag K (fi 1) c (Finsupp.single (vLabel 3) 1) =
      ∑ i, mY1 c i 3 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_fixed (.inl rfl) 3 (by decide)]
    simp [Fin.sum_univ_four, mY1, rootVec_vRoot]
  refine presBlock_of vLabel_injective _ fun j => ?_
  fin_cases j
  exacts [h0, h1, h2, h3]

theorem presBlock_yOp_two (c : K) :
    PresBlock vLabel (yOp ReeTag.F4.tag K (fi 2) c) ∧
      blockMat vLabel (yOp ReeTag.F4.tag K (fi 2) c) = mY2 c := by
  have h0 : yOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 0) 1) =
      ∑ i, mY2 c i 0 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_fixed (.inr rfl) 0 (by decide)]
    simp [Fin.sum_univ_four, mY2, rootVec_vRoot]
  have h1 : yOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 1) 1) =
      ∑ i, mY2 c i 1 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_step (.inr rfl) 1 0 (by decide) (by decide) (by decide)]
    simp [Fin.sum_univ_four, mY2, rootVec_vRoot, add_comm]
  have h2 : yOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 2) 1) =
      ∑ i, mY2 c i 2 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_fixed (.inr rfl) 2 (by decide)]
    simp [Fin.sum_univ_four, mY2, rootVec_vRoot]
  have h3 : yOp ReeTag.F4.tag K (fi 2) c (Finsupp.single (vLabel 3) 1) =
      ∑ i, mY2 c i 3 • Finsupp.single (vLabel i) 1 := by
    rw [← rootVec_vRoot, yOp_vRoot_step (.inr rfl) 3 2 (by decide) (by decide) (by decide)]
    simp [Fin.sum_univ_four, mY2, rootVec_vRoot, add_comm]
  refine presBlock_of vLabel_injective _ fun j => ?_
  fin_cases j
  exacts [h0, h1, h2, h3]

end Ops

section Group

variable (K : Type) [Field K]

noncomputable abbrev vStab
    : Subgroup (adjointGroup ReeTag.F4.tag K) :=
  blockStab vLabel vLabel_injective

variable {K}

noncomputable abbrev vMat
    (g : adjointGroup ReeTag.F4.tag K) : Matrix (Fin 4) (Fin 4) K :=
  blockMat vLabel (endHom K g)

theorem vMat_mul
    {g h : adjointGroup ReeTag.F4.tag K} (hg : g ∈ vStab K) (hh : h ∈ vStab K) :
    vMat (g * h) = vMat g * vMat h := by
  rw [vMat, map_mul]
  exact (hg.1.mul vLabel_injective hh.1).2

theorem vMat_one
    : vMat (1 : adjointGroup ReeTag.F4.tag K) = 1 := by
  rw [vMat, map_one]
  exact (presBlock_one vLabel_injective).2

theorem vMat_inv_mul
    {g : adjointGroup ReeTag.F4.tag K} (hg : g ∈ vStab K) :
    vMat g⁻¹ * vMat g = 1 := by
  rw [← vMat_mul (inv_mem hg) hg, inv_mul_cancel, vMat_one]

theorem vMat_mul_inv
    {g : adjointGroup ReeTag.F4.tag K} (hg : g ∈ vStab K) :
    vMat g * vMat g⁻¹ = 1 := by
  rw [← vMat_mul hg (inv_mem hg), mul_inv_cancel, vMat_one]

theorem xElement_one_mem_vStab
    (c : K) : xElement (fi 1) c ∈ vStab K :=
  ⟨(presBlock_xOp_one c).1, (presBlock_xOp_one (-c)).1⟩

theorem xElement_two_mem_vStab
    (c : K) : xElement (fi 2) c ∈ vStab K :=
  ⟨(presBlock_xOp_two c).1, (presBlock_xOp_two (-c)).1⟩

theorem yElement_one_mem_vStab
    (c : K) : yElement (fi 1) c ∈ vStab K :=
  ⟨(presBlock_yOp_one c).1, (presBlock_yOp_one (-c)).1⟩

theorem yElement_two_mem_vStab
    (c : K) : yElement (fi 2) c ∈ vStab K :=
  ⟨(presBlock_yOp_two c).1, (presBlock_yOp_two (-c)).1⟩

theorem vMat_xElement_one
    (c : K) : vMat (xElement (fi 1) c) = mX1 c :=
  (presBlock_xOp_one c).2

theorem vMat_xElement_two
    (c : K) : vMat (xElement (fi 2) c) = mX2 c :=
  (presBlock_xOp_two c).2

theorem vMat_yElement_one
    (c : K) : vMat (yElement (fi 1) c) = mY1 c :=
  (presBlock_yOp_one c).2

theorem vMat_yElement_two
    (c : K) : vMat (yElement (fi 2) c) = mY2 c :=
  (presBlock_yOp_two c).2

omit [Field K] in
theorem weylElement_eq_mul
    {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) :
    weylElement τ K i = xElement i 1 * yElement i (-1) * xElement i 1 := by
  have h := weylElt_eq_xUnit_mul (τ := τ) i (1 : Kˣ)
  rw [inv_one, Units.val_one] at h
  exact Subtype.ext h

theorem weylElement_one_mem_vStab
    : weylElement ReeTag.F4.tag K (fi 1) ∈ vStab K := by
  rw [weylElement_eq_mul]
  exact mul_mem (mul_mem (xElement_one_mem_vStab 1) (yElement_one_mem_vStab (-1)))
    (xElement_one_mem_vStab 1)

theorem weylElement_two_mem_vStab
    : weylElement ReeTag.F4.tag K (fi 2) ∈ vStab K := by
  rw [weylElement_eq_mul]
  exact mul_mem (mul_mem (xElement_two_mem_vStab 1) (yElement_two_mem_vStab (-1)))
    (xElement_two_mem_vStab 1)

variable [Finite K]

theorem mem_vStab_of_mem_H
    {h : adjointGroup ReeTag.F4.tag K}
    (hh : h ∈ (nativeData ReeTag.F4.tag K).H) : h ∈ vStab K := by
  have key : ∀ h ∈ (nativeData ReeTag.F4.tag K).H, PresBlock vLabel (endHom K h) := by
    intro h hh j
    obtain ⟨μ, hμ⟩ := exists_apply_single_eq_smul_of_mem_H hh (vLabel j)
    have e : blockMat vLabel (endHom K h) = Matrix.diagonal fun k =>
        (endHom K h (Finsupp.single (vLabel k) 1)) (vLabel k) := by
      ext i k
      rw [blockMat, Matrix.of_apply, Matrix.diagonal_apply]
      split_ifs with hik
      · rw [hik]
      · obtain ⟨μ', hμ'⟩ := exists_apply_single_eq_smul_of_mem_H hh (vLabel k)
        rw [endHom_apply, hμ']
        simp [vLabel_injective.ne (Ne.symm hik)]
    rw [e, Finset.sum_eq_single j (fun i _ hij => by rw [Matrix.diagonal_apply_ne _ hij,
      zero_smul]) (by simp), Matrix.diagonal_apply_eq, endHom_apply, hμ]
    simp
  exact ⟨key h hh, key _ (inv_mem hh)⟩

omit [Finite K] in
theorem vMat_eq_diagonal
    {h : adjointGroup ReeTag.F4.tag K} {μ : Fin 4 → K}
    (hμ : ∀ k, endHom K h (Finsupp.single (vLabel k) 1) = μ k • Finsupp.single (vLabel k) 1) :
    vMat h = Matrix.diagonal μ := by
  ext i k
  rw [vMat, blockMat, Matrix.of_apply, hμ k, Matrix.diagonal_apply]
  split_ifs with hik
  · rw [hik]
    simp
  · simp [vLabel_injective.ne (Ne.symm hik)]

end Group

section Mat

set_option linter.style.whitespace false in
theorem mat4_mul {α : Type*} [AddCommMonoid α] [Mul α]
    (a₀₀ a₀₁ a₀₂ a₀₃ a₁₀ a₁₁ a₁₂ a₁₃ a₂₀ a₂₁ a₂₂ a₂₃ a₃₀ a₃₁ a₃₂ a₃₃
      b₀₀ b₀₁ b₀₂ b₀₃ b₁₀ b₁₁ b₁₂ b₁₃ b₂₀ b₂₁ b₂₂ b₂₃ b₃₀ b₃₁ b₃₂ b₃₃ : α) :
    !![a₀₀, a₀₁, a₀₂, a₀₃; a₁₀, a₁₁, a₁₂, a₁₃; a₂₀, a₂₁, a₂₂, a₂₃; a₃₀, a₃₁, a₃₂, a₃₃] *
      !![b₀₀, b₀₁, b₀₂, b₀₃; b₁₀, b₁₁, b₁₂, b₁₃; b₂₀, b₂₁, b₂₂, b₂₃; b₃₀, b₃₁, b₃₂, b₃₃] =
    !![a₀₀ * b₀₀ + a₀₁ * b₁₀ + a₀₂ * b₂₀ + a₀₃ * b₃₀,
        a₀₀ * b₀₁ + a₀₁ * b₁₁ + a₀₂ * b₂₁ + a₀₃ * b₃₁,
        a₀₀ * b₀₂ + a₀₁ * b₁₂ + a₀₂ * b₂₂ + a₀₃ * b₃₂,
        a₀₀ * b₀₃ + a₀₁ * b₁₃ + a₀₂ * b₂₃ + a₀₃ * b₃₃;
      a₁₀ * b₀₀ + a₁₁ * b₁₀ + a₁₂ * b₂₀ + a₁₃ * b₃₀,
        a₁₀ * b₀₁ + a₁₁ * b₁₁ + a₁₂ * b₂₁ + a₁₃ * b₃₁,
        a₁₀ * b₀₂ + a₁₁ * b₁₂ + a₁₂ * b₂₂ + a₁₃ * b₃₂,
        a₁₀ * b₀₃ + a₁₁ * b₁₃ + a₁₂ * b₂₃ + a₁₃ * b₃₃;
      a₂₀ * b₀₀ + a₂₁ * b₁₀ + a₂₂ * b₂₀ + a₂₃ * b₃₀,
        a₂₀ * b₀₁ + a₂₁ * b₁₁ + a₂₂ * b₂₁ + a₂₃ * b₃₁,
        a₂₀ * b₀₂ + a₂₁ * b₁₂ + a₂₂ * b₂₂ + a₂₃ * b₃₂,
        a₂₀ * b₀₃ + a₂₁ * b₁₃ + a₂₂ * b₂₃ + a₂₃ * b₃₃;
      a₃₀ * b₀₀ + a₃₁ * b₁₀ + a₃₂ * b₂₀ + a₃₃ * b₃₀,
        a₃₀ * b₀₁ + a₃₁ * b₁₁ + a₃₂ * b₂₁ + a₃₃ * b₃₁,
        a₃₀ * b₀₂ + a₃₁ * b₁₂ + a₃₂ * b₂₂ + a₃₃ * b₃₂,
        a₃₀ * b₀₃ + a₃₁ * b₁₃ + a₃₂ * b₂₃ + a₃₃ * b₃₃] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc]

end Mat

section CharTwo

variable {K : Type} [Field K] [CharP K 2]

@[expose] def mN1 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def mN2 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem vMat_weylElement_one
    : vMat (weylElement ReeTag.F4.tag K (fi 1)) = mN1 := by
  rw [weylElement_eq_mul, vMat_mul (mul_mem (xElement_one_mem_vStab 1)
    (yElement_one_mem_vStab (-1))) (xElement_one_mem_vStab 1),
    vMat_mul (xElement_one_mem_vStab 1) (yElement_one_mem_vStab (-1)), vMat_xElement_one,
    vMat_yElement_one]
  simp only [mX1, mY1, mN1, mat4_mul]
  simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem vMat_weylElement_two
    : vMat (weylElement ReeTag.F4.tag K (fi 2)) = mN2 := by
  rw [weylElement_eq_mul, vMat_mul (mul_mem (xElement_two_mem_vStab 1)
    (yElement_two_mem_vStab (-1))) (xElement_two_mem_vStab 1),
    vMat_mul (xElement_two_mem_vStab 1) (yElement_two_mem_vStab (-1)), vMat_xElement_two,
    vMat_yElement_two]
  simp only [mX2, mY2, mN2, mat4_mul]
  simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem weylElement_inv_charTwo
    {τ : Tag} (i : Fin τ.rank) :
    (weylElement τ K i)⁻¹ = weylElement τ K i := by
  have h := nrep_simple_mul_self (τ := τ) K i
  rw [nrep_simple_eq] at h
  exact inv_eq_of_mul_eq_one_right h

end CharTwo

section Collection

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem inv_nrep_conj_mem_Uminus_mul
    {z w : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (z * w) =
      (coxeterSystem τ).length z + (coxeterSystem τ).length w)
    {x : adjointGroup τ K} (hx : x ∈ Uminus τ K z) :
    (nrep τ K w)⁻¹ * x * nrep τ K w ∈ Uminus τ K (z * w) := by
  have h := RootGroupData.conj_mem_iSup_of_smul (D := nativeData τ K)
    (⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ : monomialGroup τ K)
    (S := fun α => 0 < height α.1 ∧ height (z • α).1 < 0)
    (T := fun α => 0 < height α.1 ∧ height ((z * w) • α).1 < 0) (fun α hα => by
      change 0 < height (weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ • α).1 ∧
        height ((z * w) • weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ • α).1 < 0
      rw [map_inv, weylHom_nrep, mul_smul, smul_inv_smul]
      exact ⟨height_inv_smul_pos_of_length_mul hlen hα.1 hα.2, hα.2⟩) hx
  rwa [Subgroup.coe_inv, inv_inv] at h

theorem length_wordProd_append_singleton
    {ω : List (Fin τ.rank)} {i : Fin τ.rank}
    (hred : (coxeterSystem τ).IsReduced (ω ++ [i])) :
    (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω * simple τ i) =
      (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) +
        (coxeterSystem τ).length (simple τ i) := by
  have := length_mul_of_isReduced_append hred
  rwa [CoxeterSystem.wordProd_singleton] at this

theorem exists_xElement_mul_of_mem_Uminus_append
    {ω : List (Fin τ.rank)} {i : Fin τ.rank}
    (hred : (coxeterSystem τ).IsReduced (ω ++ [i])) {u : adjointGroup τ K}
    (hu : u ∈ Uminus τ K ((coxeterSystem τ).wordProd (ω ++ [i]))) :
    ∃ c : K, ∃ u' ∈ Uminus τ K ((coxeterSystem τ).wordProd ω),
      u = xElement i c * ((weylElement τ K i)⁻¹ * u' * weylElement τ K i) := by
  have hlen := length_wordProd_append_singleton hred
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton] at hu
  obtain ⟨z, hz, y, -, hy, rfl⟩ := exists_mem_Uminus_mul_conj_mem_Uminus hlen hu
  obtain ⟨c, rfl⟩ := exists_eq_xElement_of_mem (Uminus_simple_le i hz)
  refine ⟨c, _, hy, ?_⟩
  rw [nrep_simple_eq]
  group

theorem xElement_mul_mem_Uminus_append
    {ω : List (Fin τ.rank)} {i : Fin τ.rank}
    (hred : (coxeterSystem τ).IsReduced (ω ++ [i])) (c : K) {u' : adjointGroup τ K}
    (hu' : u' ∈ Uminus τ K ((coxeterSystem τ).wordProd ω)) :
    xElement i c * ((weylElement τ K i)⁻¹ * u' * weylElement τ K i) ∈
      Uminus τ K ((coxeterSystem τ).wordProd (ω ++ [i])) := by
  have hlen := length_wordProd_append_singleton hred
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton]
  refine mul_mem (Uminus_le_Uminus_mul hlen (xElement_mem_Uminus_simple i c)) ?_
  rw [← nrep_simple_eq]
  exact inv_nrep_conj_mem_Uminus_mul hlen hu'

end Collection

section NormalForm

variable {K : Type} [Field K]

@[expose] noncomputable def nfU
    (c₁ c₂ c₃ c₄ : K) : adjointGroup ReeTag.F4.tag K :=
  xElement (fi 2) c₄ * ((weylElement ReeTag.F4.tag K (fi 2))⁻¹ *
    (xElement (fi 1) c₃ * ((weylElement ReeTag.F4.tag K (fi 1))⁻¹ *
      (xElement (fi 2) c₂ * ((weylElement ReeTag.F4.tag K (fi 2))⁻¹ * xElement (fi 1) c₁ *
        weylElement ReeTag.F4.tag K (fi 2))) *
      weylElement ReeTag.F4.tag K (fi 1))) * weylElement ReeTag.F4.tag K (fi 2))

@[expose] noncomputable def nfU'
    (d₁ d₂ d₃ d₄ : K) : adjointGroup ReeTag.F4.tag K :=
  xElement (fi 1) d₄ * ((weylElement ReeTag.F4.tag K (fi 1))⁻¹ *
    (xElement (fi 2) d₃ * ((weylElement ReeTag.F4.tag K (fi 2))⁻¹ *
      (xElement (fi 1) d₂ * ((weylElement ReeTag.F4.tag K (fi 1))⁻¹ * xElement (fi 2) d₁ *
        weylElement ReeTag.F4.tag K (fi 1))) *
      weylElement ReeTag.F4.tag K (fi 2))) * weylElement ReeTag.F4.tag K (fi 1))

theorem reeOrbitWord_fi_one : ReeTag.F4.reeOrbitWord (fi 1) = [fi 1, fi 2, fi 1, fi 2] :=
  rfl

theorem isReduced_z₂ :
    (coxeterSystem ReeTag.F4.tag).IsReduced ([fi 1, fi 2, fi 1] ++ [fi 2]) :=
  isReduced_reeOrbitWord ReeTag.F4 (fi 1)

theorem isReduced_z₂_three :
    (coxeterSystem ReeTag.F4.tag).IsReduced ([fi 1, fi 2] ++ [fi 1]) :=
  (isReduced_left_right_of_append isReduced_z₂).1

theorem isReduced_z₂_two :
    (coxeterSystem ReeTag.F4.tag).IsReduced ([fi 1] ++ [fi 2]) :=
  (isReduced_left_right_of_append isReduced_z₂_three).1

theorem isReduced_z₂_one :
    (coxeterSystem ReeTag.F4.tag).IsReduced ([] ++ [fi 1]) :=
  (isReduced_left_right_of_append isReduced_z₂_two).1

theorem blockElt_fi_one_eq :
    ReeTag.F4.blockElt (fi 1) = (coxeterSystem ReeTag.F4.tag).wordProd
      ([fi 1, fi 2, fi 1] ++ [fi 2]) :=
  rfl

variable [Finite K]

theorem exists_eq_nfU
    {u : adjointGroup ReeTag.F4.tag K}
    (hu : u ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1))) :
    ∃ c₁ c₂ c₃ c₄ : K, u = nfU c₁ c₂ c₃ c₄ := by
  rw [blockElt_fi_one_eq] at hu
  obtain ⟨c₄, u₃, hu₃, rfl⟩ := exists_xElement_mul_of_mem_Uminus_append isReduced_z₂ hu
  obtain ⟨c₃, u₂, hu₂, rfl⟩ := exists_xElement_mul_of_mem_Uminus_append isReduced_z₂_three hu₃
  obtain ⟨c₂, u₁, hu₁, rfl⟩ := exists_xElement_mul_of_mem_Uminus_append isReduced_z₂_two hu₂
  obtain ⟨c₁, u₀, hu₀, rfl⟩ := exists_xElement_mul_of_mem_Uminus_append isReduced_z₂_one hu₁
  rw [CoxeterSystem.wordProd_nil, Uminus_one, Subgroup.mem_bot] at hu₀
  subst hu₀
  refine ⟨c₁, c₂, c₃, c₄, ?_⟩
  rw [nfU, mul_one, inv_mul_cancel, mul_one]

theorem nfU_mem_Uminus
    (c₁ c₂ c₃ c₄ : K) :
    nfU c₁ c₂ c₃ c₄ ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) := by
  have h₀ : (1 : adjointGroup ReeTag.F4.tag K) ∈
      Uminus ReeTag.F4.tag K ((coxeterSystem ReeTag.F4.tag).wordProd []) := one_mem _
  have h₁ := xElement_mul_mem_Uminus_append isReduced_z₂_one c₁ h₀
  rw [mul_one, inv_mul_cancel, mul_one] at h₁
  have h₂ := xElement_mul_mem_Uminus_append isReduced_z₂_two c₂ h₁
  have h₃ := xElement_mul_mem_Uminus_append isReduced_z₂_three c₃ h₂
  have h₄ := xElement_mul_mem_Uminus_append isReduced_z₂ c₄ h₃
  rw [blockElt_fi_one_eq]
  exact h₄

end NormalForm

section Words

variable {K : Type} [Field K]

inductive VLetter (K : Type) where
  | x1 (c : K)
  | x2 (c : K)
  | n1
  | n2
  | n1i
  | n2i

@[expose] noncomputable def VLetter.elt
    : VLetter K → adjointGroup ReeTag.F4.tag K
  | .x1 c => xElement (fi 1) c
  | .x2 c => xElement (fi 2) c
  | .n1 => weylElement ReeTag.F4.tag K (fi 1)
  | .n2 => weylElement ReeTag.F4.tag K (fi 2)
  | .n1i => (weylElement ReeTag.F4.tag K (fi 1))⁻¹
  | .n2i => (weylElement ReeTag.F4.tag K (fi 2))⁻¹

@[expose] def VLetter.mat : VLetter K → Matrix (Fin 4) (Fin 4) K
  | .x1 c => mX1 c
  | .x2 c => mX2 c
  | .n1 => mN1
  | .n2 => mN2
  | .n1i => mN1
  | .n2i => mN2

@[expose] noncomputable def evalV
    (w : List (VLetter K)) : adjointGroup ReeTag.F4.tag K :=
  (w.map VLetter.elt).prod

@[expose] def evalVMat (w : List (VLetter K)) : Matrix (Fin 4) (Fin 4) K :=
  (w.map VLetter.mat).prod

theorem VLetter.elt_mem_vStab
    (l : VLetter K) : l.elt ∈ vStab K := by
  cases l with
  | x1 c => exact xElement_one_mem_vStab c
  | x2 c => exact xElement_two_mem_vStab c
  | n1 => exact weylElement_one_mem_vStab
  | n2 => exact weylElement_two_mem_vStab
  | n1i => exact inv_mem weylElement_one_mem_vStab
  | n2i => exact inv_mem weylElement_two_mem_vStab

theorem evalV_mem_vStab
    (w : List (VLetter K)) : evalV w ∈ vStab K := by
  induction w with
  | nil => exact one_mem _
  | cons l w ih =>
    rw [evalV, List.map_cons, List.prod_cons]
    exact mul_mem l.elt_mem_vStab ih

theorem nfU_eq_evalV (c₁ c₂ c₃ c₄ : K) :
    nfU c₁ c₂ c₃ c₄ = evalV [.x2 c₄, .n2i, .x1 c₃, .n1i, .x2 c₂, .n2i, .x1 c₁, .n2, .n1, .n2] := by
  simp only [nfU, evalV, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    VLetter.elt, mul_assoc]

theorem nfU'_eq_evalV
    (d₁ d₂ d₃ d₄ : K) :
    nfU' d₁ d₂ d₃ d₄ = evalV [.x1 d₄, .n1i, .x2 d₃, .n2i, .x1 d₂, .n1i, .x2 d₁, .n1, .n2, .n1] := by
  simp only [nfU', evalV, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    VLetter.elt, mul_assoc]

theorem nfU_mem_vStab
    (c₁ c₂ c₃ c₄ : K) : nfU c₁ c₂ c₃ c₄ ∈ vStab K := by
  rw [nfU_eq_evalV]
  exact evalV_mem_vStab _

theorem nfU'_mem_vStab
    (d₁ d₂ d₃ d₄ : K) : nfU' d₁ d₂ d₃ d₄ ∈ vStab K := by
  rw [nfU'_eq_evalV]
  exact evalV_mem_vStab _

variable [CharP K 2]

theorem VLetter.vMat_elt
    (l : VLetter K) : vMat l.elt = l.mat := by
  cases l with
  | x1 c => exact vMat_xElement_one c
  | x2 c => exact vMat_xElement_two c
  | n1 => exact vMat_weylElement_one
  | n2 => exact vMat_weylElement_two
  | n1i =>
    change vMat (weylElement ReeTag.F4.tag K (fi 1))⁻¹ = mN1
    rw [weylElement_inv_charTwo]
    exact vMat_weylElement_one
  | n2i =>
    change vMat (weylElement ReeTag.F4.tag K (fi 2))⁻¹ = mN2
    rw [weylElement_inv_charTwo]
    exact vMat_weylElement_two

theorem vMat_evalV
    (w : List (VLetter K)) : vMat (evalV w) = evalVMat w := by
  induction w with
  | nil => exact vMat_one
  | cons l w ih =>
    have e : evalV (l :: w) = l.elt * evalV w := by
      rw [evalV, List.map_cons, List.prod_cons]
      rfl
    rw [e, vMat_mul l.elt_mem_vStab (evalV_mem_vStab w), ih, l.vMat_elt]
    rfl

theorem vMat_nfU
    (c₁ c₂ c₃ c₄ : K) :
    vMat (nfU c₁ c₂ c₃ c₄) = !![1, 0, 0, 0; c₄, 1, 0, 0; c₂, c₁, 1, 0;
      c₄ * c₂ + c₃, c₄ * c₁ + c₂, c₄, 1] := by
  rw [nfU_eq_evalV, vMat_evalV]
  simp only [evalVMat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    VLetter.mat, mX1, mX2, mN1, mN2, mat4_mul]
  simp

theorem vMat_nfU'
    (d₁ d₂ d₃ d₄ : K) :
    vMat (nfU' d₁ d₂ d₃ d₄) = !![1, 0, 0, 0; d₁, 1, 0, 0; d₄ * d₁ + d₃, d₄, 1, 0;
      d₃ * d₁ + d₂, d₃, d₁, 1] := by
  rw [nfU'_eq_evalV, vMat_evalV]
  simp only [evalVMat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    VLetter.mat, mX1, mX2, mN1, mN2, mat4_mul]
  simp

theorem eq_of_vMat_eq_of_mem_Uminus
    [Finite K] {x x' : adjointGroup ReeTag.F4.tag K}
    (hx : x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)))
    (hx' : x' ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1))) (h : vMat x = vMat x') :
    x = x' := by
  obtain ⟨c₁, c₂, c₃, c₄, rfl⟩ := exists_eq_nfU hx
  obtain ⟨c₁', c₂', c₃', c₄', rfl⟩ := exists_eq_nfU hx'
  rw [vMat_nfU, vMat_nfU] at h
  have h10 := congrFun₂ h 1 0
  have h21 := congrFun₂ h 2 1
  have h20 := congrFun₂ h 2 0
  have h30 := congrFun₂ h 3 0
  simp at h10 h21 h20 h30
  subst h10 h21 h20
  rw [add_left_cancel h30]

end Words

section Frobenius

variable {K : Type} [Field K] [Finite K] {a : ℕ}

theorem pow_two_pow_card (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    x ^ 2 ^ (2 * a + 1) = x := by
  have := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem pow_theta_pow_e (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    (x ^ 2 ^ (a + 1)) ^ 2 ^ a = x := by
  rw [← pow_mul, ← pow_add, show a + 1 + a = 2 * a + 1 by ring, pow_two_pow_card hK]

theorem pow_e_pow_theta (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    (x ^ 2 ^ a) ^ 2 ^ (a + 1) = x := by
  rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring, pow_two_pow_card hK]

omit [Finite K] in
theorem suzukiS_eq_mat {u v x₁ x₂ x₃ : K} (h₁ : x₁ = u ^ 2 ^ (a + 1))
    (h₂ : x₂ = CFSG.Blueprint.suzukiN a u v) (h₃ : x₃ = u ^ (2 ^ (a + 1) + 1) + v) :
    !![1, 0, 0, 0; u, 1, 0, 0; v, x₁, 1, 0; x₂, x₃, u, 1] = CFSG.Blueprint.suzukiS a u v := by
  rw [h₁, h₂, h₃]
  rfl

theorem perm_fi_two : ReeTag.F4.perm (fi 2) = fi 1 := by decide

omit [Field K] [Finite K] in
theorem relationExponent_fi_one (a : ℕ) : ReeTag.F4.relationExponent a (fi 1) = 2 ^ a :=
  ite_eq_left_iff.2 fun h => absurd fi_one_mem_longSet h

omit [Field K] [Finite K] in
theorem relationExponent_fi_two (a : ℕ) : ReeTag.F4.relationExponent a (fi 2) = 2 ^ (a + 1) :=
  ite_eq_right_iff.2 fun h => absurd h (by decide)

variable [CharP K ReeTag.F4.prime]

variable (a) in
theorem reeAut_nfU
    (c₁ c₂ c₃ c₄ : K) :
    ReeTag.F4.reeAut K a (nfU c₁ c₂ c₃ c₄) =
      nfU' (c₁ ^ 2 ^ a) (c₂ ^ 2 ^ (a + 1)) (c₃ ^ 2 ^ a) (c₄ ^ 2 ^ (a + 1)) := by
  simp only [nfU, nfU', map_mul, map_inv, ReeTag.reeAut_xElement, ReeTag.reeAut_weylElement,
    perm_fi_one, perm_fi_two, relationExponent_fi_one, relationExponent_fi_two]

theorem exists_vMat_eq_suzukiS
    {x : adjointGroup ReeTag.F4.tag K}
    (hx : x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)))
    (hF : ReeTag.F4.reeAut K a x = x) : ∃ u v : K, vMat x = CFSG.Blueprint.suzukiS a u v := by
  obtain ⟨c₁, c₂, c₃, c₄, rfl⟩ := exists_eq_nfU hx
  rw [reeAut_nfU] at hF
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have h := congrArg vMat hF
  rw [vMat_nfU', vMat_nfU] at h
  have h10 := congrFun₂ h 1 0
  have h21 := congrFun₂ h 2 1
  have h31 := congrFun₂ h 3 1
  have h30 := congrFun₂ h 3 0
  simp at h10 h21 h31 h30
  refine ⟨c₄, c₂, ?_⟩
  rw [vMat_nfU]
  refine suzukiS_eq_mat h21.symm ?_ (by rw [← h21]; ring)
  rw [CFSG.Blueprint.suzukiN]
  rw [h10, h31] at h30
  linear_combination -h30 - c₄ ^ 2 * h21

theorem reeAut_mem_Uminus_blockElt_one
    {x : adjointGroup ReeTag.F4.tag K}
    (hx : x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1))) :
    ReeTag.F4.reeAut K a x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) := by
  have h := ReeTag.reeAut_mem_Uminus (t := ReeTag.F4) a _ hx
  rwa [(ReeTag.mem_relWeylRee ReeTag.F4).1 (ReeTag.reeOrbitWord_mem ReeTag.F4 (fi 1))] at h

theorem exists_reeFixed_vMat_eq_suzukiS
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    (u v : K) : ∃ x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)),
      ReeTag.F4.reeAut K a x = x ∧ vMat x = CFSG.Blueprint.suzukiS a u v := by
  set x := nfU (u ^ 2 ^ (a + 1)) v (u ^ (2 ^ (a + 1) + 2) + v ^ 2 ^ (a + 1)) u with hxdef
  have hx : x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) := nfU_mem_Uminus _ _ _ _
  have hFx := reeAut_nfU (K := K) a (u ^ 2 ^ (a + 1)) v (u ^ (2 ^ (a + 1) + 2) + v ^ 2 ^ (a + 1)) u
  rw [← hxdef] at hFx
  have hFmem := reeAut_mem_Uminus_blockElt_one (a := a) hx
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hK
  have hvx : vMat x = CFSG.Blueprint.suzukiS a u v := by
    rw [hxdef, vMat_nfU]
    exact suzukiS_eq_mat rfl (by rw [CFSG.Blueprint.suzukiN]; ring) (by ring)
  have hd₃ : (u ^ (2 ^ (a + 1) + 2) + v ^ 2 ^ (a + 1)) ^ 2 ^ a = u * u ^ 2 ^ (a + 1) + v := by
    rw [add_pow_expChar_pow, pow_theta_pow_e hK', pow_add, mul_pow, pow_theta_pow_e hK',
      ← pow_mul, show 2 * 2 ^ a = 2 ^ (a + 1) by ring]
  have hvFx : vMat (ReeTag.F4.reeAut K a x) = CFSG.Blueprint.suzukiS a u v := by
    rw [hFx, vMat_nfU', pow_theta_pow_e hK', hd₃]
    have h20 : u ^ 2 ^ (a + 1) * u + (u * u ^ 2 ^ (a + 1) + v) = v := by
      linear_combination (u * u ^ 2 ^ (a + 1)) * CharTwo.two_eq_zero (R := K)
    rw [h20]
    exact suzukiS_eq_mat rfl (by rw [CFSG.Blueprint.suzukiN]; ring) (by ring)
  exact ⟨x, hx, eq_of_vMat_eq_of_mem_Uminus hFmem hx (hvFx.trans hvx.symm), hvx⟩

end Frobenius

section Torus

variable {K : Type} [Field K]

theorem endHom_torusElement_rootVec
    {τ : Tag} (i : Fin τ.rank) (t : Kˣ)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    endHom K (torusElement τ K i t) (rootVec τ K β) =
      ((t ^ (∑ j, τ.cartan i j * β j) : Kˣ) : K) • rootVec τ K β :=
  torusElt_rootVec i t hβ

variable (a : ℕ)

theorem endHom_reeTorus_rootVec
    (j : Fin ReeTag.F4.tag.rank) (u : Kˣ)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β) :
    endHom K (ReeTag.F4.reeTorus a j u) (rootVec ReeTag.F4.tag K β) =
      ((u ^ reeExp a j β : Kˣ) : K) • rootVec ReeTag.F4.tag K β := by
  rw [ReeTag.reeTorus, map_mul, Module.End.mul_apply, endHom_torusElement_rootVec _ _ hβ,
    map_smul, endHom_torusElement_rootVec _ _ hβ, smul_smul, ← Units.val_mul]
  congr 2
  simp only [reeExp, ReeTag.cartanPair]
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add, add_comm]

theorem vMat_reeTorus
    (j : Fin ReeTag.F4.tag.rank) (u : Kˣ) :
    vMat (ReeTag.F4.reeTorus a j u) =
      Matrix.diagonal fun k => ((u ^ reeExp a j (vRoot k) : Kˣ) : K) :=
  vMat_eq_diagonal fun k => by
    rw [← rootVec_vRoot, endHom_reeTorus_rootVec a j u (isRoot_vRoot k)]

@[expose] def cpTable : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, -1, -1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![2, 1, 1, 0]]

omit [Field K] in
theorem cartanPair_vRoot : ∀ j k : Fin 4,
    ReeTag.F4.cartanPair (fi j) (vRoot k) = cpTable j k := by
  decide +kernel

omit [Field K] in
theorem reeExp_one_vRoot (k : Fin 4) :
    reeExp a (fi 1) (vRoot k) =
      cpTable 1 k + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) * cpTable 2 k := by
  rw [reeExp, perm_fi_one, cartanPair_vRoot, cartanPair_vRoot]

omit [Field K] in
theorem reeExp_zero_vRoot (k : Fin 4) :
    reeExp a (fi 0) (vRoot k) =
      cpTable 0 k + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) * cpTable 3 k := by
  rw [reeExp, perm_fi_zero, cartanPair_vRoot, cartanPair_vRoot]

variable [Finite K] {a}

theorem units_zpow_congr (u : Kˣ) {x y : ℤ} (m : ℤ)
    (h : x = y + m * ((Nat.card K : ℤ) - 1)) : u ^ x = u ^ y := by
  rw [h, show y + m * ((Nat.card K : ℤ) - 1) = (y - 1) + (1 + m * ((Nat.card K : ℤ) - 1)) by
    ring, zpow_add, units_zpow_one_add_mul, ← zpow_add_one, sub_add_cancel]

theorem natCast_prime_pow (a : ℕ) : ((ReeTag.F4.prime ^ a : ℕ) : ℤ) = 2 ^ a := by
  push_cast
  rfl

theorem vMat_reeTorus_one
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (b : Kˣ) :
    vMat (ReeTag.F4.reeTorus a (fi 1) b) =
      CFSG.Blueprint.suzukiD a (b ^ (1 - 2 * (2 ^ a : ℤ))) := by
  have hq : (Nat.card K : ℤ) = 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ) ^ 2 := by
    rw [hK]
    exact two_pow_eq_two_mul_sq a
  rw [natCast_prime_pow] at hq
  rw [vMat_reeTorus, CFSG.Blueprint.suzukiD]
  congr 1
  funext k
  rw [reeExp_one_vRoot, natCast_prime_pow]
  fin_cases k
  · exact congrArg Units.val (by rw [← zpow_mul]; exact units_zpow_congr b 1 (by
      rw [hq]; simp [cpTable]; ring))
  · exact congrArg Units.val (by rw [← zpow_mul]; exact units_zpow_congr b 1 (by
      rw [hq]; simp [cpTable]; ring))
  · exact congrArg Units.val (by rw [← zpow_mul]; exact units_zpow_congr b (-1) (by
      rw [hq]; simp [cpTable]; ring))
  · exact congrArg Units.val (by rw [← zpow_mul]; exact units_zpow_congr b (-1) (by
      rw [hq]; simp [cpTable]; ring))

omit [Finite K] in
theorem det_vMat_reeTorus_zero
    (b : Kˣ) :
    (vMat (ReeTag.F4.reeTorus a (fi 0) b)).det = ((b ^ (4 * (2 ^ a : ℤ) - 2) : Kˣ) : K) := by
  rw [vMat_reeTorus, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [reeExp_zero_vRoot, natCast_prime_pow]
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add, ← zpow_add]
  congr 2
  simp [cpTable]
  ring

end Torus

section Weyl

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem nrep_blockElt_one_eq :
    nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) = evalV [.n1, .n2, .n1, .n2] := by
  rw [ReeTag.blockElt, nrep_eq_prod ReeTag.F4.tag K (isReduced_reeOrbitWord ReeTag.F4 (fi 1))]
  rfl

omit [CharP K 2] in
theorem nrep_blockElt_one_mem_vStab :
    nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) ∈ vStab K := by
  rw [nrep_blockElt_one_eq]
  exact evalV_mem_vStab _

theorem vMat_nrep_blockElt_one :
    vMat (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1))) = CFSG.Blueprint.suzukiW K := by
  rw [nrep_blockElt_one_eq, vMat_evalV]
  simp only [evalVMat, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    VLetter.mat, mN1, mN2, mat4_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.Blueprint.suzukiW]

end Weyl

end CFSG.SectionRank.LargeRee
