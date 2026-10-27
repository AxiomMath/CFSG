module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

namespace TwE6UniqAbs

set_option maxRecDepth 100000

@[expose] def zlC (m0 m1 m2 m3 m4 m5 : ℤ) : List ℕ :=
  (if m0 + 2 * m1 + 2 * m2 + 3 * m3 + 2 * m4 + m5 = 3 then [0] else []) ++
  (if m0 = 0 then [1] else []) ++ (if m1 = 0 then [2] else []) ++ (if m2 = 0 then [3] else []) ++
  (if m3 = 0 then [4] else []) ++ (if m4 = 0 then [5] else []) ++ (if m5 = 0 then [6] else [])

@[expose] def cmpF (zl : List ℕ) (x : ℕ) : Finset (Option (Fin Tag.E6.rank)) :=
  ((compIdx (Tag.E6.rank + 1) (treePath e6Anc) zl x).map (idxNode (r := Tag.E6.rank))).toFinset

@[expose] def θ6 : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def szF (zl : List ℕ) (x : ℕ) : ℕ := kacCount Tag.E6 θ6 (cmpF zl x)

@[expose] def R6 : List (Fin Tag.E6.rank → ℤ) := Tag.E6.artifactRoots.map (toVec Tag.E6.rank)

@[expose] def dotμ (γ : Fin Tag.E6.rank → ℤ) (m0 m1 m2 m3 m4 m5 : ℤ) : ℤ :=
  γ 0 * m0 + γ 1 * m1 + γ 2 * m2 + γ 3 * m3 + γ 4 * m4 + γ 5 * m5

@[expose] def kcCountB (zl : List ℕ) : Bool := decide ((zl.map (cmpF zl)).toFinset.card ≤ 3)

@[expose] def kcTripleB (zl : List ℕ) : Bool :=
  zl.all fun x => zl.all fun y => zl.all fun z =>
    (cmpF zl x == cmpF zl y) || (cmpF zl x == cmpF zl z) || (cmpF zl y == cmpF zl z) ||
      ((szF zl x == 6) && (szF zl y == 6) && (szF zl z == 6))

@[expose] def kcGlueB (m0 m1 m2 m3 m4 m5 : ℤ) : Bool :=
  (zlC m0 m1 m2 m3 m4 m5).all fun x => (szF (zlC m0 m1 m2 m3 m4 m5) x != 6) ||
    ((R6.any fun γ => dotμ γ m0 m1 m2 m3 m4 m5 % 3 != 0) &&
     R6.all fun γ => R6.all fun γ' =>
       (!((R6.filter fun δ => decide (kacTest θ6
            (cmpF (zlC m0 m1 m2 m3 m4 m5) x) δ)).all fun δ => (iform γ δ == iform γ' δ))) ||
        ((dotμ γ m0 m1 m2 m3 m4 m5 - dotμ γ' m0 m1 m2 m3 m4 m5) % 3 == 0))

@[expose] def kcPairB (zl : List ℕ) : Bool :=
  zl.all fun x => (szF zl x != 6) ||
    (match compIdx (Tag.E6.rank + 1) (treePath e6Anc) zl x with
      | [u, v] => decide ((u, v) ∈ e6EdgeIdx)
      | _ => false)

theorem kc_sizes : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 2 ∨
      szF (zlC m0 m1 m2 m3 m4 m5) x = 6 ∨ 12 ≤ szF (zlC m0 m1 m2 m3 m4 m5) x := by
  decide +kernel

theorem kc_card2 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 2 →
      (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card = 1 := by
  decide +kernel

theorem kc_big : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, ∀ y ∈ zlC m0 m1 m2 m3 m4 m5,
      cmpF (zlC m0 m1 m2 m3 m4 m5) x ≠ cmpF (zlC m0 m1 m2 m3 m4 m5) y →
      12 ≤ szF (zlC m0 m1 m2 m3 m4 m5) x → 12 ≤ szF (zlC m0 m1 m2 m3 m4 m5) y → False := by
  decide +kernel

theorem kc_one : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, ∀ y ∈ zlC m0 m1 m2 m3 m4 m5,
      szF (zlC m0 m1 m2 m3 m4 m5) x = 2 → szF (zlC m0 m1 m2 m3 m4 m5) y = 2 →
        cmpF (zlC m0 m1 m2 m3 m4 m5) x = cmpF (zlC m0 m1 m2 m3 m4 m5) y := by
  decide +kernel

theorem kc_count : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    kcCountB (zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel

theorem kc_triple : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    kcTripleB (zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel

theorem kc_glue : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    kcGlueB m0 m1 m2 m3 m4 m5 = true := by
  decide +kernel

theorem kc_pair : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    kcPairB (zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel


section Bridge


theorem sum_rank_E6 {M : Type*} [AddCommMonoid M] (f : Fin Tag.E6.rank → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  have hr : Tag.E6.rank = 6 := rfl
  have h := Fintype.sum_equiv (finCongr hr) f
    (fun i : Fin 6 => f ((finCongr hr).symm i)) (fun i => by simp)
  rw [h, Fin.sum_univ_six]
  rfl

theorem dot_eq_dotμ (γ μ : Fin Tag.E6.rank → ℤ) :
    γ ⬝ᵥ μ = dotμ γ (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) (μ 5) := by
  unfold dotProduct dotμ
  rw [sum_rank_E6]

theorem θ_dot (μ : Fin Tag.E6.rank → ℤ) :
    kacE6.θ ⬝ᵥ μ = μ 0 + 2 * μ 1 + 2 * μ 2 + 3 * μ 3 + 2 * μ 4 + μ 5 := by
  unfold dotProduct
  rw [sum_rank_E6]
  simp [kacE6]

theorem exists_tuple_of_isNormal {μ : Fin Tag.E6.rank → ℤ} (hμ : kacE6.IsNormal 3 μ) :
    ∃ m0 m1 m2 m3 m4 m5 : Fin 4,
      (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) ∧
      μ 0 = ((m0 : ℕ) : ℤ) ∧ μ 1 = ((m1 : ℕ) : ℤ) ∧ μ 2 = ((m2 : ℕ) : ℤ) ∧
      μ 3 = ((m3 : ℕ) : ℤ) ∧ μ 4 = ((m4 : ℕ) : ℤ) ∧ μ 5 = ((m5 : ℕ) : ℤ) := by
  obtain ⟨h0, hle⟩ := hμ
  rw [θ_dot] at hle
  have a0 := h0 0
  have a1 := h0 1
  have a2 := h0 2
  have a3 := h0 3
  have a4 := h0 4
  have a5 := h0 5
  have hle' : μ 0 + 2 * μ 1 + 2 * μ 2 + 3 * μ 3 + 2 * μ 4 + μ 5 ≤ 3 := by exact_mod_cast hle
  refine ⟨⟨(μ 0).toNat, by omega⟩, ⟨(μ 1).toNat, by omega⟩, ⟨(μ 2).toNat, by omega⟩,
    ⟨(μ 3).toNat, by omega⟩, ⟨(μ 4).toNat, by omega⟩, ⟨(μ 5).toNat, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> simp <;> omega

theorem idxNode_zero' : idxNode (r := Tag.E6.rank) 0 = none := by
  simp [idxNode]

theorem idxNode_succ' {j : ℕ} (hj : j < Tag.E6.rank) :
    idxNode (r := Tag.E6.rank) (j + 1) = some ⟨j, hj⟩ := by
  unfold idxNode
  rw [dif_pos ⟨by omega, by simpa using hj⟩]
  rfl

theorem mem_zeroIdx_iff (μ : Fin Tag.E6.rank → ℤ) (n : ℕ) :
    n ∈ kacE6.zeroIdx 3 μ ↔ n ∈ zlC (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) (μ 5) := by
  rw [kacE6.mem_zeroIdx]
  have hd := θ_dot μ
  have h7 : Tag.E6.rank + 1 = 7 := rfl
  rw [h7]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n
    · rw [idxNode_zero']
      simp [KacData.IsZ, zlC, hd]
    · rw [idxNode_succ' (j := 0) (by decide)]
      simp [KacData.IsZ, zlC]
      try rfl
    · rw [idxNode_succ' (j := 1) (by decide)]
      simp [KacData.IsZ, zlC]
      try rfl
    · rw [idxNode_succ' (j := 2) (by decide)]
      simp [KacData.IsZ, zlC]
      try rfl
    · rw [idxNode_succ' (j := 3) (by decide)]
      simp [KacData.IsZ, zlC]
      try rfl
    · rw [idxNode_succ' (j := 4) (by decide)]
      simp [KacData.IsZ, zlC]
      try rfl
    · rw [idxNode_succ' (j := 5) (by decide)]
      simp [KacData.IsZ, zlC]
      try rfl
  · have : ¬ n < 7 := by omega
    simp only [this, false_and, false_iff]
    unfold zlC
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton]
    omega

theorem compIdx_congr {n : ℕ} {tp : ℕ → ℕ → List ℕ} {zl zl' : List ℕ}
    (h : ∀ w, w ∈ zl ↔ w ∈ zl') (x : ℕ) : compIdx n tp zl x = compIdx n tp zl' x := by
  simp [compIdx, List.elem_eq_mem, h]

theorem lt_of_mem_compIdx {n : ℕ} {tp : ℕ → ℕ → List ℕ} {zl : List ℕ} {x c : ℕ}
    (h : c ∈ compIdx n tp zl x) : c < n := by
  simp only [compIdx, List.mem_filter, List.mem_range] at h
  exact h.1

theorem comp_eq_cmpF {μ : Fin Tag.E6.rank → ℤ} {x : Option (Fin Tag.E6.rank)}
    (hx : kacE6.IsZ 3 μ x) :
    kacE6.comp 3 μ x =
      (cmpF (zlC (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) (μ 5)) (nodeIdx x) :
        Set (Option (Fin Tag.E6.rank))) := by
  rw [kacE6.comp_eq_compIdx e6_tree e6_adj hx]
  have hcong := compIdx_congr (n := Tag.E6.rank + 1) (tp := treePath e6Anc) (mem_zeroIdx_iff μ)
    (nodeIdx x)
  rw [hcong]
  ext y
  simp only [Set.mem_setOf_eq, cmpF, Finset.mem_coe, List.mem_toFinset, List.mem_map]
  constructor
  · intro hy
    exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
  · rintro ⟨c, hc, rfl⟩
    rw [nodeIdx_idxNode (lt_of_mem_compIdx hc)]
    exact hc

theorem nodeIdx_mem_zlC {μ : Fin Tag.E6.rank → ℤ} {x : Option (Fin Tag.E6.rank)}
    (hx : kacE6.IsZ 3 μ x) : nodeIdx x ∈ zlC (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) (μ 5) :=
  (mem_zeroIdx_iff μ _).1 (kacE6.mem_zeroIdx.2 ⟨nodeIdx_lt x, by rw [idxNode_nodeIdx]; exact hx⟩)

theorem kac_pinned_classes {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) :
    ∃ (ζ : Lˣ) (w : WeylGroup Tag.E6) (μ : Fin Tag.E6.rank → ℤ),
      IsPrimitiveRoot (ζ : L) 3 ∧ kacE6.IsNormal 3 μ ∧
      (∀ β, rootChar a β = ζ ^ ((w • β) ⬝ᵥ μ)) ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ (x : Option (Fin Tag.E6.rank))
        (C : Finset (Option (Fin Tag.E6.rank))),
        kacE6.IsZ 3 μ x ∧ kacE6.comp 3 μ x = (C : Set (Option (Fin Tag.E6.rank))) ∧ (∃ y, y ∉ C) ∧
        componentRoots (rootCharHom a) i =
          (fun α => w⁻¹ • α) '' kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) ∧
        compRank (componentRoots (rootCharHom a) i) = C.card ∧
        (componentRoots (rootCharHom a) i).ncard = kacCount Tag.E6 kacE6.θ C := by
  classical
  have : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ₀ := hζ₀.isUnit (by norm_num)
  have hζ : IsPrimitiveRoot ((hu.unit : Lˣ) : L) 3 := by simpa using hζ₀
  obtain ⟨w, μ, hμ, hw⟩ := kacE6.exists_weyl_normal (by norm_num : 0 < 3) hζ a hap
  set a' : Fin Tag.E6.rank → Lˣ := fun i => hu.unit ^ μ i with ha'
  have hζu : IsPrimitiveRoot hu.unit 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hconj : IsCharConj (rootCharHom a) (rootCharHom a') w := by
    intro v
    change rootChar a' v = rootChar a (w⁻¹ • v)
    rw [hw, smul_inv_smul, ha', KacData.rootChar_eq_zpow]
  have hχ : ∀ γ, IsRoot Tag.E6 γ →
      ((rootCharHom a') (Multiplicative.ofAdd γ) = 1 ↔ ((3 : ℕ) : ℤ) ∣ γ ⬝ᵥ μ) := by
    intro γ _
    change rootChar a' γ = 1 ↔ _
    rw [ha', KacData.rootChar_eq_zpow]
    exact hζu.zpow_eq_one_iff_dvd _
  refine ⟨hu.unit, w, μ, hζ, hμ, hw, fun i => ?_⟩
  obtain ⟨i', hi'⟩ := KacData.componentRoots_smul_of_isCharConj hconj i
  obtain ⟨x, hx, hxi⟩ := kacE6.componentRoots_eq_rootsOf facts_E6 (by norm_num) hμ hχ i'
  obtain ⟨C, hC⟩ := (Set.toFinite (kacE6.comp 3 μ x)).exists_finset_coe
  have hC' : kacE6.comp 3 μ x = (C : Set (Option (Fin Tag.E6.rank))) := hC.symm
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacE6 (by norm_num : 0 < 3) μ x
    exact ⟨y, fun h => hy (by rw [hC']; exact h)⟩
  have hi : componentRoots (rootCharHom a) i =
      (fun α => w⁻¹ • α) '' kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) := by
    rw [hi', hxi, hC']
  refine ⟨x, C, hx, hC', hCp, hi, ?_, ?_⟩
  · rw [hi, compRank_image, compRank_rootsOf kacE6 facts_E6 hCp]
  · rw [hi, ncard_image_smul, ncard_rootsOf kacE6 facts_E6 hCp]

theorem kac_class_data {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) :
    ∃ (ζ : Lˣ) (w : WeylGroup Tag.E6) (m0 m1 m2 m3 m4 m5 : Fin 4),
      IsPrimitiveRoot (ζ : L) 3 ∧
      (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) ∧
      (∀ β, rootChar a β = ζ ^ dotμ (w • β) ((m0 : ℕ) : ℤ) ((m1 : ℕ) : ℤ) ((m2 : ℕ) : ℤ)
        ((m3 : ℕ) : ℤ) ((m4 : ℕ) : ℤ) ((m5 : ℕ) : ℤ)) ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ x : ℕ, x ∈ zlC m0 m1 m2 m3 m4 m5 ∧
        componentRoots (rootCharHom a) i =
          (fun α => w⁻¹ • α) '' kacE6.rootsOf
            (cmpF (zlC m0 m1 m2 m3 m4 m5) x : Set (Option (Fin Tag.E6.rank))) ∧
        (componentRoots (rootCharHom a) i).ncard = szF (zlC m0 m1 m2 m3 m4 m5) x ∧
        compRank (componentRoots (rootCharHom a) i) = (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card ∧
        ∃ y, y ∉ cmpF (zlC m0 m1 m2 m3 m4 m5) x := by
  obtain ⟨ζ, w, μ, hζ, hμ, hw, hcl⟩ := kac_pinned_classes h3 hap
  obtain ⟨m0, m1, m2, m3, m4, m5, hsum, e0, e1, e2, e3, e4, e5⟩ := exists_tuple_of_isNormal hμ
  refine ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, fun β => ?_, fun i => ?_⟩
  · rw [hw β, dot_eq_dotμ, e0, e1, e2, e3, e4, e5]
  obtain ⟨x, C, hx, hxC, hCp, hi, hrank, hn⟩ := hcl i
  have hxz := nodeIdx_mem_zlC hx
  rw [e0, e1, e2, e3, e4, e5] at hxz
  have hCeq : C = cmpF (zlC m0 m1 m2 m3 m4 m5) (nodeIdx x) := by
    apply Finset.coe_injective
    rw [← hxC, comp_eq_cmpF hx, e0, e1, e2, e3, e4, e5]
  refine ⟨nodeIdx x, hxz, ?_, ?_, ?_, ?_⟩
  · rw [hi, hCeq]
  · rw [hn, hCeq]
    rfl
  · rw [hrank, hCeq]
  · rw [← hCeq]
    exact hCp

end Bridge


section Classes


theorem eq_of_componentRoots_eq {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i j : KernelComponent χ}
    (h : componentRoots χ i = componentRoots χ j) : i = j := by
  obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
  have h1 : α ∈ componentRoots χ (⟦⟨α, hα⟩⟧ : KernelComponent χ) := ⟨hα, rfl⟩
  rw [h] at h1
  obtain ⟨hα', e⟩ := h1
  exact e

theorem four_le_card {α : Type*} [DecidableEq α] {T : Finset α} {a b c d : α} (ha : a ∈ T)
    (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ T.card := by
  have hsub : ({a, b, c, d} : Finset α) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a, b, c, d} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  exact h4 ▸ Finset.card_le_card hsub

structure KacFacts {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) : Prop where
  sizes : ∀ i : KernelComponent (rootCharHom a),
    (componentRoots (rootCharHom a) i).ncard = 2 ∨ (componentRoots (rootCharHom a) i).ncard = 6 ∨
      12 ≤ (componentRoots (rootCharHom a) i).ncard
  rank_one : ∀ i : KernelComponent (rootCharHom a),
    (componentRoots (rootCharHom a) i).ncard = 2 →
      compRank (componentRoots (rootCharHom a) i) = 1
  big : ∀ i j : KernelComponent (rootCharHom a), i ≠ j →
    12 ≤ (componentRoots (rootCharHom a) i).ncard →
      12 ≤ (componentRoots (rootCharHom a) j).ncard → False
  one : ∀ i j : KernelComponent (rootCharHom a),
    (componentRoots (rootCharHom a) i).ncard = 2 →
      (componentRoots (rootCharHom a) j).ncard = 2 → i = j
  four : ∀ i j k l : KernelComponent (rootCharHom a), i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
    k ≠ l → False
  three : ∀ i j k : KernelComponent (rootCharHom a), i ≠ j → i ≠ k → j ≠ k →
    (componentRoots (rootCharHom a) i).ncard = 6 ∧ (componentRoots (rootCharHom a) j).ncard = 6 ∧
      (componentRoots (rootCharHom a) k).ncard = 6
  frame : ∀ i : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) i).ncard = 6 →
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2) ∧
        componentRoots (rootCharHom a) i = frameRoots σ
  glue : ∀ i : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) i).ncard = 6 →
    (∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ rootChar a γ ≠ 1) ∧
      ∀ γ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → IsRoot Tag.E6 γ' →
        (∀ δ ∈ componentRoots (rootCharHom a) i, iform γ δ = iform γ' δ) →
          rootChar a γ = rootChar a γ'

end Classes

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
