module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPairs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

variable (r) in
@[expose] def plusPos : Fin r ⊕ Fin r → ℕ :=
  Sum.elim (fun i => i.val) (fun i => 2 * r - 1 - i.val)

theorem plusPos_inl (i : Fin r) : plusPos r (Sum.inl i) = i := rfl

theorem plusPos_inr (i : Fin r) : plusPos r (Sum.inr i) = 2 * r - 1 - i := rfl

theorem plusPos_lt (x : Fin r ⊕ Fin r) : plusPos r x < 2 * r := by
  rcases x with i | i
  · rw [plusPos_inl]; have := i.isLt; omega
  · rw [plusPos_inr]; have := i.isLt; omega

variable (r K) in
@[expose] def plusCutSpace (c : ℕ) : Submodule K (Fin r ⊕ Fin r → K) where
  carrier := {v | ∀ u, c ≤ plusPos r u → v u = 0}
  add_mem' ha hb u hu := by simp [ha u hu, hb u hu]
  zero_mem' _ _ := rfl
  smul_mem' c v hv u hu := by simp [hv u hu]

theorem mem_plusCutSpace {c : ℕ} {v : Fin r ⊕ Fin r → K} :
    v ∈ plusCutSpace r K c ↔ ∀ u, c ≤ plusPos r u → v u = 0 :=
  Iff.rfl

theorem plusCutSpace_zero : plusCutSpace r K 0 = ⊥ := by
  ext v
  simp only [mem_plusCutSpace, zero_le, true_implies, Submodule.mem_bot]
  exact ⟨fun h => funext h, fun h u => by rw [h]; rfl⟩

theorem plusCutSpace_mono {c c' : ℕ} (h : c ≤ c') : plusCutSpace r K c ≤ plusCutSpace r K c' :=
  fun _ hv u hu => hv u (h.trans hu)

theorem flag_eq_plusCutSpace {d : ℕ} (hd : d ≤ r) : flag r K d = plusCutSpace r K d := by
  ext v
  rw [mem_flag, mem_plusCutSpace]
  constructor
  · rintro ⟨h1, h2⟩ u hu
    rcases u with j | j
    · exact h2 j hu
    · exact h1 j
  · intro h
    refine ⟨fun j => h _ ?_, fun j hj => h _ hj⟩
    rw [plusPos_inr]
    have := j.isLt
    omega

theorem mem_orthogonal_flag_iff {d : ℕ} (hd : d ≤ r) {v : Fin r ⊕ Fin r → K} :
    v ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus r K)) (flag r K d) ↔
      v ∈ plusCutSpace r K (2 * r - d) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_plusCutSpace]
  have key : (∀ n ∈ flag r K d, polarBilin (quadPlus r K) n v = 0) ↔
      ∀ w ∈ flag r K d, polar (quadPlus r K) v w = 0 := by
    refine forall₂_congr fun w _ => ?_
    rw [polarBilin_apply_apply, polar_comm]
  rw [key, polar_flag_eq_zero_iff]
  constructor
  · intro h u hu
    rcases u with j | j
    · rw [plusPos_inl] at hu
      have := j.isLt
      omega
    · rw [plusPos_inr] at hu
      exact h j (by have := j.isLt; omega)
  · intro h j hj
    exact h _ (by rw [plusPos_inr]; omega)

@[expose] def PlusCut (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (c : ℕ) : Prop :=
  ∀ u w, plusPos r w < c → c ≤ plusPos r u → autMat g u w = 0

theorem autMat_apply_eq (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
    (u w : Fin r ⊕ Fin r) : autMat g u w = g (Pi.single w 1) u := by
  rw [apply_eq_autMat_mulVec, mulVec_single_one, col_apply]

theorem plusCut_of_mapsTo {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} {c : ℕ}
    (hg : ∀ v ∈ plusCutSpace r K c, g v ∈ plusCutSpace r K c) : PlusCut g c := by
  intro u w hw hu
  rw [autMat_apply_eq]
  refine hg _ (fun x hx => ?_) u hu
  refine Pi.single_eq_of_ne ?_ _
  rintro rfl
  omega

theorem plusCut_zero (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) : PlusCut g 0 :=
  fun _ _ hw _ => absurd hw (Nat.not_lt_zero _)

theorem plusCut_of_smul_flag {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} {d : ℕ}
    (hd : d ≤ r) (hg : g • flag r K d = flag r K d) : PlusCut g d := by
  refine plusCut_of_mapsTo fun v hv => ?_
  rw [← flag_eq_plusCutSpace hd] at hv ⊢
  rw [← hg]
  exact ⟨v, hv, rfl⟩

theorem mapsTo_orthogonal_of_smul_eq {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) {d : ℕ} (hd : d ≤ r)
    (hg : g • flag r K d = flag r K d) :
    ∀ v ∈ plusCutSpace r K (2 * r - d), g v ∈ plusCutSpace r K (2 * r - d) := by
  intro v hv
  rw [← mem_orthogonal_flag_iff hd] at hv ⊢
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro y hy
  have hy' : g.symm y ∈ flag r K d := by
    rw [← hg] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa using hz
  have h := hv _ hy'
  rw [polarBilin_apply_apply] at h ⊢
  rw [← polar_map_of_mem hgO, LinearEquiv.apply_symm_apply] at h
  exact h

theorem plusCut_of_smul_flag_orthogonal {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) {d : ℕ} (hd : d ≤ r)
    (hg : g • flag r K d = flag r K d) : PlusCut g (2 * r - d) :=
  plusCut_of_mapsTo (mapsTo_orthogonal_of_smul_eq hgO hd hg)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def plusBlockHom
    (H : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) {φ : ι → Fin r ⊕ Fin r}
    (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ plusPos r x ∧ plusPos r x < b)
    (ha : ∀ g ∈ H, PlusCut g a) (hb : ∀ g ∈ H, PlusCut g b) : ↥H →* GL ι K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] _)).submatrix φ φ
      map_one' := by
        rw [Subgroup.coe_one, map_one]
        exact submatrix_one_embedding ⟨φ, hφ⟩
      map_mul' := fun g h => by
        rw [Subgroup.coe_mul, map_mul]
        exact submatrix_mul_of_cuts hφ hrange (ha g g.2) (hb h h.2) }

omit [Fintype ι] in
theorem sub_mem_plusCutSpace_of_block_eq_one
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} {φ : ι → Fin r ⊕ Fin r} {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ plusPos r x ∧ plusPos r x < b) (ha : PlusCut g a)
    (h1 : (autMat g).submatrix φ φ = 1) {x : Fin r ⊕ Fin r → K} (hx : x ∈ plusCutSpace r K b)
    (hgx : g x ∈ plusCutSpace r K b) : g x - x ∈ plusCutSpace r K a := by
  intro u hu
  rw [Pi.sub_apply]
  by_cases hub : b ≤ plusPos r u
  · rw [hgx u hub, hx u hub, sub_zero]
  obtain ⟨s, rfl⟩ := (hrange u).2 ⟨hu, not_le.mp hub⟩
  rw [apply_eq_autMat_mulVec, mulVec, dotProduct, sub_eq_zero]
  rw [Finset.sum_eq_single_of_mem (φ s) (Finset.mem_univ _)]
  · have := congrFun (congrFun h1 s) s
    rw [submatrix_apply, one_apply_eq] at this
    rw [this, one_mul]
  · intro w _ hws
    by_cases hwb : b ≤ plusPos r w
    · rw [hx w hwb, mul_zero]
    by_cases hwa : a ≤ plusPos r w
    · obtain ⟨s', rfl⟩ := (hrange w).2 ⟨hwa, not_le.mp hwb⟩
      have hss : s ≠ s' := fun h => hws (by rw [h])
      have := congrFun (congrFun h1 s) s'
      rw [submatrix_apply, one_apply_ne hss] at this
      rw [this, zero_mul]
    · rw [ha _ _ (not_le.mp hwa) hu, zero_mul]

end CFSG.AGLEmbedding.LeviBlock
