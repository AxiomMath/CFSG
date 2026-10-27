module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearEigen
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearBlocks

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K] {n : ℕ}

@[expose] def cutBlockVec (n c d : ℕ) (w : Fin (d - c) → K) : Fin n → K :=
  fun k => if h : c ≤ (k : ℕ) ∧ (k : ℕ) < d then w ⟨k - c, by omega⟩ else 0

theorem cutBlockVec_mem_flagSpace {c d : ℕ} (w : Fin (d - c) → K) :
    cutBlockVec n c d w ∈ flagSpace n K d :=
  mem_flagSpace.mpr fun _ hk => dite_eq_right (by omega)

theorem cutBlockVec_not_mem_flagSpace {c d : ℕ} (hd : d ≤ n) {w : Fin (d - c) → K}
    (hw : w ≠ 0) : cutBlockVec n c d w ∉ flagSpace n K c := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' := i.isLt
  intro hmem
  have h := mem_flagSpace.mp hmem ⟨c + i, by omega⟩ (by simp)
  rw [cutBlockVec, dite_eq_left (by simp; omega)] at h
  exact hi (by simpa using h)

theorem mulVec_cutBlockVec_sub_mem_flagSpace {I : Set ℕ} {c d : ℕ} (h : IsConsecutiveCut n I c d)
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ flagStabilizer n K I) {μ : K}
    {w : Fin (d - c) → K}
    (hw : cutBlock (x : Matrix (Fin n) (Fin n) K) c d h.2.1 *ᵥ w = μ • w) :
    (x : Matrix (Fin n) (Fin n) K) *ᵥ cutBlockVec n c d w - μ • cutBlockVec n c d w ∈
      flagSpace n K c := by
  have hdn : d ≤ n := h.2.1
  rw [mem_flagSpace]
  intro k hk
  rw [Pi.sub_apply, Pi.smul_apply, sub_eq_zero]
  by_cases hkd : (k : ℕ) < d
  · have hsum : ((x : Matrix (Fin n) (Fin n) K) *ᵥ cutBlockVec n c d w) k =
        (cutBlock (x : Matrix (Fin n) (Fin n) K) c d h.2.1 *ᵥ w) ⟨k - c, by omega⟩ := by
      simp only [Matrix.mulVec, dotProduct, cutBlock_apply]
      symm
      refine Fintype.sum_of_injective
        (fun i : Fin (d - c) => (⟨c + i, by have := i.isLt; omega⟩ : Fin n))
        (fun i₁ i₂ hi => Fin.ext (by simpa using congrArg Fin.val hi)) _ _
        (fun j hj => ?_) (fun i => ?_)
      · rw [cutBlockVec, dite_eq_right, mul_zero]
        rintro ⟨hcj, hjd⟩
        exact hj ⟨⟨(j : ℕ) - c, by omega⟩, Fin.ext (by simp; omega)⟩
      · have hi := i.isLt
        rw [cutBlockVec, dite_eq_left (by simp; omega)]
        have e1 : (⟨c + ((k : ℕ) - c), by omega⟩ : Fin n) = k := Fin.ext (Nat.add_sub_cancel' hk)
        rw [e1]
        exact congrArg _ (congrArg w (Fin.ext (by simp)))
    rw [hsum, hw, Pi.smul_apply, cutBlockVec, dite_eq_left ⟨hk, hkd⟩]
  · have hd : d ∈ I := h.2.2.2.1.resolve_left (by omega)
    have hzero : ((x : Matrix (Fin n) (Fin n) K) *ᵥ cutBlockVec n c d w) k = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < d
      · rw [apply_eq_zero_of_mem_flagStabilizer (Or.inr hd) hx hj (by omega), zero_mul]
      · rw [cutBlockVec, dite_eq_right (by omega), mul_zero]
    rw [hzero, cutBlockVec, dite_eq_right (by omega), smul_zero]

theorem mulVec_mem_flagSpace_of_mem {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ flagStabilizer n K I) {d : ℕ} (hd : d = 0 ∨ d = n ∨ d ∈ I) {y : Fin n → K}
    (hy : y ∈ flagSpace n K d) : (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ flagSpace n K d := by
  rcases hd with rfl | rfl | hd
  · rw [flagSpace_zero, Submodule.mem_bot] at hy ⊢
    rw [hy, Matrix.mulVec_zero]
  · exact mem_flagSpace.mpr fun j hj => absurd j.isLt (by omega)
  · rw [← mem_stabilizer.mp (mem_flagStabilizer.mp hx d hd)]
    exact ⟨y, hy, rfl⟩

theorem ne_zero_of_pow_three_eq_scalar (hn : 1 ≤ n) {t : SpecialLinearGroup (Fin n) K} {ζ : K}
    (ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ) : ζ ≠ 0 := by
  rintro rfl
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := congrArg Matrix.det ht
  rw [Matrix.det_pow, t.2, one_pow, map_zero, Matrix.det_zero] at h
  exact one_ne_zero h

theorem cutBlock_pow_three_eq_scalar {I : Set ℕ} {c d : ℕ} (h : IsConsecutiveCut n I c d)
    {t : SpecialLinearGroup (Fin n) K} (htI : t ∈ flagStabilizer n K I) {ζ : K}
    (ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ) :
    cutBlock (t : Matrix (Fin n) (Fin n) K) c d h.2.1 ^ 3 = scalar (Fin (d - c)) ζ := by
  have h1 : cutBlock (t : Matrix (Fin n) (Fin n) K) c d h.2.1 ^ 3 =
      cutBlockHom h (⟨t, htI⟩ ^ 3) := by
    rw [map_pow, cutBlockHom_apply]
  rw [h1, cutBlockHom_apply, Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, ht]
  ext i j
  rw [cutBlock_apply, scalar_apply, scalar_apply, diagonal_apply, diagonal_apply]
  simp [Fin.ext_iff]

variable [CharP K 2]

theorem exists_eigen_of_cutBlock {I : Set ℕ} {t : SpecialLinearGroup (Fin n) K} {ζ μ : K}
    (ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ) (hμ : μ ^ 3 = ζ) {c d : ℕ}
    (h : IsConsecutiveCut n I c d) (htI : t ∈ flagStabilizer n K I) {w : Fin (d - c) → K}
    (hw : cutBlock (t : Matrix (Fin n) (Fin n) K) c d h.2.1 *ᵥ w = μ • w) (hw0 : w ≠ 0) :
    ∃ v : Fin n → K, (t : Matrix (Fin n) (Fin n) K) *ᵥ v = μ • v ∧ v ∈ flagSpace n K d ∧
      v ∉ flagSpace n K c := by
  set T : Matrix (Fin n) (Fin n) K := (t : Matrix (Fin n) (Fin n) K) with hT
  set b : Fin n → K := cutBlockVec n c d w with hb
  have hf := mulVec_cutBlockVec_sub_mem_flagSpace h htI hw
  have hμ0 : μ ≠ 0 := fun h0 => ne_zero_of_pow_three_eq_scalar
    (by have := h.1; have := h.2.1; omega) ht (by rw [← hμ, h0, zero_pow three_ne_zero])
  have hT3 : T *ᵥ (T *ᵥ (T *ᵥ b)) = ζ • b := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', ht, scalarMatrix_mulVec]
  set v : Fin n → K := T *ᵥ (T *ᵥ b) + μ • (T *ᵥ b) + μ ^ 2 • b with hv
  have hvb : v - μ ^ 2 • b = T *ᵥ (T *ᵥ b - μ • b) := by
    have hneg : -μ = μ := CharTwo.neg_eq μ
    calc v - μ ^ 2 • b = T *ᵥ (T *ᵥ b) + μ • (T *ᵥ b) := by rw [hv]; abel
      _ = T *ᵥ (T *ᵥ b) + (-μ) • (T *ᵥ b) := by rw [hneg]
      _ = T *ᵥ (T *ᵥ b - μ • b) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, neg_smul, sub_eq_add_neg]
  have hvb' : v - μ ^ 2 • b ∈ flagSpace n K c := by
    rw [hvb]
    exact mulVec_mem_flagSpace_of_mem htI (h.2.2.1.imp id Or.inr) hf
  refine ⟨v, ?_, ?_, fun hvc => ?_⟩
  · rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hT3,
      ← hμ]
    module
  · have hbd : b ∈ flagSpace n K d := cutBlockVec_mem_flagSpace w
    have hcd : flagSpace n K c ≤ flagSpace n K d := fun y hy =>
      mem_flagSpace.mpr fun j hj => mem_flagSpace.mp hy j (by have := h.1; omega)
    have := Submodule.add_mem _ (hcd hvb') (Submodule.smul_mem _ (μ ^ 2) hbd)
    rwa [sub_add_cancel] at this
  · have h2 : μ ^ 2 • b ∈ flagSpace n K c := by
      have := Submodule.sub_mem _ hvc hvb'
      rwa [sub_sub_cancel] at this
    exact cutBlockVec_not_mem_flagSpace h.2.1 hw0
      ((Submodule.smul_mem_iff _ (pow_ne_zero 2 hμ0)).mp h2)

theorem false_of_eigen_mem_of_not_mem {t : SpecialLinearGroup (Fin n) K} {ζ μ : K}
    (ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ) {W : Submodule K (Fin n → K)}
    (hW : ∀ g ∈ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {v v' : Fin n → K} (hv : (t : Matrix (Fin n) (Fin n) K) *ᵥ v = μ • v)
    (hv' : (t : Matrix (Fin n) (Fin n) K) *ᵥ v' = μ • v') (hvW : v ∈ W) (hv0 : v ≠ 0)
    (hv'W : v' ∉ W) : False := by
  set E := LinearMap.ker (mulVecLin (t : Matrix (Fin n) (Fin n) K) - μ • LinearMap.id) with hE
  have hvE : v ∈ E := mem_ker_sub_smul_iff.mpr hv
  have hv'E : v' ∈ E := mem_ker_sub_smul_iff.mpr hv'
  have hli := LinearThreeKit.linearIndependent_pair_of_notMem hvW hv0 hv'W
  have hdim : 2 ≤ Module.finrank K E := by
    have hle : Submodule.span K (Set.range ![v, v']) ≤ E := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hvE
      · exact hv'E
    have := Submodule.finrank_mono hle
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at this
  rcases eigenSpaceRigid_holds K n 3 ⟨1, rfl⟩ t ζ μ ht hdim W hW with h | h
  · have hmem : v ∈ W ⊓ E := ⟨hvW, hvE⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hv0 hmem
  · exact hv'W (h hv'E)

theorem false_of_eigen_cutBlocks {I : Set ℕ} {t : SpecialLinearGroup (Fin n) K} {ζ μ : K}
    (ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ) (hμ : μ ^ 3 = ζ)
    (hC : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I) {c d c' d' : ℕ} (h : IsConsecutiveCut n I c d)
    (h' : IsConsecutiveCut n I c' d') (hdc : d ≤ c') {w : Fin (d - c) → K}
    {w' : Fin (d' - c') → K}
    (hw : cutBlock (t : Matrix (Fin n) (Fin n) K) c d h.2.1 *ᵥ w = μ • w) (hw0 : w ≠ 0)
    (hw' : cutBlock (t : Matrix (Fin n) (Fin n) K) c' d' h'.2.1 *ᵥ w' = μ • w')
    (hw'0 : w' ≠ 0) : False := by
  have htI : t ∈ flagStabilizer n K I :=
    hC (Subgroup.mem_centralizer_iff.mpr fun x hx => by rw [Set.mem_singleton_iff.mp hx])
  obtain ⟨v, hv, hvd, hvc⟩ := exists_eigen_of_cutBlock ht hμ h htI hw hw0
  obtain ⟨v', hv', -, hv'c⟩ := exists_eigen_of_cutBlock ht hμ h' htI hw' hw'0
  have hc' : c' ∈ I := h'.2.2.1.resolve_left (by have := h.1; omega)
  refine false_of_eigen_mem_of_not_mem ht (W := flagSpace n K c')
    (fun g hg y hy => mulVec_mem_flagSpace_of_mem (hC hg) (Or.inr (Or.inr hc')) hy) hv hv'
    (mem_flagSpace.mpr fun j hj => mem_flagSpace.mp hvd j (by omega)) ?_ hv'c
  rintro rfl
  exact hvc (Submodule.zero_mem _)

end CFSG.AGLEmbedding.ToralCensus
