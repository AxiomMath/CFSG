module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag3

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] {m : ℕ}

section Point

theorem mem_pt_iff {g : SpecialLinearGroup (Fin (m + 1)) K} :
    g ∈ flagStabilizer (m + 1) K {1} ↔ ∀ i : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.succ 0 = 0 := by
  rw [flagStabilizer_singleton]
  constructor
  · intro h i
    exact stabilizer_entries h (by simp) (by simp)
  · intro h
    refine mem_stabilizer_flagSpace_of_entries fun k l hl hk => ?_
    have hl0 : l = 0 := Fin.ext (by simpa using hl)
    obtain ⟨i, rfl⟩ : ∃ i : Fin m, i.succ = k := by
      refine ⟨⟨k - 1, by omega⟩, Fin.ext ?_⟩
      simp; omega
    rw [hl0]
    exact h i

theorem det_pt (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (h : ∀ i : Fin m, A i.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]


theorem pt_g00 [Finite K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin (m + 1)) K}
    (hg : g ∈ flagStabilizer (m + 1) K {1}) : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 = 1 := by
  have hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1 := g.2
  rw [det_pt _ (mem_pt_iff.1 hg)] at hdet
  rcases eq_zero_or_eq_one_of_card_two hK ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0) with
    h0 | h1
  · rw [h0, zero_mul] at hdet
    exact absurd hdet zero_ne_one
  · exact h1

theorem pt_det_block [Finite K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin (m + 1)) K}
    (hg : g ∈ flagStabilizer (m + 1) K {1}) :
    ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ).det = 1 := by
  have hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1 := g.2
  rw [det_pt _ (mem_pt_iff.1 hg), pt_g00 hK hg, one_mul] at hdet
  exact hdet

theorem pt_mul_block {g h : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hg : ∀ i : Fin m, g i.succ 0 = 0) :
    (g * h).submatrix Fin.succ Fin.succ = g.submatrix Fin.succ Fin.succ * h.submatrix Fin.succ Fin.succ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, hg]

@[expose] noncomputable def leviPt [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    ↥(flagStabilizer (m + 1) K {1}) →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨(g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ,
    pt_det_block hK g.2⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.submatrix_one _ (Fin.succ_injective _)
  map_mul' g h := by
    apply Subtype.ext
    exact pt_mul_block (mem_pt_iff.1 g.2)

theorem leviPt_apply [Finite K] (hK : Nat.card K = 2) (g : ↥(flagStabilizer (m + 1) K {1})) (i j : Fin m) :
    ((leviPt hK m g : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) i j =
      (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.succ j.succ := rfl

theorem pt_ker_sq [Finite K] [CharP K 2] (hK : Nat.card K = 2) (g : ↥(flagStabilizer (m + 1) K {1}))
    (hg : leviPt hK m g = 1) : g * g = 1 := by
  have h00 := pt_g00 hK g.2
  have hcol := mem_pt_iff.1 g.2
  have hblk : ∀ i j : Fin m, (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.succ j.succ =
      (1 : Matrix (Fin m) (Fin m) K) i j := fun i j => by
    have := congrFun (congrFun (congrArg (fun x : SpecialLinearGroup (Fin m) K =>
      (x : Matrix (Fin m) (Fin m) K)) hg) i) j
    exact this
  apply Subtype.ext
  apply Subtype.ext
  show (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h00, hcol]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h00, hblk, Matrix.one_apply]
    exact CharTwo.add_self_eq_zero _
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h00, hcol]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hcol, hblk, Matrix.one_apply]

theorem pt_ker_isPGroup [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    IsPGroup 2 (leviPt (K := K) hK m).ker := by
  intro x
  refine ⟨1, ?_⟩
  have hxx : x * x = 1 := Subtype.ext (pt_ker_sq hK x.1 (MonoidHom.mem_ker.1 x.2))
  rw [pow_one, pow_two]
  exact hxx

@[expose] def diagPt (A : Matrix (Fin m) (Fin m) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

theorem diagPt_col (A : Matrix (Fin m) (Fin m) K) (i : Fin m) : diagPt A i.succ 0 = 0 := by
  simp [diagPt]

theorem diagPt_block (A : Matrix (Fin m) (Fin m) K) :
    (diagPt A).submatrix Fin.succ Fin.succ = A := by
  ext i j
  simp [diagPt]

theorem diagPt_det (A : Matrix (Fin m) (Fin m) K) : (diagPt A).det = A.det := by
  rw [det_pt _ (diagPt_col A), diagPt_block]
  simp [diagPt]

theorem leviPt_surjective [Finite K] (hK : Nat.card K = 2) :
    Function.Surjective (leviPt (K := K) hK m) := by
  intro A
  let g : SpecialLinearGroup (Fin (m + 1)) K := ⟨diagPt (A : Matrix (Fin m) (Fin m) K), by
    rw [diagPt_det]; exact A.2⟩
  have hg : g ∈ flagStabilizer (m + 1) K {1} := mem_pt_iff.2 (diagPt_col _)
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  exact diagPt_block _

@[expose] noncomputable def ptT (K : Type) [Field K] (j : Fin m) : SpecialLinearGroup (Fin (m + 1)) K :=
  SpecialLinearGroup.transvection (show (0 : Fin (m + 1)) ≠ j.succ from (Fin.succ_ne_zero j).symm) 1

theorem coe_ptT (j : Fin m) :
    ((ptT K j : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      1 + Matrix.single 0 j.succ 1 := rfl

theorem ptT_mem (j : Fin m) : ptT K j ∈ flagStabilizer (m + 1) K {1} := by
  refine mem_pt_iff.2 fun i => ?_
  rw [coe_ptT]
  simp [Fin.succ_ne_zero]

theorem ptT_ker [Finite K] (hK : Nat.card K = 2) (j : Fin m) :
    leviPt hK m ⟨ptT K j, ptT_mem j⟩ = 1 := by
  apply Subtype.ext
  ext a b
  simp [leviPt_apply, coe_ptT, Matrix.single_apply, Matrix.one_apply]
  intro h
  exact absurd h.symm (Fin.succ_ne_zero a)

theorem pt_centralizer [Finite K] (hK : Nat.card K = 2) (x : ↥(flagStabilizer (m + 1) K {1}))
    (hx : ∀ n : ↥(flagStabilizer (m + 1) K {1}), n ∈ (leviPt hK m).ker → x * n = n * x) :
    x ∈ (leviPt hK m).ker := by
  have h00 := pt_g00 hK x.2
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  ext j j'
  have h := congrArg (fun y : ↥(flagStabilizer (m + 1) K {1}) =>
    ((y : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 j'.succ)
    (hx ⟨ptT K j, ptT_mem j⟩ (MonoidHom.mem_ker.2 (ptT_ker hK j)))
  simp [coe_ptT, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, Fin.sum_univ_succ,
    Fin.succ_ne_zero, h00, Matrix.one_apply, Fin.succ_inj, (Fin.succ_ne_zero _).symm] at h
  simp [leviPt_apply, Matrix.one_apply]
  linear_combination -h

end Point

section Hyperplane

theorem mem_hyp_iff {g : SpecialLinearGroup (Fin (m + 1)) K} :
    g ∈ flagStabilizer (m + 1) K {m} ↔
      ∀ j : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) j.castSucc = 0 := by
  rw [flagStabilizer_singleton]
  constructor
  · intro h j
    exact stabilizer_entries h (by simp) (by simp)
  · intro h
    refine mem_stabilizer_flagSpace_of_entries fun k l hl hk => ?_
    have hk' : k = Fin.last m := Fin.ext (by have := k.isLt; simp; omega)
    obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = l := ⟨⟨l, hl⟩, Fin.ext rfl⟩
    rw [hk']
    exact h j

theorem det_hyp (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (h : ∀ j : Fin m, A (Fin.last m) j.castSucc = 0) :
    A.det = A (Fin.last m) (Fin.last m) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last m), Fin.sum_univ_castSucc]
  simp [h, Fin.succAbove_last]

theorem hyp_gll [Finite K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin (m + 1)) K}
    (hg : g ∈ flagStabilizer (m + 1) K {m}) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) = 1 := by
  have hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1 := g.2
  rw [det_hyp _ (mem_hyp_iff.1 hg)] at hdet
  rcases eq_zero_or_eq_one_of_card_two hK
    ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) with h0 | h1
  · rw [h0, zero_mul] at hdet
    exact absurd hdet zero_ne_one
  · exact h1

theorem hyp_det_block [Finite K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin (m + 1)) K}
    (hg : g ∈ flagStabilizer (m + 1) K {m}) :
    ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.castSucc Fin.castSucc).det = 1 := by
  have hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = 1 := g.2
  rw [det_hyp _ (mem_hyp_iff.1 hg), hyp_gll hK hg, one_mul] at hdet
  exact hdet

theorem hyp_mul_block {g h : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hh : ∀ j : Fin m, h (Fin.last m) j.castSucc = 0) :
    (g * h).submatrix Fin.castSucc Fin.castSucc =
      g.submatrix Fin.castSucc Fin.castSucc * h.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hh]

@[expose] noncomputable def leviHyp [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    ↥(flagStabilizer (m + 1) K {m}) →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨(g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.castSucc Fin.castSucc,
    hyp_det_block hK g.2⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.submatrix_one _ (Fin.castSucc_injective _)
  map_mul' g h := by
    apply Subtype.ext
    exact hyp_mul_block (mem_hyp_iff.1 h.2)

theorem leviHyp_apply [Finite K] (hK : Nat.card K = 2) (g : ↥(flagStabilizer (m + 1) K {m}))
    (i j : Fin m) :
    ((leviHyp hK m g : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) i j =
      (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc j.castSucc := rfl

theorem hyp_ker_sq [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (g : ↥(flagStabilizer (m + 1) K {m})) (hg : leviHyp hK m g = 1) : g * g = 1 := by
  have hll := hyp_gll hK g.2
  have hrow := mem_hyp_iff.1 g.2
  have hblk : ∀ i j : Fin m, (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc j.castSucc =
      (1 : Matrix (Fin m) (Fin m) K) i j := fun i j => by
    have := congrFun (congrFun (congrArg (fun x : SpecialLinearGroup (Fin m) K =>
      (x : Matrix (Fin m) (Fin m) K)) hg) i) j
    exact this
  apply Subtype.ext
  apply Subtype.ext
  show (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hll, hrow]
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hll, hrow]
    exact (Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne').symm
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hll, hblk, Matrix.one_apply]
    exact CharTwo.add_self_eq_zero _
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hrow, hblk, Matrix.one_apply]

theorem hyp_ker_isPGroup [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    IsPGroup 2 (leviHyp (K := K) hK m).ker := by
  intro x
  refine ⟨1, ?_⟩
  have hxx : x * x = 1 := Subtype.ext (hyp_ker_sq hK x.1 (MonoidHom.mem_ker.1 x.2))
  rw [pow_one, pow_two]
  exact hxx

@[expose] def diagHyp (A : Matrix (Fin m) (Fin m) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem diagHyp_row (A : Matrix (Fin m) (Fin m) K) (j : Fin m) :
    diagHyp A (Fin.last m) j.castSucc = 0 := by
  simp [diagHyp]

theorem diagHyp_block (A : Matrix (Fin m) (Fin m) K) :
    (diagHyp A).submatrix Fin.castSucc Fin.castSucc = A := by
  ext i j
  simp [diagHyp]

theorem diagHyp_det (A : Matrix (Fin m) (Fin m) K) : (diagHyp A).det = A.det := by
  rw [det_hyp _ (diagHyp_row A), diagHyp_block]
  simp [diagHyp]

theorem leviHyp_surjective [Finite K] (hK : Nat.card K = 2) :
    Function.Surjective (leviHyp (K := K) hK m) := by
  intro A
  let g : SpecialLinearGroup (Fin (m + 1)) K := ⟨diagHyp (A : Matrix (Fin m) (Fin m) K), by
    rw [diagHyp_det]; exact A.2⟩
  have hg : g ∈ flagStabilizer (m + 1) K {m} := mem_hyp_iff.2 (diagHyp_row _)
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  exact diagHyp_block _

@[expose] noncomputable def hypT (K : Type) [Field K] (j : Fin m) : SpecialLinearGroup (Fin (m + 1)) K :=
  SpecialLinearGroup.transvection
    (show j.castSucc ≠ Fin.last m from (Fin.castSucc_lt_last j).ne) 1

theorem coe_hypT (j : Fin m) :
    ((hypT K j : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      1 + Matrix.single j.castSucc (Fin.last m) 1 := rfl

theorem hypT_mem (j : Fin m) : hypT K j ∈ flagStabilizer (m + 1) K {m} := by
  refine mem_hyp_iff.2 fun i => ?_
  rw [coe_hypT]
  simp
  exact Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne'

theorem hypT_ker [Finite K] (hK : Nat.card K = 2) (j : Fin m) :
    leviHyp hK m ⟨hypT K j, hypT_mem j⟩ = 1 := by
  apply Subtype.ext
  ext a b
  simp [leviHyp_apply, coe_hypT, Matrix.single_apply, Matrix.one_apply]
  intro _
  exact (Fin.castSucc_lt_last b).ne'

theorem hyp_centralizer [Finite K] (hK : Nat.card K = 2) (x : ↥(flagStabilizer (m + 1) K {m}))
    (hx : ∀ n : ↥(flagStabilizer (m + 1) K {m}), n ∈ (leviHyp hK m).ker → x * n = n * x) :
    x ∈ (leviHyp hK m).ker := by
  have hll := hyp_gll hK x.2
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  ext j' j
  have h := congrArg (fun y : ↥(flagStabilizer (m + 1) K {m}) =>
    ((y : SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      j'.castSucc (Fin.last m))
    (hx ⟨hypT K j, hypT_mem j⟩ (MonoidHom.mem_ker.2 (hypT_ker hK j)))
  have hne : ∀ i : Fin m, Fin.last m ≠ i.castSucc := fun i => (Fin.castSucc_lt_last i).ne'
  simp [coe_hypT, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, Fin.sum_univ_castSucc,
    hll, Matrix.one_apply, Fin.castSucc_inj, hne] at h
  simp [leviHyp_apply, Matrix.one_apply]
  have hite : (if j = j' then (1 : K) else 0) = if j' = j then 1 else 0 := by
    by_cases hh : j = j'
    · simp [hh]
    · simp [hh, Ne.symm hh]
  linear_combination h + hite

end Hyperplane

section Pairs

theorem flagStabilizer_sup_eq_top_of_disjoint' {n : ℕ} {I J : Set ℕ}
    (hIJ : ∀ i, 1 ≤ i → i < n → i ∉ I ∨ i ∉ J) :
    flagStabilizer n K I ⊔ flagStabilizer n K J = ⊤ := by
  set A := flagStabilizer n K I ⊔ flagStabilizer n K J with hA
  have hBA : upperTriangular n K ≤ A :=
    (upperTriangular_le_flagStabilizer (K := K) (n := n) I).trans le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : borelOvergroupCuts A = ∅ := by
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hi, hin, hnot⟩
    apply hnot
    rcases hIJ i hi hin with h | h
    · exact Subgroup.mem_sup_left
        (((subflag_stabilizer_generation (K := K) (n := n) I).2.2 i hi hin).2 h)
    · exact Subgroup.mem_sup_right
        (((subflag_stabilizer_generation (K := K) (n := n) J).2.2 i hi hin).2 h)
  rw [hAeq, hcuts]
  exact flagStabilizer_empty n K

theorem pt_ne_top (hm : 1 ≤ m) : flagStabilizer (m + 1) K {1} ≠ ⊤ := by
  intro h
  have := ((subflag_stabilizer_generation (K := K) (n := m + 1) ({1} : Set ℕ)).2.2 1 le_rfl
    (by omega)).1 (h ▸ Subgroup.mem_top _)
  exact this (Set.mem_singleton 1)

theorem hyp_ne_top (hm : 1 ≤ m) : flagStabilizer (m + 1) K {m} ≠ ⊤ := by
  intro h
  have := ((subflag_stabilizer_generation (K := K) (n := m + 1) ({m} : Set ℕ)).2.2 m hm
    (by omega)).1 (h ▸ Subgroup.mem_top _)
  exact this (Set.mem_singleton m)

theorem pt_sup_hyp (hm : 2 ≤ m) :
    flagStabilizer (m + 1) K {1} ⊔ flagStabilizer (m + 1) K {m} = ⊤ :=
  flagStabilizer_sup_eq_top_of_disjoint' fun i hi1 _ => by
    simp only [Set.mem_singleton_iff]
    omega

theorem sl_pairs [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hm : 2 ≤ m) :
    ∃ P₁ P₂ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K),
      unitriangular (m + 1) K ≤ P₁ ∧ unitriangular (m + 1) K ≤ P₂ ∧ P₁ ≠ ⊤ ∧ P₂ ≠ ⊤ ∧
      P₁ ⊔ P₂ = ⊤ ∧
      (∃ q : ↥P₁ →* SpecialLinearGroup (Fin m) K, Function.Surjective q ∧ IsPGroup 2 q.ker ∧
        ∀ x : ↥P₁, (∀ n : ↥P₁, n ∈ q.ker → x * n = n * x) → x ∈ q.ker) ∧
      (∃ q : ↥P₂ →* SpecialLinearGroup (Fin m) K, Function.Surjective q ∧ IsPGroup 2 q.ker ∧
        ∀ x : ↥P₂, (∀ n : ↥P₂, n ∈ q.ker → x * n = n * x) → x ∈ q.ker) :=
  ⟨flagStabilizer (m + 1) K {1}, flagStabilizer (m + 1) K {m},
    (unitriangular_le_upperTriangular _ _).trans (upperTriangular_le_flagStabilizer _),
    (unitriangular_le_upperTriangular _ _).trans (upperTriangular_le_flagStabilizer _),
    pt_ne_top (by omega), hyp_ne_top (by omega), pt_sup_hyp hm,
    ⟨leviPt hK m, leviPt_surjective hK, pt_ker_isPGroup hK, pt_centralizer hK⟩,
    ⟨leviHyp hK m, leviHyp_surjective hK, hyp_ker_isPGroup hK, hyp_centralizer hK⟩⟩

end Pairs

end CFSG.QuasithinUnique.Vol2Native.L239
