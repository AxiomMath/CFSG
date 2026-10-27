module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open scoped commutatorElement

variable {F : Type} [Field F]

theorem eq_one_of_mem_scalars_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : SpecialLinearGroup (Fin 4) F} (hz : z ∈ scalars 4 F) (hzp : z ^ p = 1) : z = 1 := by
  obtain ⟨c, hc4, hzc⟩ := mem_scalars.1 hz
  have hcp : c ^ p = 1 := by
    have h1 := congrArg (fun x : SpecialLinearGroup (Fin 4) F =>
      (x : Matrix (Fin 4) (Fin 4) F) 0 0) hzp
    simp only [Matrix.SpecialLinearGroup.coe_pow, hzc, Matrix.SpecialLinearGroup.coe_one] at h1
    rw [← map_pow, scalar_apply, diagonal_apply_eq, one_apply_eq] at h1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
  have hgcd : Nat.gcd 4 p = 1 := by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have : Nat.Coprime (2 ^ 2) p := Nat.Coprime.pow_left 2 h2
    simpa using this
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc4, hcp⟩
    rwa [hgcd, pow_one] at this
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [hzc, hc1, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

@[expose] def diagSL (d : Fin 4 → F) (hd : ∏ i, d i = 1) : SpecialLinearGroup (Fin 4) F :=
  ⟨diagonal d, by rw [det_diagonal, hd]⟩

theorem coe_diagSL (d : Fin 4 → F) (hd : ∏ i, d i = 1) :
    ((diagSL d hd : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal d :=
  rfl

theorem mem_centralizer_diagSL_iff {d : Fin 4 → F} {hd : ∏ i, d i = 1}
    {g : SpecialLinearGroup (Fin 4) F} :
    g ∈ Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F)) ↔
      ∀ i j, d i ≠ d j → (g : Matrix (Fin 4) (Fin 4) F) i j = 0 := by
  have key : ∀ i j, ((g * diagSL d hd : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) i j = (g : Matrix (Fin 4) (Fin 4) F) i j * d j ∧
      ((diagSL d hd * g : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i j =
        d i * (g : Matrix (Fin 4) (Fin 4) F) i j := fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL,
      mul_diagonal, diagonal_mul]
    exact ⟨rfl, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, Matrix.SpecialLinearGroup.ext_iff]
  constructor
  · intro h i j hij
    have h1 := h i j
    rw [(key i j).1, (key i j).2] at h1
    have h2 : (d j - d i) * (g : Matrix (Fin 4) (Fin 4) F) i j = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hij
    · exact h0
  · intro h i j
    rw [(key i j).1, (key i j).2]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

abbrev blockJ : Finset (Fin 4) := {0}ᶜ

theorem mem_blockJ {i : Fin 4} : i ∈ blockJ ↔ i ≠ 0 := by simp

variable {d : Fin 4 → F} {hd : ∏ i, d i = 1}

theorem coordBlockSL_le_centralizer_diagSL' {I : Finset (Fin 4)}
    (hI : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    coordBlockSL F I ≤
      Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F)) := by
  intro g hg
  rw [mem_centralizer_diagSL_iff]
  intro i j hij
  have hg' := mem_coordBlockSL_iff.1 hg
  by_cases hiI : i ∈ I
  · by_cases hjI : j ∈ I
    · exact absurd (hI i hiI j hjI) hij
    · rw [hg' i j (Or.inr hjI), if_neg]
      rintro rfl
      exact hij rfl
  · rw [hg' i j (Or.inl hiI), if_neg]
    rintro rfl
    exact hij rfl

theorem coordBlockSL_le_centralizer_diagSL (hJ : ∀ i j, i ≠ 0 → j ≠ 0 → d i = d j) :
    coordBlockSL F blockJ ≤
      Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F)) :=
  coordBlockSL_le_centralizer_diagSL' fun i hi j hj =>
    hJ i j (mem_blockJ.1 hi) (mem_blockJ.1 hj)

variable (d hd) in
abbrev cent : Subgroup (SpecialLinearGroup (Fin 4) F) :=
  Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F))

variable (hd0 : ∀ j, j ≠ 0 → d 0 ≠ d j)
include hd0

theorem corner_entries {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F)))
    {j : Fin 4} (hj : j ≠ 0) :
    (g : Matrix (Fin 4) (Fin 4) F) 0 j = 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) j 0 = 0 := by
  rw [mem_centralizer_diagSL_iff] at hg
  exact ⟨hg 0 j (hd0 j hj), hg j 0 (fun h => hd0 j hj h.symm)⟩

theorem corner_ne_zero {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F))) :
    (g : Matrix (Fin 4) (Fin 4) F) 0 0 ≠ 0 := by
  intro h0
  have hdet : (g : Matrix (Fin 4) (Fin 4) F).det = 0 :=
    det_eq_zero_of_row_eq_zero 0 fun j => by
      by_cases hj : j = 0
      · rw [hj, h0]
      · exact (corner_entries hd0 hg hj).1
  rw [Matrix.SpecialLinearGroup.det_coe] at hdet
  exact one_ne_zero hdet

theorem corner_mul {g h : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ Subgroup.centralizer ({diagSL d hd} : Set (SpecialLinearGroup (Fin 4) F))) :
    ((g * h : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 =
      (g : Matrix (Fin 4) (Fin 4) F) 0 0 * (h : Matrix (Fin 4) (Fin 4) F) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Finset.sum_eq_single 0]
  · intro b _ hb
    rw [(corner_entries hd0 hg hb).1, zero_mul]
  · simp

@[expose] noncomputable def cornerHom : cent d hd →* Fˣ where
  toFun g := Units.mk0 (((g : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0)
    (corner_ne_zero hd0 g.2)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    exact corner_mul hd0 g.2

theorem cornerHom_apply (g : cent d hd) :
    ((cornerHom hd0 g : Fˣ) : F) =
      ((g : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 :=
  rfl

theorem mem_coordBlockSL_of_corner {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ cent d hd) (h1 : (g : Matrix (Fin 4) (Fin 4) F) 0 0 = 1) :
    g ∈ coordBlockSL F blockJ := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  have hij' : i = 0 ∨ j = 0 := by simpa [mem_blockJ] using hij
  rcases hij' with rfl | rfl
  · by_cases hj : j = 0
    · subst hj
      simp [h1]
    · rw [(corner_entries hd0 hg hj).1, if_neg (Ne.symm hj)]
  · by_cases hi : i = 0
    · subst hi
      simp [h1]
    · rw [(corner_entries hd0 hg hi).2, if_neg hi]

omit hd0 in
theorem corner_of_mem_coordBlockSL {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ coordBlockSL F blockJ) : (g : Matrix (Fin 4) (Fin 4) F) 0 0 = 1 := by
  rw [mem_coordBlockSL_iff.1 hg 0 0 (Or.inl (by simp [mem_blockJ])), if_pos rfl]

theorem coordBlockSL_subgroupOf_eq_ker (hJ : ∀ i j, i ≠ 0 → j ≠ 0 → d i = d j) :
    (coordBlockSL F blockJ).subgroupOf (cent d hd) = (cornerHom hd0).ker := by
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    ext
    rw [cornerHom_apply, Units.val_one]
    exact corner_of_mem_coordBlockSL hg
  · intro hg
    have h1 := congrArg (fun u : Fˣ => (u : F)) hg
    rw [cornerHom_apply, Units.val_one] at h1
    exact mem_coordBlockSL_of_corner hd0 g.2 h1

theorem coordBlockSL_normal (hJ : ∀ i j, i ≠ 0 → j ≠ 0 → d i = d j) :
    ((coordBlockSL F blockJ).subgroupOf (cent d hd)).Normal := by
  rw [coordBlockSL_subgroupOf_eq_ker hd0 hJ]
  exact MonoidHom.normal_ker _

theorem commutator_centralizer_le_coordBlockSL :
    ⁅cent d hd, cent d hd⁆ ≤ coordBlockSL F blockJ := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hgh : ⁅g, h⁆ ∈ cent d hd := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  apply mem_coordBlockSL_of_corner hd0 hgh
  have h1 : cornerHom hd0 ⁅(⟨g, hg⟩ : cent d hd), ⟨h, hh⟩⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_inv_eq_one.2 (by rw [mul_inv_eq_iff_eq_mul, mul_comm])
  have h2 := congrArg (fun u : Fˣ => (u : F)) h1
  simp only [cornerHom_apply, Units.val_one] at h2
  have h3 : ((⁅(⟨g, hg⟩ : cent d hd), ⟨h, hh⟩⁆ : cent d hd) : SpecialLinearGroup (Fin 4) F) =
      ⁅g, h⁆ := rfl
  rwa [h3] at h2

end CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
