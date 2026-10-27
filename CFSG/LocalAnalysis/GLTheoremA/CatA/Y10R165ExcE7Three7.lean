module

public import CFSG.RankThree.PartOne.KLR.RootKernel
public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical2 CFSG.Open
  CFSG.RankThree.PartOne.KLR
open CFSG.RankThree.E6
open scoped Matrix MatrixGroups Pointwise

@[expose] def e7T3AVec : Fin Tag.E7.rank → ℤ :=
  Pi.single (1 : Fin Tag.E7.rank) 1 - Pi.single (2 : Fin Tag.E7.rank) 1 +
    Pi.single (3 : Fin Tag.E7.rank) 1 - Pi.single (4 : Fin Tag.E7.rank) 1

@[expose] def e7T3DVec : Fin Tag.E7.rank → ℤ :=
  Pi.single (1 : Fin Tag.E7.rank) 1 - Pi.single (2 : Fin Tag.E7.rank) 1 +
    Pi.single (4 : Fin Tag.E7.rank) 1 - Pi.single (5 : Fin Tag.E7.rank) 1

def e7T3XA (α : Fin Tag.E7.rank → ℤ) : ℤ := ∑ i, α i * e7T3AVec i

def e7T3XD (α : Fin Tag.E7.rank → ℤ) : ℤ := ∑ i, α i * e7T3DVec i

@[expose] def e7T3XColumn {p : ℕ} (ε : ℤ) (q : ZMod p) : Fin Tag.E7.rank → ZMod p :=
  (fun i => (e7T3AVec i : ZMod p)) + ((ε : ZMod p) * q) • (fun i => (e7T3DVec i : ZMod p))

theorem charVal_intVec {p : ℕ} (v : Fin Tag.E7.rank → ℤ) (α : Fin Tag.E7.rank → ℤ) :
    charVal (fun i => (v i : ZMod p)) α = ((∑ i, α i * v i : ℤ) : ZMod p) := by
  simp only [charVal, Int.cast_sum, Int.cast_mul]

theorem charVal_e7T3XColumn {p : ℕ} {ε : ℤ} {q : ZMod p} (α : Fin Tag.E7.rank → ℤ) :
    charVal (e7T3XColumn ε q) α =
      (e7T3XA α : ZMod p) + (ε : ZMod p) * q * (e7T3XD α : ZMod p) := by
  rw [e7T3XColumn, CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three.charVal_column_add,
    charVal_smul_col, charVal_intVec, charVal_intVec, e7T3XA, e7T3XD]

theorem e7T3W_transpose_mulVec_A : e7T3W.transpose *ᵥ e7T3AVec = -e7T3DVec := by
  decide +kernel

theorem e7T3W_transpose_mulVec_D : e7T3W.transpose *ᵥ e7T3DVec = e7T3AVec - e7T3DVec := by
  decide +kernel

private theorem map_mulVec_intCast {p : ℕ} (M : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ)
    (v : Fin Tag.E7.rank → ℤ) :
    (fun i => ((M *ᵥ v) i : ZMod p)) =
      (M.map (Int.cast : ℤ → ZMod p)) *ᵥ (fun i => (v i : ZMod p)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul]

theorem e7T3_eigen_coord {R : Type*} [CommRing R] {ε q : R} (hε : ε * ε = 1)
    (hq : q ^ 2 + ε * q + 1 = 0) (A D : R) :
    ε * (-D) + ε * (ε * q) * (A - D) = q * (A + ε * q * D) := by
  have hq' : q ^ 2 = -ε * q - 1 := by linear_combination hq
  calc ε * (-D) + ε * (ε * q) * (A - D) = -ε * D + (ε * ε) * q * (A - D) := by ring
    _ = -ε * D + q * (A - D) := by rw [hε]; ring
    _ = q * A + ε * q ^ 2 * D := by rw [hq']; linear_combination (D * q) * hε
    _ = q * (A + ε * q * D) := by ring

theorem e7T3XColumn_eigen {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ZMod p}
    (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    ((ε • e7T3W).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ e7T3XColumn ε q =
      q • e7T3XColumn ε q := by
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hA : ((e7T3W.map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
      (fun i => (e7T3AVec i : ZMod p)) = -(fun i => (e7T3DVec i : ZMod p)) := by
    rw [← Matrix.transpose_map, ← map_mulVec_intCast, e7T3W_transpose_mulVec_A]
    funext i
    simp
  have hD : ((e7T3W.map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
      (fun i => (e7T3DVec i : ZMod p)) =
        (fun i => (e7T3AVec i : ZMod p)) - (fun i => (e7T3DVec i : ZMod p)) := by
    rw [← Matrix.transpose_map, ← map_mulVec_intCast, e7T3W_transpose_mulVec_D]
    funext i
    simp
  have hsm : ((ε • e7T3W).map (Int.cast : ℤ → ZMod p)) =
      (ε : ZMod p) • (e7T3W.map (Int.cast : ℤ → ZMod p)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have key : ∀ a d : Fin Tag.E7.rank → ZMod p,
      (ε : ZMod p) • (-d + ((ε : ZMod p) * q) • (a - d)) =
        q • (a + ((ε : ZMod p) * q) • d) := by
    intro a d
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    have h1 : (↑ε : ZMod p) * (-d i + ↑ε * q * (a i - d i)) =
        ↑ε * (-d i) + ↑ε * (↑ε * q) * (a i - d i) := by ring
    rw [h1]
    exact e7T3_eigen_coord hε2 hq _ _
  rw [e7T3XColumn, hsm, Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, hA, hD]
  exact key _ _

theorem e7T3XA_norm_mem (l : List ℤ) (hl : l ∈ Tag.E7.artifactRoots) :
    let α := toVec Tag.E7.rank l
    e7T3XA α * e7T3XA α - e7T3XA α * e7T3XD α + e7T3XD α * e7T3XD α ∈
      ({0, 1, 3} : Finset ℤ) := by
  revert l
  decide +kernel

theorem e7T3XA_eq_zero_of_charVal_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0)
    {A D : ℤ} (hAD : A * A - A * D + D * D ∈ ({0, 1, 3} : Finset ℤ))
    (h : (A : ZMod p) + (ε : ZMod p) * q * (D : ZMod p) = 0) : A = 0 ∧ D = 0 := by
  have hcast : ((A * A - A * D + D * D : ℤ) : ZMod p) = 0 := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three.e8T3_norm_identity hε hq A D, h,
      zero_mul]
  have hk1 : ((1 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd : (p : ℤ) ∣ (1 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 p).1 hz
    have hle : (p : ℤ) ≤ (1 : ℤ) := Int.le_of_dvd (by norm_num) hd
    have := hp.two_le
    omega
  have hk3 : ((3 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd : (p : ℤ) ∣ (3 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).1 hz
    have hle : (p : ℤ) ≤ (3 : ℤ) := Int.le_of_dvd (by norm_num) hd
    omega
  have hnorm : A * A - A * D + D * D = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hAD
    rcases hAD with h0 | h1 | h3
    · exact h0
    · exact absurd (h1 ▸ hcast) hk1
    · exact absurd (h3 ▸ hcast) hk3
  have h4eq : 4 * (A * A - A * D + D * D) = (2 * A - D) ^ 2 + 3 * D ^ 2 := by ring
  have hD : D = 0 := by nlinarith [sq_nonneg (2 * A - D), sq_nonneg D]
  have hA : A = 0 := by nlinarith
  exact ⟨hA, hD⟩

theorem e7T3XA_eq_zero_iff_charVal_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0)
    {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot Tag.E7 α) :
    charVal (e7T3XColumn ε q) α = 0 ↔ e7T3XA α = 0 ∧ e7T3XD α = 0 := by
  constructor
  · intro h0
    have hnorm := e7T3XA_norm_mem (List.ofFn α) (isRoot_iff_mem_artifactRoots.1 hα)
    rw [toVec_ofFn] at hnorm
    rw [charVal_e7T3XColumn] at h0
    exact e7T3XA_eq_zero_of_charVal_eq_zero hp hp3 hε hq hnorm h0
  · rintro ⟨hA, hD⟩
    rw [charVal_e7T3XColumn, hA, hD]
    simp

@[expose] def e7T3CertA5 : E7T3Cert :=
  { cls := [0, 1, 8, 9, 15],
    w := [2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2],
    comps := [{ kind := 3, u := [6, 5, 1, 3], rot := false }] }

theorem e7T3CertA5_good : e7T3CertA5.Good := by
  decide +kernel

theorem e7T3XA_eq_zero_iff_mem (l : List ℤ) (hl : l ∈ Tag.E7.artifactRoots) :
    (let α := toVec Tag.E7.rank l
     e7T3XA α = 0 ∧ e7T3XD α = 0) ↔ l ∈ e7T3CertA5.rootList := by
  revert l
  decide +kernel

theorem rootCharKernel_e7T3XColumn {p : ℕ} [NeZero p] {L : Type} [Field L] {ζ : Lˣ}
    (hp : p.Prime) (hp3 : 3 < p) (hζ : IsPrimitiveRoot ζ p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    rootCharKernel (fun i => ζ ^ (e7T3XColumn ε q i).val) =
      {α | ∃ l ∈ e7T3CertA5.rootList, α = toVec Tag.E7.rank l} := by
  ext α
  rw [rootCharKernel, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hα, h1⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    have h0 : charVal (e7T3XColumn ε q) (toVec Tag.E7.rank l) = 0 :=
      (rootChar_zetaPow_eq_one_iff_charVal hζ (e7T3XColumn ε q) _).1 h1
    obtain ⟨hA, hD⟩ :=
      e7T3XA_eq_zero_iff_charVal_eq_zero hp hp3 hε hq (isRoot_toVec hl) |>.1 h0
    exact ⟨l, (e7T3XA_eq_zero_iff_mem l hl).1 ⟨hA, hD⟩, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    have hmemA : l ∈ Tag.E7.artifactRoots := e7T3CertA5_good.2.2.1 l hl
    refine ⟨isRoot_toVec hmemA, ?_⟩
    obtain ⟨hA, hD⟩ := (e7T3XA_eq_zero_iff_mem l hmemA).2 hl
    rw [rootChar_zetaPow_eq_one_iff_charVal hζ, charVal_e7T3XColumn, hA, hD]
    simp

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
