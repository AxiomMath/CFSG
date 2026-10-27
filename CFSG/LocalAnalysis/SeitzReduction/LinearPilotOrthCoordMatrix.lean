module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordBlock
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR7iiiAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthTorus

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)

variable {n : ℕ} {K : Type*} [Field K]

section Shape

structure IsPairShape (a b : Fin n) (A : Matrix (Fin n) (Fin n) K) (l ν : K) : Prop where
  col_left : ∀ i, i ≠ a → A i a = 0
  row_right : ∀ j, j ≠ b → A b j = 0
  left_left : A a a = l
  right_right : A b b = l
  block : ∀ i j, i ≠ a → i ≠ b → j ≠ a → j ≠ b → A i j = if i = j then ν else 0

@[expose] def pairDiag (a b : Fin n) (l ν : K) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => if i ∈ ({a, b} : Finset (Fin n)) then l else ν

theorem pairDiag_apply (a b : Fin n) (l ν : K) (i j : Fin n) :
    pairDiag a b l ν i j = if i = j then (if i = a ∨ i = b then l else ν) else 0 := by
  rw [pairDiag, diagonal_apply]
  simp

end Shape

section Semisimple

variable [CharP K 2]

theorem eq_zero_of_sub_mulVec_eq {A : Matrix (Fin n) (Fin n) K} {m : ℕ} (hm : Odd m) {μ : K}
    (hμ : μ ≠ 0) (hA : A ^ m = μ • (1 : Matrix (Fin n) (Fin n) K)) {l c : K} {a : Fin n}
    {v : Fin n → K} (hv : (A - l • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ v = c • Pi.single a 1)
    (ha : (A - l • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ Pi.single a 1 = 0) : c = 0 := by
  have h2 : (A - l • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ
      ((A - l • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ v) = 0 := by
    rw [hv, Matrix.mulVec_smul, ha, smul_zero]
  have h1 := sub_smul_mulVec_eq_zero hm hμ hA l h2
  rw [hv] at h1
  have := congrFun h1 a
  simpa using this

omit [CharP K 2] in
theorem eq_zero_of_level_lt {k : ℕ} (P : InvPlacement n k) {N : Matrix (Fin n) (Fin n) K}
    (hN : ∀ i j, P.level j ≤ P.level i → N i j = 0)
    (hss : ∀ v, N *ᵥ (N *ᵥ v) = 0 → N *ᵥ v = 0) : N = 0 := by
  have h2 : ∀ i j, (N * N) i j ≠ 0 → P.level i + 2 ≤ P.level j := by
    intro i j hij
    rw [mul_apply] at hij
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
    have h1 : N i m ≠ 0 := left_ne_zero_of_mul hm
    have h2 : N m j ≠ 0 := right_ne_zero_of_mul hm
    have h3 : ¬ P.level m ≤ P.level i := fun h => h1 (hN i m h)
    have h4 : ¬ P.level j ≤ P.level m := fun h => h2 (hN m j h)
    omega
  have h3 : N * N * N = 0 := by
    ext i j
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : (N * N) i m = 0
    · rw [hm, zero_mul]
    · have h := h2 i m hm
      have hl := P.level_le_two j
      rw [hN m j (by omega), mul_zero]
  have hv2 : ∀ v, N *ᵥ (N *ᵥ v) = 0 := by
    intro v
    apply hss
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3, Matrix.zero_mulVec]
  ext i j
  have h := congrFun (hss _ (hv2 (Pi.single j 1))) i
  rw [mulVec_single_one] at h
  simpa using h

theorem eq_smul_one_of_isPairShape {a b : Fin n} (hab : a ≠ b) {A : Matrix (Fin n) (Fin n) K}
    {l : K} (hA : IsPairShape a b A l l) {m : ℕ} (hm : Odd m) {μ : K} (hμ : μ ≠ 0)
    (hAm : A ^ m = μ • (1 : Matrix (Fin n) (Fin n) K)) :
    A = l • (1 : Matrix (Fin n) (Fin n) K) := by
  have hN : A - l • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
    refine eq_zero_of_level_lt (pairPlacement hab) (fun i j hij => ?_)
      (fun v hv => sub_smul_mulVec_eq_zero hm hμ hAm l hv)
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hja : j = a
    · subst hja
      by_cases hia : i = j
      · subst hia
        rw [hA.left_left, one_apply_eq, mul_one, sub_self]
      · rw [hA.col_left i hia, one_apply_ne hia, mul_zero, sub_zero]
    · by_cases hjb : j = b
      · subst hjb
        have hib : i = j := by
          by_contra hib
          by_cases hia : i = a
          · subst hia
            rw [pairPlacement_level_left, pairPlacement_level_right] at hij
            omega
          · rw [pairPlacement_level_of_ne hab hia hib, pairPlacement_level_right] at hij
            omega
        subst hib
        rw [hA.right_right, one_apply_eq, mul_one, sub_self]
      · have hia : i ≠ a := by
          rintro rfl
          rw [pairPlacement_level_left, pairPlacement_level_of_ne hab hja hjb] at hij
          omega
        by_cases hib : i = b
        · subst hib
          rw [hA.row_right j hjb, one_apply_ne (Ne.symm hjb), mul_zero, sub_zero]
        · rw [hA.block i j hia hib hja hjb]
          by_cases hij' : i = j
          · rw [ite_eq_left hij', hij', one_apply_eq, mul_one, sub_self]
          · rw [ite_eq_right hij', one_apply_ne hij', mul_zero, sub_zero]
  exact sub_eq_zero.1 hN

end Semisimple

section Diagonalize

variable [CharP K 2]

theorem exists_mul_eq_mul_pairDiag {a b : Fin n} (hab : a ≠ b) {A : Matrix (Fin n) (Fin n) K}
    {l ν : K} (hA : IsPairShape a b A l ν) (hlν : l ≠ ν) {m : ℕ} (hm : Odd m) {μ : K}
    (hμ : μ ≠ 0) (hAm : A ^ m = μ • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ W : SpecialLinearGroup (Fin n) K, W ∈ (pairPlacement hab).radical K ∧
      A * (W : Matrix (Fin n) (Fin n) K) = (W : Matrix (Fin n) (Fin n) K) * pairDiag a b l ν := by
  classical
  set J : Finset (Fin n) := ({a, b} : Finset (Fin n))ᶜ with hJ
  have hmemJ : ∀ j, j ∈ J ↔ j ≠ a ∧ j ≠ b := fun j => by simp [hJ]
  have haJ : a ∉ J := fun h => ((hmemJ a).1 h).1 rfl
  have hbJ : b ∉ J := fun h => ((hmemJ b).1 h).2 rfl
  have hlν' : l - ν ≠ 0 := sub_ne_zero.2 hlν
  have hνl' : ν - l ≠ 0 := sub_ne_zero.2 (Ne.symm hlν)
  set E : Matrix (Fin n) (Fin n) K := Matrix.of fun i k =>
    if i = a ∧ k ∈ J then A a k / (ν - l) else if i ∈ J ∧ k = b then A i b / (l - ν) else 0
    with hE
  have hEa : ∀ j, E j a = 0 := fun j => by
    simp only [hE, Matrix.of_apply]
    rw [ite_eq_right (fun h => haJ h.2), ite_eq_right (fun h => hab h.2)]
  have hEJ : ∀ j k, k ∈ J → E j k = if j = a then A a k / (ν - l) else 0 := fun j k hk => by
    simp only [hE, Matrix.of_apply]
    by_cases hj : j = a
    · rw [ite_eq_left ⟨hj, hk⟩, ite_eq_left hj]
    · rw [ite_eq_right (fun h => hj h.1), ite_eq_right (fun h : j ∈ J ∧ k = b => hbJ (h.2 ▸ hk)),
        ite_eq_right hj]
  have hEb : ∀ j, E j b = if j ∈ J then A j b / (l - ν) else 0 := fun j => by
    rw [hE, Matrix.of_apply, ite_eq_right (fun h : j = a ∧ b ∈ J => hbJ h.2)]
    by_cases hj : j ∈ J
    · rw [ite_eq_left ⟨hj, rfl⟩, ite_eq_left hj]
    · rw [ite_eq_right (fun h => hj h.1), ite_eq_right hj]
  have hElev : ∀ i k, (pairPlacement hab).level k ≤ (pairPlacement hab).level i → E i k = 0 := by
    intro i k hik
    by_cases hka : k = a
    · rw [hka, hEa]
    by_cases hkb : k = b
    · rw [hkb, hEb]
      refine ite_eq_right fun hi => ?_
      obtain ⟨hia, hib⟩ := (hmemJ i).1 hi
      rw [hkb, pairPlacement_level_right, pairPlacement_level_of_ne hab hia hib] at hik
      omega
    · have hk : k ∈ J := (hmemJ k).2 ⟨hka, hkb⟩
      rw [hEJ i k hk]
      refine ite_eq_right fun hia => ?_
      rw [hia, pairPlacement_level_left, pairPlacement_level_of_ne hab hka hkb] at hik
      omega
  have hdet : (1 + E).det = 1 := (pairPlacement hab).det_one_add_of_strict hElev
  set W : SpecialLinearGroup (Fin n) K := ⟨1 + E, hdet⟩ with hW
  have hWc : (W : Matrix (Fin n) (Fin n) K) = 1 + E := rfl
  have hWR : W ∈ (pairPlacement hab).radical K := by
    intro i j hij
    rw [hWc, Matrix.add_apply, hElev i j hij, add_zero]
  refine ⟨W, hWR, ?_⟩
  have hAEa : ∀ i, (A * E) i a = 0 := fun i => by
    rw [mul_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [hEa, mul_zero]
  have hAEJ : ∀ i k, k ∈ J → (A * E) i k = A i a * (A a k / (ν - l)) := fun i k hk => by
    rw [mul_apply]
    simp_rw [hEJ _ k hk, mul_ite, mul_zero]
    simp
  have hAEb : ∀ i, (A * E) i b = ∑ j ∈ J, A i j * (A j b / (l - ν)) := fun i => by
    rw [mul_apply]
    simp_rw [hEb, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsumJ : ∀ i ∈ J, ∀ x : Fin n → K, ∑ j ∈ J, A i j * x j = ν * x i := fun i hi x => by
    obtain ⟨hia, hib⟩ := (hmemJ i).1 hi
    rw [Finset.sum_eq_single i]
    · rw [hA.block i i hia hib hia hib, ite_eq_left rfl]
    · intro j hj hji
      obtain ⟨hja, hjb⟩ := (hmemJ j).1 hj
      rw [hA.block i j hia hib hja hjb, ite_eq_right (Ne.symm hji), zero_mul]
    · intro h
      exact absurd hi h
  have hsumb : ∀ x : Fin n → K, ∑ j ∈ J, A b j * x j = 0 := fun x =>
    Finset.sum_eq_zero fun j hj => by rw [hA.row_right j ((hmemJ j).1 hj).2, zero_mul]
  set c : K := A a b + ∑ j ∈ J, A a j * (A j b / (l - ν)) with hc
  have hcol : ∀ i, ((A - l • (1 : Matrix (Fin n) (Fin n) K)) * (1 + E)) i b =
      if i = a then c else 0 := by
    intro i
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.add_apply, hAEb, smul_eq_mul]
    by_cases hia : i = a
    · rw [hia, ite_eq_left rfl, one_apply_ne hab, hEb, ite_eq_right haJ]
      ring
    · rw [ite_eq_right hia]
      by_cases hib : i = b
      · rw [hib, hsumb, hEb, ite_eq_right hbJ, one_apply_eq, hA.right_right]
        ring
      · have hi : i ∈ J := (hmemJ i).2 ⟨hia, hib⟩
        rw [hsumJ i hi, hEb, ite_eq_left hi, one_apply_ne hib]
        field_simp
        ring
  have hc0 : c = 0 := by
    refine eq_zero_of_sub_mulVec_eq hm hμ hAm (l := l) (v := (1 + E) *ᵥ Pi.single b 1) (a := a)
      ?_ ?_
    · rw [Matrix.mulVec_mulVec, mulVec_single_one]
      ext i
      rw [Matrix.col_apply, hcol i, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hia : i = a
      · rw [ite_eq_left hia, ite_eq_left hia, mul_one]
      · rw [ite_eq_right hia, ite_eq_right hia, mul_zero]
    · rw [mulVec_single_one]
      ext i
      rw [Matrix.col_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hia : i = a
      · rw [hia, hA.left_left, one_apply_eq, mul_one, sub_self]
      · rw [hA.col_left i hia, one_apply_ne hia, mul_zero, sub_zero]
  rw [hWc]
  ext i k
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.add_apply, pairDiag, mul_diagonal, diagonal_apply]
  by_cases hka : k = a
  · rw [hka, hAEa, hEa, zero_mul, add_zero, add_zero]
    by_cases hia : i = a
    · rw [hia, hA.left_left]
      simp
    · rw [hA.col_left i hia, ite_eq_right hia]
  by_cases hkb : k = b
  · rw [hkb, hAEb, hEb]
    by_cases hia : i = a
    · rw [hia, ← hc, hc0, ite_eq_right hab, ite_eq_right haJ]
      ring
    by_cases hib : i = b
    · rw [hib, hsumb, hA.right_right, ite_eq_right hbJ]
      simp
    · have hi : i ∈ J := (hmemJ i).2 ⟨hia, hib⟩
      rw [hsumJ i hi (fun j => A j b / (l - ν)), ite_eq_right hib, ite_eq_left hi]
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true, ite_true]
      field_simp
      ring
  · have hk : k ∈ J := (hmemJ k).2 ⟨hka, hkb⟩
    have hk' : k ∉ ({a, b} : Finset (Fin n)) := by simp [hka, hkb]
    rw [hAEJ i k hk, hEJ i k hk, ite_eq_right hk']
    by_cases hia : i = a
    · rw [hia, hA.left_left, ite_eq_left rfl, ite_eq_right (Ne.symm hka)]
      field_simp
      ring
    · rw [hA.col_left i hia, zero_mul, add_zero, ite_eq_right hia, zero_mul, add_zero]
      by_cases hib : i = b
      · rw [hib, hA.row_right k hkb, ite_eq_right (Ne.symm hkb)]
      · rw [hA.block i k hia hib hka hkb]
        by_cases hik : i = k
        · rw [ite_eq_left hik, ite_eq_left hik, hik, ite_eq_right hk']
        · rw [ite_eq_right hik, ite_eq_right hik]

end Diagonalize

section BlockJ

theorem radical_mul_apply_of_ne {a b : Fin n} (hab : a ≠ b) {r : SpecialLinearGroup (Fin n) K}
    (hr : r ∈ (pairPlacement hab).radical K) {N : Matrix (Fin n) (Fin n) K} {p q : Fin n}
    (hpa : p ≠ a) (hpb : p ≠ b) (hN : N b q = 0) :
    ((r : Matrix (Fin n) (Fin n) K) * N) p q = N p q := by
  rw [mul_apply, Finset.sum_eq_single p]
  · rw [hr p p le_rfl, one_apply_eq, one_mul]
  · intro m _ hmp
    by_cases hmb : m = b
    · rw [hmb, hN, mul_zero]
    · rw [hr p m (by
        rw [pairPlacement_level_of_ne hab hpa hpb]
        by_cases hma : m = a
        · rw [hma, pairPlacement_level_left]
          omega
        · rw [pairPlacement_level_of_ne hab hma hmb]), one_apply_ne (Ne.symm hmp), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem radical_mul_apply_left {a b : Fin n} (hab : a ≠ b) {r : SpecialLinearGroup (Fin n) K}
    (hr : r ∈ (pairPlacement hab).radical K) {N : Matrix (Fin n) (Fin n) K}
    (hN : ∀ p, p ≠ a → N p a = 0) :
    ((r : Matrix (Fin n) (Fin n) K) * N) a a = N a a := by
  rw [mul_apply, Finset.sum_eq_single a]
  · rw [hr a a le_rfl, one_apply_eq, one_mul]
  · intro m _ hma
    rw [hN m hma, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem exists_smul_of_conjAut_proj_eq (A : GL (Fin n) K) {X Y : SpecialLinearGroup (Fin n) K}
    (h : conjAut n K A (proj n K X) = proj n K Y) :
    ∃ s : K, (Y : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      s • ((A : Matrix (Fin n) (Fin n) K) * X) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  set Z := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A X
    with hZ
  have hYZ : (Y : Matrix (Fin n) (Fin n) K) = (c : K) • (Z : Matrix (Fin n) (Fin n) K) := by
    have e : Y = Z * (Z⁻¹ * Y) := by group
    rw [e, Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one]
  refine ⟨c, ?_⟩
  rw [hYZ, hZ, coe_slConjugation, Matrix.smul_mul, Matrix.mul_assoc, Units.inv_mul,
    Matrix.mul_one]

theorem block_apply_of_conjAut_eq {a b : Fin n} (hab : a ≠ b) (A : GL (Fin n) K)
    (hcol : ∀ p, p ≠ a → (A : Matrix (Fin n) (Fin n) K) p a = 0)
    (hrow : ∀ q, q ≠ b → (A : Matrix (Fin n) (Fin n) K) b q = 0)
    (haa : (A : Matrix (Fin n) (Fin n) K) a a ≠ 0)
    (hX : ∀ X ∈ blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n)),
      ∃ r ∈ (pairPlacement hab).radical K, conjAut n K A (proj n K X) = proj n K (r * X))
    {i k : Fin n} (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hik : i ≠ k) :
    (A : Matrix (Fin n) (Fin n) K) k i = 0 ∧
      (A : Matrix (Fin n) (Fin n) K) i i = (A : Matrix (Fin n) (Fin n) K) k k := by
  set M := (A : Matrix (Fin n) (Fin n) K) with hM
  set X := SpecialLinearGroup.transvection hik (1 : K) with hXdef
  have hXJ : X ∈ blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n)) :=
    transvection_mem_blockSpecialLinear hik (by simp [hia, hib]) (by simp [hka, hkb]) 1
  obtain ⟨r, hr, hrX⟩ := hX X hXJ
  obtain ⟨s, hs⟩ := exists_smul_of_conjAut_proj_eq A hrX
  have hXc : (X : Matrix (Fin n) (Fin n) K) = 1 + single i k 1 := rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc] at hs
  have hXM : ∀ p q, ((X : Matrix (Fin n) (Fin n) K) * M) p q =
      M p q + if p = i then M k q else 0 := by
    intro p q
    rw [hXc, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    by_cases hpi : p = i
    · rw [hpi, single_mul_apply_same, one_mul, ite_eq_left rfl]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hpi, ite_eq_right hpi]
  have hMX : ∀ p q, (M * (X : Matrix (Fin n) (Fin n) K)) p q =
      M p q + if q = k then M p i else 0 := by
    intro p q
    rw [hXc, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    by_cases hqk : q = k
    · rw [hqk, mul_single_apply_same, mul_one, ite_eq_left rfl]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hqk, ite_eq_right hqk]
  have hXMb : ∀ q, q ≠ b → ((X : Matrix (Fin n) (Fin n) K) * M) b q = 0 := fun q hq => by
    rw [hXM, hrow q hq, ite_eq_right (fun h => hib h.symm), add_zero]
  have hs1 : s = 1 := by
    have h := congrFun (congrFun hs a) a
    have hXMa : ∀ p, p ≠ a → ((X : Matrix (Fin n) (Fin n) K) * M) p a = 0 := fun p hp => by
      rw [hXM, hcol p hp, hcol k hka]
      simp
    rw [radical_mul_apply_left hab hr hXMa, Matrix.smul_apply, hMX, hXM,
      ite_eq_right (fun h => hia h.symm), ite_eq_right (fun h => hka h.symm), add_zero,
      smul_eq_mul] at h
    have h' : M a a * (1 - s) = 0 := by linear_combination h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left haa)).symm
  rw [hs1, one_smul] at hs
  refine ⟨?_, ?_⟩
  ·
    have h := congrFun (congrFun hs i) i
    rw [radical_mul_apply_of_ne hab hr hia hib (hXMb i hib), hXM, hMX, ite_eq_left rfl,
      ite_eq_right hik, add_zero] at h
    linear_combination h
  ·
    have h := congrFun (congrFun hs i) k
    rw [radical_mul_apply_of_ne hab hr hia hib (hXMb k hkb), hXM, hMX, ite_eq_left rfl,
      ite_eq_left rfl] at h
    linear_combination -h

end BlockJ

theorem isPairShape_of_conjAut_eq {a b : Fin n} (hab : a ≠ b) (A : GL (Fin n) K)
    (hA : Commute (single a b (1 : K)) (A : Matrix (Fin n) (Fin n) K))
    (hX : ∀ X ∈ blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n)),
      ∃ r ∈ (pairPlacement hab).radical K, conjAut n K A (proj n K X) = proj n K (r * X)) :
    ∃ ν, IsPairShape a b (A : Matrix (Fin n) (Fin n) K) ((A : Matrix (Fin n) (Fin n) K) a a) ν := by
  classical
  set M := (A : Matrix (Fin n) (Fin n) K) with hM
  have hcol : ∀ p, p ≠ a → M p a = 0 := fun p hp => col_eq_zero_of_commute_single hA hp
  have hrow : ∀ q, q ≠ b → M b q = 0 := fun q hq => row_eq_zero_of_commute_single hA hq
  have hdiag : M a a = M b b := diag_eq_of_commute_single hA
  have haa : M a a ≠ 0 := by
    intro h0
    refine Matrix.GeneralLinearGroup.det_ne_zero A (det_eq_zero_of_column_eq_zero a fun p => ?_)
    by_cases hp : p = a
    · rw [hp]
      exact h0
    · exact hcol p hp
  have hblock : ∀ i k, i ≠ a → i ≠ b → k ≠ a → k ≠ b → i ≠ k → M k i = 0 ∧ M i i = M k k :=
    fun i k h1 h2 h3 h4 h5 => block_apply_of_conjAut_eq hab A hcol hrow haa hX h1 h2 h3 h4 h5
  by_cases hJ : ∃ j, j ≠ a ∧ j ≠ b
  · obtain ⟨j₀, hj₀a, hj₀b⟩ := hJ
    refine ⟨M j₀ j₀, hcol, hrow, rfl, hdiag.symm, fun i j hia hib hja hjb => ?_⟩
    by_cases hij : i = j
    · rw [ite_eq_left hij, ← hij]
      by_cases hij₀ : i = j₀
      · rw [hij₀]
      · exact ((hblock j₀ i hj₀a hj₀b hia hib (Ne.symm hij₀)).2).symm
    · rw [ite_eq_right hij]
      exact (hblock j i hja hjb hia hib (Ne.symm hij)).1
  · push Not at hJ
    refine ⟨0, hcol, hrow, rfl, hdiag.symm, fun i j hia hib _ _ => absurd (hJ i hia) hib⟩

variable [CharP K 2] in
theorem eq_pairDiag_of_conjAut_fix (hn : 4 ≤ n) {a b : Fin n} (hab : a ≠ b) (A : GL (Fin n) K)
    (hA : Commute (single a b (1 : K)) (A : Matrix (Fin n) (Fin n) K)) {m : ℕ} (hm : Odd m)
    {μ : K} (hμ : μ ≠ 0) (hAm : (A : Matrix (Fin n) (Fin n) K) ^ m = μ • 1)
    (hfix : ∀ X ∈ blockSpecialLinear (K := K) ({a, b}ᶜ : Finset (Fin n)),
      conjAut n K A (proj n K X) = proj n K X) :
    ∃ ν, (A : Matrix (Fin n) (Fin n) K) = pairDiag a b ((A : Matrix (Fin n) (Fin n) K) a a) ν := by
  classical
  set M := (A : Matrix (Fin n) (Fin n) K) with hM
  have hcol : ∀ p, p ≠ a → M p a = 0 := fun p hp => col_eq_zero_of_commute_single hA hp
  have hrow : ∀ q, q ≠ b → M b q = 0 := fun q hq => row_eq_zero_of_commute_single hA hq
  have hdiag : M a a = M b b := diag_eq_of_commute_single hA
  have hcomm : ∀ i k, i ≠ a → i ≠ b → k ≠ a → k ≠ b → i ≠ k →
      Commute (single i k (1 : K)) M := by
    intro i k hia hib hka hkb hik
    have hT := hfix (SpecialLinearGroup.transvection hik (1 : K))
      (transvection_mem_blockSpecialLinear hik (by simp [hia, hib]) (by simp [hka, hkb]) 1)
    rw [conjAut_proj] at hT
    have hsq : single i k (1 : K) * single i k 1 = 0 :=
      single_mul_single_of_ne 1 i k i (Ne.symm hik) 1
    exact mul_eq_of_proj_eq A (by rw [coe_slConjugation]; rfl) rfl hsq hsq
      (k := i) (by rw [single_apply]; exact ite_eq_right fun h => hik h.2.symm) hT
  have hpartner : ∀ j, j ≠ a → j ≠ b → ∃ j', j' ≠ a ∧ j' ≠ b ∧ j' ≠ j := by
    intro j hja hjb
    have hcard : 0 < (({a, b, j} : Finset (Fin n))ᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      have : ({a, b, j} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
      omega
    obtain ⟨j', hj'⟩ : (({a, b, j} : Finset (Fin n))ᶜ).Nonempty := Finset.card_pos.1 hcard
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    exact ⟨j', hj'.1, hj'.2.1, hj'.2.2⟩
  have hrowJ : ∀ j, j ≠ a → j ≠ b → ∀ q, q ≠ j → M j q = 0 := by
    intro j hja hjb q hq
    obtain ⟨j', hj'a, hj'b, hj'j⟩ := hpartner j hja hjb
    exact row_eq_zero_of_commute_single (hcomm j' j hj'a hj'b hja hjb hj'j) hq
  have hcolJ : ∀ j, j ≠ a → j ≠ b → ∀ q, q ≠ j → M q j = 0 := by
    intro j hja hjb q hq
    obtain ⟨j', hj'a, hj'b, hj'j⟩ := hpartner j hja hjb
    exact col_eq_zero_of_commute_single (hcomm j j' hja hjb hj'a hj'b (Ne.symm hj'j)) hq
  have hab0 : M a b = 0 := by
    refine eq_zero_of_sub_mulVec_eq hm hμ hAm (l := M a a) (v := Pi.single b 1) (a := a) ?_ ?_
    · rw [mulVec_single_one]
      ext i
      rw [Matrix.col_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
        smul_eq_mul, Pi.single_apply]
      by_cases hia : i = a
      · rw [hia, one_apply_ne hab, ite_eq_left rfl]
        ring
      · rw [ite_eq_right hia, mul_zero]
        by_cases hib : i = b
        · rw [hib, ← hdiag, one_apply_eq]
          ring
        · rw [hrowJ i hia hib b (Ne.symm hib), one_apply_ne hib]
          ring
    · rw [mulVec_single_one]
      ext i
      rw [Matrix.col_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hia : i = a
      · rw [hia, one_apply_eq, mul_one, sub_self]
      · rw [hcol i hia, one_apply_ne hia, mul_zero, sub_zero]
  obtain ⟨j₀, hj₀⟩ : (({a, b} : Finset (Fin n))ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hj₀
  obtain ⟨hj₀a, hj₀b⟩ := hj₀
  refine ⟨M j₀ j₀, ?_⟩
  ext i j
  rw [pairDiag_apply]
  by_cases hia : i = a
  · rw [hia]
    by_cases hja : j = a
    · rw [hja]
      simp
    · rw [ite_eq_right (Ne.symm hja)]
      by_cases hjb : j = b
      · rw [hjb, hab0]
      · exact hcolJ j hja hjb a (Ne.symm hja)
  · by_cases hib : i = b
    · rw [hib]
      by_cases hjb : j = b
      · rw [hjb, ← hdiag]
        simp
      · rw [ite_eq_right (Ne.symm hjb), hrow j hjb]
    · by_cases hij : i = j
      · rw [ite_eq_left hij, ite_eq_right (fun h => h.elim hia hib), ← hij]
        by_cases hij₀ : i = j₀
        · rw [hij₀]
        · exact diag_eq_of_commute_single (hcomm i j₀ hia hib hj₀a hj₀b hij₀)
      · rw [ite_eq_right hij]
        exact hrowJ i hia hib j (Ne.symm hij)

section RadicalFix

theorem blockSL_compl_le_normalizer_radicalP {a b : Fin n} (hab : a ≠ b) :
    blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) ≤
      normalizer ((pairPlacement hab).radicalP K : Set (projectiveSL n K)) := by
  have h := (pairPlacement hab).levi_le_normalizer_radicalP (K := K)
  rw [pairPlacement_free] at h
  exact le_sup_right.trans h

variable [CharP K 2]

theorem radicalP_sup_blockSL_inf_fixAut_le (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (D : GL (Fin n) K) {l ν : K} (hlν : l ≠ ν)
    (hD : (D : Matrix (Fin n) (Fin n) K) = pairDiag a b l ν) :
    ((pairPlacement hab).radicalP K ⊔ blockSL ({a, b}ᶜ : Finset (Fin n))) ⊓
        fixAut (conjAut n K D) ≤ rootGroup hab ⊔ blockSL ({a, b}ᶜ : Finset (Fin n)) := by
  rintro x ⟨hx, hxfix⟩
  have hx' : x ∈ (((pairPlacement hab).radicalP K ⊔
      blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) : Subgroup (projectiveSL n K)) :
        Set (projectiveSL n K)) := hx
  rw [coe_mul_of_right_le_normalizer_left _ _ (blockSL_compl_le_normalizer_radicalP hab)] at hx'
  obtain ⟨q, ⟨r, hr, rfl⟩, s, ⟨X, hX, rfl⟩, rfl⟩ := hx'
  have hI : ({a, b} : Finset (Fin n)).Nonempty := ⟨a, by simp⟩
  have hIc : ({a, b} : Finset (Fin n))ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  have hfix : conjAut n K D (proj n K (r * X)) = proj n K (r * X) := by
    rw [map_mul]
    exact hxfix
  have hrX := mem_blockDiagSL_of_conjAut_proj_eq hI hIc D hlν hD hfix
  have hXd : X ∈ blockDiagSL (K := K) ({a, b} : Finset (Fin n)) :=
    blockSpecialLinear_compl_le_blockDiagSL _ hX
  have hrd : r ∈ blockDiagSL (K := K) ({a, b} : Finset (Fin n)) := by
    have h := mul_mem hrX (inv_mem hXd)
    rwa [mul_inv_cancel_right] at h
  have hrB : r ∈ blockSpecialLinear (K := K) ({a, b} : Finset (Fin n)) := by
    intro i j hij
    by_cases hi : i ∈ ({a, b} : Finset (Fin n))
    · have hj : j ∉ ({a, b} : Finset (Fin n)) := hij.resolve_left (not_not.2 hi)
      rw [mem_blockDiagSL.1 hrd i j ⟨fun _ => hj, fun _ => hi⟩,
        one_apply_ne (fun h => hj (by rw [← h]; exact hi))]
    · by_cases hj : j ∈ ({a, b} : Finset (Fin n))
      · rw [mem_blockDiagSL.1 hrd i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩,
          one_apply_ne (fun h => hi (by rw [h]; exact hj))]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi hj
        refine hr i j ?_
        rw [pairPlacement_level_of_ne hab hi.1 hi.2, pairPlacement_level_of_ne hab hj.1 hj.2]
  show proj n K r * proj n K X ∈ _
  rw [eq_transvection_of_mem_radical_of_mem_blockSpecialLinear hab hr hrB]
  exact mul_mem (mem_sup_left (xab_mem_rootGroup hab _)) (mem_sup_right ⟨X, hX, rfl⟩)

end RadicalFix

section OddAut

variable [Finite K]

theorem exists_conjAut_of_fix_xab (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {β : MulAut (projectiveSL n K)} {m : ℕ} (hm : Odd m) (hβm : β ^ m = 1)
    (hfix : ∀ c : K, β (xab hab c) = xab hab c) :
    ∃ A : GL (Fin n) K, β = conjAut n K A ∧
      Commute (single a b (1 : K)) (A : Matrix (Fin n) (Fin n) K) ∧
      ∃ μ : K, μ ≠ 0 ∧ (A : Matrix (Fin n) (Fin n) K) ^ m = μ • 1 := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1
    (mem_semilinearAutGroup_of_pow_eq_one_of_odd hn hm hβm)
  obtain ⟨rfl, hE⟩ := eq_one_and_commute_of_fix_transvection A σ hab hfix
  rw [map_one, mul_one] at hβm ⊢
  refine ⟨A, rfl, hE, ?_⟩
  have h1 : conjAut n K (A ^ m) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_pow, hβm]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ m) 1 h1
  refine ⟨c, c.ne_zero, ?_⟩
  have h2 := congrArg (fun B : GL (Fin n) K => (B : Matrix (Fin n) (Fin n) K)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at h2
  rw [← h2, scalar_apply, smul_one_eq_diagonal]

end OddAut

end CFSG.SeitzReduction.LinearPilot
