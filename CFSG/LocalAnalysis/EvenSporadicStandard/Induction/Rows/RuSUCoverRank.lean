module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuCoverRankSection
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuOrders
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Unitary

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

@[expose] def uMat (m : ℕ) (a b : Fin n → K) (s : K) : Matrix (Fin n) (Fin n) K :=
  1 + s • Matrix.vecMulVec a b + s ^ 2 ^ m • Matrix.vecMulVec b a

section Facts

variable {a b : Fin n → K} (haa : a ⬝ᵥ a = 0) (hbb : b ⬝ᵥ b = 0) (hab : a ⬝ᵥ b = 0)
include haa hbb hab

theorem uMat_add (s t : K) : uMat m a b (s + t) = uMat m a b s * uMat m a b t := by
  have hba : b ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact hab
  have hfr : (s + t) ^ 2 ^ m = s ^ 2 ^ m + t ^ 2 ^ m := add_pow_char_pow _ _ _ _
  simp only [uMat, hfr, add_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, haa, hbb, hab, hba,
    zero_smul, Matrix.vecMulVec_zero, smul_zero, add_zero]
  abel

theorem uMat_zero : uMat m a b 0 = 1 := by
  simp [uMat, zero_pow (pow_ne_zero m two_ne_zero)]

theorem uMat_mul_self (s : K) : uMat m a b s * uMat m a b s = 1 := by
  rw [← uMat_add haa hbb hab, CharTwo.add_self_eq_zero, uMat_zero haa hbb hab]

end Facts

section Frobenius

variable {a b : Fin n → K} (hK : Nat.card K = (2 ^ m) ^ 2)
  (hfa : ∀ i, a i ^ 2 ^ m = a i) (hfb : ∀ i, b i ^ 2 ^ m = b i)
include hK hfa hfb

theorem pow_pow_eq (s : K) : (s ^ 2 ^ m) ^ 2 ^ m = s := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card s
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [← pow_mul, ← sq]
  exact h

theorem uMat_map_frob (s : K) : (uMat m a b s).map (· ^ 2 ^ m) = (uMat m a b s)ᵀ := by
  ext i j
  have hss := pow_pow_eq hK hfa hfb s
  simp only [uMat, Matrix.map_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, mul_pow, mul_pow, hss, hfa, hfb, hfa,
    hfb]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, one_pow]
    ring
  · have hji : ¬ j = i := fun h => hij h.symm
    simp only [Matrix.one_apply_ne hij, Matrix.one_apply_ne hji,
      zero_pow (pow_ne_zero m two_ne_zero)]
    ring

end Frobenius

section Group

variable {a b : Fin n → K} (haa : a ⬝ᵥ a = 0) (hbb : b ⬝ᵥ b = 0) (hab : a ⬝ᵥ b = 0)
  (hK : Nat.card K = (2 ^ m) ^ 2) (hfa : ∀ i, a i ^ 2 ^ m = a i) (hfb : ∀ i, b i ^ 2 ^ m = b i)
include haa hbb hab

theorem det_uMat (s : K) : (uMat m a b s).det = 1 := by
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hd : (uMat m a b s).det * (uMat m a b s).det = 1 := by
    rw [← Matrix.det_mul, uMat_mul_self haa hbb hab s, Matrix.det_one]
  have h0 : ((uMat m a b s).det - 1) ^ 2 = 0 := by
    linear_combination hd + (1 - (uMat m a b s).det) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

@[expose] def uGL (s : K) : GL (Fin n) K :=
  ⟨uMat m a b s, uMat m a b s, uMat_mul_self haa hbb hab s, uMat_mul_self haa hbb hab s⟩

include hK hfa hfb in
theorem uGL_mem (s : K) : uGL (m := m) haa hbb hab s ∈ StatedSU n (2 ^ m) K := by
  refine Subgroup.subset_closure ⟨det_uMat haa hbb hab s, ?_⟩
  change ((uMat m a b s).map (· ^ 2 ^ m))ᵀ * uMat m a b s = 1
  rw [uMat_map_frob hK hfa hfb, Matrix.transpose_transpose, uMat_mul_self haa hbb hab]

include hK hfa hfb in
@[expose] noncomputable def uHom : Multiplicative K →* StatedSU n (2 ^ m) K where
  toFun t := ⟨uGL (m := m) haa hbb hab t.toAdd, uGL_mem haa hbb hab hK hfa hfb t.toAdd⟩
  map_one' := Subtype.ext (Units.ext (by
    show uMat m a b (Multiplicative.toAdd 1) = 1
    rw [toAdd_one, uMat_zero haa hbb hab]))
  map_mul' s t := Subtype.ext (Units.ext (by
    show uMat m a b (Multiplicative.toAdd (s * t)) =
      uMat m a b (Multiplicative.toAdd s) * uMat m a b (Multiplicative.toAdd t)
    rw [toAdd_mul, uMat_add haa hbb hab]))

theorem uMat_apply {i j : Fin n} (hij : i ≠ j) (hai : a i = 1) (hbi : b i = 0) (haj : a j = 0)
    (hbj : b j = 1) (s : K) : uMat m a b s i j = s := by
  simp [uMat, Matrix.vecMulVec_apply, Matrix.one_apply_ne hij, hai, hbi, haj, hbj]

include hK hfa hfb in
theorem three_le_pRank_of_su_cover {i j : Fin n} (hij : i ≠ j) (hai : a i = 1) (hbi : b i = 0)
    (haj : a j = 0) (hbj : b j = 1) (h8 : 8 ≤ Nat.card K) {X : Type} [Group X] [Finite X]
    {φ : X →* StatedProj (StatedSU n (2 ^ m) K)} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU n (2 ^ m) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → ∃ s : StatedSU n (2 ^ m) K →* E,
        ∀ g, π (s g) = g) : 3 ≤ CFSG.pRank 2 X := by
  let ρ : StatedSU n (2 ^ m) K →* StatedProj (StatedSU n (2 ^ m) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ m) K))
  let U := uHom (m := m) haa hbb hab hK hfa hfb
  have hUk : ∀ t : Multiplicative K, ((U t : StatedSU n (2 ^ m) K) : GL (Fin n) K) =
      uGL (m := m) haa hbb hab (Multiplicative.toAdd t) := fun t => rfl
  have hinjU : Function.Injective U := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 := congrArg (fun g : StatedSU n (2 ^ m) K =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ht
    change uMat m a b (Multiplicative.toAdd t) i j = (1 : Matrix (Fin n) (Fin n) K) i j at h1
    rw [uMat_apply haa hbb hab hij hai hbi haj hbj, Matrix.one_apply_ne hij] at h1
    exact Multiplicative.toAdd.injective (by simpa using h1)
  refine three_le_pRank_of_section (ρ := ρ) (E := U.range) hφ hker hsec ?_ ?_ ?_ ?_
  · rintro _ ⟨t, rfl⟩
    rw [← map_mul]
    have : t * t = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact CharTwo.add_self_eq_zero _
    rw [this, map_one]
  · rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinjU).toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact h8
  · rintro _ ⟨t, rfl⟩ hx
    have h1 : ((U t : StatedSU n (2 ^ m) K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K :=
      (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 hx)
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) hc
    rw [hUk] at h2
    change (Matrix.scalar (Fin n) (c : K)) i j = uMat m a b (Multiplicative.toAdd t) i j at h2
    rw [uMat_apply haa hbb hab hij hai hbi haj hbj] at h2
    have h3 : Multiplicative.toAdd t = 0 := by
      rw [← h2]
      simp [Matrix.scalar_apply, hij]
    have : t = 1 := Multiplicative.toAdd.injective (by simpa using h3)
    rw [this, map_one]

end Group

set_option linter.unusedSimpArgs false in
theorem exists_vectors (hn : 4 ≤ n) (m : ℕ) :
    ∃ a b : Fin n → K, a ⬝ᵥ a = 0 ∧ b ⬝ᵥ b = 0 ∧ a ⬝ᵥ b = 0 ∧ (∀ i, a i ^ 2 ^ m = a i) ∧
      (∀ i, b i ^ 2 ^ m = b i) ∧ ∃ i j : Fin n, i ≠ j ∧ a i = 1 ∧ b i = 0 ∧ a j = 0 ∧ b j = 1 := by
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by linear_combination h2
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  set i3 : Fin n := ⟨3, by omega⟩ with hi3
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [hi0, hi2, Fin.ext_iff]
  have h03 : i0 ≠ i3 := by simp [hi0, hi3, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [hi1, hi2, Fin.ext_iff]
  have h13 : i1 ≠ i3 := by simp [hi1, hi3, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [hi2, hi3, Fin.ext_iff]
  have hfrob : ∀ (x y : Fin n) (hxy : x ≠ y) (i : Fin n),
      ((Pi.single x (1 : K) + Pi.single y (1 : K) : Fin n → K) i) ^ 2 ^ m =
        (Pi.single x (1 : K) + Pi.single y (1 : K) : Fin n → K) i := by
    intro x y hxy i
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs with h h'
    · exact absurd (h.symm.trans h') hxy
    all_goals simp [zero_pow (pow_ne_zero m two_ne_zero)]
  refine ⟨Pi.single i0 1 + Pi.single i1 1, Pi.single i2 1 + Pi.single i3 1, ?_, ?_, ?_,
    hfrob i0 i1 h01, hfrob i2 i3 h23, ⟨i0, i2, h02, ?_, ?_, ?_, ?_⟩⟩
  · simp only [dotProduct_add, dotProduct_single, Pi.add_apply, Pi.single_apply, h01, h01.symm,
      ite_true, ite_false, mul_one, add_zero, zero_add]
    exact h11
  · simp only [dotProduct_add, dotProduct_single, Pi.add_apply, Pi.single_apply, h23, h23.symm,
      ite_true, ite_false, mul_one, add_zero, zero_add]
    exact h11
  · simp [dotProduct_add, dotProduct_single, h02, h03, h12, h13, h02.symm, h03.symm, h12.symm,
      h13.symm]
  all_goals simp [Pi.single_apply, h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm,
    h12.symm, h13.symm, h23.symm]

end Unitary

theorem three_le_pRank_of_psu_model_cover
    {n m : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : 3 ≤ m) {X : Type} [Group X] [Finite X] (h : LieModel (X ⧸ center X) .PSU n 2 m) :
    3 ≤ CFSG.pRank 2 X := by
  have hn4 : 4 ≤ n := by omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by omega) h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hq : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  let φ : X →* StatedProj (StatedSU n (2 ^ m) K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU n (2 ^ m) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : StatedSU n (2 ^ m) K →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hcen
    rcases hn with rfl | rfl
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hK
        (by decide) le_rfl hq hπ hcen
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hK
        (by omega) (by norm_num) (by decide) (by
          intro h
          have := congrArg Prod.fst h
          norm_num at this) hπ hcen
  obtain ⟨a, b, haa, hbb, hab, hfa, hfb, i, j, hij, hai, hbi, haj, hbj⟩ :=
    exists_vectors (K := K) hn4 m
  exact three_le_pRank_of_su_cover haa hbb hab hK hfa hfb hij hai hbi haj hbj h8 hφ hker hsec

end CFSG.EvenSporadicStandard.Induction
