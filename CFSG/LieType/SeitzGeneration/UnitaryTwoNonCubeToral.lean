module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoNonCubeCore
public import CFSG.LieType.SeitzGeneration.UnitaryTwoInduct

public section

namespace CFSG.LieType.SeitzGeneration

namespace TwoNonCube

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.SeitzGeneration.UnitaryTwo CFSG.LieType.SeitzGeneration.NonCube
  CFSG.LieType.SeitzGeneration.Centers CFSG.LieType.SeitzGeneration.ONExt
  CFSG.RankThree.PartOne.KFU

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_eigenframe_of_comm (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (G : Subgroup (primeFormUnitary h (idGram K n))) (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x)
    (hexp : ∀ x ∈ G, x ^ 3 = 1) :
    ∃ u : Fin n → Fin n → K, IsON σ₀ u ∧ (∀ v, ∃ c, orthoEmb u c = v) ∧
      ∀ g ∈ G, ∃ d : Fin n → K, ∀ i,
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = d i • u i := by
  classical
  have hσ : (⇑σ₀ : K → K) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hq3 G hcomm hexp
  set Pm : Matrix (Fin n) (Fin n) K := ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hPm
  have hPunit : conjTr σ₀ Pm * Pm = 1 := by
    have h1 := mem_primeFormUnitary.1 P.2
    simp only [idGram, Units.val_one, Matrix.mul_one] at h1
    rw [conjTr, hσ]
    exact h1
  have hPinv : Pm * ((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) = 1 := by
    rw [hPm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPinv' : (((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm = 1 := by
    rw [hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨fun i => Pm *ᵥ Pi.single i 1, ?_, ?_, ?_⟩
  · intro i j
    rw [herm_mulVec, hPunit, one_mulVec, herm_single_left, map_one, one_mul, Pi.single_apply]
  · intro v
    refine ⟨(((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v, ?_⟩
    have hcol : colMat (fun i => Pm *ᵥ (Pi.single i 1 : Fin n → K)) = Pm := by
      ext k j
      simp [colMat, Matrix.mulVec_single_one]
    rw [← colMat_mulVec, hcol, mulVec_mulVec, hPinv, one_mulVec]
  · intro y hy
    have hdiag := hP y hy
    set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY
    set Pi' : Matrix (Fin n) (Fin n) K :=
      (((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hPi'
    have hcoe : (((P⁻¹ * y * P : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = Pi' * Y * Pm := by
      simp [hPi', hY, hPm, Units.val_mul]
    rw [hcoe] at hdiag
    obtain ⟨d, hd⟩ : ∃ d : Fin n → K, Pi' * Y * Pm = diagonal d :=
      ⟨_, hdiag.diagonal_diag.symm⟩
    have hYP : Y * Pm = Pm * diagonal d := by
      calc Y * Pm = (Pm * Pi') * Y * Pm := by rw [hPinv, Matrix.one_mul]
        _ = Pm * (Pi' * Y * Pm) := by simp only [Matrix.mul_assoc]
        _ = Pm * diagonal d := by rw [hd]
    refine ⟨d, fun i => ?_⟩
    have hdi : (diagonal d *ᵥ (Pi.single i 1 : Fin n → K)) = d i • Pi.single i 1 := by
      funext k
      simp only [mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp_all
    rw [mulVec_mulVec, hYP, ← mulVec_mulVec, hdi, mulVec_smul]

theorem mulVec_pow_eig {M : Matrix (Fin n) (Fin n) K} {v : Fin n → K} {d : K}
    (h : M *ᵥ v = d • v) (k : ℕ) : (M ^ k) *ᵥ v = d ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

theorem zmod3_pair : ∀ aa ab ba bb : ZMod 3, aa = ab ∨ ba = bb ∨ aa + ba = ab + bb ∨
    aa + 2 * ba = ab + 2 * bb := by decide

theorem zmod3_triple_aux : ∀ s₁ s₂ pj qj pk qk : ZMod 3, (s₁ ≠ 0 ∨ s₂ ≠ 0) →
    s₁ * pj + s₂ * qj = 0 → s₁ * pk + s₂ * qk = 0 →
    (pj = 0 ∧ pk = 0) ∨ (qj = 0 ∧ qk = 0) ∨ (pj + qj = 0 ∧ pk + qk = 0) ∨
      (pj + 2 * qj = 0 ∧ pk + 2 * qk = 0) := by decide

theorem zmod3_triple {s₁ s₂ ai aj ak bi bj bk : ZMod 3} (hs : s₁ ≠ 0 ∨ s₂ ≠ 0)
    (hj : s₁ * ai + s₂ * bi = s₁ * aj + s₂ * bj) (hk : s₁ * ai + s₂ * bi = s₁ * ak + s₂ * bk) :
    (ai = aj ∧ ai = ak) ∨ (bi = bj ∧ bi = bk) ∨ (ai + bi = aj + bj ∧ ai + bi = ak + bk) ∨
      (ai + 2 * bi = aj + 2 * bj ∧ ai + 2 * bi = ak + 2 * bk) := by
  have := zmod3_triple_aux s₁ s₂ (ai - aj) (bi - bj) (ai - ak) (bi - bk) hs
    (by linear_combination hj) (by linear_combination hk)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by linear_combination h1, by linear_combination h2⟩
  · exact Or.inr (Or.inl ⟨by linear_combination h1, by linear_combination h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by linear_combination h1, by linear_combination h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by linear_combination h1, by linear_combination h2⟩))

theorem eq_top_toral_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) {H : Subgroup (SUid σ₀ n)}
    (hHx : ∀ g : SUid σ₀ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (x : Matrix (Fin n) (Fin n) K) = (x : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    (hHy : ∀ g : SUid σ₀ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (y : Matrix (Fin n) (Fin n) K) = (y : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    (hHxy : ∀ g : SUid σ₀ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    (hHxy2 : ∀ g : SUid σ₀ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H) :
    H = ⊤ := by
  classical
  have hq3 : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  obtain ⟨ζ, hζ3, hζ1, -⟩ := exists_primitive_cube_root h hq3
  have hK : Field4 σ₀ ζ := field4_of_two h hq hζ3 hζ1
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hXdef
  set Y : Matrix (Fin n) (Fin n) K := (y : Matrix (Fin n) (Fin n) K) with hYdef
  have hX3 : X ^ 3 = 1 := by rw [hXdef, ← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hY3 : Y ^ 3 = 1 := by rw [hYdef, ← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hxy2 : ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = X * (Y * Y) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, pow_two]
  have hxy1 : ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = X * Y := rfl
  have unitM : ∀ z ∈ primeFormUnitary h (idGram K n), ∀ u w,
      herm σ₀ (((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u)
        (((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = herm σ₀ u w := by
    intro z hz u w
    have hzB : ∀ u v, idForm h n (Matrix.toLin' (z : Matrix (Fin n) (Fin n) K) u)
        (Matrix.toLin' (z : Matrix (Fin n) (Fin n) K) v) = idForm h n u v := fun u v =>
      mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff z).mpr hz) u v
    have := hzB u w
    rw [Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  have hXU : ∀ u w, herm σ₀ (X *ᵥ u) (X *ᵥ w) = herm σ₀ u w := unitM x hx
  have hYU : ∀ u w, herm σ₀ (Y *ᵥ u) (Y *ᵥ w) = herm σ₀ u w := unitM y hy
  let x' : primeFormUnitary h (idGram K n) := ⟨x, hx⟩
  let y' : primeFormUnitary h (idGram K n) := ⟨y, hy⟩
  have hx'3 : x' ^ 3 = 1 := Subtype.ext hx3
  have hy'3 : y' ^ 3 = 1 := Subtype.ext hy3
  have hxy' : x' * y' = y' * x' := Subtype.ext hxy
  let S : Set (primeFormUnitary h (idGram K n)) := {x', y'}
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl) <;> first | rfl | exact hxy' | exact hxy'.symm
  letI : CommGroup (Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm (fun a ha b hb _ => hS a ha b hb)
  have hcommG : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Subgroup.closure S) ⟨b, hb⟩)
  have hexpG : ∀ a ∈ Subgroup.closure S, a ^ 3 = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact hx'3
      · exact hy'3
    | one => simp
    | mul g g' hg hg' ihg ihg' =>
      rw [(show Commute g g' from hcommG g hg g' hg').mul_pow, ihg, ihg', one_mul]
    | inv g _ ihg => rw [inv_pow, ihg, inv_one]
  obtain ⟨u, hu, hspan, heig⟩ := exists_eigenframe_of_comm h hq3 (Subgroup.closure S) hcommG hexpG
  obtain ⟨dx, hdx⟩ := heig x' (Subgroup.subset_closure (by simp [S]))
  obtain ⟨dy, hdy⟩ := heig y' (Subgroup.subset_closure (by simp [S]))
  have hdx' : ∀ i, X *ᵥ u i = dx i • u i := hdx
  have hdy' : ∀ i, Y *ᵥ u i = dy i • u i := hdy
  have hu1 : ∀ i, herm σ₀ (u i) (u i) = 1 := fun i => herm_self_of_isON hu i
  have hu0 : ∀ i, u i ≠ 0 := fun i h0 => by
    have := hu1 i
    rw [h0, herm_zero_left] at this
    exact zero_ne_one this
  have hcube : ∀ (M : Matrix (Fin n) (Fin n) K) (d : K) (v : Fin n → K), M ^ 3 = 1 → v ≠ 0 →
      M *ᵥ v = d • v → d ^ 3 = 1 := by
    intro M d v hM hv hMv
    have h1 := mulVec_pow_eig hMv 3
    rw [hM, one_mulVec] at h1
    have h2 : (d ^ 3 - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)
  have hdx3 : ∀ i, dx i ^ 3 = 1 := fun i => hcube X (dx i) (u i) hX3 (hu0 i) (hdx' i)
  have hdy3 : ∀ i, dy i ^ 3 = 1 := fun i => hcube Y (dy i) (u i) hY3 (hu0 i) (hdy' i)
  have hdx0 : ∀ i, dx i ≠ 0 := fun i h0 => by
    have := hdx3 i
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  have hdy0 : ∀ i, dy i ≠ 0 := fun i h0 => by
    have := hdy3 i
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  have hKcard : Nat.card K = 4 := by
    rw [h.card_eq_sq, hq]
    norm_num
  have hKu : Nat.card Kˣ = 3 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hKcard]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
  let e : Kˣ ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hKu hZ
  let px : Fin n → Kˣ := fun i => Units.mk0 (dx i) (hdx0 i)
  let py : Fin n → Kˣ := fun i => Units.mk0 (dy i) (hdy0 i)
  let a : Fin n → ZMod 3 := fun i => Multiplicative.toAdd (e (px i))
  let b : Fin n → ZMod 3 := fun i => Multiplicative.toAdd (e (py i))
  have hlam : ∀ (s t : ℕ) (i j : Fin n), (s : ZMod 3) * a i + (t : ZMod 3) * b i =
      (s : ZMod 3) * a j + (t : ZMod 3) * b j → dx i ^ s * dy i ^ t = dx j ^ s * dy j ^ t := by
    intro s t i j hij
    have key : ∀ i : Fin n, e (px i ^ s * py i ^ t) =
        Multiplicative.ofAdd ((s : ZMod 3) * a i + (t : ZMod 3) * b i) := by
      intro i
      rw [map_mul, map_pow, map_pow]
      have h1 : e (px i) = Multiplicative.ofAdd (a i) := rfl
      have h2 : e (py i) = Multiplicative.ofAdd (b i) := rfl
      rw [h1, h2, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, nsmul_eq_mul, nsmul_eq_mul]
    have h3 := e.injective ((key i).trans ((congrArg Multiplicative.ofAdd hij).trans
      (key j).symm))
    have h4 := congrArg Units.val h3
    simpa [px, py] using h4
  let Ms : Fin 4 → Matrix (Fin n) (Fin n) K := ![X, Y, X * Y, X * (Y * Y)]
  let lams : Fin 4 → Fin n → K := ![dx, dy, fun i => dx i * dy i, fun i => dx i * (dy i * dy i)]
  have hMeig : ∀ l i, Ms l *ᵥ u i = lams l i • u i := by
    intro l i
    fin_cases l
    · exact hdx' i
    · exact hdy' i
    · show (X * Y) *ᵥ u i = (dx i * dy i) • u i
      rw [← Matrix.mulVec_mulVec, hdy', Matrix.mulVec_smul, hdx', smul_smul, mul_comm]
    · show (X * (Y * Y)) *ᵥ u i = (dx i * (dy i * dy i)) • u i
      have hYY : (Y * Y) *ᵥ u i = (dy i * dy i) • u i := by
        rw [← Matrix.mulVec_mulVec, hdy', Matrix.mulVec_smul, hdy', smul_smul]
      rw [← Matrix.mulVec_mulVec, hYY, Matrix.mulVec_smul, hdx', smul_smul]
      congr 1
      ring
  have hMU : ∀ l, ∀ u w, herm σ₀ (Ms l *ᵥ u) (Ms l *ᵥ w) = herm σ₀ u w := by
    intro l u w
    fin_cases l
    · exact hXU u w
    · exact hYU u w
    · show herm σ₀ ((X * Y) *ᵥ u) ((X * Y) *ᵥ w) = _
      simp only [← Matrix.mulVec_mulVec, hXU, hYU]
    · show herm σ₀ ((X * (Y * Y)) *ᵥ u) ((X * (Y * Y)) *ᵥ w) = _
      simp only [← Matrix.mulVec_mulVec, hXU, hYU]
  have hMH : ∀ l, ∀ g : SUid σ₀ n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Ms l =
      Ms l * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H := by
    intro l g hg
    fin_cases l
    · exact hHx g hg
    · exact hHy g hg
    · exact hHxy g hg
    · exact hHxy2 g (by rw [hxy2]; exact hg)
  have hlam0 : ∀ l i, lams l i ≠ 0 := by
    intro l i
    fin_cases l
    · exact hdx0 i
    · exact hdy0 i
    · exact mul_ne_zero (hdx0 i) (hdy0 i)
    · exact mul_ne_zero (hdx0 i) (mul_ne_zero (hdy0 i) (hdy0 i))
  have hcenter : ∀ i j : Fin n, i ≠ j → IsCenter H (u i + u j) := by
    intro i j hij
    obtain ⟨l, hl⟩ : ∃ l : Fin 4, lams l i = lams l j := by
      rcases zmod3_pair (a i) (a j) (b i) (b j) with h1 | h1 | h1 | h1
      · refine ⟨0, ?_⟩
        have := hlam 1 0 i j (by simpa using h1)
        show dx i = dx j
        simpa using this
      · refine ⟨1, ?_⟩
        have := hlam 0 1 i j (by simpa using h1)
        show dy i = dy j
        simpa using this
      · refine ⟨2, ?_⟩
        have := hlam 1 1 i j (by simpa using h1)
        show dx i * dy i = dx j * dy j
        simpa using this
      · refine ⟨3, ?_⟩
        have := hlam 1 2 i j (by simpa using h1)
        show dx i * (dy i * dy i) = dx j * (dy j * dy j)
        simpa [pow_two] using this
    have hv : herm σ₀ (u i + u j) (u i + u j) = 0 := by
      simp only [herm_add_left, herm_add_right, hu1, herm_eq_zero_of_isON hu hij,
        herm_eq_zero_of_isON hu hij.symm]
      linear_combination hK.two
    refine isCenter_of_eigen_matrix hσ.invol (hMH l) (hMU l) hv (l := lams l i)
      (hK.norm_one _ (hlam0 l i)) ?_
    rw [mulVec_add, hMeig, hMeig, ← hl, smul_add]
  obtain ⟨τ, hτ, l, hl1, hl2⟩ : ∃ τ : Fin 5 → Fin n, Function.Injective τ ∧
      ∃ l : Fin 4, lams l (τ 0) = lams l (τ 1) ∧ lams l (τ 0) = lams l (τ 2) := by
    have hE : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 9 := by simp
    let χ : Fin n → Multiplicative (ZMod 3 × ZMod 3) →* Multiplicative (ZMod 3) := fun i =>
      AddMonoidHom.toMultiplicative
        (AddMonoidHom.mk' (fun p : ZMod 3 × ZMod 3 => p.1 * a i + p.2 * b i) (fun p q => by
          simp only [Prod.fst_add, Prod.snd_add]
          ring))
    obtain ⟨s, hs1, i, j, k, hij, hik, hjk, hc1, hc2⟩ := exists_eq_triple hE hZ
      (fun t : Fin 5 => χ (Fin.castLE hn t))
    obtain ⟨⟨s₁, s₂⟩, rfl⟩ : ∃ p : ZMod 3 × ZMod 3, s = Multiplicative.ofAdd p :=
      ⟨Multiplicative.toAdd s, rfl⟩
    have hs : s₁ ≠ 0 ∨ s₂ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hs1
      rw [hcon.1, hcon.2]
      rfl
    have h1 : s₁ * a (Fin.castLE hn i) + s₂ * b (Fin.castLE hn i) =
        s₁ * a (Fin.castLE hn j) + s₂ * b (Fin.castLE hn j) := by
      have h1' : Multiplicative.ofAdd (s₁ * a (Fin.castLE hn i) + s₂ * b (Fin.castLE hn i)) =
          Multiplicative.ofAdd (s₁ * a (Fin.castLE hn j) + s₂ * b (Fin.castLE hn j)) := hc1
      exact Multiplicative.ofAdd.injective h1'
    have h2 : s₁ * a (Fin.castLE hn i) + s₂ * b (Fin.castLE hn i) =
        s₁ * a (Fin.castLE hn k) + s₂ * b (Fin.castLE hn k) := by
      have h2' : Multiplicative.ofAdd (s₁ * a (Fin.castLE hn i) + s₂ * b (Fin.castLE hn i)) =
          Multiplicative.ofAdd (s₁ * a (Fin.castLE hn k) + s₂ * b (Fin.castLE hn k)) := hc2
      exact Multiplicative.ofAdd.injective h2'
    obtain ⟨l', m', hli, hlj, hlk, hmi, hmj, hmk, hlm⟩ := exists_two_complement i j k hij hik hjk
    let ρ : Fin 5 → Fin 5 := ![i, j, k, l', m']
    have hρ : Function.Injective ρ :=
      injective_five hij hik (Ne.symm hli) (Ne.symm hmi) hjk (Ne.symm hlj) (Ne.symm hmj)
        (Ne.symm hlk) (Ne.symm hmk) hlm
    refine ⟨fun t => Fin.castLE hn (ρ t), fun p q hpq => hρ (Fin.castLE_injective hn hpq), ?_⟩
    show ∃ l : Fin 4, lams l (Fin.castLE hn i) = lams l (Fin.castLE hn j) ∧
      lams l (Fin.castLE hn i) = lams l (Fin.castLE hn k)
    rcases zmod3_triple hs h1 h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · refine ⟨0, ?_, ?_⟩
      · show dx _ = dx _
        simpa using hlam 1 0 _ _ (by simpa using h3)
      · show dx _ = dx _
        simpa using hlam 1 0 _ _ (by simpa using h4)
    · refine ⟨1, ?_, ?_⟩
      · show dy _ = dy _
        simpa using hlam 0 1 _ _ (by simpa using h3)
      · show dy _ = dy _
        simpa using hlam 0 1 _ _ (by simpa using h4)
    · refine ⟨2, ?_, ?_⟩
      · show dx _ * dy _ = dx _ * dy _
        simpa using hlam 1 1 _ _ (by simpa using h3)
      · show dx _ * dy _ = dx _ * dy _
        simpa using hlam 1 1 _ _ (by simpa using h4)
    · refine ⟨3, ?_, ?_⟩
      · show dx _ * (dy _ * dy _) = dx _ * (dy _ * dy _)
        simpa [pow_two] using hlam 1 2 _ _ (by simpa using h3)
      · show dx _ * (dy _ * dy _) = dx _ * (dy _ * dy _)
        simpa [pow_two] using hlam 1 2 _ _ (by simpa using h4)
  let x5 : Fin 5 → Fin n → K := fun t => u (τ t)
  have hx5 : IsON σ₀ x5 := isON_comp hu hτ
  have hP : ∀ i j : Fin 4, i ≠ j → IsCenter H (x5 i.castSucc + x5 j.castSucc) := fun i j hij =>
    hcenter _ _ (fun hc => hij (Fin.castSucc_injective 4 (hτ hc)))
  have hD : ∀ hh : IsON σ₀ ![x5 0, x5 1, x5 2], dft3 hK hh ∈ H := fun hh =>
    dft3_mem hK (hMU l) (hMH l) hh (l := lams l (τ 0)) (hMeig l (τ 0))
      (by rw [hl1]; exact hMeig l (τ 1)) (by rw [hl2]; exact hMeig l (τ 2))
  have hS : ∀ (i : Fin 4) (hh : IsON σ₀ ![x5 i.castSucc, x5 4]) (t : K) (ht : t ≠ 0),
      scale2 hK hh ht ∈ H := fun i hh t ht =>
    scale2_mem hK (hMU 0) (hMH 0) hh (hMeig 0 _) (hMeig 0 _) ht
  have hblk := allCenters_blk4 hK hx5 hP hD hS
  let S₀ : Finset (Fin n) := Finset.univ.image (fun t : Fin 4 => τ t.castSucc)
  have hinj : Function.Injective (fun t : Fin 4 => τ t.castSucc) := fun p q hpq =>
    Fin.castSucc_injective 4 (hτ hpq)
  have hS₀card : S₀.card = 4 := by
    rw [show S₀ = Finset.univ.image (fun t : Fin 4 => τ t.castSucc) from rfl,
      Finset.card_image_of_injective _ hinj]
    simp
  have hS₀span : spanS u S₀ = Submodule.span K (Set.range (blk4 x5)) := by
    unfold spanS
    congr 1
    ext v
    constructor
    · rintro ⟨a', ha, rfl⟩
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨τ t.castSucc, Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩), rfl⟩
  have hpt : ∀ j, j ∉ S₀ → ∃ w ∈ spanS u S₀, herm σ₀ w w = 1 ∧ IsCenter H (w + u j) := by
    intro j hj
    have h0 : τ 0 ∈ S₀ := Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
    refine ⟨u (τ 0), Submodule.subset_span ⟨τ 0, Finset.mem_coe.2 h0, rfl⟩, hu1 _,
      hcenter _ _ ?_⟩
    intro hc
    exact hj (hc ▸ h0)
  have hgrow := allCenters_grow hK hu (S₀ := S₀) (by omega) (by rw [hS₀span]; exact hblk) hpt
    Finset.univ
  rw [Finset.union_eq_right.2 (Finset.subset_univ _)] at hgrow
  have htop : spanS u Finset.univ = ⊤ := by
    rw [spanS, Finset.coe_univ, Set.image_univ, eq_top_iff]
    intro v _
    obtain ⟨c, rfl⟩ := hspan v
    exact orthoEmb_mem_span u c
  rw [htop] at hgrow
  exact eq_top_of_forall_isCenter hσ (by omega) (fun h3 => by omega) fun a' ha' =>
    hgrow a' Submodule.mem_top ha'

end TwoNonCube

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem closure_planeFixUn_toral_two {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) :
    Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊤ := by
  classical
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  let ε : SUid (unitaryInvolution K ℓ f) n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let H : Subgroup (SUid (unitaryInvolution K ℓ f) n) :=
    (Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).comap
        ε.toMonoidHom
  have hH : H = ⊤ := by
    refine TwoNonCube.eq_top_toral_two h hq hn hx hy hxy hx3 hy3 ?_ ?_ ?_ ?_
    · exact fun g hg => Subgroup.subset_closure
        (Or.inl (Or.inl (Or.inl (mem_FixUn_of_mul_comm (g := ε g) hg))))
    · exact fun g hg => Subgroup.subset_closure
        (Or.inl (Or.inl (Or.inr (mem_FixUn_of_mul_comm (g := ε g) hg))))
    · exact fun g hg => Subgroup.subset_closure
        (Or.inl (Or.inr (mem_FixUn_of_mul_comm (g := ε g) hg)))
    · exact fun g hg => Subgroup.subset_closure
        (Or.inr (mem_FixUn_of_mul_comm (g := ε g) hg))
  rw [eq_top_iff]
  intro u _
  have hu : ε.symm u ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using hu

end CFSG.LieType.SeitzGeneration
