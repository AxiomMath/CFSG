module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFourDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFourMono
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix
public import CFSG.ClassicalInvolution.Models.LinearFrames.SignsPow

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalInvolution.Models

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem eq_diagonal_self_of_eq_diagonal {M : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (h : M = diagonal d) : M = diagonal (fun i => M i i) := by
  rw [h]
  exact ((Matrix.isDiag_diagonal d).diagonal_diag).symm

theorem eq_diagonal_of_col_single {c : Matrix (Fin 3) (Fin 3) K} {σ : Equiv.Perm (Fin 3)}
    {a : Fin 3 → K} (hcol : ∀ j, c *ᵥ Pi.single j 1 = a j • Pi.single (σ j) 1)
    (hσ : σ = 1) : c = diagonal a := by
  subst hσ
  have hdiag : c.IsDiag := by
    intro i j hij
    have h := congrFun (hcol j) i
    rw [Matrix.mulVec_single_one] at h
    have hij' : i ≠ (1 : Equiv.Perm (Fin 3)) j := by simpa using hij
    rw [Pi.smul_apply, Pi.single_eq_of_ne hij'] at h
    simpa using h
  rw [← hdiag.diagonal_diag]
  congr 1
  funext j
  have h := congrFun (hcol j) j
  rw [Matrix.mulVec_single_one] at h
  change c j j = a j
  simpa using h

private theorem conj_scalar_eq (g : GL (Fin 3) K) (ξ : Kˣ) :
    g * GeneralLinearGroup.scalar (Fin 3) ξ * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) ξ := by
  rw [mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc, mul_inv_cancel, one_mul]

theorem inv_conj_mem_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g z : GL (Fin 3) K}
    (hz : z ∈ zPi π 3 (p ^ f) K) :
    g⁻¹ * z * g ∈ zPi π 3 (p ^ f) K := by
  obtain ⟨ξ, hξ, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  have hsc : g⁻¹ * GeneralLinearGroup.scalar (Fin 3) ξ * g =
      GeneralLinearGroup.scalar (Fin 3) ξ := by
    simpa using conj_scalar_eq g⁻¹ ξ
  rw [hsc]
  exact scalar_mem_zPi hK hq hτ hτ1 hξ

theorem conj_cube_eq_scalar (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K) {g b : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (hb : b ∈ B) :
    ∃ ξ : Kˣ, (g⁻¹ * b * g) ^ 3 = GeneralLinearGroup.scalar (Fin 3) ξ := by
  have hmem : (g⁻¹ * b * g) ^ 3 ∈ zPi π 3 (p ^ f) K := by
    have h : (g⁻¹ * b * g) ^ 3 = g⁻¹ * b ^ 3 * g := by
      rw [show g⁻¹ * b * g = MulAut.conj g⁻¹ b by rfl, ← map_pow]
      rfl
    rw [h]
    exact inv_conj_mem_zPi hK hq hτ hτ1 (hB b hb)
  obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hmem
  exact ⟨ξ, hξ.symm⟩

theorem diag_pow_three_eq_of_pow_three_scalar {c : GL (Fin 3) K} {d : Fin 3 → K}
    (hd : (c : Matrix (Fin 3) (Fin 3) K) = diagonal d) {ξ : Kˣ}
    (h3 : c ^ 3 = GeneralLinearGroup.scalar (Fin 3) ξ) :
    d 0 ^ 3 = d 1 ^ 3 ∧ d 1 ^ 3 = d 2 ^ 3 := by
  have hmat : (c : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (GeneralLinearGroup.scalar (Fin 3) ξ : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_pow_eq_pow_val, h3]
  rw [hd, Matrix.diagonal_pow, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hmat
  have hfun : (fun i : Fin 3 => d i ^ 3) = fun _ => (ξ : K) :=
    Matrix.diagonal_injective hmat
  exact ⟨(congrFun hfun 0).trans (congrFun hfun 1).symm,
    (congrFun hfun 1).trans (congrFun hfun 2).symm⟩

theorem isMonomial_conj (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K)
    {g b₀ b : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hb₀ : b₀ ∈ B) (hb : b ∈ B)
    (hD : g⁻¹ * b₀ * g = diagTau hτ) :
    ∃ σ : Equiv.Perm (Fin 3),
      IsMonomialFor (g⁻¹ * b * g : Matrix (Fin 3) (Fin 3) K) σ := by
  classical
  have hζZ : ⁅b, b₀⁆ ∈ zPi π 3 (p ^ f) K := hBc b hb b₀ hb₀
  have hζconjZ : g⁻¹ * ⁅b, b₀⁆ * g ∈ zPi π 3 (p ^ f) K :=
    inv_conj_mem_zPi hK hq hτ hτ1 hζZ
  obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hζconjZ
  have hbconj : b * b₀ * b⁻¹ = ⁅b, b₀⁆ * b₀ := by
    rw [commutatorElement_def]
    group
  have hmain : (g⁻¹ * b * g) * diagTau hτ * (g⁻¹ * b * g)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ξ * diagTau hτ := by
    calc (g⁻¹ * b * g) * diagTau hτ * (g⁻¹ * b * g)⁻¹
        = (g⁻¹ * b * g) * (g⁻¹ * b₀ * g) * (g⁻¹ * b * g)⁻¹ := by rw [hD]
      _ = g⁻¹ * (b * b₀ * b⁻¹) * g := by group
      _ = g⁻¹ * (⁅b, b₀⁆ * b₀) * g := by rw [hbconj]
      _ = (g⁻¹ * ⁅b, b₀⁆ * g) * (g⁻¹ * b₀ * g) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ξ * diagTau hτ := by rw [← hξ, hD]
  exact isMonomial_of_conj_diagTau hτ hτ1 hmain

theorem support_pow_three_eq_one {c : GL (Fin 3) K} {σ : Equiv.Perm (Fin 3)}
    (hmono : IsMonomialFor (c : Matrix (Fin 3) (Fin 3) K) σ)
    {ξ : Kˣ} (h3 : c ^ 3 = GeneralLinearGroup.scalar (Fin 3) ξ) : σ ^ 3 = 1 := by
  classical
  apply Equiv.ext
  intro j
  by_contra hne
  obtain ⟨b, hb, hbcol⟩ := hmono.pow 3 j
  have hmat : (c : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (GeneralLinearGroup.scalar (Fin 3) ξ : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_pow_eq_pow_val, h3]
  rw [hmat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mulVec_single] at hbcol
  have hcoord := congrFun hbcol j
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at hcoord
  have hne' : (σ ^ 3) j ≠ j := hne
  rw [Pi.single_eq_of_ne (Ne.symm hne'), mul_zero] at hcoord
  exact ξ.ne_zero hcoord

theorem exists_conj_diagTau' (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9)
    (hno : ∀ b ∈ B, ∀ z ∈ zPi π 3 (p ^ f) K, ∀ g ∈ glPi π 3 (p ^ f) K, ∀ e : Kˣ,
      ((e : K) = τ ∨ (e : K) = τ ^ 2) → g⁻¹ * (b * z) * g ≠ diagE e) :
    ∃ b ∈ B, ∃ g ∈ glPi π 3 (p ^ f) K, g⁻¹ * b * g = diagTau hτ := by
  obtain ⟨b, hb, z, hz, g, hg, hD⟩ :=
    exists_conj_diagTau hK hq hτ hτ1 hBH hZB hB hBc hB9 hno
  refine ⟨b * z, B.mul_mem hb (hZB hz), g, hg, ?_⟩
  simpa only [Subgroup.coe_mul] using hD

private noncomputable def conjDiag {B : Subgroup (GL (Fin 3) K)} (g : GL (Fin 3) K) (b : B) :
    Fin 3 → K :=
  fun i => ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) i i

private theorem conjDiag_ne_zero {B : Subgroup (GL (Fin 3) K)} {g : GL (Fin 3) K}
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (b : B) (i : Fin 3) : conjDiag g b i ≠ 0 :=
  CFSG.StandardType.TypeA.PGLTor.diag_ne_zero_of_eq_diagonal (hdiag b) i

private theorem conjDiag_one {B : Subgroup (GL (Fin 3) K)} {g : GL (Fin 3) K}
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b)) (i : Fin 3) :
    conjDiag g (1 : B) i = 1 := by
  have h1 := hdiag (1 : B)
  have hc1 : (g⁻¹ * ((1 : B) : GL (Fin 3) K) * g : GL (Fin 3) K) = 1 := by simp
  rw [hc1] at h1
  have h := congrFun (congrFun h1 i) i
  simpa using h.symm

private theorem conjDiag_mul {B : Subgroup (GL (Fin 3) K)} {g : GL (Fin 3) K}
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (b b' : B) (i : Fin 3) :
    conjDiag g (b * b') i = conjDiag g b i * conjDiag g b' i := by
  have hc_mul : (g⁻¹ * (((b * b' : B) : GL (Fin 3) K)) * g : GL (Fin 3) K) =
      (g⁻¹ * (b : GL (Fin 3) K) * g) * (g⁻¹ * (b' : GL (Fin 3) K) * g) := by
    rw [Subgroup.coe_mul]
    group
  have hM : ((g⁻¹ * (((b * b' : B) : GL (Fin 3) K)) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => conjDiag g b i * conjDiag g b' i) := by
    rw [hc_mul, Units.val_mul, hdiag b, hdiag b', Matrix.diagonal_mul_diagonal]
  have h1 := hdiag (b * b')
  rw [hM] at h1
  exact (congrFun (Matrix.diagonal_injective h1) i).symm

private noncomputable def conjRatio {B : Subgroup (GL (Fin 3) K)} (g : GL (Fin 3) K)
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0) : B →* Kˣ × Kˣ where
  toFun b :=
    (Units.mk0 (conjDiag g b 0) (hd b 0) *
        (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹,
      Units.mk0 (conjDiag g b 1) (hd b 1) *
        (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹)
  map_one' := by
    apply Prod.ext <;> apply Units.ext <;>
      simp [conjDiag_one hdiag]
  map_mul' b b' := by
    apply Prod.ext <;> apply Units.ext
    · simp only [Prod.fst_mul, Units.val_mul, Units.val_inv_eq_inv_val,
        conjDiag_mul hdiag, Units.val_mk0]
      field_simp [hd b 2, hd b' 2]
    · simp only [Prod.snd_mul, Units.val_mul, Units.val_inv_eq_inv_val,
        conjDiag_mul hdiag, Units.val_mk0]
      field_simp [hd b 2, hd b' 2]

private theorem conjRatio_ker (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    {g : GL (Fin 3) K}
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0) :
    (conjRatio g hdiag hd).ker = (zPi π 3 (p ^ f) K).subgroupOf B := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  let u : B → Fin 3 → Kˣ := fun b i => Units.mk0 (conjDiag g b i) (hd b i)
  ext b
  constructor
  · intro hbker
    rw [MonoidHom.mem_ker] at hbker
    change (u b 0 * (u b 2)⁻¹, u b 1 * (u b 2)⁻¹) = 1 at hbker
    have h0 : u b 0 * (u b 2)⁻¹ = 1 := congrArg Prod.fst hbker
    have h1 : u b 1 * (u b 2)⁻¹ = 1 := congrArg Prod.snd hbker
    have h02 : conjDiag g b 0 = conjDiag g b 2 := by
      have h := congrArg (fun x : Kˣ => x * u b 2) h0
      have h' : u b 0 = u b 2 := by simpa [mul_assoc] using h
      have := congrArg Units.val h'
      simpa [u] using this
    have h12 : conjDiag g b 1 = conjDiag g b 2 := by
      have h := congrArg (fun x : Kˣ => x * u b 2) h1
      have h' : u b 1 = u b 2 := by simpa [mul_assoc] using h
      have := congrArg Units.val h'
      simpa [u] using this
    have hdeq : conjDiag g b = fun _ => conjDiag g b 2 := by
      funext i
      fin_cases i
      · exact h02
      · exact h12
      · rfl
    have hc_scalar : (g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) (u b 2) := by
      apply Units.ext
      rw [hdiag b, hdeq, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      rfl
    have hb_scalar : (b : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) (u b 2) := by
      calc (b : GL (Fin 3) K) = g * (g⁻¹ * (b : GL (Fin 3) K) * g) * g⁻¹ := by group
        _ = g * GeneralLinearGroup.scalar (Fin 3) (u b 2) * g⁻¹ := by rw [hc_scalar]
        _ = GeneralLinearGroup.scalar (Fin 3) (u b 2) := conj_scalar_eq g (u b 2)
    rw [Subgroup.mem_subgroupOf]
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.mpr ⟨hBH b.2, ⟨u b 2, hb_scalar.symm⟩⟩
  · intro hbZ
    rw [Subgroup.mem_subgroupOf] at hbZ
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hbZ
    have hc_scalar : (g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) ξ := by
      rw [← hξ]
      simpa using conj_scalar_eq g⁻¹ ξ
    have hdeq : conjDiag g b = fun _ => (ξ : K) := by
      have h : ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => (ξ : K)) := by
        rw [hc_scalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      have h2 := hdiag b
      rw [h] at h2
      exact (Matrix.diagonal_injective h2).symm
    have h0 : u b 0 * (u b 2)⁻¹ = 1 := by
      apply Units.ext
      simp [u, hdeq]
    have h1 : u b 1 * (u b 2)⁻¹ = 1 := by
      apply Units.ext
      simp [u, hdeq]
    rw [MonoidHom.mem_ker]
    change (u b 0 * (u b 2)⁻¹, u b 1 * (u b 2)⁻¹) = 1
    rw [h0, h1]
    rfl

private theorem conjRatio_card_range (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    {g : GL (Fin 3) K}
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9) :
    Nat.card (conjRatio g hdiag hd).range = 9 := by
  haveI : Finite K := hK.finite
  have hker := conjRatio_ker hK hq hτ hτ1 hBH hZB hdiag hd
  have hker_card : Nat.card (conjRatio g hdiag hd).ker = Nat.card (zPi π 3 (p ^ f) K) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv
  have hBcard : Nat.card B = 9 * Nat.card (zPi π 3 (p ^ f) K) := by
    have h := Subgroup.relIndex_mul_card (H := zPi π 3 (p ^ f) K) (K := B)
    rw [inf_of_le_left hZB, hB9] at h
    exact h.symm
  have hprod := Subgroup.card_ker_mul_card_range (conjRatio g hdiag hd)
  rw [hker_card] at hprod
  have hZpos : 0 < Nat.card (zPi π 3 (p ^ f) K) := Nat.card_pos
  have h1 : Nat.card (zPi π 3 (p ^ f) K) * Nat.card (conjRatio g hdiag hd).range =
      Nat.card (zPi π 3 (p ^ f) K) * 9 := by
    rw [hprod, hBcard]
    ring
  exact Nat.mul_left_cancel hZpos h1

private theorem conjRatio_range_le (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0) :
    (conjRatio g hdiag hd).range ≤ (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) := by
  rintro x ⟨b, rfl⟩
  obtain ⟨ξ, hξ⟩ := conj_cube_eq_scalar hK hq hτ hτ1 hB hg b.2
  have hcube := diag_pow_three_eq_of_pow_three_scalar (hdiag b) hξ
  change (Units.mk0 (conjDiag g b 0) (hd b 0) *
      (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹,
    Units.mk0 (conjDiag g b 1) (hd b 1) *
      (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹) ∈
    (rootsOfUnity 3 K).prod (rootsOfUnity 3 K)
  rw [Subgroup.mem_prod]
  constructor
  · rw [mem_rootsOfUnity]
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [show (Units.mk0 (conjDiag g b 0) (hd b 0) : K) = conjDiag g b 0 from rfl,
      show (Units.mk0 (conjDiag g b 2) (hd b 2) : K) = conjDiag g b 2 from rfl]
    rw [mul_pow, inv_pow, hcube.1.trans hcube.2,
      mul_inv_cancel₀ (pow_ne_zero 3 (hd b 2))]
    rfl
  · rw [mem_rootsOfUnity]
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [show (Units.mk0 (conjDiag g b 1) (hd b 1) : K) = conjDiag g b 1 from rfl,
      show (Units.mk0 (conjDiag g b 2) (hd b 2) : K) = conjDiag g b 2 from rfl]
    rw [mul_pow, inv_pow, hcube.2, mul_inv_cancel₀ (pow_ne_zero 3 (hd b 2))]
    rfl

private theorem conjRatio_range_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0) :
    (conjRatio g hdiag hd).range = (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) := by
  haveI : Finite K := hK.finite
  have hle := conjRatio_range_le hK hq hτ hτ1 hB hg hdiag hd
  have hcard := conjRatio_card_range hK hq hτ hτ1 hBH hZB hdiag hd hB9
  have hMle : Nat.card ((rootsOfUnity 3 K).prod (rootsOfUnity 3 K)) ≤ 9 := by
    have hcardM : Nat.card ((rootsOfUnity 3 K).prod (rootsOfUnity 3 K)) =
        Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) :=
      (Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv).trans (Nat.card_prod _ _)
    rw [hcardM]
    calc Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K)
        ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 3) (card_rootsOfUnity K 3)
      _ = 9 := by norm_num
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard]
  exact hMle

private theorem exists_conjRatio_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0) :
    ∃ (b : B) (e : Kˣ), (e : K) = τ ∧ conjRatio g hdiag hd b = (e, 1) := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  let eτ : Kˣ := Units.mk0 τ hτ0
  have heτ3 : eτ ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    simpa [eτ] using hτ
  have hmem : (eτ, 1) ∈ (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) := by
    rw [Subgroup.mem_prod]
    exact ⟨heτ3, Subgroup.one_mem _⟩
  have hrange := conjRatio_range_eq hK hq hτ hτ1 hBH hZB hB hB9 hg hdiag hd
  have hmem' : (eτ, 1) ∈ (conjRatio g hdiag hd).range := by
    rw [hrange]
    exact hmem
  rw [MonoidHom.mem_range] at hmem'
  obtain ⟨b, hb⟩ := hmem'
  exact ⟨b, eτ, rfl, hb⟩

private theorem exists_scalar_mul_diagE (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b))
    (hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0) :
    ∃ (b : B) (mu : Kˣ) (e : Kˣ), (e : K) = τ ∧
      (g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) mu * diagE e := by
  obtain ⟨b, e, he, hb⟩ :=
    exists_conjRatio_eq hK hq hτ hτ1 hBH hZB hB hB9 hg hdiag hd
  change (Units.mk0 (conjDiag g b 0) (hd b 0) *
      (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹,
    Units.mk0 (conjDiag g b 1) (hd b 1) *
      (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹) = (e, 1) at hb
  have h0 : Units.mk0 (conjDiag g b 0) (hd b 0) *
      (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹ = e := congrArg Prod.fst hb
  have h1 : Units.mk0 (conjDiag g b 1) (hd b 1) *
      (Units.mk0 (conjDiag g b 2) (hd b 2))⁻¹ = 1 := congrArg Prod.snd hb
  have h0K : conjDiag g b 0 = (e : K) * conjDiag g b 2 := by
    have h := congrArg Units.val h0
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at h
    field_simp [hd b 2] at h
    simpa [mul_comm] using h
  have h1K : conjDiag g b 1 = conjDiag g b 2 := by
    have h := congrArg Units.val h1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one,
      Units.val_mk0] at h
    field_simp [hd b 2] at h
    simpa using h
  refine ⟨b, Units.mk0 (conjDiag g b 2) (hd b 2), e, he, ?_⟩
  apply Units.ext
  rw [hdiag b, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    coe_diagE, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [h0K, h1K, Units.val_mk0, mul_comm]

theorem diagonal_case_false (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9)
    (hno : ∀ b ∈ B, ∀ z ∈ zPi π 3 (p ^ f) K, ∀ g ∈ glPi π 3 (p ^ f) K, ∀ e : Kˣ,
      ((e : K) = τ ∨ (e : K) = τ ^ 2) → g⁻¹ * (b * z) * g ≠ diagE e)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hdiag : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i i)) : False := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hdiag' : ∀ b : B, ((g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (conjDiag g b) := hdiag
  have hd : ∀ (b : B) (i : Fin 3), conjDiag g b i ≠ 0 :=
    fun b i => conjDiag_ne_zero hdiag' b i
  obtain ⟨b, mu, e, he, hc_eq⟩ :=
    exists_scalar_mul_diagE hK hq hτ hτ1 hBH hZB hB hB9 hg hdiag' hd
  have he3 : e ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, he]
    exact hτ
  have heq : e ∈ rootsOfUnity (qSubPi π (p ^ f)) K := cube_root_mem_qSubPi hq he3
  have hcH : (g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K :=
    mul_mem (mul_mem (inv_mem hg) (hBH b.2)) hg
  have hE : diagE e ∈ glPi π 3 (p ^ f) K := by
    rw [diagE]
    exact diagUnits_mem_glPi hK heq (Subgroup.one_mem _) (Subgroup.one_mem _)
  have hscalarH : GeneralLinearGroup.scalar (Fin 3) mu ∈ glPi π 3 (p ^ f) K := by
    have hEq : GeneralLinearGroup.scalar (Fin 3) mu =
        (g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) * (diagE e)⁻¹ := by
      rw [hc_eq]
      group
    rw [hEq]
    exact mul_mem hcH (inv_mem hE)
  have hzZ : GeneralLinearGroup.scalar (Fin 3) mu⁻¹ ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.mpr ⟨inv_mem hscalarH, ⟨mu⁻¹, rfl⟩⟩
  have hcz : (g⁻¹ * (b : GL (Fin 3) K) * g : GL (Fin 3) K) *
      GeneralLinearGroup.scalar (Fin 3) mu⁻¹ = diagE e := by
    rw [hc_eq, GeneralLinearGroup.scalar_commute, mul_assoc,
      show GeneralLinearGroup.scalar (Fin 3) mu *
        GeneralLinearGroup.scalar (Fin 3) mu⁻¹ = 1 by
      rw [← map_mul, mul_inv_cancel, map_one],
      mul_one]
  have hz_central : g⁻¹ * GeneralLinearGroup.scalar (Fin 3) mu⁻¹ * g =
      GeneralLinearGroup.scalar (Fin 3) mu⁻¹ := by
    simpa using conj_scalar_eq g⁻¹ mu⁻¹
  have hEq : g⁻¹ * ((b : GL (Fin 3) K) *
      GeneralLinearGroup.scalar (Fin 3) mu⁻¹) * g = diagE e := by
    calc g⁻¹ * ((b : GL (Fin 3) K) *
          GeneralLinearGroup.scalar (Fin 3) mu⁻¹) * g
        = (g⁻¹ * (b : GL (Fin 3) K) * g) *
            (g⁻¹ * GeneralLinearGroup.scalar (Fin 3) mu⁻¹ * g) := by group
      _ = (g⁻¹ * (b : GL (Fin 3) K) * g) *
            GeneralLinearGroup.scalar (Fin 3) mu⁻¹ := by rw [hz_central]
      _ = diagE e := hcz
  exact hno (b : GL (Fin 3) K) b.2 (GeneralLinearGroup.scalar (Fin 3) mu⁻¹) hzZ g hg e
    (Or.inl he) hEq


theorem exists_threeCycle_support (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {B : Subgroup (GL (Fin 3) K)} (hBH : B ≤ glPi π 3 (p ^ f) K)
    (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9)
    (hno : ∀ b ∈ B, ∀ z ∈ zPi π 3 (p ^ f) K, ∀ g ∈ glPi π 3 (p ^ f) K, ∀ e : Kˣ,
      ((e : K) = τ ∨ (e : K) = τ ^ 2) → g⁻¹ * (b * z) * g ≠ diagE e) :
    ∃ (g b : GL (Fin 3) K) (σ : Equiv.Perm (Fin 3)),
      g ∈ glPi π 3 (p ^ f) K ∧ b ∈ B ∧
      IsMonomialFor ((g⁻¹ * b * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ ∧
      σ ^ 3 = 1 ∧ σ ≠ 1 ∧
      (∀ b' ∈ B, ∃ σ' : Equiv.Perm (Fin 3), IsMonomialFor
        ((g⁻¹ * b' * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ') := by
  classical
  haveI : Finite K := hK.finite
  obtain ⟨b₀, hb₀, g, hg, hD⟩ :=
    exists_conj_diagTau' hK hq hτ hτ1 hBH hZB hB hBc hB9 hno
  have hmono : ∀ b ∈ B, ∃ σ : Equiv.Perm (Fin 3),
      IsMonomialFor ((g⁻¹ * b * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ :=
    fun b hb => isMonomial_conj hK hq hτ hτ1 hBc hg hb₀ hb hD
  have hex : ∃ b ∈ B, ¬ ∃ d : Fin 3 → K,
      ((g⁻¹ * b * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    by_contra hall
    push Not at hall
    refine diagonal_case_false hK hq hτ hτ1 hBH hZB hB hB9 hno hg (fun b => ?_)
    obtain ⟨d, hd⟩ := hall (b : GL (Fin 3) K) b.2
    exact eq_diagonal_self_of_eq_diagonal hd
  obtain ⟨b, hb, hnd⟩ := hex
  obtain ⟨σ, hσ⟩ := hmono b hb
  have hσ3 : σ ^ 3 = 1 := by
    obtain ⟨ξ, hξ⟩ := conj_cube_eq_scalar hK hq hτ hτ1 hB hg hb
    exact support_pow_three_eq_one hσ hξ
  have hσne : σ ≠ 1 := by
    intro hσ1
    choose a ha using hσ
    exact hnd ⟨a, eq_diagonal_of_col_single (fun j => (ha j).2) hσ1⟩
  exact ⟨g, b, σ, hg, hb, hσ, hσ3, hσne, hmono⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
