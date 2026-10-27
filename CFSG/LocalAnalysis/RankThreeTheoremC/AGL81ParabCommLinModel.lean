module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinModelFlag
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped commutatorElement

section Block

variable {K : Type} [Field K] {n : ℕ} {I : Set ℕ}

theorem map_one_add_single {m : ℕ} (σ : K →+* K) (i j : Fin m) (t : K) :
    (1 + Matrix.single i j t : Matrix (Fin m) (Fin m) K).map σ =
      1 + Matrix.single i j (σ t) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem block_relation {A : GL (Fin n) K} {σ : K ≃+* K} {α : MulAut (projectiveSL n K)}
    (hα : α = conjAut n K A * fieldAut n K σ)
    (hfix : ∀ a : Fin n, 2 ≤ linBlockLen n I a → ∀ x : flagStabilizer n K I,
      (∀ b : Fin n, b ≠ a → linLeviHom K n I x b = 1) →
      α (proj n K x) * (proj n K x)⁻¹ ∈ projUni K n I)
    (hA : BlockPat I (A : Matrix (Fin n) (Fin n) K)) (a : Fin n) (ha2 : 2 ≤ linBlockLen n I a)
    (i j : Fin (linBlockLen n I a)) (hij : i ≠ j) (t : K) :
    ∃ c : K, blkAt a (linBlockLen n I a) (linBlockLen_le a) (A : Matrix (Fin n) (Fin n) K) *
        (1 + Matrix.single i j (σ t)) =
      c • ((1 + Matrix.single i j t) *
        blkAt a (linBlockLen n I a) (linBlockLen_le a) (A : Matrix (Fin n) (Fin n) K)) := by
  have hle := linBlockLen_le (n := n) (I := I) a
  have hstart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I := by
    by_contra hns
    rw [linBlockLen_of_not_start hns] at ha2
    omega
  obtain ⟨-, -, hend, hno⟩ := linBlockLen_spec (I := I) hstart
  have hxQ := transvection_blk_mem_flagStabilizer (K := K) hle hno hij t
  set x := SpecialLinearGroup.transvection (blkIdxN_ne (h := hle) hij) t with hx
  have hlevi : ∀ b : Fin n, b ≠ a → linLeviHom K n I ⟨x, hxQ⟩ b = 1 := by
    intro b hb
    apply Units.ext
    rw [coe_linLeviHom_apply, Units.val_one]
    exact blkAt_transvection_other hle (linBlockLen_le b)
      (fun r h1 h2 h3 h4 => linBlock_disjoint (Ne.symm hb) h1 h2 h3 h4) hij t
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hfix a ha2 ⟨x, hxQ⟩ hlevi)
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  have hyeq' : proj n K (u : SpecialLinearGroup (Fin n) K) =
      α (proj n K x) * (proj n K x)⁻¹ := hyeq
  have hαx : α (proj n K x) =
      proj n K (slConjugation n K A (SpecialLinearGroup.map σ.toRingHom x)) := by
    rw [hα, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  rw [hαx, ← map_inv, ← map_mul] at hyeq'
  set S := slConjugation n K A (SpecialLinearGroup.map σ.toRingHom x) with hSdef
  have hsc : (u : SpecialLinearGroup (Fin n) K)⁻¹ * (S * x⁻¹) ∈ scalars n K :=
    proj_eq_proj_iff.mp hyeq'
  generalize hz : (u : SpecialLinearGroup (Fin n) K)⁻¹ * (S * x⁻¹) = z at hsc
  have hS : S = (u : SpecialLinearGroup (Fin n) K) * z * x := by rw [← hz]; group
  obtain ⟨c, -, hcm⟩ := mem_scalars.mp hsc
  have hSm : (S : Matrix (Fin n) (Fin n) K) = ((u : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * (z : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) := by
    rw [hS, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hSval : (S : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ.toRingHom *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hSdef, slConjugation_matrix, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hsc1 : (Matrix.scalar (Fin n) (c : K) : Matrix (Fin n) (Fin n) K) = (c : K) • 1 := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h5 : (A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ.toRingHom =
      (c : K) • (((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) := by
    have h6 : (A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ.toRingHom *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((c : K) • 1) *
          (x : Matrix (Fin n) (Fin n) K) := by
      rw [← hSval, hSm, hcm, hsc1]
    calc (A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ.toRingHom
        = (A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ.toRingHom *
          (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) := by
          rw [Units.inv_mul, mul_one]
      _ = ((A : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K).map σ.toRingHom *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (A : Matrix (Fin n) (Fin n) K) := by
          rw [mul_assoc _ _ (A : Matrix (Fin n) (Fin n) K)]
      _ = (((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((c : K) • 1) *
          (x : Matrix (Fin n) (Fin n) K)) * (A : Matrix (Fin n) (Fin n) K) := by rw [h6]
      _ = (c : K) • (((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (x : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, smul_mul_assoc]
  have hU : BlockPat I ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    blockPat_of_mem_flagStabilizer u.2
  have hX : BlockPat I (x : Matrix (Fin n) (Fin n) K) := blockPat_of_mem_flagStabilizer hxQ
  have hXσ : BlockPat I ((x : Matrix (Fin n) (Fin n) K).map σ.toRingHom) := hX.map _
  have hUblk : blkAt a (linBlockLen n I a) hle
      ((u : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h1 : linLeviHom K n I u a = 1 := congrFun (MonoidHom.mem_ker.mp hu) a
    have h2 := coe_linLeviHom_apply u a
    rw [h1, Units.val_one] at h2
    exact h2.symm
  have hXblk : blkAt a (linBlockLen n I a) hle (x : Matrix (Fin n) (Fin n) K) =
      1 + Matrix.single i j t := by
    rw [hx, blkAt_transvection_self hle hij t, SpecialLinearGroup.transvection_coe]
  have hXσblk : blkAt a (linBlockLen n I a) hle
      ((x : Matrix (Fin n) (Fin n) K).map σ.toRingHom) = 1 + Matrix.single i j (σ t) := by
    rw [blkAt_map, hXblk, map_one_add_single]
    rfl
  refine ⟨(c : K), ?_⟩
  have h7 := congrArg (blkAt a (linBlockLen n I a) hle) h5
  rw [blkAt_mul_of_blockPat hle hstart hend hA hXσ, blkAt_smul,
    blkAt_mul_of_blockPat hle hstart hend (hU.mul hX) hA,
    blkAt_mul_of_blockPat hle hstart hend hU hX, hUblk, hXblk, hXσblk, one_mul] at h7
  exact h7

end Block

section Struct

variable {K : Type} [Field K] {n : ℕ} {I : Set ℕ}

theorem exists_smul_one_of_le_one {m : ℕ} (hm : m ≤ 1) (B : Matrix (Fin m) (Fin m) K) :
    ∃ r : K, B = r • 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
  · exact ⟨0, Subsingleton.elim _ _⟩
  · refine ⟨B 0 0, ?_⟩
    ext k l
    obtain rfl : k = 0 := Subsingleton.elim _ _
    obtain rfl : l = 0 := Subsingleton.elim _ _
    simp

theorem exists_conj_of_normFix [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hblk : ∃ a : Fin n, 2 ≤ linBlockLen n I a)
    {α : MulAut (projectiveSL n K)} (hodd : Odd (orderOf α)) (hNF : NormFix I α) :
    ∃ A : GL (Fin n) K, α = conjAut n K A ∧ BlockPat I (A : Matrix (Fin n) (Fin n) K) ∧
      BlockPat I ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      ScalarBlocks I (A : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨A, σ, hα⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn hodd
    (pow_orderOf_eq_one α)
  obtain ⟨hNF1, hNF2⟩ := hNF
  rw [hα] at hNF1
  obtain ⟨hAi, hA⟩ := blockPat_of_conj_mem hI A (conj_mem_of_map_projFlag hNF1)
  have hblock : ∀ a : Fin n, 2 ≤ linBlockLen n I a →
      (∀ t : K, σ.toRingHom t = t) ∧ ∃ r : K, blkAt a (linBlockLen n I a) (linBlockLen_le a)
        (A : Matrix (Fin n) (Fin n) K) = r • 1 := by
    intro a ha2
    have hle := linBlockLen_le (n := n) (I := I) a
    have hstart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I := by
      by_contra hns
      rw [linBlockLen_of_not_start hns] at ha2
      omega
    obtain ⟨-, -, hend, -⟩ := linBlockLen_spec (I := I) hstart
    have hBB' : blkAt a (linBlockLen n I a) hle
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          blkAt a (linBlockLen n I a) hle (A : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← blkAt_mul_of_blockPat hle hstart hend hAi hA, Units.inv_mul, blkAt_one]
    obtain ⟨hσ, r, -, hr⟩ := eq_scalar_of_transvection_rel ha2 σ.toRingHom hBB'
      (fun i j hij t => block_relation hα hNF2 hA a ha2 i j hij t)
    exact ⟨hσ, r, hr⟩
  obtain ⟨a₀, ha₀⟩ := hblk
  have hσ1 : σ = 1 := RingEquiv.ext fun t => (hblock a₀ ha₀).1 t
  refine ⟨A, by rw [hα, hσ1, map_one, mul_one], hA, hAi, fun a => ?_⟩
  by_cases h : 2 ≤ linBlockLen n I a
  · exact (hblock a h).2
  · exact exists_smul_one_of_le_one (by omega) _

end Struct

section Comm

variable {K : Type} [Field K] {n : ℕ} {I : Set ℕ}

theorem eq_inv_smul_one_of_mul {m : ℕ} (hm : 1 ≤ m) {r : K} {B' : Matrix (Fin m) (Fin m) K}
    (h : B' * (r • 1) = 1) : r ≠ 0 ∧ B' = r⁻¹ • 1 := by
  have h1 : r • B' = 1 := by rw [Matrix.mul_smul, mul_one] at h; exact h
  have hr : r ≠ 0 := by
    rintro rfl
    have h2 := congrFun (congrFun h1 ⟨0, hm⟩) ⟨0, hm⟩
    simp at h2
  refine ⟨hr, ?_⟩
  calc B' = r⁻¹ • (r • B') := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
    _ = r⁻¹ • 1 := by rw [h1]

theorem matrix_eq_of_eq_zero {m : ℕ} (hm : m = 0) (M N : Matrix (Fin m) (Fin m) K) : M = N := by
  subst hm
  exact Subsingleton.elim _ _

theorem blkAt_commutator {A₁ A₂ : GL (Fin n) K}
    (h₁ : BlockPat I (A₁ : Matrix (Fin n) (Fin n) K))
    (h₁' : BlockPat I ((A₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h₂ : BlockPat I (A₂ : Matrix (Fin n) (Fin n) K))
    (h₂' : BlockPat I ((A₂⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (b₁ : ScalarBlocks I (A₁ : Matrix (Fin n) (Fin n) K))
    (b₂ : ScalarBlocks I (A₂ : Matrix (Fin n) (Fin n) K)) (a : Fin n) :
    blkAt a (linBlockLen n I a) (linBlockLen_le a)
      ((⁅A₁, A₂⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  by_cases hstart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I
  · obtain ⟨-, hm1, hend, -⟩ := linBlockLen_spec (I := I) hstart
    have hle := linBlockLen_le (n := n) (I := I) a
    obtain ⟨r₁, hr₁⟩ := b₁ a
    obtain ⟨r₂, hr₂⟩ := b₂ a
    have hi₁ : blkAt a (linBlockLen n I a) hle ((A₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (r₁ • 1) = 1 := by
      rw [← hr₁, ← blkAt_mul_of_blockPat hle hstart hend h₁' h₁, Units.inv_mul, blkAt_one]
    have hi₂ : blkAt a (linBlockLen n I a) hle ((A₂⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (r₂ • 1) = 1 := by
      rw [← hr₂, ← blkAt_mul_of_blockPat hle hstart hend h₂' h₂, Units.inv_mul, blkAt_one]
    obtain ⟨hr₁0, hi₁'⟩ := eq_inv_smul_one_of_mul hm1 hi₁
    obtain ⟨hr₂0, hi₂'⟩ := eq_inv_smul_one_of_mul hm1 hi₂
    rw [commutatorElement_def]
    simp only [Units.val_mul]
    rw [blkAt_mul_of_blockPat hle hstart hend ((h₁.mul h₂).mul h₁') h₂',
      blkAt_mul_of_blockPat hle hstart hend (h₁.mul h₂) h₁',
      blkAt_mul_of_blockPat hle hstart hend h₁ h₂, hr₁, hr₂, hi₁', hi₂']
    have h3 : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ = 1 := by field_simp
    calc ((r₁ • 1 : Matrix (Fin (linBlockLen n I a)) (Fin (linBlockLen n I a)) K) * (r₂ • 1) *
          (r₁⁻¹ • 1) * (r₂⁻¹ • 1))
        = (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) • (1 : Matrix (Fin (linBlockLen n I a))
            (Fin (linBlockLen n I a)) K) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one]
          congr 1
          ring
      _ = 1 := by rw [h3, one_smul]
  · exact matrix_eq_of_eq_zero (linBlockLen_of_not_start hstart) _ _

theorem exists_pow_two_eq_one_commutator [Finite K] [CharP K 2] (hn : 1 ≤ n) {A₁ A₂ : GL (Fin n) K}
    (h₁ : BlockPat I (A₁ : Matrix (Fin n) (Fin n) K))
    (h₁' : BlockPat I ((A₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h₂ : BlockPat I (A₂ : Matrix (Fin n) (Fin n) K))
    (h₂' : BlockPat I ((A₂⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (b₁ : ScalarBlocks I (A₁ : Matrix (Fin n) (Fin n) K))
    (b₂ : ScalarBlocks I (A₂ : Matrix (Fin n) (Fin n) K)) :
    ∃ k : ℕ, (conjAut n K ⁅A₁, A₂⁆) ^ 2 ^ k = 1 := by
  have hCpat : BlockPat I ((⁅A₁, A₂⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [commutatorElement_def]
    simp only [Units.val_mul]
    exact ((h₁.mul h₂).mul h₁').mul h₂'
  have hdet : ((⁅A₁, A₂⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _), Units.val_one]
  let g : SpecialLinearGroup (Fin n) K := ⟨((⁅A₁, A₂⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
    hdet⟩
  have hgQ : g ∈ flagStabilizer n K I := mem_flagStabilizer_of_blockPat hCpat
  have hker : (⟨g, hgQ⟩ : flagStabilizer n K I) ∈ (linLeviHom K n I).ker := by
    rw [MonoidHom.mem_ker]
    funext a
    apply Units.ext
    rw [coe_linLeviHom_apply, Pi.one_apply, Units.val_one]
    exact blkAt_commutator h₁ h₁' h₂ h₂' b₁ b₂ a
  obtain ⟨k, hk⟩ := isPGroup_ker_linLeviHom (K := K) (n := n) (I := I) hn ⟨_, hker⟩
  refine ⟨k, ?_⟩
  have hgpow : g ^ 2 ^ k = 1 := by
    have h1 := congrArg (fun y : (linLeviHom K n I).ker =>
      ((y : flagStabilizer n K I) : SpecialLinearGroup (Fin n) K)) hk
    simpa using h1
  have hCg : (SpecialLinearGroup.toGL g : GL (Fin n) K) = ⁅A₁, A₂⁆ := Units.ext rfl
  rw [← hCg, conjAut_toGL, ← map_pow, ← map_pow, hgpow, map_one, map_one]

end Comm

theorem linModelComm_holds : LinModelComm := by
  intro K _ _ _ n I hn hI hblk α₁ α₂ ho₁ ho₂ hoc hN₁ hN₂
  obtain ⟨A₁, hα₁, h₁, h₁', b₁⟩ := exists_conj_of_normFix hn hI hblk ho₁ hN₁
  obtain ⟨A₂, hα₂, h₂, h₂', b₂⟩ := exists_conj_of_normFix hn hI hblk ho₂ hN₂
  obtain ⟨k, hk⟩ := exists_pow_two_eq_one_commutator (by omega) h₁ h₁' h₂ h₂' b₁ b₂
  have hcomm : ⁅α₁, α₂⁆ = conjAut n K ⁅A₁, A₂⁆ := by rw [hα₁, hα₂, map_commutatorElement]
  have hdvd : orderOf ⁅α₁, α₂⁆ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [hcomm]; exact hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hoc
    exact (Nat.not_even_iff_odd.mpr hoc) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
