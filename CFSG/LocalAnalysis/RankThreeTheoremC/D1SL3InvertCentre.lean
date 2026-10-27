module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockCenterFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace SL3InvertCentreAux

section Block

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

@[expose] def blockMatrix (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

@[expose] def lowerBlock (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => g i.succ j.succ

theorem det_blockMatrix (B : Matrix (Fin 2) (Fin 2) K) : (blockMatrix B).det = B.det := by
  simp [blockMatrix, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def blockEmb : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun B := ⟨blockMatrix B, by rw [det_blockMatrix, B.2]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMatrix]
  map_mul' B C := by
    refine Subtype.ext ?_
    change blockMatrix ((B * C : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blockMatrix (B : Matrix (Fin 2) (Fin 2) K) * blockMatrix (C : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_blockEmb (B : SpecialLinearGroup (Fin 2) K) :
    (blockEmb B : Matrix (Fin 3) (Fin 3) K) = blockMatrix B :=
  rfl

theorem lowerBlock_blockMatrix (B : Matrix (Fin 2) (Fin 2) K) :
    lowerBlock (blockMatrix B) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerBlock, blockMatrix]

variable (K) in
@[expose] def pointFixer : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1}
  one_mem' := by
    change ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
      Pi.single 0 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  mul_mem' := fun {g h} hg hh => by
    change (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 at hg
    change (h : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 at hh
    change ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
      Pi.single 0 1
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := fun {g} hg => by
    change (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 at hg
    change ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 =
      Pi.single 0 1
    calc ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1
        = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1) := by rw [hg]
      _ = Pi.single 0 1 := by rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]

theorem mem_pointFixer_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ pointFixer K ↔ (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  change (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = Pi.single 0 1 ↔ _
  constructor
  · intro h
    exact ⟨by simpa [Matrix.mulVec_single_one] using congrFun h 0,
      by simpa [Matrix.mulVec_single_one] using congrFun h 1,
      by simpa [Matrix.mulVec_single_one] using congrFun h 2⟩
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i <;> simp [h0, h1, h2]

theorem blockEmb_mem_pointFixer (B : SpecialLinearGroup (Fin 2) K) :
    blockEmb B ∈ pointFixer K := by
  rw [mem_pointFixer_iff]
  simp [coe_blockEmb, blockMatrix]

theorem lowerBlock_mul {g h : Matrix (Fin 3) (Fin 3) K} (h10 : g 1 0 = 0) (h20 : g 2 0 = 0) :
    lowerBlock (g * h) = lowerBlock g * lowerBlock h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerBlock, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]

theorem det_lowerBlock {g : Matrix (Fin 3) (Fin 3) K} (h00 : g 0 0 = 1) (h10 : g 1 0 = 0)
    (h20 : g 2 0 = 0) : (lowerBlock g).det = g.det := by
  simp [lowerBlock, Matrix.det_fin_three, Matrix.det_fin_two, h00, h10, h20]

@[expose] def blockProj : pointFixer K →* SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨lowerBlock ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), by
    obtain ⟨h00, h10, h20⟩ := mem_pointFixer_iff.mp g.2
    rw [det_lowerBlock h00 h10 h20, (g : SpecialLinearGroup (Fin 3) K).2]⟩
  map_one' := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerBlock]
  map_mul' g h := by
    refine Subtype.ext ?_
    obtain ⟨-, h10, h20⟩ := mem_pointFixer_iff.mp g.2
    change lowerBlock (((g * h : pointFixer K) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = lowerBlock ((g : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * lowerBlock ((h : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact lowerBlock_mul h10 h20

theorem blockProj_blockEmb (B : SpecialLinearGroup (Fin 2) K) :
    blockProj ⟨blockEmb B, blockEmb_mem_pointFixer B⟩ = B :=
  Subtype.ext (lowerBlock_blockMatrix (B : Matrix (Fin 2) (Fin 2) K))

theorem mem_stabilizer_one_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ stabilizer (flagSpace 3 K 1) ↔
      (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  constructor
  · intro hg
    exact ⟨CFSG.AGLEmbedding.LinearThreeKit.apply_zero_eq_zero_of_mem_stabilizer_one hg
      (by decide), CFSG.AGLEmbedding.LinearThreeKit.apply_zero_eq_zero_of_mem_stabilizer_one hg
      (by decide)⟩
  · rintro ⟨h1, h2⟩
    refine mem_stabilizer_of_map_le ?_
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    rw [mem_flagSpace] at hv ⊢
    intro j hj
    have hv1 := hv 1 le_rfl
    have hv2 := hv 2 (by decide)
    rw [mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    fin_cases j
    · simp at hj
    · simp [h1, hv1, hv2]
    · simp [h2, hv1, hv2]

theorem mem_stabilizer_two_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ stabilizer (flagSpace 3 K 2) ↔
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  constructor
  · intro hg
    exact ⟨CFSG.AGLEmbedding.LinearThreeKit.apply_two_eq_zero_of_mem_stabilizer_two hg
      (by decide), CFSG.AGLEmbedding.LinearThreeKit.apply_two_eq_zero_of_mem_stabilizer_two hg
      (by decide)⟩
  · rintro ⟨h0, h1⟩
    refine mem_stabilizer_of_map_le ?_
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    rw [CFSG.AGLEmbedding.LinearThreeKit.mem_flagSpace_two_iff] at hv ⊢
    rw [mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp [h0, h1, hv]

theorem pointFixer_le_stabilizer : pointFixer K ≤ stabilizer (flagSpace 3 K 1) := fun _ hg =>
  mem_stabilizer_one_iff.mpr (mem_pointFixer_iff.mp hg).2

end Block

section Simple

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

theorem eq_one_of_sq_eq_one [CharP K 2] {ω : K} (h : ω ^ 2 = 1) : ω = 1 := by
  have h1 : (ω + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, one_pow]
    exact CharTwo.add_self_eq_zero 1
  have h2 : ω + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  rw [← CharTwo.neg_eq 1]
  exact eq_neg_of_add_eq_zero_left h2

theorem center_sl2_eq_bot [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := eq_one_of_sq_eq_one (by simpa using hr)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [← hAr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem diag2_pow_three {ω : K} (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) :
    Matrix.SpecialLinearGroup.diag2 ω hω0 ^ 3 = 1 := by
  refine Subtype.ext ?_
  have hi : (ω⁻¹) ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.diag2_coe', Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← pow_three', hω3, hi]

theorem lowerBlock_eq_one_of_normal [CharP K 2] {ω : K} (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) (hNP : N ≤ pointFixer K)
    (hcop : Nat.Coprime 3 (Nat.card N))
    (hnorm : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, ∀ n ∈ N,
      blockEmb B * n * (blockEmb B)⁻¹ ∈ N)
    {n : Matrix.SpecialLinearGroup (Fin 3) K} (hn : n ∈ N) :
    lowerBlock (n : Matrix (Fin 3) (Fin 3) K) = 1 := by
  classical
  set N₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (N.subgroupOf (pointFixer K)).map blockProj with hN₂
  have hnormal : N₂.Normal := by
    refine ⟨fun x hx B => ?_⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hqN : (q : Matrix.SpecialLinearGroup (Fin 3) K) ∈ N := hq
    have hB := blockEmb_mem_pointFixer B
    refine Subgroup.mem_map.mpr ⟨⟨blockEmb B * q * (blockEmb B)⁻¹,
      mul_mem (mul_mem hB q.2) (inv_mem hB)⟩, hnorm B _ hqN, ?_⟩
    have : (⟨blockEmb B * q * (blockEmb B)⁻¹, mul_mem (mul_mem hB q.2) (inv_mem hB)⟩ :
        pointFixer K) = ⟨blockEmb B, hB⟩ * q * ⟨blockEmb B, hB⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, blockProj_blockEmb]
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
      ⟨ω, hω0, fun h => hω1 (eq_one_of_sq_eq_one h)⟩
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) with hπ
  have : (N₂.map π).Normal := hnormal.map π (QuotientGroup.mk'_surjective _)
  have hker : ∀ x y : Matrix.SpecialLinearGroup (Fin 2) K, π x = π y → x = y := by
    intro x y hxy
    have : x⁻¹ * y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      QuotientGroup.eq.mp hxy
    rw [center_sl2_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this
  rcases Subgroup.Normal.eq_bot_or_eq_top (N₂.map π) with h | h
  · have hx : blockProj ⟨n, hNP hn⟩ ∈ N₂ := Subgroup.mem_map.mpr ⟨⟨n, hNP hn⟩, hn, rfl⟩
    have h1 : π (blockProj ⟨n, hNP hn⟩) = π 1 := by
      have : π (blockProj ⟨n, hNP hn⟩) ∈ N₂.map π := Subgroup.mem_map_of_mem π hx
      rw [h, Subgroup.mem_bot] at this
      rw [this, map_one]
    have := hker _ _ h1
    exact congrArg Subtype.val this
  · exfalso
    set z : Matrix.SpecialLinearGroup (Fin 2) K := Matrix.SpecialLinearGroup.diag2 ω hω0 with hz
    have hzmem : π z ∈ N₂.map π := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨x, hxN, hxz⟩ := Subgroup.mem_map.mp hzmem
    have hxz' : x = z := hker _ _ hxz
    rw [hxz'] at hxN
    obtain ⟨q, hq, hqz⟩ := Subgroup.mem_map.mp hxN
    have hqN : (q : Matrix.SpecialLinearGroup (Fin 3) K) ∈ N := hq
    have hord : orderOf (q : Matrix.SpecialLinearGroup (Fin 3) K) ∣ Nat.card N :=
      Subgroup.orderOf_dvd_natCard N hqN
    have hpow : (q : Matrix.SpecialLinearGroup (Fin 3) K) ^ Nat.card N = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hord
    have hqpow : q ^ Nat.card N = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
    have hzpow : z ^ Nat.card N = 1 := by
      rw [← hqz, ← map_pow, hqpow, map_one]
    have hz3 : z ^ 3 = 1 := diag2_pow_three hω0 hω3
    have hz1 : z ≠ 1 := by
      intro h1
      have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) K =>
        (y : Matrix (Fin 2) (Fin 2) K) 0 0) h1
      simp [hz, Matrix.SpecialLinearGroup.diag2_coe'] at this
      exact hω1 this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hz3' : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have h3dvd : orderOf z ∣ Nat.card N := orderOf_dvd_of_pow_eq_one hzpow
    rw [hz3'] at h3dvd
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3dvd) (by norm_num)

end Simple

section Aut

open Matrix

variable {K : Type*} [Field K]

theorem conj_one_add_single_apply (A B : Matrix (Fin 3) (Fin 3) K) (hAB : A * B = 1)
    (i j : Fin 3) (c : K) (k l : Fin 3) :
    (A * (1 + Matrix.single i j c) * B) k l = (1 : Matrix (Fin 3) (Fin 3) K) k l +
      A k i * c * B j l := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAB, Matrix.add_apply]
  congr 1
  have h1 : ∀ m, (A * Matrix.single i j c) k m = if j = m then A k i * c else 0 := by
    intro m
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [Matrix.single_apply]
    · intro p _ hp
      simp [Ne.symm hp]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [h1]
  · intro m _ hm
    simp [h1, Ne.symm hm]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem map_one_add_single (σ : K ≃+* K) (i j : Fin 3) (a : K) :
    (1 + Matrix.single i j a).map σ = 1 + Matrix.single i j (σ a) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem blockEmb_transvection_zero_one (a : K) :
    blockEmb (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a := by
  refine Subtype.ext ?_
  rw [coe_blockEmb, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMatrix]

theorem blockEmb_transvection_one_zero (a : K) :
    blockEmb (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a := by
  refine Subtype.ext ?_
  rw [coe_blockEmb, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMatrix]

theorem transpose_map_inv_transvection (σ : K ≃+* K) {i j : Fin 3} (hij : i ≠ j) (a : K) :
    (((Matrix.SpecialLinearGroup.transvection hij a)⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).transpose.map σ =
        1 + Matrix.single j i (-σ a) := by
  rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, map_one_add_single,
    map_neg]

theorem false_of_block_fixed [Finite K] (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K))
    (hblk : ∀ (B : Matrix.SpecialLinearGroup (Fin 2) K) (i j : Fin 2),
      ((α (blockEmb B) : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        i.succ j.succ = (B : Matrix (Fin 2) (Fin 2) K) i j)
    (hQ : ((α (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    {ω : K} (hω : ω⁻¹ ≠ ω) (z : Matrix.SpecialLinearGroup (Fin 3) K)
    (hz : (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (hαz : (α z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω⁻¹) : False := by
  obtain ⟨A, σ, hform⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (by norm_num : 3 ≤ 3) α
  set Am : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hAm
  set Bm : Matrix (Fin 3) (Fin 3) K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hBm
  have hAB : Am * Bm = 1 := Units.mul_inv A
  have hBA : Bm * Am = 1 := Units.inv_mul A
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hF1 : ∀ a : K, ((α (Matrix.SpecialLinearGroup.transvection h12 a) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = a := fun a => by
    have := hblk (Matrix.SpecialLinearGroup.transvection h01 a) 0 1
    rw [blockEmb_transvection_zero_one] at this
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply] using this
  have hF2 : ((α (Matrix.SpecialLinearGroup.transvection h12 1) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have := hblk (Matrix.SpecialLinearGroup.transvection h01 1) 1 1
    rw [blockEmb_transvection_zero_one] at this
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply] using this
  have hF3 : ((α (Matrix.SpecialLinearGroup.transvection h21 1) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 1 := by
    have := hblk (Matrix.SpecialLinearGroup.transvection h10 1) 1 0
    rw [blockEmb_transvection_one_zero] at this
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply] using this
  have hF4 : ((α (Matrix.SpecialLinearGroup.transvection h21 1) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    have := hblk (Matrix.SpecialLinearGroup.transvection h10 1) 0 0
    rw [blockEmb_transvection_one_zero] at this
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply] using this
  rcases hform with h0 | h1
  · have hT : ∀ a : K, ∀ k l : Fin 3, ((α (Matrix.SpecialLinearGroup.transvection h12 a) :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k l =
        (1 : Matrix (Fin 3) (Fin 3) K) k l + Am k 1 * σ a * Bm 2 l := fun a k l => by
      rw [h0, Matrix.SpecialLinearGroup.transvection_coe, map_one_add_single,
        conj_one_add_single_apply Am Bm hAB]
    have key : ∀ a : K, Am 1 1 * σ a * Bm 2 2 = a := fun a => by
      have := hF1 a
      rw [hT] at this
      simpa using this
    have hk1 : Am 1 1 * Bm 2 2 = 1 := by simpa using key 1
    have hσω : σ ω = ω := by linear_combination key ω - σ ω * hk1
    have hmap : (Matrix.scalar (Fin 3) ω).map σ = Matrix.scalar (Fin 3) (σ ω) := by
      ext k l
      simp only [Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
    have hc : Am * Matrix.scalar (Fin 3) (σ ω) * Bm = Matrix.scalar (Fin 3) (σ ω) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hAB]
    have hscal : ((α z : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) (σ ω) := by
      rw [h0, hz, hmap, hc]
    rw [hscal] at hαz
    have := congrFun (congrFun hαz 0) 0
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact hω (by rw [← this, hσω])
  · have hT : ∀ {i j : Fin 3} (hij : i ≠ j) (a : K) (k l : Fin 3),
        ((α (Matrix.SpecialLinearGroup.transvection hij a) :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k l =
        (1 : Matrix (Fin 3) (Fin 3) K) k l + Am k j * (-σ a) * Bm i l :=
      fun hij a k l => by
        rw [h1, transpose_map_inv_transvection, conj_one_add_single_apply Am Bm hAB]
    have hI12 : (1 : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := Matrix.one_apply_ne (by decide)
    have hI21 : (1 : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := Matrix.one_apply_ne (by decide)
    have hI20 : (1 : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := Matrix.one_apply_ne (by decide)
    have hI22 : (1 : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := Matrix.one_apply_eq _
    have hI11 : (1 : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := Matrix.one_apply_eq _
    have e1 : Am 1 2 * Bm 1 2 = -1 := by
      have := hF1 1
      rw [hT, hI12, map_one] at this
      linear_combination -this
    have e3 : Am 2 2 * Bm 1 2 = 0 := by
      have := hF2
      rw [hT, hI22, map_one] at this
      linear_combination -this
    have e4 : Am 2 1 * Bm 2 1 = -1 := by
      have := hF3
      rw [hT, hI21, map_one] at this
      linear_combination -this
    have e5 : Am 1 1 * Bm 2 1 = 0 := by
      have := hF4
      rw [hT, hI11, map_one] at this
      linear_combination -this
    have e7 : Am 2 1 * Bm 0 0 = 0 := by
      have := hQ
      rw [hT, hI20, map_one] at this
      linear_combination -this
    have hA21 : Am 2 1 ≠ 0 := fun h => by rw [h] at e4; simp at e4
    have hB21 : Bm 2 1 ≠ 0 := fun h => by rw [h] at e4; simp at e4
    have hB12 : Bm 1 2 ≠ 0 := fun h => by rw [h] at e1; simp at e1
    have hA12 : Am 1 2 ≠ 0 := fun h => by rw [h] at e1; simp at e1
    have hA11 : Am 1 1 = 0 := (mul_eq_zero.mp e5).resolve_right hB21
    have hA22 : Am 2 2 = 0 := (mul_eq_zero.mp e3).resolve_right hB12
    have hB00 : Bm 0 0 = 0 := (mul_eq_zero.mp e7).resolve_left hA21
    have hBA01 := congrFun (congrFun hBA 0) 1
    have hBA02 := congrFun (congrFun hBA 0) 2
    have hBA00 := congrFun (congrFun hBA 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hA11, hA22, hB00] at hBA01 hBA02 hBA00
    have hB02 : Bm 0 2 = 0 := hBA01.resolve_right hA21
    have hB01 : Bm 0 1 = 0 := hBA02.resolve_right hA12
    simp [hB02, hB01] at hBA00

end Aut

section Dual

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification

variable {K : Type*} [Field K]

@[expose] def reversalMatrix (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem reversalMatrix_mul_self : reversalMatrix K * reversalMatrix K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reversalMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem reversal_conj_transpose_apply (M : Matrix (Fin 3) (Fin 3) K) :
    (reversalMatrix K * M.transpose * reversalMatrix K) 1 0 = M 2 1 ∧
      (reversalMatrix K * M.transpose * reversalMatrix K) 2 0 = M 2 0 := by
  constructor <;>
    simp [reversalMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem exists_dual_aut :
    ∃ θ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K), ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
      θ g ∈ stabilizer (flagSpace 3 K 1) ↔ g ∈ stabilizer (flagSpace 3 K 2) := by
  let r : Matrix.GeneralLinearGroup (Fin 3) K :=
    ⟨reversalMatrix K, reversalMatrix K, reversalMatrix_mul_self, reversalMatrix_mul_self⟩
  refine ⟨CatalogueBHigherLinearAction.slConjugation 3 K r *
    CatalogueBGraphForm.slGraphAut 3 K, fun g => ?_⟩
  have hθ : ∀ i j : Fin 3, ((((CatalogueBHigherLinearAction.slConjugation 3 K r *
      CatalogueBGraphForm.slGraphAut 3 K) g : Matrix.SpecialLinearGroup (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) i j =
      (reversalMatrix K * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).transpose * reversalMatrix K) i j := by
    intro i j
    rw [MulAut.mul_apply, CatalogueBHigherLinearAction.slConjugation_matrix,
      CatalogueBGraphForm.slGraphAut_matrix]
    rfl
  rw [mem_stabilizer_one_iff, ← inv_mem_iff (x := g), mem_stabilizer_two_iff, hθ, hθ,
    (reversal_conj_transpose_apply _).1, (reversal_conj_transpose_apply _).2]
  exact and_comm

end Dual

section Core

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

theorem commutator_blockEmb_range {ω : K} (hω0 : ω ≠ 0) (hω2 : ω ^ 2 ≠ 1) :
    ⁅(blockEmb : Matrix.SpecialLinearGroup (Fin 2) K →* _).range,
      (blockEmb : Matrix.SpecialLinearGroup (Fin 2) K →* _).range⁆ =
      (blockEmb : Matrix.SpecialLinearGroup (Fin 2) K →* _).range := by
  have h : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Matrix.SL2.commutator_eq_top hω0 hω2
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem false_of_inverting_block [CharP K 2] [Finite K]
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K))
    (hQ : ∀ g : Matrix.SpecialLinearGroup (Fin 3) K, g ∈ stabilizer (flagSpace 3 K 1) →
      α g ∈ stabilizer (flagSpace 3 K 1))
    {ω : K} (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (z : Matrix.SpecialLinearGroup (Fin 3) K)
    (hz : (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω)
    (hαz : (α z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω⁻¹)
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) (hNQ : N ≤ stabilizer (flagSpace 3 K 1))
    (hN3 : Nat.Coprime 3 (Nat.card N))
    (hNn : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, ∀ n ∈ N,
      blockEmb B * n * (blockEmb B)⁻¹ ∈ N)
    (hNc : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, blockEmb B * (α (blockEmb B))⁻¹ ∈ N) :
    False := by
  have hω2 : ω ^ 2 ≠ 1 := fun h => hω1 (eq_one_of_sq_eq_one h)
  set S := (blockEmb : Matrix.SpecialLinearGroup (Fin 2) K →*
    Matrix.SpecialLinearGroup (Fin 3) K).range with hS
  have hSperf : ⁅S, S⁆ = S := commutator_blockEmb_range hω0 hω2
  have hSQ : S ≤ stabilizer (flagSpace 3 K 1) := by
    rintro _ ⟨B, rfl⟩
    exact pointFixer_le_stabilizer (blockEmb_mem_pointFixer B)
  have hαSperf : ⁅S.map α.toMonoidHom, S.map α.toMonoidHom⁆ = S.map α.toMonoidHom := by
    rw [← Subgroup.map_commutator, hSperf]
  have hαQ : ∀ B, α (blockEmb B) ∈ stabilizer (flagSpace 3 K 1) := by
    intro B
    have hc := hNQ (hNc B)
    have hs : blockEmb B ∈ stabilizer (flagSpace 3 K 1) := hSQ ⟨B, rfl⟩
    have : α (blockEmb B) = (blockEmb B * (α (blockEmb B))⁻¹)⁻¹ * blockEmb B := by group
    rw [this]
    exact mul_mem (inv_mem hc) hs
  have hαS_le : S.map α.toMonoidHom ≤ stabilizer (flagSpace 3 K 1) := by
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    exact hαQ B
  have hαfix : ∀ B, α (blockEmb B) ∈ pointFixer K := fun B =>
    CFSG.AGLEmbedding.LinearThreeKit.mulVec_single_zero_of_perfect hαS_le hαSperf
      ⟨blockEmb B, ⟨B, rfl⟩, rfl⟩
  have hc_mem : ∀ B, blockEmb B * (α (blockEmb B))⁻¹ ∈ N ⊓ pointFixer K := fun B =>
    Subgroup.mem_inf.mpr ⟨hNc B, Subgroup.mul_mem _ (blockEmb_mem_pointFixer B)
      (Subgroup.inv_mem _ (hαfix B))⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥(N ⊓ pointFixer K)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hN3
  have hblock1 : ∀ n ∈ N ⊓ pointFixer K, lowerBlock (n : Matrix (Fin 3) (Fin 3) K) = 1 :=
    fun n hn => lowerBlock_eq_one_of_normal hω0 hω3 hω1 (N ⊓ pointFixer K) inf_le_right hcop
      (fun B n hn => Subgroup.mem_inf.mpr ⟨hNn B n (Subgroup.mem_inf.mp hn).1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (blockEmb_mem_pointFixer B)
          (Subgroup.mem_inf.mp hn).2) (Subgroup.inv_mem _ (blockEmb_mem_pointFixer B))⟩) hn
  have hblk : ∀ (B : Matrix.SpecialLinearGroup (Fin 2) K) (i j : Fin 2),
      ((α (blockEmb B) : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        i.succ j.succ = (B : Matrix (Fin 2) (Fin 2) K) i j := by
    intro B i j
    have hc := hc_mem B
    obtain ⟨-, hc10, hc20⟩ := mem_pointFixer_iff.mp (Subgroup.mem_inf.mp hc).2
    have hmul : blockEmb B = (blockEmb B * (α (blockEmb B))⁻¹) * α (blockEmb B) := by group
    have h1 : lowerBlock ((blockEmb B : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = lowerBlock (((blockEmb B * (α (blockEmb B))⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
        lowerBlock ((α (blockEmb B) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
      conv_lhs => rw [hmul]
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact lowerBlock_mul hc10 hc20
    rw [hblock1 _ hc, one_mul, coe_blockEmb, lowerBlock_blockMatrix] at h1
    have := congrFun (congrFun h1 i) j
    simpa [lowerBlock] using this.symm
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hT01 : Matrix.SpecialLinearGroup.transvection h01 (1 : K) ∈
      stabilizer (flagSpace 3 K 1) := by
    rw [mem_stabilizer_one_iff]
    simp [Matrix.SpecialLinearGroup.transvection_coe]
  have hQ20 := (mem_stabilizer_one_iff.mp (hQ _ hT01)).2
  refine false_of_block_fixed α hblk hQ20 (ω := ω) ?_ z hz hαz
  intro h
  apply hω2
  have := mul_inv_cancel₀ hω0
  rw [h] at this
  rw [sq]
  exact this

end Core

section Main

open CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Transport

variable {Y : Type*} [Group Y] {L : Subgroup Y} {K : Type*} [Field K]

@[expose] noncomputable def conjByAut (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (t : Y)
    (ht : t ∈ Subgroup.normalizer (L : Set Y)) : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) :=
  MulAut.congr ψ (Subgroup.normalizerMonoidHom L ⟨t, ht⟩)

theorem conjByAut_apply (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (t : Y)
    (ht : t ∈ Subgroup.normalizer (L : Set Y)) (l : ↥L) :
    conjByAut ψ t ht (ψ l) = ψ ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht l).mp l.2⟩ := by
  have h : (Subgroup.normalizerMonoidHom L ⟨t, ht⟩) l =
      ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht l).mp l.2⟩ := Subtype.ext (by simp)
  simp [conjByAut, MulAut.congr_apply, h]

theorem coe_inv_scalar {g : Matrix.SpecialLinearGroup (Fin 3) K} {ω : K} (hω : ω ≠ 0)
    (h : (g : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) ω⁻¹ := by
  have h1 := coe_inv_mul_coe g
  rw [h] at h1
  calc ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (Matrix.scalar (Fin 3) ω * Matrix.scalar (Fin 3) ω⁻¹) := by
        rw [← map_mul, mul_inv_cancel₀ hω, map_one, mul_one]
    _ = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Matrix.scalar (Fin 3) ω * Matrix.scalar (Fin 3) ω⁻¹ := by rw [mul_assoc]
    _ = Matrix.scalar (Fin 3) ω⁻¹ := by rw [h1, one_mul]

theorem no_normal_subgroup_one [Finite K] [CharP K 2] (J V : Subgroup Y)
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (hJ : ∀ l : ↥L, (l : Y) ∈ J ↔ ψ l ∈ stabilizer (flagSpace 3 K 1))
    (hVJ : V ≤ J) (hVmax : ∀ W : Subgroup Y, W ≤ J → ⁅W, W⁆ = W → W ≤ V)
    {ζ : Y} (hζL : ζ ∈ L) (hζc : ζ ∈ Subgroup.centralizer (L : Set Y)) (hζ1 : ζ ≠ 1)
    {t : Y} (htL : t ∈ Subgroup.normalizer (L : Set Y)) (htJ : t ∈ Subgroup.normalizer (J : Set Y))
    (htζ : t * ζ * t⁻¹ = ζ⁻¹) :
    ¬ ∃ N : Subgroup Y, N ≤ V ∧ (∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N) ∧
      Nat.Coprime 3 (Nat.card N) ∧ ∀ v ∈ V, v * t * v⁻¹ * t⁻¹ ∈ N := by
  rintro ⟨N, hNV, hNn, hN3, hNc⟩
  set α := conjByAut ψ t htL with hα
  have hψζ : ψ ⟨ζ, hζL⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hζc l l.2))
  rw [← scalars_eq_center] at hψζ
  obtain ⟨c, hc3, hcz⟩ := mem_scalars.mp hψζ
  have hω0 : (c : K) ≠ 0 := c.ne_zero
  have hω3 : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hω1 : (c : K) ≠ 1 := by
    intro h
    apply hζ1
    have h1 : ψ ⟨ζ, hζL⟩ = 1 := by
      refine Subtype.ext ?_
      rw [hcz, h, map_one, Matrix.SpecialLinearGroup.coe_one]
    have := ψ.injective (h1.trans (map_one ψ).symm)
    exact congrArg Subtype.val this
  have hαz : (α (ψ ⟨ζ, hζL⟩) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c : K)⁻¹ := by
    rw [hα, conjByAut_apply]
    have hinv : (⟨t * ζ * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL ζ).mp hζL⟩ : ↥L) =
        ⟨ζ, hζL⟩⁻¹ := Subtype.ext (by simpa using htζ)
    rw [hinv, map_inv]
    exact coe_inv_scalar hω0 hcz
  have hQ : ∀ g, g ∈ stabilizer (flagSpace 3 K 1) → α g ∈ stabilizer (flagSpace 3 K 1) := by
    intro g hg
    obtain ⟨l, rfl⟩ := ψ.surjective g
    rw [hα, conjByAut_apply, ← hJ]
    rw [← hJ] at hg
    exact (Subgroup.mem_normalizer_iff.mp htJ _).mp hg
  set S := (blockEmb : Matrix.SpecialLinearGroup (Fin 2) K →*
    Matrix.SpecialLinearGroup (Fin 3) K).range with hS
  have hSQ : S ≤ stabilizer (flagSpace 3 K 1) := by
    rintro _ ⟨B, rfl⟩
    exact pointFixer_le_stabilizer (blockEmb_mem_pointFixer B)
  have hSperf : ⁅S, S⁆ = S :=
    commutator_blockEmb_range hω0 (fun h => hω1 (eq_one_of_sq_eq_one h))
  set W : Subgroup Y := (S.map ψ.symm.toMonoidHom).map L.subtype with hW
  have hWJ : W ≤ J := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact (hJ (ψ.symm s)).mpr (by simpa using hSQ hs)
  have hWperf : ⁅W, W⁆ = W := by
    rw [hW, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hSperf]
  have hWV : W ≤ V := hVmax W hWJ hWperf
  have hblockV : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, ((ψ.symm (blockEmb B) : ↥L) : Y) ∈ V :=
    fun B => hWV ⟨ψ.symm (blockEmb B), ⟨blockEmb B, ⟨B, rfl⟩, rfl⟩, rfl⟩
  set N' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := (N.subgroupOf L).map ψ.toMonoidHom
    with hN'
  have hN'Q : N' ≤ stabilizer (flagSpace 3 K 1) := by
    rintro _ ⟨n, hn, rfl⟩
    exact (hJ n).mp (hVJ (hNV hn))
  have hdvd : Nat.card N' ∣ Nat.card N := by
    have h1 : Nat.card N' ∣ Nat.card (N.subgroupOf L) := Subgroup.card_map_dvd _ _
    refine h1.trans ?_
    have h2 : Nat.card ((N.subgroupOf L).map L.subtype) = Nat.card (N.subgroupOf L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [← h2, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcop : Nat.Coprime 3 (Nat.card N') := Nat.Coprime.coprime_dvd_right hdvd hN3
  have hNn' : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, ∀ n' ∈ N',
      blockEmb B * n' * (blockEmb B)⁻¹ ∈ N' := by
    rintro B _ ⟨n, hn, rfl⟩
    refine Subgroup.mem_map.mpr ⟨ψ.symm (blockEmb B) * n * (ψ.symm (blockEmb B))⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := hNn _ (hblockV B) _ hn
      simpa using this
    · simp
  have hNc' : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
      blockEmb B * (α (blockEmb B))⁻¹ ∈ N' := by
    intro B
    set w : ↥L := ψ.symm (blockEmb B) with hw
    have hψw : ψ w = blockEmb B := ψ.apply_symm_apply _
    have hαw : α (blockEmb B) =
        ψ ⟨t * w * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL w).mp w.2⟩ := by
      rw [← hψw, hα]
      exact conjByAut_apply ψ t htL w
    refine Subgroup.mem_map.mpr ⟨w * (⟨t * w * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htL w).mp w.2⟩ : ↥L)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := hNc (w : Y) (hblockV B)
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · show ψ (w * (⟨t * w * t⁻¹, (Subgroup.mem_normalizer_iff.mp htL w).mp w.2⟩ : ↥L)⁻¹) = _
      rw [map_mul, map_inv, hψw, ← hαw]
  exact false_of_inverting_block α hQ hω0 hω3 hω1 _ hcz hαz N' hN'Q hcop hNn' hNc'

end Transport

end Main

end SL3InvertCentreAux

open SL3InvertCentreAux in
theorem sl3InvertCentre_holds : SL3InvertCentre := by
  intro Y _ _ L J V K _ _ _ ψ d hd hJL hJ hVJ hVp hVmax h3 ζ hζL hζc hζ3 hζ1 t htL htJ htζ
  rcases hd with rfl | rfl
  · exact no_normal_subgroup_one J V ψ hJ hVJ hVmax hζL hζc hζ1 htL htJ htζ
  · obtain ⟨θ, hθ⟩ := exists_dual_aut (K := K)
    exact no_normal_subgroup_one J V (ψ.trans θ) (fun l => (hJ l).trans (hθ (ψ l)).symm) hVJ
      hVmax hζL hζc hζ1 htL htJ htζ

end CFSG.LocalAnalysis.RankThreeTheoremC
