module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3L3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.QuasithinUnique.A5.G3

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Sp4

variable {K : Type} [Field K] [Finite K]

theorem N1_shape (g : ↥(perfectCore (Q2 K 1))) :
    ∃ C : Matrix (Fin 2) (Fin 2) K, Cᵀ = C ∧ spMat (g : StatedSp 2 K) =
      blockMat ((blkN 1 g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) C := by
  have hgQ : (g : StatedSp 2 K) ∈ Q2 K 1 := perfectCore_le _ g.2
  have h21 : (spMat (g : StatedSp 2 K)).toBlocks₂₁ = 0 := by
    ext i k
    exact spMat_inr_inl_of_mem_Q2_one hgQ i k
  obtain ⟨-, C, hC, hM⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
  refine ⟨C, hC, ?_⟩
  have h11 : ((blkN 1 g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (spMat (g : StatedSp 2 K)).toBlocks₁₁ := by
    ext i k
    rw [blkN_coe]
    fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, Matrix.toBlocks₁₁]
  rw [h11]
  exact hM

theorem N1_fixed [CharP K 2] (x u : ↥(perfectCore (Q2 K 1))) (hu : blkN 1 u = 1)
    (hxu : x * u = u * x) :
    ∃ C : Matrix (Fin 2) (Fin 2) K, Cᵀ = C ∧ spMat (u : StatedSp 2 K) = blockMat 1 C ∧
      C 0 0 = ((blkN 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 *
          C 0 0 + ((blkN 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2 *
            C 1 1 ∧
      C 1 1 = ((blkN 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 *
          C 0 0 + ((blkN 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2 *
            C 1 1 := by
  obtain ⟨Cx, hCx, hx⟩ := N1_shape x
  obtain ⟨Cu, hCu, hu'⟩ := N1_shape u
  have hA1 : ((blkN 1 u : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [hu]
    rfl
  rw [hA1] at hu'
  set A : Matrix (Fin 2) (Fin 2) K :=
    ((blkN 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hA
  have hdetA : IsUnit A.det := by
    rw [hA, (blkN 1 x).2]
    exact isUnit_one
  have hm : spMat (x : StatedSp 2 K) * spMat (u : StatedSp 2 K) =
      spMat (u : StatedSp 2 K) * spMat (x : StatedSp 2 K) := by
    have := congrArg (fun g : ↥(perfectCore (Q2 K 1)) => spMat (g : StatedSp 2 K)) hxu
    simpa [spMat_mul] using this
  rw [hx, hu', blockMat_mul (by simp : IsUnit (1 : Matrix (Fin 2) (Fin 2) K).det),
    blockMat_mul hdetA] at hm
  have h12 := congrArg Matrix.toBlocks₁₂ hm
  simp only [blockMat, Matrix.toBlocks_fromBlocks₁₂, Matrix.mul_one, Matrix.one_mul, inv_one,
    Matrix.transpose_one] at h12
  have h3 : Cu + Cx = Cx + A⁻¹ * Cu * A⁻¹ᵀ := by
    have := congrArg (fun M => A⁻¹ * M) h12
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetA, Matrix.one_mul] using this
  have h4 : Cu = A⁻¹ * Cu * A⁻¹ᵀ := by
    have := h3
    rw [add_comm Cu Cx] at this
    exact add_left_cancel this
  have h5 : A * Cu * Aᵀ = Cu := by
    calc A * Cu * Aᵀ = A * (A⁻¹ * Cu * A⁻¹ᵀ) * Aᵀ := by rw [← h4]
      _ = (A * A⁻¹) * Cu * (A⁻¹ᵀ * Aᵀ) := by simp only [Matrix.mul_assoc]
      _ = Cu := by
        rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdetA]
        simp
  have hsym : Cu 1 0 = Cu 0 1 := congrFun (congrFun hCu 0) 1
  have e00 := congrFun (congrFun h5 0) 0
  have e11 := congrFun (congrFun h5 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hsym] at e00 e11
  refine ⟨Cu, hCu, hu', ?_, ?_⟩
  · linear_combination -e00 + (A 0 0 * A 0 1 * Cu 0 1) * (CharTwo.two_eq_zero : (2 : K) = 0)
  · linear_combination -e11 + (A 1 0 * A 1 1 * Cu 0 1) * (CharTwo.two_eq_zero : (2 : K) = 0)

@[expose] def zMat0 (p : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 1 !![p, 0; 0, 0] 0 1

theorem N0_key [CharP K 2] (x u : ↥(perfectCore (Q2 K 0))) (hu : blkN 0 u = 1) (hxu : x * u = u * x)
    (hx3 : (blkN 0 x) ^ 3 = 1) (hx1 : blkN 0 x ≠ 1) :
    ∃ p : K, spMat (u : StatedSp 2 K) = zMat0 p := by
  obtain ⟨Au, ⟨hAu1, hAu2⟩, Cu, hCu, hM⟩ : ∃ Au : Matrix (Fin 2) (Fin 2) K, IsUnitriangular Au ∧
      ∃ Cu : Matrix (Fin 2) (Fin 2) K, Cuᵀ = Cu ∧ spMat (u : StatedSp 2 K) = blockMat Au Cu := by
    obtain ⟨Au, Cu, hA, hC, hM⟩ := blkN_ker 0 u hu
    exact ⟨Au, hA, Cu, hC, hM⟩
  have hxQ : (x : StatedSp 2 K) ∈ Q2 K 0 := perfectCore_le _ x.2
  have hlam := spMat_inl_zero_eq_one_of_perfectCore x.2
  have hAu10 : Au 1 0 = 0 := hAu1 (show (0 : Fin 2) < 1 by decide)
  have hAu00 : Au 0 0 = 1 := hAu2 0
  have hAu11 : Au 1 1 = 1 := hAu2 1
  have hblk : ∀ i k : Fin 2, spMat (u : StatedSp 2 K) (sigma2 0 i) (sigma2 0 k) =
      (1 : Matrix (Fin 2) (Fin 2) K) i k := by
    intro i k
    have := congrFun₂ (congrArg Subtype.val hu) i k
    exact this
  have hu22 : spMat (u : StatedSp 2 K) (Sum.inr 1) (Sum.inr 1) = 1 := by
    simpa [sigma2] using hblk 1 1
  have hu12 : spMat (u : StatedSp 2 K) (Sum.inl 1) (Sum.inr 1) = 0 := by
    simpa [sigma2] using hblk 0 1
  have hAuinv10 : Au⁻¹ 1 0 = 0 :=
    (IsUnitriangular.inv (⟨hAu1, hAu2⟩ : IsUnitriangular Au)).1 (show (0 : Fin 2) < 1 by decide)
  have hsym : Cu 1 0 = Cu 0 1 := congrFun (congrFun hCu 0) 1
  have hm : spMat (x : StatedSp 2 K) * spMat (u : StatedSp 2 K) =
      spMat (u : StatedSp 2 K) * spMat (x : StatedSp 2 K) := by
    have := congrArg (fun g : ↥(perfectCore (Q2 K 0)) => spMat (g : StatedSp 2 K)) hxu
    simpa [spMat_mul] using this
  have e12 := congrFun₂ hm (Sum.inl 0) (Sum.inl 1)
  have e1f2 := congrFun₂ hm (Sum.inl 0) (Sum.inr 1)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at e12 e1f2
  have xf1e2 : spMat (x : StatedSp 2 K) (Sum.inr 0) (Sum.inl 1) = 0 :=
    spMat_inr_zero_of_mem_Q2_zero hxQ (by simp)
  have xf1f2 : spMat (x : StatedSp 2 K) (Sum.inr 0) (Sum.inr 1) = 0 :=
    spMat_inr_zero_of_mem_Q2_zero hxQ (by simp)
  have ue1e1 : spMat (u : StatedSp 2 K) (Sum.inl 0) (Sum.inl 0) = 1 := by
    rw [hM]; simp [blockMat, hAu00]
  have ue1e2 : spMat (u : StatedSp 2 K) (Sum.inl 0) (Sum.inl 1) = Au 0 1 := by
    rw [hM]; simp [blockMat]
  have ue2e1 : spMat (u : StatedSp 2 K) (Sum.inl 1) (Sum.inl 0) = 0 := by
    rw [hM]; simp [blockMat, hAu10]
  have ue2e2 : spMat (u : StatedSp 2 K) (Sum.inl 1) (Sum.inl 1) = 1 := by
    rw [hM]; simp [blockMat, hAu11]
  have ufe : ∀ i k : Fin 2, spMat (u : StatedSp 2 K) (Sum.inr i) (Sum.inl k) = 0 := by
    intro i k; rw [hM]; simp [blockMat]
  have uf1f2 : spMat (u : StatedSp 2 K) (Sum.inr 0) (Sum.inr 1) = 0 := by
    rw [hM]; simp [blockMat, hAuinv10]
  have ue1f2 : spMat (u : StatedSp 2 K) (Sum.inl 0) (Sum.inr 1) = (Au * Cu) 0 1 := by
    rw [hM]; simp [blockMat]
  have hr : Cu 1 1 = 0 := by
    have : (Au * Cu) 1 1 = 0 := by
      rw [← hu12, hM]; simp [blockMat]
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hAu10, hAu11] using this
  set t := (Au * Cu) 0 1 with ht
  have f1 : Au 0 1 = Au 0 1 * spMat (x : StatedSp 2 K) (Sum.inl 1) (Sum.inl 1) +
      t * spMat (x : StatedSp 2 K) (Sum.inr 1) (Sum.inl 1) := by
    rw [hlam, ue1e2, ue2e2, ufe, ufe, ue1e1, xf1e2, ue1f2] at e12
    simp only [mul_zero, add_zero, mul_one, one_mul] at e12
    linear_combination e12
  have f2 : t = Au 0 1 * spMat (x : StatedSp 2 K) (Sum.inl 1) (Sum.inr 1) +
      t * spMat (x : StatedSp 2 K) (Sum.inr 1) (Sum.inr 1) := by
    rw [hlam, hu12, uf1f2, hu22, ue1e1, ue1e2, xf1f2, ue1f2] at e1f2
    simp only [mul_zero, add_zero, mul_one, one_mul] at e1f2
    linear_combination e1f2
  have hw : ¬ (![Au 0 1, t] ≠ (0 : Fin 2 → K)) := by
    intro hw
    apply hx1
    refine sl2_eq_one_of_fixed _ hx3 ⟨![Au 0 1, t], hw, Or.inl ?_⟩
    funext k
    fin_cases k
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, blkN_coe, blkIdx,
        Matrix.submatrix_apply]
      simp [sigma2]
      linear_combination -f1
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, blkN_coe, blkIdx,
        Matrix.submatrix_apply]
      simp [sigma2]
      linear_combination -f2
  have hw' : ![Au 0 1, t] = (0 : Fin 2 → K) := not_not.mp hw
  have ha : Au 0 1 = 0 := by simpa using congrFun hw' 0
  have ht0 : t = 0 := by simpa using congrFun hw' 1
  have hAu : Au = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hAu00, hAu11, hAu10, ha]
  have hc01 : Cu 0 1 = 0 := by
    have : t = Cu 0 1 := ht.trans (by simp [Matrix.mul_apply, Fin.sum_univ_two, hAu00, ha, hr])
    rw [← this]
    exact ht0
  have hc10 : Cu 1 0 = 0 := hsym.trans hc01
  obtain ⟨p, hp⟩ : ∃ p : K, Cu = !![p, 0; 0, 0] := by
    refine ⟨Cu 0 0, ?_⟩
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hc01, hc10, hr]
  subst hAu hp
  exact ⟨p, by rw [hM]; simp [blockMat, zMat0]⟩

theorem exists_order_three_fixing : ∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) → w ≠ 0 →
    ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ ≠ 1 ∧ σ ^ 3 = 1 ∧
      ∀ i, w (σ⁻¹ i) = w i := by
  decide +kernel

theorem IsDelta5Group.exists_three_comm_of_ne {B : Type} [Group B] [Finite B]
    (hD : IsDelta5Group B) (u : B) (hu : u ∈ CFSG.pCore 2 B) (hu1 : u ≠ 1) :
    ∃ y : B, orderOf y = 3 ∧ y * u = u * y := by
  classical
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set uu : ↥(CFSG.pCore 2 B) := ⟨u, hu⟩ with huu
  set w : Fin 5 → ZMod 2 := ((Multiplicative.toAdd (β uu) : evenWeight 5) : Fin 5 → ZMod 2)
    with hw
  have hwe : ∑ i, w i = 0 := (Delta5.mem_evenWeight_iff w).1 (Multiplicative.toAdd (β uu)).2
  have hwn : w ≠ 0 := by
    intro h0
    apply hu1
    have h1 : β uu = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact h0
    have : uu = 1 := hβb.1 (h1.trans (map_one β).symm)
    exact congrArg Subtype.val this
  obtain ⟨σ, hsign, hσ1, hσ3, hσfix⟩ := exists_order_three_fixing w hwe hwn
  have hσA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  set σ' : alternatingGroup (Fin 5) := ⟨σ, hσA⟩ with hσ'
  have hσ'3 : σ' ^ 3 = 1 := Subtype.ext (by simpa using hσ3)
  have hσ'1 : σ' ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
  obtain ⟨y₀, hy₀⟩ := hαs σ'
  have hy₀3 : y₀ ^ 3 ∈ CFSG.pCore 2 B := by
    rw [← hαk, MonoidHom.mem_ker, map_pow, hy₀]
    exact hσ'3
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := B) (p := 2)) ⟨y₀ ^ 3, hy₀3⟩
  have hk' : (y₀ ^ 3) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  set y := y₀ ^ (2 ^ k) with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul]
    exact hk'
  have hαy : α y = σ' ^ (2 ^ k) := by rw [hy, map_pow, hy₀]
  have hy1 : y ≠ 1 := by
    intro h1
    have h2 : σ' ^ (2 ^ k) = 1 := by rw [← hαy, h1, map_one]
    apply hσ'1
    have h3 : orderOf σ' ∣ 3 := orderOf_dvd_of_pow_eq_one hσ'3
    have h4 : orderOf σ' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    have h5 : orderOf σ' ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h3 h4
    have h6 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by norm_num)
    rw [h6] at h5
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  refine ⟨y, hord, ?_⟩
  have hpow : ∀ m : ℕ, ∀ i, w (((σ ^ m)⁻¹ : Equiv.Perm (Fin 5)) i) = w i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ, _root_.mul_inv_rev, Equiv.Perm.mul_apply, hσfix ((σ ^ m)⁻¹ i), ih i]
  have hmem : y * u * y⁻¹ ∈ CFSG.pCore 2 B :=
    (CFSG.pCore_normal (G := B) (p := 2)).conj_mem _ hu y
  set u2 : ↥(CFSG.pCore 2 B) := ⟨y * u * y⁻¹, hmem⟩ with hu2
  have h2 : β u2 = β uu := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    have := hβe y uu u2 rfl i
    rw [this]
    have hαyv : ((α y : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = σ ^ (2 ^ k) := by
      rw [hαy]
      rfl
    rw [hαyv]
    exact hpow _ i
  have h3 : u2 = uu := hβb.1 h2
  have hcomm : y * u * y⁻¹ = u := congrArg Subtype.val h3
  exact mul_inv_eq_iff_eq_mul.mp hcomm

theorem exists_comm_data [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2)
    (hD : IsDelta5Group ↥(perfectCore (Q2 K j))) (u : ↥(perfectCore (Q2 K j)))
    (hu : u ∈ CFSG.pCore 2 ↥(perfectCore (Q2 K j))) (hu1 : u ≠ 1) :
    ∃ x : ↥(perfectCore (Q2 K j)), blkN j u = 1 ∧ (blkN j x) ^ 3 = 1 ∧ blkN j x ≠ 1 ∧
      x * u = u * x := by
  have := sl2_isSimple hK4
  have hpc : CFSG.pCore 2 ↥(perfectCore (Q2 K j)) = (blkN j).ker :=
    pCore_two_eq_ker (sl2_nonabelian hK4) (blkN j) (blkN_surjective hK4 j)
      (blkN_ker_isPGroup hK j)
  obtain ⟨x, hx3, hxu⟩ := hD.exists_three_comm_of_ne u hu hu1
  have hx : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hxk : blkN j x ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨x, MonoidHom.mem_ker.mpr h1⟩
    have h2 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  exact ⟨x, MonoidHom.mem_ker.mp (hpc ▸ hu), by rw [← map_pow, hx, map_one], hxk, hxu⟩

omit [Finite K] in
theorem zMat0_zero : zMat0 (0 : K) = 1 := by
  have h : (!![(0 : K), 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [zMat0, h, fromBlocks_one]

theorem shape0 [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (hD : IsDelta5Group ↥(perfectCore (Q2 K 0)))
    (u : ↥(perfectCore (Q2 K 0))) (hu : u ∈ CFSG.pCore 2 ↥(perfectCore (Q2 K 0))) :
    ∃ p : K, spMat (u : StatedSp 2 K) = zMat0 p := by
  by_cases hu1 : u = 1
  · refine ⟨0, ?_⟩
    rw [hu1, zMat0_zero]
    exact spMat_one
  · obtain ⟨x, hu0, hx3, hx1, hxu⟩ := exists_comm_data hK hK4 0 hD u hu hu1
    exact N0_key x u hu0 hxu hx3 hx1

theorem shape1 [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (hD : IsDelta5Group ↥(perfectCore (Q2 K 1)))
    (u : ↥(perfectCore (Q2 K 1))) (hu : u ∈ CFSG.pCore 2 ↥(perfectCore (Q2 K 1))) :
    ∃ C : Matrix (Fin 2) (Fin 2) K, Cᵀ = C ∧ spMat (u : StatedSp 2 K) = blockMat 1 C ∧
      C 0 0 = 0 ∧ C 1 1 = 0 := by
  by_cases hu1 : u = 1
  · refine ⟨0, Matrix.transpose_zero, ?_, rfl, rfl⟩
    rw [hu1]
    exact spMat_one.trans blockMat_one.symm
  · obtain ⟨x, hu0, hx3, hx1, hxu⟩ := exists_comm_data hK hK4 1 hD u hu hu1
    obtain ⟨C, hC, hM, h00, h11⟩ := N1_fixed x u hu0 hxu
    obtain ⟨e0, e1⟩ := sl2_twisted_fixed (blkN 1 x) hx3 hx1 (C 0 0) (C 1 1) h00 h11
    exact ⟨C, hC, hM, e0, e1⟩

theorem card_pCore_le_zero [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (hD : IsDelta5Group ↥(perfectCore (Q2 K 0))) :
    Nat.card (CFSG.pCore 2 ↥(perfectCore (Q2 K 0))) ≤ Nat.card K := by
  let F : ↥(CFSG.pCore 2 ↥(perfectCore (Q2 K 0))) → K := fun u =>
    spMat ((u : ↥(perfectCore (Q2 K 0))) : StatedSp 2 K) (Sum.inl 0) (Sum.inr 0)
  refine Nat.card_le_card_of_injective F ?_
  intro u v huv
  obtain ⟨p, hp⟩ := shape0 hK hK4 hD u u.2
  obtain ⟨q, hq⟩ := shape0 hK hK4 hD v v.2
  have hFu : F u = p := by simp [F, hp, zMat0]
  have hFv : F v = q := by simp [F, hq, zMat0]
  have hpq : p = q := hFu.symm.trans (huv.trans hFv)
  apply Subtype.ext
  apply Subtype.ext
  apply statedSp_ext
  show spMat _ = spMat _
  rw [hp, hq, hpq]

theorem card_pCore_le_one [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (hD : IsDelta5Group ↥(perfectCore (Q2 K 1))) :
    Nat.card (CFSG.pCore 2 ↥(perfectCore (Q2 K 1))) ≤ Nat.card K := by
  let F : ↥(CFSG.pCore 2 ↥(perfectCore (Q2 K 1))) → K := fun u =>
    spMat ((u : ↥(perfectCore (Q2 K 1))) : StatedSp 2 K) (Sum.inl 0) (Sum.inr 1)
  refine Nat.card_le_card_of_injective F ?_
  intro u v huv
  obtain ⟨Cu, hCu, hu', hu00, hu11⟩ := shape1 hK hK4 hD u u.2
  obtain ⟨Cv, hCv, hv', hv00, hv11⟩ := shape1 hK hK4 hD v v.2
  have hFu : F u = Cu 0 1 := by simp [F, hu', blockMat]
  have hFv : F v = Cv 0 1 := by simp [F, hv', blockMat]
  have h01 : Cu 0 1 = Cv 0 1 := hFu.symm.trans (huv.trans hFv)
  have hsu : Cu 1 0 = Cu 0 1 := congrFun (congrFun hCu 0) 1
  have hsv : Cv 1 0 = Cv 0 1 := congrFun (congrFun hCv 0) 1
  have hC : Cu = Cv := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hu00, hv00, hu11, hv11, h01, hsu, hsv]
  apply Subtype.ext
  apply Subtype.ext
  apply statedSp_ext
  show spMat _ = spMat _
  rw [hu', hv', hC]

theorem not_isDelta5_perfectCore_Q2 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf2 : 2 ≤ f) (j : Fin 2) : ¬ IsDelta5Group ↥(perfectCore (Q2 K j)) := by
  intro hD
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4' : 4 ≤ Nat.card K := by
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4'
  have hle : 16 ≤ Nat.card K := by
    have h16 := hD.card_pCore
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) j with rfl | rfl
    · have := card_pCore_le_zero hK hK4 hD
      omega
    · have := card_pCore_le_one hK hK4 hD
      omega
  have hdvd : Nat.card (SpecialLinearGroup (Fin 2) K) ∣ Nat.card ↥(perfectCore (Q2 K j)) :=
    Subgroup.card_dvd_of_surjective (blkN_surjective hK4 j)
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hD.card] at hdvd
  have hle2 := Nat.le_of_dvd (by norm_num) hdvd
  have h1 : 256 ≤ Nat.card K ^ 2 := by nlinarith
  have h2 : 255 ≤ Nat.card K ^ 2 - 1 := by omega
  have h3 : 16 * 255 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul hle h2
  omega

theorem not_isDelta5_perfectCore_of_projSp4 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf2 : 2 ≤ f) {Pa : Subgroup (StatedProj (StatedSp 2 K))}
    (hpar : IsParabolic2 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsDelta5Group ↥(perfectCore Pa) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  refine not_isDelta5_perfectCore_parabolic hU hres (fun j h => ?_) hpar hne
  exact not_isDelta5_perfectCore_Q2 hf hf2 j
    (h.of_equiv (perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)).symm)

end Sp4

theorem not_isDelta5_perfectCore_sp4 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : IsPSp4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsDelta5Group ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isDelta5_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  exact not_isDelta5_perfectCore_of_equiv e
    (not_isDelta5_perfectCore_of_projSp4 hcard hf (isParabolic2_top_map_equiv e hpa)
      (map_ne_top_of_equiv e hna))

end CFSG.QuasithinUnique.A5.G3
