module

public import CFSG.ClassicalInvolution.AschTight.S19NIdx
public import CFSG.ClassicalInvolution.AschTight.S19LTrace
public import CFSG.ClassicalInvolution.AschTight.S19LU

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.GorensteinWalter
open scoped MatrixGroups

section Matrix

variable {F : Type} [Field F]

theorem trace_mul_self_sl2 (M : SL(2, F)) :
    Matrix.trace ((M : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F)) =
      Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) ^ 2 - 2 := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-2 : F) * hdet

theorem trace_eq_zero_of_mul_self_eq_neg_one (N : SL(2, F))
    (hN : (N : Matrix (Fin 2) (Fin 2) F) * (N : Matrix (Fin 2) (Fin 2) F) = -1) :
    Matrix.trace (N : Matrix (Fin 2) (Fin 2) F) = 0 := by
  have hdet : (N : Matrix (Fin 2) (Fin 2) F).det = 1 := N.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  have h00 := congrFun (congrFun hN 0) 0
  have h11 := congrFun (congrFun hN 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq] at h00 h11
  by_contra hne
  have ha : (N : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
    have : (N : Matrix (Fin 2) (Fin 2) F) 0 0 *
        ((N : Matrix (Fin 2) (Fin 2) F) 0 0 + (N : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination h00 + hdet
    exact (mul_eq_zero.mp this).resolve_right hne
  have hd : (N : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    have : (N : Matrix (Fin 2) (Fin 2) F) 1 1 *
        ((N : Matrix (Fin 2) (Fin 2) F) 0 0 + (N : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination h11 + hdet
    exact (mul_eq_zero.mp this).resolve_right hne
  exact hne (by rw [ha, hd, add_zero])

theorem trace_map_ringEquiv (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (A.map σ) = σ (Matrix.trace A) := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
  rfl

theorem false_of_trace_cube_eq (h2 : (2 : F) ≠ 0) (M : SL(2, F))
    (h4 : (M : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) *
      ((M : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F)) = -1)
    (hfix : Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) ^ 3 =
      Matrix.trace (M : Matrix (Fin 2) (Fin 2) F)) : False := by
  have hN := trace_eq_zero_of_mul_self_eq_neg_one (M * M)
    (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact h4)
  rw [Matrix.SpecialLinearGroup.coe_mul, trace_mul_self_sl2] at hN
  have h0 : Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) = 0 := by
    linear_combination hfix - Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) * hN
  rw [h0] at hN
  apply h2
  linear_combination -hN

end Matrix

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf {c : G} {N : ℕ} (hN : orderOf c = 2 ^ N) :
    IsPGroup 2 (Subgroup.zpowers c) :=
  IsPGroup.of_card (n := N) (by rw [Nat.card_zpowers, hN])

omit [Finite G] in
theorem pow_half_eq (hI : IsUniqueInvolution K z) {c : G} (hcK : c ∈ K) {N : ℕ}
    (hN : orderOf c = 2 ^ N) (h2 : 2 ≤ orderOf c) : c ^ (orderOf c / 2) = z := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, pow_zero] at hN
      omega
    · omega⟩
  have hhalf : orderOf c / 2 + orderOf c / 2 = orderOf c := by
    rw [hN, pow_succ]
    omega
  have hsq : c ^ (orderOf c / 2) * c ^ (orderOf c / 2) = 1 := by
    rw [← pow_add, hhalf, pow_orderOf_eq_one]
  have hne : c ^ (orderOf c / 2) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  exact (hI.unique _ (K.pow_mem hcK _) hsq).resolve_left hne

theorem slProj_eq_neg_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (hI : IsUniqueInvolution K z) :
    ((S1911.slProj K e ⟨z, hI.mem⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : S1911.slProj K e ⟨z, hI.mem⟩ ≠ 1 := by
    intro h
    rw [S1911.slProj_eq_one_iff] at h
    have hmem : z ∈ Subgroup.zpowers z ⊓ Asc77.oddCoreOf K := ⟨Subgroup.mem_zpowers z, h⟩
    have hz2 : orderOf z = 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one
    rw [S1916.inf_oddCoreOf_eq_bot (isPGroup_zpowers_of_orderOf hz2) K, Subgroup.mem_bot] at hmem
    exact hI.ne_one hmem
  have hz2 : S1911.slProj K e ⟨z, hI.mem⟩ ^ 2 = 1 := by
    rw [← map_pow, sq, show (⟨z, hI.mem⟩ : K) * ⟨z, hI.mem⟩ = 1 from Subtype.ext hI.sq, map_one]
  exact CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ hz2 hz1

theorem false_of_conj_eq_z_mul [IsSimpleGroup G] (hd : Sec19Data p f K z S W) {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyH : y ∈ sec19X K z ⊔ centralizerModOdd ⊤ K)
    {c₀ : G} (hc₀K : c₀ ∈ K) {N : ℕ} (hN : orderOf c₀ = 2 ^ N) (h8 : 8 ≤ orderOf c₀)
    (hor : y * c₀ * y⁻¹ = z * c₀ ∨ y * c₀ * y⁻¹ = z * c₀⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD hd.tight
  let n : Subgroup.normalizer (K : Set G) := ⟨y, hyN⟩
  have hfield : (normalizerToPGammaL2Mod e hFcard hF h3 n).right = 1 := by
    obtain ⟨g, hg⟩ := (S1916.psi_mem_iff hd e hFcard hF h3 n).mpr hyH
    rw [← hg]
    rfl
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p f) p]; exact hd.tight.branch.odd)
  obtain ⟨g, hg⟩ := S1911.exists_semilinHom_of_mem e hFcard hF h3 n
  rw [hfield] at hg
  obtain ⟨ε, hε, hyε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ y * c₀ * y⁻¹ = z * c₀ ^ ε := by
    rcases hor with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, zpow_one]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, zpow_neg_one]⟩
  set M := S1911.slProj K e ⟨c₀, hc₀K⟩ with hM
  have hbM : S1911.slAut K e n M = S1911.slProj K e ⟨z, hI.mem⟩ * M ^ ε := by
    rw [hM, S1911.slAut_slProj, ← map_zpow, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    exact hyε
  rw [hg] at hbM
  have hmat := congrArg
    (fun A : SL(2, GaloisField p f) => (A : Matrix (Fin 2) (Fin 2) (GaloisField p f))) hbM
  simp only [coe_semilinHom, Matrix.SpecialLinearGroup.coe_mul, slProj_eq_neg_one h2 e hI,
    neg_one_mul] at hmat
  have hmap : (M : Matrix (Fin 2) (Fin 2) (GaloisField p f)).map
      ((1 : GaloisField p f ≃+* GaloisField p f) : GaloisField p f → GaloisField p f) =
        (M : Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
    ext i j
    rfl
  rw [hmap] at hmat
  have hsq := S19L.mul_self_eq_neg_one_of_conj h2 g M hε hmat
  have hcc : S1911.slProj K e (⟨c₀, hc₀K⟩ * ⟨c₀, hc₀K⟩) = S1911.slProj K e ⟨z, hI.mem⟩ := by
    apply Subtype.ext
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hsq, slProj_eq_neg_one h2 e hI]
  have h1 : S1911.slProj K e (⟨c₀, hc₀K⟩ * ⟨c₀, hc₀K⟩ * (⟨z, hI.mem⟩ : K)⁻¹) = 1 := by
    rw [map_mul, hcc, map_inv, mul_inv_cancel]
  rw [S1911.slProj_eq_one_iff] at h1
  have hz : z ∈ Subgroup.zpowers c₀ := by
    rw [← pow_half_eq hI hc₀K hN (by omega)]
    exact Subgroup.npow_mem_zpowers _ _
  have hmem : c₀ * c₀ * z⁻¹ ∈ Subgroup.zpowers c₀ ⊓ Asc77.oddCoreOf K :=
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
      (Subgroup.inv_mem _ hz), h1⟩
  rw [S1916.inf_oddCoreOf_eq_bot (isPGroup_zpowers_of_orderOf hN) K, Subgroup.mem_bot] at hmem
  have hcz : c₀ * c₀ = z := by
    calc c₀ * c₀ = c₀ * c₀ * z⁻¹ * z := by group
      _ = z := by rw [hmem, one_mul]
  have hc4 : c₀ ^ 4 = 1 := by
    calc c₀ ^ 4 = (c₀ * c₀) * (c₀ * c₀) := by
          rw [pow_succ, pow_succ, pow_succ, pow_one]
          group
      _ = 1 := by rw [hcz, hI.sq]
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc4)
  omega

theorem zpow_of_mem [IsSimpleGroup G] (hd : Sec19Data p f K z S W) {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hy2 : y * y = 1)
    (hyH : y ∈ sec19X K z ⊔ centralizerModOdd ⊤ K) {c₀ : G} (hc₀K : c₀ ∈ K) {N : ℕ}
    (hN : orderOf c₀ = 2 ^ N) (h8 : 8 ≤ orderOf c₀)
    (hyc : y * c₀ * y⁻¹ ∈ Subgroup.zpowers c₀) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ Subgroup.zpowers c₀, y * x * y⁻¹ = x ^ ε := by
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hcases : y * c₀ * y⁻¹ = c₀ ∨ y * c₀ * y⁻¹ = c₀⁻¹ := by
    by_contra hne
    push Not at hne
    obtain ⟨-, hor⟩ := S19L.conj_eq_z_mul_or hN (by omega) hyc hy2 hne.1 hne.2
    rw [pow_half_eq hI hc₀K hN (by omega)] at hor
    exact false_of_conj_eq_z_mul hd hyN hyH hc₀K hN h8 hor
  rcases hcases with h | h
  · refine ⟨1, Or.inl rfl, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, h, zpow_one]
  · refine ⟨-1, Or.inr rfl, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, h, inv_zpow, zpow_neg_one]

theorem mem_of_zpow [IsSimpleGroup G] (hd : Sec19Data p f K z S W) (hq : p ^ f = 9) {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) {c₀ : G} (hc₀K : c₀ ∈ K) {N : ℕ}
    (hN : orderOf c₀ = 2 ^ N) (h8 : 8 ≤ orderOf c₀) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hyε : ∀ x ∈ Subgroup.zpowers c₀, y * x * y⁻¹ = x ^ ε) :
    y ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  by_contra hyH
  obtain ⟨rfl, rfl⟩ := eq_three_two Fact.out hq
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD hd.tight
  let n : Subgroup.normalizer (K : Set G) := ⟨y, hyN⟩
  have hfield : (normalizerToPGammaL2Mod e hFcard hF h3 n).right ≠ 1 := fun h =>
    hyH ((S1916.psi_mem_iff hd e hFcard hF h3 n).mp (mem_range_inl_of_right_eq_one h))
  have hfrob := eq_frobenius_of_ne_one hfield
  have h2 : (2 : GaloisField 3 2) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField 3 2) 3]; norm_num)
  obtain ⟨g, hg⟩ := S1911.exists_semilinHom_of_mem e hFcard hF h3 n
  have hN3 : 3 ≤ N := by
    by_contra h
    have : 2 ^ N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ : 8 ∣ orderOf c₀ := by
    rw [hN, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.pow_dvd_pow 2 hN3
  have hc4 : (c₀ ^ k) ^ 4 = z := by
    rw [← pow_mul, ← pow_half_eq hI hc₀K hN (by omega)]
    congr 1
    omega
  have hcK : c₀ ^ k ∈ K := K.pow_mem hc₀K k
  have hyc : y * c₀ ^ k * y⁻¹ = (c₀ ^ k) ^ ε := hyε _ (Subgroup.npow_mem_zpowers c₀ k)
  set M := S1911.slProj K e ⟨c₀ ^ k, hcK⟩ with hM
  have hbM : S1911.slAut K e n M = M ^ ε := by
    rw [hM, S1911.slAut_slProj, ← map_zpow]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    exact hyc
  rw [hg] at hbM
  have htr := congrArg
    (fun A : SL(2, GaloisField 3 2) =>
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) hbM
  simp only [coe_semilinHom, Matrix.trace_units_conj, trace_map_ringEquiv] at htr
  have hinv : Matrix.trace ((M ^ ε : SL(2, GaloisField 3 2)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) =
        Matrix.trace (M : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) := by
    rcases hε with rfl | rfl
    · rw [zpow_one]
    · rw [zpow_neg_one, S19L.trace_inv_sl2]
  rw [hinv, hfrob] at htr
  have h4 : (M : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) *
      (M : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) *
        ((M : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) *
          (M : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) = -1 := by
    have hpow : M * M * (M * M) = S1911.slProj K e ⟨z, hI.mem⟩ := by
      rw [hM, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change c₀ ^ k * c₀ ^ k * (c₀ ^ k * c₀ ^ k) = z
      rw [← hc4]
      group
    rw [← slProj_eq_neg_one h2 e hI, ← hpow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
  exact false_of_trace_cube_eq h2 M h4 htr

omit [Finite G] in
theorem conj_inv_zpow (c x : G) (k : ℤ) : (c⁻¹ * x * c) ^ k = c⁻¹ * x ^ k * c := by
  simpa using (conj_zpow (a := c⁻¹) (b := x) (i := k))

theorem mem_of_zpow_conj [IsSimpleGroup G] (hd : Sec19Data p f K z S W) (hq : p ^ f = 9)
    {c y : G} (hyN : y ∈ Subgroup.normalizer ((conjSub c K : Subgroup G) : Set G)) {c₀ : G}
    (hc₀K : c₀ ∈ conjSub c K) {N : ℕ} (hN : orderOf c₀ = 2 ^ N) (h8 : 8 ≤ orderOf c₀) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hyε : ∀ x ∈ Subgroup.zpowers c₀, y * x * y⁻¹ = x ^ ε) :
    c⁻¹ * y * c ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  have hord : orderOf (c⁻¹ * c₀ * c) = orderOf c₀ := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) c₀
    rwa [MulAut.conj_apply, inv_inv] at this
  refine mem_of_zpow hd hq ?_ (mem_conjSub_iff.mp hc₀K) (hord.trans hN) (hord ▸ h8) hε ?_
  · rw [mem_normalizer_iff_conjSub_eq] at hyN ⊢
    rw [conjSub_mul, conjSub_mul, hyN, conjSub_inv_conjSub]
  · intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 := hyε (c₀ ^ k) (Subgroup.zpow_mem_zpowers c₀ k)
    rw [conj_inv_zpow c c₀ k]
    calc c⁻¹ * y * c * (c⁻¹ * c₀ ^ k * c) * (c⁻¹ * y * c)⁻¹ =
        c⁻¹ * (y * c₀ ^ k * y⁻¹) * c := by group
      _ = c⁻¹ * (c₀ ^ k) ^ ε * c := by rw [h1]
      _ = (c⁻¹ * c₀ ^ k * c) ^ ε := (conj_inv_zpow c _ ε).symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N
