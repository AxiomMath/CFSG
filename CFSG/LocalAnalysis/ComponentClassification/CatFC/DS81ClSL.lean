module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClCore
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSL
public import CFSG.Walter.Cited.OddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic

public section

namespace CFSG.ComponentClassification.CatFC.DS81.ClSL

open Matrix Subgroup CFSG.Open CFSG.ComponentClassification.CatFC.DS81.ClLift

variable {n : ℕ} {K : Type} [Field K]

theorem exists_diag_commute_ggInvSL (n l : ℕ) (hn : 3 ≤ n) (hl : 1 ≤ l) (hl2 : 2 * l ≤ n)
    (w : Kˣ) (hw : orderOf w = 89) :
    ∃ D : Matrix.SpecialLinearGroup (Fin n) K, Commute D (CFSG.StandardType.ggInvSL n l K) ∧
      D ^ 89 = 1 ∧ ∀ c : K, (D : Matrix (Fin n) (Fin n) K) ≠ Matrix.scalar (Fin n) c := by
  classical
  obtain ⟨i0, i1, j0, j1, hpair, hi0, hj0⟩ : ∃ i0 i1 j0 j1 : Fin n,
      (∀ a b : Fin n, (b : ℕ) < l → (a : ℕ) = b + (n - l) → (b : ℕ) < a →
        (((if a = i0 then (1 : ℤ) else 0) + (if a = i1 then 1 else 0)
          - (if a = j0 then 1 else 0) - (if a = j1 then 1 else 0)) =
         ((if b = i0 then (1 : ℤ) else 0) + (if b = i1 then 1 else 0)
          - (if b = j0 then 1 else 0) - (if b = j1 then 1 else 0)))) ∧
      ((if i0 = i0 then (1 : ℤ) else 0) + (if i0 = i1 then 1 else 0)
          - (if i0 = j0 then 1 else 0) - (if i0 = j1 then 1 else 0)) = 1 ∧
      (((if j0 = i0 then (1 : ℤ) else 0) + (if j0 = i1 then 1 else 0)
          - (if j0 = j0 then 1 else 0) - (if j0 = j1 then 1 else 0)) = -1 ∨
       ((if j0 = i0 then (1 : ℤ) else 0) + (if j0 = i1 then 1 else 0)
          - (if j0 = j0 then 1 else 0) - (if j0 = j1 then 1 else 0)) = -2) := by
    by_cases h : 2 * l < n
    · refine ⟨⟨0, by omega⟩, ⟨n - l, by omega⟩, ⟨l, by omega⟩, ⟨l, by omega⟩, ?_, ?_, ?_⟩
      · intro a b hb ha hab
        simp only [Fin.ext_iff]
        split_ifs <;> omega
      · simp only [Fin.ext_iff]; split_ifs <;> omega
      · right; simp only [Fin.ext_iff]; split_ifs <;> omega
    · have hl2' : 2 ≤ l := by omega
      refine ⟨⟨0, by omega⟩, ⟨l, by omega⟩, ⟨1, by omega⟩, ⟨l + 1, by omega⟩, ?_, ?_, ?_⟩
      · intro a b hb ha hab
        simp only [Fin.ext_iff, Fin.val_mk]
        split_ifs <;> omega
      · have h1 : (0 : ℕ) ≠ l := by omega
        have h2 : (0 : ℕ) ≠ l + 1 := by omega
        simp [Fin.ext_iff, h1, h2]
      · left
        have h1 : (1 : ℕ) ≠ l := by omega
        have h2 : (1 : ℕ) ≠ l + 1 := by omega
        have h3 : l ≠ 0 := by omega
        simp [Fin.ext_iff, h1, h2, h3]
  set e : Fin n → ℤ := fun i => (if i = i0 then (1 : ℤ) else 0) + (if i = i1 then 1 else 0)
    - (if i = j0 then 1 else 0) - (if i = j1 then 1 else 0) with he
  have hsum : ∑ i, e i = 0 := by
    simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    norm_num
  have hprod : ∀ s : Finset (Fin n), ∏ i ∈ s, w ^ e i = w ^ (∑ i ∈ s, e i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, _root_.zpow_add, ih]
  have hw89 : w ^ 89 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  let Dm : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => ((w ^ e i : Kˣ) : K)
  have hdet : Dm.det = 1 := by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hprod, hsum, zpow_zero, Units.val_one]
  refine ⟨⟨Dm, hdet⟩, ?_, ?_, ?_⟩
  ·
    refine Subtype.ext ?_
    change Dm * CFSG.StandardType.ggInvMatrix n l K = CFSG.StandardType.ggInvMatrix n l K * Dm
    simp only [CFSG.StandardType.ggInvMatrix, mul_add, add_mul, mul_one, one_mul]
    congr 1
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, CFSG.StandardType.ggInvNil_apply]
    split_ifs with hab
    · obtain ⟨hb, ha, hba⟩ := hab
      rw [show e a = e b from hpair a b hb ha hba]
      ring
    · simp
  ·
    refine Subtype.ext ?_
    show (Matrix.diagonal fun i => ((w ^ e i : Kˣ) : K)) ^ 89 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hw89, _root_.one_zpow, Units.val_one]
  ·
    intro c hc
    have h1 : Dm i0 i0 = Dm j0 j0 := by
      have := congrFun (congrFun hc i0) i0
      have := congrFun (congrFun hc j0) j0
      simp_all [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    simp only [Dm, Matrix.diagonal_apply_eq] at h1
    have h2 : w ^ e i0 = w ^ e j0 := Units.ext h1
    rw [zpow_eq_zpow_iff_modEq, hw] at h2
    have he0 : e i0 = 1 := hi0
    have hej : e j0 = -1 ∨ e j0 = -2 := hj0
    rw [he0] at h2
    rcases hej with h | h <;> rw [h] at h2 <;> revert h2 <;> decide

theorem odd_card_statedScalars_subgroupOf [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (H : Subgroup (GL ι K)) :
    Odd (Nat.card ((StatedScalars ι K).subgroupOf H)) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hz⟩, hzord⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 h)
  rw [Subgroup.orderOf_mk] at hzord
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzord, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzord
    omega
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨u, hu⟩ := hz
  have hzm : ((z : GL ι K) : Matrix ι ι K) = Matrix.scalar ι (u : K) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have huu : (u : K) * u = 1 := by
    have h1 := congrArg (fun y : H => ((y : GL ι K) : Matrix ι ι K) i₀ i₀) hz2
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, hzm] at h1
    simpa [Matrix.scalar_apply] using h1
  have hu1 : (u : K) = 1 := by
    rcases mul_self_eq_one_iff.1 huu with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  apply hz1
  apply Subtype.ext
  apply Units.ext
  rw [hzm, hu1]
  simp

theorem eightynine_dvd_card_centralizer_of_not_dvd [Finite K] [CharP K 2]
    (hK : ¬ 89 ∣ Nat.card K - 1) (τ : StatedProj (StatedSL n K)) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSL n K))))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSL n K)))) := by
  classical
  obtain ⟨th, rfl⟩ := QuotientGroup.mk_surjective τ
  have hτ2 : (QuotientGroup.mk th : StatedProj (StatedSL n K)) ^ 2 = 1 := by
    rw [← hτ]; exact pow_orderOf_eq_one _
  obtain ⟨yh, b, hyb, hy1, hc⟩ := exists_commuting_pow_lift th hτ2 h23
  set g : Matrix (Fin n) (Fin n) K :=
    (((yh : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hg
  have hgb : g ^ (23 ^ b) = 1 := (pow_eq_one_iff_matrix yh _).mp hyb
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    rw [(matrix_eq_one_iff yh).mp h, QuotientGroup.mk_one]
  obtain ⟨zM, hzR, hdet, hz89, hzs⟩ := ClCore.exists_det_one_order_eightynine hK g hgb hg1
  let zU : GL (Fin n) K := glOfPow89 zM hz89
  have hzU : (zU : Matrix (Fin n) (Fin n) K) = zM := rfl
  let zh : StatedSL n K := ⟨zU, StatedAPI.mem_statedSL_iff.mpr (by rw [hzU]; exact hdet)⟩
  have hzh : (((zh : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = zM := rfl
  have hcm : Commute ((((th : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) g :=
    (commute_iff_matrix th yh).mp hc
  have hcz : Commute zM ((((th : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hzR hcm).symm
  have hzth : Commute th zh := by
    rw [commute_iff_matrix, hzh]
    exact hcz.symm
  have hzh89 : zh ^ 89 = 1 := (pow_eq_one_iff_matrix zh 89).mpr (by rw [hzh]; exact hz89)
  have hzne : (QuotientGroup.mk zh : StatedProj (StatedSL n K)) ≠ 1 := by
    apply mk_ne_one_of_not_scalar
    intro c hcM
    rw [hzh] at hcM
    exact hzs c hcM
  exact eightynine_dvd_of_commute th zh hzth hzh89 hzne

theorem eightynine_dvd_card_centralizer_of_dvd [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hK : 89 ∣ Nat.card K - 1) (τ : StatedProj (StatedSL n K)) (hτ : orderOf τ = 2) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSL n K)))) := by
  classical
  set C := centralizer ({τ} : Set (StatedProj (StatedSL n K)))
  set N := (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hNodd : Odd (Nat.card N) := odd_card_statedScalars_subgroupOf _
  obtain ⟨t, ht2, htτ⟩ := CFSG.Walter.Suzuki.exists_orderOf_eq_two_mk_eq N hNodd hτ
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
  set tS := e.symm t with htS
  have htS2 : orderOf tS = 2 := by rw [htS, MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨l, hl1, hl2, a, ha⟩ := CFSG.StandardType.ggSLInvolutionClassInput K n tS htS2
  have hKu : 89 ∣ Nat.card Kˣ := by
    have := Fintype.ofFinite K
    rwa [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card]
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 89 hKu
  obtain ⟨D, hDc, hD89, hDs⟩ := exists_diag_commute_ggInvSL n l hn hl1 hl2 w hw
  set zS := a * D * a⁻¹ with hzS
  have hzSt : Commute zS tS := by
    rw [ha, hzS]
    have := hDc.eq
    show a * D * a⁻¹ * (a * CFSG.StandardType.ggInvSL n l K * a⁻¹) =
      a * CFSG.StandardType.ggInvSL n l K * a⁻¹ * (a * D * a⁻¹)
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc D, this, mul_assoc]
  have hzS89 : zS ^ 89 = 1 := by
    rw [hzS, conj_pow, hD89, mul_one, mul_inv_cancel]
  set zh := e zS with hzh
  have hzht : Commute zh t := by
    have h1 : e tS = t := by rw [htS, MulEquiv.apply_symm_apply]
    rw [hzh, ← h1]
    exact hzSt.map e
  set z : StatedProj (StatedSL n K) := QuotientGroup.mk zh with hz
  have hz89' : z ^ 89 = 1 := by
    rw [hz, ← QuotientGroup.mk_pow, hzh, ← map_pow, hzS89, map_one, QuotientGroup.mk_one]
  have hz1' : z ≠ 1 := by
    intro h
    rw [hz, QuotientGroup.eq_one_iff] at h
    obtain ⟨c, hc⟩ : (zh : GL (Fin n) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin n)).range := h
    have h1 : ((zS : Matrix (Fin n) (Fin n) K)) = Matrix.scalar (Fin n) (c : K) := by
      rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K zS]
      have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
      simpa [Matrix.GeneralLinearGroup.coe_scalar, hzh] using this.symm
    apply hDs (c : K)
    have h2 : (D : Matrix (Fin n) (Fin n) K) =
        ((a⁻¹ * zS * a : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
      rw [hzS]; simp [mul_assoc]
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1,
      ← Matrix.scalar_commute (c : K) (fun _ => Commute.all _ _) ((a⁻¹ : Matrix.SpecialLinearGroup
        (Fin n) K) : Matrix (Fin n) (Fin n) K), Matrix.mul_assoc]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_one]
  have hzo : orderOf z = 89 := orderOf_eq_prime hz89' hz1'
  have hzC : z ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff, hz, ← htτ, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hzht.eq]
  have := orderOf_dvd_natCard (⟨z, hzC⟩ : ↥C)
  rwa [Subgroup.orderOf_mk, hzo] at this

theorem ggInvMatrix_two_one : CFSG.StandardType.ggInvMatrix 2 1 K = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.StandardType.ggInvMatrix, CFSG.StandardType.ggInvNil_apply]

theorem sq_eq_one_of_commute_ggInvSL_two [CharP K 2] (B : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : Commute B (CFSG.StandardType.ggInvSL 2 1 K)) : B ^ 2 = 1 := by
  have hm := congrArg
    (fun X : Matrix.SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K))
    h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.StandardType.coe_ggInvSL,
    ggInvMatrix_two_one] at hm
  have hdet := B.2
  set M := (B : Matrix (Fin 2) (Fin 2) K) with hM
  rw [Matrix.eta_fin_two M] at hm hdet
  simp only [Matrix.mul_fin_two, Matrix.det_fin_two_of] at hm hdet
  have h01 : M 0 1 = 0 := by
    have := congrFun (congrFun hm 0) 0
    simp at this; exact this
  have h11 : M 1 1 = M 0 0 := by
    have := congrFun (congrFun hm 1) 0
    simp at this; linear_combination this
  have h00 : M 0 0 = 1 := by
    rw [h01, h11, zero_mul, sub_zero] at hdet
    have : M 0 0 ^ 2 = 1 ^ 2 := by rw [one_pow, sq]; exact hdet
    exact frobenius_inj K 2 this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hM,
    Matrix.eta_fin_two M, sq, Matrix.mul_fin_two, h01, h11, h00]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← two_mul, CharTwo.two_eq_zero]

theorem not_twentythree_dvd_card_centralizer_two [Finite K] [CharP K 2]
    (τ : StatedProj (StatedSL 2 K)) (hτ : orderOf τ = 2) :
    ¬ 23 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSL 2 K)))) := by
  classical
  intro h23
  haveI : Nonempty (Fin 2) := ⟨0⟩
  set N := (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K)
  have hNodd : Odd (Nat.card N) := odd_card_statedScalars_subgroupOf _
  obtain ⟨t, ht2, htτ⟩ := CFSG.Walter.Suzuki.exists_orderOf_eq_two_mk_eq N hNodd hτ
  have hτ2 : (QuotientGroup.mk t : StatedProj (StatedSL 2 K)) ^ 2 = 1 := by
    rw [htτ]; have := pow_orderOf_eq_one τ; rwa [hτ] at this
  have h23' : 23 ∣ Nat.card ↥(centralizer ({(QuotientGroup.mk t : StatedProj (StatedSL 2 K))} :
      Set (StatedProj (StatedSL 2 K)))) := by rw [htτ]; exact h23
  obtain ⟨yh, b, hyhb, hy1, hcomm⟩ := exists_commuting_pow_lift t hτ2 h23'
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  have htS2 : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨l, hl1, hl2, a, ha⟩ := CFSG.StandardType.ggSLInvolutionClassInput K 2 (e.symm t) htS2
  have hl : l = 1 := by omega
  subst hl
  set yS := e.symm yh with hyS
  have hcS : Commute (e.symm t) yS := hcomm.map e.symm
  have hB : Commute (a⁻¹ * yS * a) (CFSG.StandardType.ggInvSL 2 1 K) := by
    rw [ha] at hcS
    have h := (hcS.map (MulAut.conj a⁻¹)).symm
    simp only [MulAut.conj_apply, inv_inv] at h
    rwa [show a⁻¹ * (a * CFSG.StandardType.ggInvSL 2 1 K * a⁻¹) * a =
      CFSG.StandardType.ggInvSL 2 1 K by group] at h
  have hB2 := sq_eq_one_of_commute_ggInvSL_two (a⁻¹ * yS * a) hB
  have hyS2 : yS ^ 2 = 1 := by
    have : yS = a * (a⁻¹ * yS * a) * a⁻¹ := by group
    rw [this, conj_pow, hB2, mul_one, mul_inv_cancel]
  have hyh2 : yh ^ 2 = 1 := by
    have := congrArg e hyS2
    rwa [map_pow, hyS, MulEquiv.apply_symm_apply, map_one] at this
  have hyh1 : yh = 1 := by
    have h1 : orderOf yh ∣ 2 := orderOf_dvd_of_pow_eq_one hyh2
    have h2 : orderOf yh ∣ 23 ^ b := orderOf_dvd_of_pow_eq_one hyhb
    have hcop : Nat.Coprime 2 (23 ^ b) := Nat.Coprime.pow_right b (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  exact hy1 (by rw [hyh1, QuotientGroup.mk_one])

theorem eightynine_dvd_card_centralizer [Finite K] [CharP K 2] (hn : 2 ≤ n)
    (τ : StatedProj (StatedSL n K)) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSL n K))))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSL n K)))) := by
  by_cases hK : 89 ∣ Nat.card K - 1
  · rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact absurd h23 (not_twentythree_dvd_card_centralizer_two τ hτ)
    · exact eightynine_dvd_card_centralizer_of_dvd hn3 hK τ hτ
  · exact eightynine_dvd_card_centralizer_of_not_dvd hK τ hτ h23

theorem lie23To89_psl {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hm : StatedClassicalModel X .PSL n 2 f) (τ : X) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  obtain ⟨hadm, K, _, _, hcard, ⟨φ⟩⟩ := hm
  have hn : 2 ≤ n := hadm.2.2.1
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  rw [card_centralizer_eq φ τ] at h23 ⊢
  exact eightynine_dvd_card_centralizer hn (φ τ) (by rw [MulEquiv.orderOf_eq]; exact hτ) h23

end CFSG.ComponentClassification.CatFC.DS81.ClSL
