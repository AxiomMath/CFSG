module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (diagGL coe_diagGL det_diagGL
  exists_elemAbelian_four_projDiag)
open CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem (four_le_pRank_four_of_rotGL)
open CFSG.LieType.Universal.Unitary (SU mem_SU conjTr antidiag)

section Tools

theorem four_le_pRank_of_elemAbelian {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
  CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

theorem four_le_pRank_statedProj_conj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {H : Subgroup (GL ι K)} (P : GL ι K) {x y z w : GL ι K}
    (hxH : P * x * P⁻¹ ∈ H) (hyH : P * y * P⁻¹ ∈ H) (hzH : P * z * P⁻¹ ∈ H)
    (hwH : P * w * P⁻¹ ∈ H) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) (hw : w ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hxw : Commute x w)
    (hyw : Commute y w) (hzw : Commute z w) (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y)
    (hz1 : ∀ n m : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * c ≠ z)
    (hw1 : ∀ n m l : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * z ^ l * c ≠ w) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : GL ι K ≃* GL ι K := MulAut.conj P with hφ
  have hS : ∀ c ∈ StatedScalars ι K, φ.symm c ∈ StatedScalars ι K := fun c hc => by
    have := (StatedScalars.normal ι K).conj_mem c hc P⁻¹
    simpa [hφ, MulAut.conj_symm_apply] using this
  have hpow : ∀ g : GL ι K, g ^ 3 = 1 → φ g ^ 3 = 1 := fun g hg => by rw [← map_pow, hg, map_one]
  refine CFSG.HardMathSupport.Timmesfeld.DFour.four_le_pRank_statedProj (x := φ x) (y := φ y)
    (z := φ z) (w := φ w) hxH hyH hzH hwH (hpow x hx) (hpow y hy) (hpow z hz) (hpow w hw)
    (hxy.map φ) (hxz.map φ) (hyz.map φ) (hxw.map φ) (hyw.map φ) (hzw.map φ) ?_ ?_ ?_ ?_
  · intro h
    exact hx1 (by simpa using hS _ h)
  · intro n c hc h
    refine hy1 n _ (hS c hc) (φ.injective ?_)
    rw [map_mul, map_pow, MulEquiv.apply_symm_apply, h]
  · intro n m c hc h
    refine hz1 n m _ (hS c hc) (φ.injective ?_)
    rw [map_mul, map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, h]
  · intro n m l c hc h
    refine hw1 n m l _ (hS c hc) (φ.injective ?_)
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, MulEquiv.apply_symm_apply, h]

theorem diagGL_mul_scalar_ne {F : Type} [Field F] {n : ℕ} {u v : Fin n → Fˣ}
    {c : GL (Fin n) F} (hc : c ∈ StatedScalars (Fin n) F) {i j : Fin n} (hu : u i = u j)
    (hv : v i ≠ v j) : diagGL n u * c ≠ diagGL n v := by
  obtain ⟨s, rfl⟩ := hc
  intro h
  have key : ∀ k, (u k : F) * s = v k := fun k => by
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) k k) h
    simpa [coe_diagGL, Matrix.scalar_apply] using this
  exact hv (Units.ext (by rw [← key i, ← key j, hu]))

end Tools

section Linear

theorem four_le_pRank_projSL_of_dvd {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 5 ≤ n)
    (h1 : 3 ∣ Nat.card F - 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n F))) := by
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_four_projDiag Nat.prime_three hn (by omega) hω
    (StatedSL n F) (fun u _ _ hprod => by
      rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod,
        Units.val_one])
  exact four_le_pRank_of_elemAbelian hE hEcard

theorem four_le_pRank_projSL_of_eight_le {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 8 ≤ n) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n F))) :=
  four_le_pRank_four_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (CFSG.SectionRank.ClassicalEven.det_rotMatrix _ _)

theorem four_le_pRank_projSp_of_four_le {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 4 ≤ n) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n F))) :=
  four_le_pRank_four_of_rotGL ((Fin.castLE_injective hn).sumMap (Fin.castLE_injective hn))
    fun _ => Subgroup.subset_closure
      (CFSG.SectionRank.ClassicalEven.rotMatrix_inl_inr_symplectic _)

theorem four_le_pRank_projSU_of_dvd_add {L : Type} [Field L] [Finite L] {n q : ℕ}
    (hL : Nat.card L = q ^ 2) (hn : 5 ≤ n) (h1 : 3 ∣ q + 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n q L))) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := L)
    rw [hL] at this
    norm_num at this
  have hdvd : 3 ∣ Nat.card L - 1 := by
    rw [hL, show q ^ 2 - 1 = q ^ 2 - 1 ^ 2 by norm_num, Nat.pow_two_sub_pow_two]
    exact h1.mul_right _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) 3 (by rwa [Nat.card_units])
  obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_four_projDiag Nat.prime_three hn (by omega) hω
    (StatedSU n q L) (fun u hu _ hprod =>
      CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.PSUThree.diagGL_mem hq0 u
        (fun i => orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_of_mem_zpowers (hu i)).trans (hω ▸ h1))) hprod)
  exact four_le_pRank_of_elemAbelian hE hEcard

end Linear

section UnitaryMinus

variable {F : Type} [Field F]

theorem diagGL_mem_SU (σ : F ≃+* F) {n : ℕ} (u : Fin n → Fˣ) (hprod : ∏ i, u i = 1)
    (hu : ∀ i, σ (u i : F) * (u (Fin.rev i) : F) = 1) : diagGL n u ∈ SU σ n := by
  rw [mem_SU]
  refine ⟨by rw [det_diagGL, ← Units.coe_prod, hprod, Units.val_one], ?_⟩
  rw [coe_diagGL]
  ext i j
  simp only [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, antidiag, Matrix.of_apply]
  split_ifs with h
  · rw [h, mul_one, hu]
  · rw [mul_zero, zero_mul]

@[expose] def pairFun {n : ℕ} (ω : Fˣ) (k : Fin n) : Fin n → Fˣ :=
  Pi.mulSingle k ω * Pi.mulSingle (Fin.rev k) ω⁻¹

theorem pairFun_apply_self {n : ℕ} (ω : Fˣ) {k : Fin n} (hk : k ≠ Fin.rev k) :
    pairFun ω k k = ω := by
  simp [pairFun, Pi.mulSingle_apply, hk]

theorem pairFun_apply_rev {n : ℕ} (ω : Fˣ) {k : Fin n} (hk : k ≠ Fin.rev k) :
    pairFun ω k (Fin.rev k) = ω⁻¹ := by
  simp [pairFun, Pi.mulSingle_apply, Ne.symm hk]

theorem pairFun_apply_of_ne {n : ℕ} (ω : Fˣ) {k i : Fin n} (h1 : i ≠ k) (h2 : i ≠ Fin.rev k) :
    pairFun ω k i = 1 := by
  simp [pairFun, Pi.mulSingle_apply, h1, h2]

theorem pairFun_pow_three {n : ℕ} {ω : Fˣ} (hω : ω ^ 3 = 1) (k : Fin n) :
    pairFun ω k ^ 3 = 1 := by
  rw [pairFun, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, inv_pow, hω, inv_one,
    Pi.mulSingle_one, Pi.mulSingle_one, mul_one]

theorem diagGL_pairFun_mem_SU (σ : F ≃+* F) {n : ℕ} {ω : Fˣ} (hσ : σ (ω : F) = ω) {k : Fin n}
    (hk : k ≠ Fin.rev k) : diagGL n (pairFun ω k) ∈ SU σ n := by
  refine diagGL_mem_SU σ _ ?_ fun i => ?_
  · simp [pairFun, Finset.prod_mul_distrib]
  · by_cases h1 : i = k
    · subst h1
      rw [pairFun_apply_self ω hk, pairFun_apply_rev ω hk, hσ, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ ω.ne_zero]
    by_cases h2 : i = Fin.rev k
    · subst h2
      rw [pairFun_apply_rev ω hk, Fin.rev_rev, pairFun_apply_self ω hk, Units.val_inv_eq_inv_val,
        map_inv₀, hσ, inv_mul_cancel₀ ω.ne_zero]
    · have h3 : Fin.rev i ≠ k := fun h => h2 (by rw [← h, Fin.rev_rev])
      have h4 : Fin.rev i ≠ Fin.rev k := fun h => h1 (Fin.rev_injective h)
      rw [pairFun_apply_of_ne ω h1 h2, pairFun_apply_of_ne ω h3 h4, Units.val_one, map_one,
        one_mul]

variable [Finite F]

theorem four_le_pRank_projSU_of_dvd_sub {p f n : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hn : 8 ≤ n) (h1 : p ^ f % 3 = 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) F))) := by
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  have hmem : ∀ A ∈ SU (CFSG.LieType.BorelTits.unitaryInvolution F p f) n,
      P * A * P⁻¹ ∈ StatedSU n (p ^ f) F := fun A hA => by
    have h := (CFSG.LieType.Universal.Unitary.conjEquiv P hP ⟨A, hA⟩).2
    rw [CFSG.LieType.Universal.Unitary.coe_conjEquiv,
      CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n] at h
    exact h
  have hdvd : 3 ∣ Nat.card F - 1 := by
    obtain ⟨Q, hQ⟩ : ∃ Q, p ^ f = Q := ⟨_, rfl⟩
    rw [hF, hQ]
    rw [hQ] at h1
    have : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by
      rw [show Q ^ 2 - 1 = Q ^ 2 - 1 ^ 2 by norm_num, Nat.pow_two_sub_pow_two]
    rw [this]
    exact Dvd.dvd.mul_left (by omega) _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hσ : CFSG.LieType.BorelTits.unitaryInvolution F p f (ω : F) = ω := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    have h3 : p ^ f = 3 * (p ^ f / 3) + 1 := by omega
    rw [h3, pow_succ, pow_mul, ← Units.val_pow_eq_pow_val, hω3, Units.val_one, one_pow, one_mul]
  have hωinv : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel ω
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hω] at this
    norm_num at this
  set j : ℕ → Fin n := fun a => ⟨a % 4, by omega⟩ with hj
  have hjv : ∀ a, (j a).val = a % 4 := fun a => rfl
  have hrv : ∀ a, (Fin.rev (j a)).val = n - (a % 4 + 1) := fun a => by
    rw [Fin.val_rev, hjv]
  have hjr : ∀ a b, j a ≠ Fin.rev (j b) := fun a b h => by
    have := congrArg Fin.val h
    rw [hjv, hrv] at this
    omega
  have hjj : ∀ a b, a < 4 → b < 4 → a ≠ b → j a ≠ j b := fun a b ha hb hab h => by
    have := congrArg Fin.val h
    rw [hjv, hjv] at this
    omega
  have hrr : ∀ a b, a < 4 → b < 4 → a ≠ b → Fin.rev (j a) ≠ Fin.rev (j b) :=
    fun a b ha hb hab h => hjj a b ha hb hab (Fin.rev_injective h)
  set t : ℕ → GL (Fin n) F := fun a => diagGL n (pairFun ω (j a)) with ht
  have htmem : ∀ a, P * t a * P⁻¹ ∈ StatedSU n (p ^ f) F := fun a =>
    hmem _ (diagGL_pairFun_mem_SU _ hσ (hjr a a))
  have ht3 : ∀ a, t a ^ 3 = 1 := fun a => by
    rw [ht, ← map_pow, pairFun_pow_three hω3, map_one]
  have htc : ∀ a b, Commute (t a) (t b) := fun a b =>
    (Commute.all (pairFun ω (j a)) (pairFun ω (j b))).map (diagGL n)
  have hval : ∀ a b, a < 4 → b < 4 → a ≠ b → ∀ m : ℕ,
      (pairFun ω (j a) ^ m) (j b) = 1 ∧ (pairFun ω (j a) ^ m) (Fin.rev (j b)) = 1 :=
    fun a b ha hb hab m => by
      refine ⟨?_, ?_⟩
      · rw [Pi.pow_apply, pairFun_apply_of_ne ω (hjj b a hb ha (Ne.symm hab)) (hjr b a), one_pow]
      · rw [Pi.pow_apply, pairFun_apply_of_ne ω (fun h => hjr a b h.symm)
          (hrr b a hb ha (Ne.symm hab)), one_pow]
  have hnew : ∀ b, pairFun ω (j b) (j b) ≠ pairFun ω (j b) (Fin.rev (j b)) := fun b => by
    rw [pairFun_apply_self ω (hjr b b), pairFun_apply_rev ω (hjr b b)]
    exact hωinv
  refine four_le_pRank_statedProj_conj P (htmem 0) (htmem 1) (htmem 2) (htmem 3) (ht3 0)
    (ht3 1) (ht3 2) (ht3 3) (htc 0 1) (htc 0 2) (htc 1 2) (htc 0 3) (htc 1 3) (htc 2 3) ?_ ?_ ?_
    ?_
  · intro h
    refine diagGL_mul_scalar_ne (u := 1) h (i := j 0) (j := Fin.rev (j 0)) rfl (hnew 0) ?_
    rw [map_one, one_mul]
  · intro m c hc h
    refine diagGL_mul_scalar_ne (u := pairFun ω (j 0) ^ m) hc (i := j 1) (j := Fin.rev (j 1))
      ?_ (hnew 1) ?_
    · rw [(hval 0 1 (by norm_num) (by norm_num) (by norm_num) m).1,
        (hval 0 1 (by norm_num) (by norm_num) (by norm_num) m).2]
    · rw [map_pow]
      exact h
  · intro m l c hc h
    refine diagGL_mul_scalar_ne (u := pairFun ω (j 0) ^ m * pairFun ω (j 1) ^ l) hc (i := j 2)
      (j := Fin.rev (j 2)) ?_ (hnew 2) ?_
    · rw [Pi.mul_apply, Pi.mul_apply,
        (hval 0 2 (by norm_num) (by norm_num) (by norm_num) m).1,
        (hval 0 2 (by norm_num) (by norm_num) (by norm_num) m).2,
        (hval 1 2 (by norm_num) (by norm_num) (by norm_num) l).1,
        (hval 1 2 (by norm_num) (by norm_num) (by norm_num) l).2]
    · rw [map_mul, map_pow, map_pow]
      exact h
  · intro m l r c hc h
    refine diagGL_mul_scalar_ne
      (u := pairFun ω (j 0) ^ m * pairFun ω (j 1) ^ l * pairFun ω (j 2) ^ r) hc (i := j 3)
      (j := Fin.rev (j 3)) ?_ (hnew 3) ?_
    · rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply,
        (hval 0 3 (by norm_num) (by norm_num) (by norm_num) m).1,
        (hval 0 3 (by norm_num) (by norm_num) (by norm_num) m).2,
        (hval 1 3 (by norm_num) (by norm_num) (by norm_num) l).1,
        (hval 1 3 (by norm_num) (by norm_num) (by norm_num) l).2,
        (hval 2 3 (by norm_num) (by norm_num) (by norm_num) r).1,
        (hval 2 3 (by norm_num) (by norm_num) (by norm_num) r).2]
    · rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      exact h

end UnitaryMinus

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
