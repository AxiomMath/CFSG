module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.QuasithinUnique.Vol2Native.EvenWit

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven Matrix

theorem two_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
  CFSG.SectionRank.two_le_pRank_top_of_commute hx hy hxy hx1 hy1

theorem two_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : ∃ c ∈ StatedScalars ι K, x * y = c * (y * x))
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  have hcomm : Commute (π ⟨x, hxH⟩) (π ⟨y, hyH⟩) := by
    obtain ⟨c, hc, hcxy⟩ := hxy
    obtain ⟨u, rfl⟩ := hc
    change π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩
    rw [← map_mul, ← map_mul]
    change QuotientGroup.mk' N _ = QuotientGroup.mk' N _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    refine ⟨u⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcen : ∀ g : GL ι K, g * (GeneralLinearGroup.scalar ι u)⁻¹ =
        (GeneralLinearGroup.scalar ι u)⁻¹ * g := fun g => by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← GeneralLinearGroup.scalar_commute u g,
        inv_mul_cancel_left]
    have h1 : (x * y)⁻¹ * (y * x) = (GeneralLinearGroup.scalar ι u)⁻¹ := by
      rw [hcxy, _root_.mul_inv_rev, hcen, mul_assoc, inv_mul_cancel, mul_one]
    rw [h1, map_inv]
  refine two_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy) hcomm (fun h => hx1 ?_)
    (fun n h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)

theorem two_le_pRank_of_mulEquiv {S G : Type} [Group S] [Finite S] [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) (e : S ≃* G) (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)) :
    2 ≤ CFSG.pRank r S := by
  rw [pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact h

theorem two_le_pRank_three_of_rotGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {e : Fin 2 ⊕ Fin 2 → ι} (he : Function.Injective e)
    (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  have hcomm : Commute (rotGL (K := K) (e (.inl 0)) (e (.inr 0)))
      (rotGL (e (.inl 1)) (e (.inr 1))) :=
    rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))
  refine two_le_pRank_statedProj (hH 0) (hH 1) (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    ⟨1, one_mem _, by rw [one_mul]; exact hcomm.eq⟩
    (fun hx => mul_scalar_ne (g := 1) (hne _ _ (by decide)) (one_mulVec _)
      (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n c hc => mul_scalar_ne (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n)
      (rotMatrix_mulVec_left _ _) hc)

theorem two_le_pRank_three_psl {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
  two_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)

theorem two_le_pRank_three_psp {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) :=
  two_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).sumMap (Fin.castLE_injective hn))
    fun _ => Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _)

theorem exists_two_le_pRank_psl_of_four_le {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hn : 4 ≤ n) (hm : StatedClassicalModel S .PSL n 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
  exact ⟨3, Nat.prime_three, by norm_num,
    two_le_pRank_of_mulEquiv Nat.prime_three e (two_le_pRank_three_psl hn)⟩

theorem exists_two_le_pRank_psp_of_two_le {S : Type} [Group S] [Finite S] {n f : ℕ}
    (hn : 2 ≤ n) (hm : StatedClassicalModel S .PSp n 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
  exact ⟨3, Nat.prime_three, by norm_num,
    two_le_pRank_of_mulEquiv Nat.prime_three e (two_le_pRank_three_psp hn)⟩


theorem two_le_pRank_torus {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {H : Subgroup (GL ι K)} {r : ℕ} [Fact r.Prime] (hr3 : r ≠ 3) {ζ : Kˣ}
    (hζ : orderOf ζ = r) {i₀ i₁ i₂ : ι} (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (h₀ : torusDiag (torusVec ζ i₀ i₂) ∈ H) (h₁ : torusDiag (torusVec ζ i₁ i₂) ∈ H) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj H)) := by
  have hr : r.Prime := Fact.out
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hr.one_lt.ne hζ
  have hpow (j : ι) : torusDiag (torusVec ζ j i₂) ^ r = 1 := by
    rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
  have hcomm (a b : ι → Kˣ) : Commute (torusDiag a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  have hent {d d' : ι → Kˣ} (h : torusDiag d = torusDiag d') (i : ι) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine two_le_pRank_statedProj h₀ h₁ (hpow i₀) (hpow i₁)
    ⟨1, one_mem _, by rw [one_mul]; exact (hcomm _ _).eq⟩ ?_ ?_
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := hent hc i₀
    have e1 := hent hc i₁
    rw [torusVec_apply_left ζ h02] at e0
    rw [torusVec_apply_of_ne ζ h01.symm h12] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro n _ ⟨c, rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e0 := hent h i₀
    have e1 := hent h i₁
    have e2 := hent h i₂
    simp only [Pi.mul_apply, torusVec_apply_left _ h02, torusVec_apply_right _ h02,
      torusVec_apply_of_ne _ h01 h02, torusVec_apply_of_ne _ h01.symm h12,
      torusVec_apply_right _ h12, torusVec_apply_left _ h12, one_mul] at e0 e1 e2
    rw [e1] at e0 e2
    have hn : ζ ^ n = ζ⁻¹ := eq_inv_of_mul_eq_one_left e0
    rw [hn, inv_inv] at e2
    have h3 : ζ ^ 3 = 1 := by
      calc ζ ^ 3 = (ζ * ζ) * ζ := by rw [pow_succ, pow_two]
        _ = ζ⁻¹ * ζ := by rw [e2]
        _ = 1 := inv_mul_cancel ζ
    have hdvd : r ∣ 3 := hζ ▸ orderOf_dvd_of_pow_eq_one h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hdvd)

@[expose] def cycMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem cycMat_mul_transpose (K : Type) [Field K] : cycMat K * (cycMat K)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, mul_apply, Fin.sum_univ_succ]

theorem cycMat_transpose_mul (K : Type) [Field K] : (cycMat K)ᵀ * cycMat K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, mul_apply, Fin.sum_univ_succ]

@[expose] def cycGL (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨cycMat K, (cycMat K)ᵀ, cycMat_mul_transpose K, cycMat_transpose_mul K⟩

theorem coe_cycGL (K : Type) [Field K] : (cycGL K : Matrix (Fin 3) (Fin 3) K) = cycMat K :=
  rfl

theorem det_cycMat (K : Type) [Field K] : (cycMat K).det = 1 := by
  simp [cycMat, det_fin_three]

theorem cycMat_map_pow (K : Type) [Field K] {q : ℕ} (hq : q ≠ 0) :
    (cycMat K).map (· ^ q) = cycMat K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, zero_pow hq]

theorem cycGL_mem_SL (K : Type) [Field K] : cycGL K ∈ StatedSL 3 K :=
  Subgroup.subset_closure (det_cycMat K)

theorem cycGL_mem_SU (K : Type) [Field K] {q : ℕ} (hq : q ≠ 0) : cycGL K ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨det_cycMat K, ?_⟩
  rw [coe_cycGL, cycMat_map_pow K hq]
  exact cycMat_transpose_mul K

theorem two_le_pRank_three_of_cubic {K : Type} [Field K] [Finite K] {ζ : Kˣ}
    (hζ : orderOf ζ = 3) (H : Subgroup (GL (Fin 3) K))
    (haH : torusDiag ![ζ, ζ⁻¹, 1] ∈ H) (hbH : torusDiag ![1, ζ, ζ⁻¹] ∈ H) (hcH : cycGL K ∈ H) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have ha : ((torusDiag ![ζ, ζ⁻¹, 1] : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1] := by
    rw [coe_torusDiag]
    congr 1
    funext i
    fin_cases i <;> simp
  have hb : ((torusDiag ![1, ζ, ζ⁻¹] : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, (ζ : K), ((ζ⁻¹ : Kˣ) : K)] := by
    rw [coe_torusDiag]
    congr 1
    funext i
    fin_cases i <;> simp
  have hC : ∀ x ∈ (StatedScalars (Fin 3) K).subgroupOf H, ∃ r : K,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) r := by
    intro x hx
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 hx
    refine ⟨(u : K), ?_⟩
    rw [← hu, GeneralLinearGroup.coe_scalar]
  obtain ⟨E, hE, hcard⟩ := RankThree.Chevalley.cubic_monomial_scalar_quotient_has_elementary_nine hζ
    H ha hb (coe_cycGL K) haH hbH hcH ((StatedScalars (Fin 3) K).subgroupOf H) hC
  exact le_pRank (by norm_num) le_top ((isElementaryAbelian_iff_isElemAbelian 3 E).1 hE)
    (k := 2) (by rw [hcard]; norm_num)

theorem two_pow_even_mod (k : ℕ) : 2 ^ (2 * k) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_odd_mod (k : ℕ) : 2 ^ (2 * k + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_two_le_pRank_psl_three_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hm : StatedClassicalModel S .PSL 3 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hKu : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' f
  ·
    have h3 : 3 ∣ Nat.card Kˣ := by
      rw [hKu]
      have := two_pow_even_mod k
      rw [← hk] at this
      have : 0 < 2 ^ f := by positivity
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
    refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_mulEquiv Nat.prime_three e ?_⟩
    exact two_le_pRank_three_of_cubic hζ (StatedSL 3 K)
      (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
      (torusDiag_mem_SL (by simp [Fin.prod_univ_three])) (cycGL_mem_SL K)
  ·
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmod : 2 ^ f % 3 = 2 := by rw [hk]; exact two_pow_odd_mod k
    have hodd : (2 ^ f - 1) % 2 = 1 := by
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    have hr : (2 ^ f - 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hr2 : (2 ^ f - 1).minFac ≠ 2 := fun h => by
      have h' := Nat.minFac_dvd (2 ^ f - 1)
      rw [h] at h'
      omega
    have hr3 : (2 ^ f - 1).minFac ≠ 3 := fun h => by
      have h' := Nat.minFac_dvd (2 ^ f - 1)
      rw [h] at h'
      omega
    have := Fact.mk hr
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (2 ^ f - 1).minFac
      (by rw [hKu]; exact Nat.minFac_dvd _)
    refine ⟨_, hr, hr2, two_le_pRank_of_mulEquiv hr e ?_⟩
    exact two_le_pRank_torus hr3 hζ (i₀ := (0 : Fin 3)) (i₁ := 1) (i₂ := 2) (by decide)
      (by decide) (by decide) (torusDiag_mem_SL (prod_torusVec ζ _ _))
      (torusDiag_mem_SL (prod_torusVec ζ _ _))

theorem exists_two_le_pRank_psu_three_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hm : StatedClassicalModel S .PSU 3 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hq0 : 2 ^ f ≠ 0 := by positivity
  have hKu : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' f
  ·
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hmod : 2 ^ f % 3 = 1 := by rw [hk]; exact two_pow_even_mod k
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have hr : (2 ^ f + 1).minFac.Prime := Nat.minFac_prime (by omega)
    have hr2 : (2 ^ f + 1).minFac ≠ 2 := fun h => by
      have h' := Nat.minFac_dvd (2 ^ f + 1)
      rw [h] at h'
      omega
    have hr3 : (2 ^ f + 1).minFac ≠ 3 := fun h => by
      have h' := Nat.minFac_dvd (2 ^ f + 1)
      rw [h] at h'
      omega
    have := Fact.mk hr
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (2 ^ f + 1).minFac
      (by rw [hKu]; exact (Nat.minFac_dvd _).mul_right _)
    have hζq : ζ ^ (2 ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact Nat.minFac_dvd _)
    refine ⟨_, hr, hr2, two_le_pRank_of_mulEquiv hr e ?_⟩
    exact two_le_pRank_torus hr3 hζ (i₀ := (0 : Fin 3)) (i₁ := 1) (i₂ := 2) (by decide)
      (by decide) (by decide)
      (torusDiag_mem_SU hq0 (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
      (torusDiag_mem_SU hq0 (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
  ·
    have hmod : 2 ^ f % 3 = 2 := by rw [hk]; exact two_pow_odd_mod k
    have h3 : 3 ∣ 2 ^ f + 1 := by omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
      (by rw [hKu]; exact h3.mul_right _)
    have hζq : ζ ^ (2 ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h3)
    refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_mulEquiv Nat.prime_three e ?_⟩
    refine two_le_pRank_three_of_cubic hζ (StatedSU 3 (2 ^ f) K) ?_ ?_ (cycGL_mem_SU K hq0)
    · refine torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_
      funext i
      fin_cases i <;> simp [hζq, inv_pow]
    · refine torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_
      funext i
      fin_cases i <;> simp [hζq, inv_pow]

end CFSG.QuasithinUnique.Vol2Native.EvenWit
