module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLFlagKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace EvenLinearSL

theorem odd_orderOf_of_mem_oddCore {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ CFSG.oddCore X) : Odd (orderOf x) := by
  have h := Subgroup.orderOf_dvd_natCard (CFSG.oddCore X) hx
  exact EvenCatalog.odd_card_oddCore.of_dvd_nat h

theorem eq_one_of_odd_orderOf {G : Type*} [Group G] {x : G} (hodd : Odd (orderOf x)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))

theorem oddCore_eq_bot_of_twoSubgroup {G : Type*} [Group G] {X R : Subgroup G} [Finite X]
    (hRX : R ≤ X) (hR : IsPGroup 2 R)
    (hnorm : ∀ q : X, q ∈ CFSG.oddCore X → ∀ r ∈ R, (q : G) * r * (q : G)⁻¹ ∈ R)
    (hcent : ∀ q : X, q ∈ CFSG.oddCore X → (∀ r ∈ R, (q : G) * r = r * q) →
      ∃ k : ℕ, (q : G) ^ 2 ^ k = 1) :
    CFSG.oddCore X = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hQn : (CFSG.oddCore X).Normal := CFSG.oddCore_normal X
  have hcomm : ∀ r ∈ R, (q : G) * r = r * q := by
    intro r hr
    set rX : X := ⟨r, hRX hr⟩ with hrX
    set c : X := q * rX * q⁻¹ * rX⁻¹ with hc
    have hcQ : c ∈ CFSG.oddCore X := by
      have h1 : rX * q⁻¹ * rX⁻¹ ∈ CFSG.oddCore X := hQn.conj_mem _ (inv_mem hq) rX
      have h2 := mul_mem hq h1
      rwa [show q * (rX * q⁻¹ * rX⁻¹) = c by rw [hc]; group] at h2
    have hcR : (c : G) ∈ R := by
      have h1 := hnorm q hq r hr
      have h2 := mul_mem h1 (inv_mem hr)
      simpa [hc, hrX, mul_assoc] using h2
    have hodd : Odd (orderOf (c : G)) := by
      rw [Subgroup.orderOf_coe]
      exact odd_orderOf_of_mem_oddCore hcQ
    obtain ⟨k, hk⟩ := hR ⟨c, hcR⟩
    have hk' : (c : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hc1 : (c : G) = 1 := eq_one_of_odd_orderOf hodd hk'
    have hc1' : (q : G) * r * (q : G)⁻¹ * r⁻¹ = 1 := by
      simpa [hc, hrX] using hc1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1'
    exact hc1'
  obtain ⟨k, hk⟩ := hcent q hq hcomm
  have hodd : Odd (orderOf (q : G)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem_oddCore hq
  exact Subtype.ext (eq_one_of_odd_orderOf hodd hk)

variable {K : Type*} [Field K] {n : ℕ}

theorem mul_self_mem_semilinearAutGroup [Finite K] (hn : 3 ≤ n) (x : MulAut (projectiveSL n K)) :
    x * x ∈ semilinearAutGroup n K := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform x
  have he : conjAut n K A * fieldAut n K σ ∈ semilinearAutGroup n K :=
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one]
    exact mul_mem he he
  · rw [pow_one]
    have h := dualAut_mul_mul_dualAut_mem he
    have h2 := mul_mem he h
    rwa [show conjAut n K A * fieldAut n K σ * (dualAut n K * (conjAut n K A * fieldAut n K σ) *
      dualAut n K) = conjAut n K A * fieldAut n K σ * dualAut n K *
        (conjAut n K A * fieldAut n K σ * dualAut n K) by group] at h2

theorem mem_semilinearAutGroup_of_odd [Finite K] (hn : 3 ≤ n) {x : MulAut (projectiveSL n K)}
    (hx : Odd (orderOf x)) : x ∈ semilinearAutGroup n K := by
  obtain ⟨m, hm⟩ := hx
  have h1 : x = (x * x) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h1]
  exact pow_mem (mul_self_mem_semilinearAutGroup hn x) _

theorem finite_mulAut' (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun e : MulAut G => (e : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem units_eq_one_of_mul_self [CharP K 2] {c : Kˣ} (hc : c * c = 1) : c = 1 := by
  have h2 : (c : K) ^ 4 = 1 := by
    have h1 : (c : K) * c = 1 := by rw [← Units.val_mul, hc, Units.val_one]
    calc (c : K) ^ 4 = ((c : K) * c) * ((c : K) * c) := by ring
      _ = 1 := by rw [h1, one_mul]
  exact Units.ext (eq_one_of_pow_four h2)

theorem exists_involution_rep [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {t : MulAut (projectiveSL n K)} (htI : t ∈ inner (projectiveSL n K)) (ht : orderOf t = 2) :
    ∃ s : GL (Fin n) K, conjAut n K s = t ∧ s * s = 1 ∧ s ≠ 1 := by
  obtain ⟨p, rfl⟩ := htI
  obtain ⟨g, rfl⟩ := proj_surjective n K p
  rw [← conjAut_toGL] at ht ⊢
  set g' := SpecialLinearGroup.toGL g with hg'
  have h2 : conjAut n K (g' * g') = 1 := by
    rw [map_mul, ← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp h2
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (c : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact c.ne_zero hμ
  set m : Kˣ := Units.mk0 μ hμ0 with hm
  refine ⟨g' * GeneralLinearGroup.scalar (Fin n) m⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, mul_one]
  · have hcomm := GeneralLinearGroup.scalar_commute m⁻¹ g'
    have hcm : c * (m⁻¹ * m⁻¹) = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val, hm,
        Units.val_mk0, hμ]
      field_simp
    calc g' * GeneralLinearGroup.scalar (Fin n) m⁻¹ * (g' * GeneralLinearGroup.scalar (Fin n) m⁻¹)
        = g' * (GeneralLinearGroup.scalar (Fin n) m⁻¹ * g') *
          GeneralLinearGroup.scalar (Fin n) m⁻¹ := by group
      _ = g' * g' * (GeneralLinearGroup.scalar (Fin n) m⁻¹ *
          GeneralLinearGroup.scalar (Fin n) m⁻¹) := by rw [hcomm]; group
      _ = GeneralLinearGroup.scalar (Fin n) (c * (m⁻¹ * m⁻¹)) := by rw [← hc, map_mul, map_mul]
      _ = 1 := by rw [hcm, map_one]
  · intro h1
    have h3 : conjAut n K g' = 1 := by
      have h4 := congrArg (conjAut n K) h1
      rwa [map_mul, conjAut_scalar, mul_one, map_one] at h4
    rw [h3, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem sub_one_mul_sub_one_eq_zero [CharP K 2] [NeZero n] {s : GL (Fin n) K} (hs : s * s = 1) :
    ((s : Matrix (Fin n) (Fin n) K) - 1) * ((s : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  have hs' : (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, hs, Units.val_one]
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  calc ((s : Matrix (Fin n) (Fin n) K) - 1) * ((s : Matrix (Fin n) (Fin n) K) - 1)
      = (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) + 1 -
        ((s : Matrix (Fin n) (Fin n) K) + (s : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = 0 := by rw [hs', CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, sub_zero]

end EvenLinearSL

open EvenLinearSL

theorem even_linear_higher_inner_involution_full_centralizer_odd_core {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) {K : Type*} [Field K] (hK : Nat.card K = 2 ^ f)
    {H : Subgroup (MulAut (projectiveSL n K))} (hH : inner (projectiveSL n K) ≤ H)
    {t : MulAut (projectiveSL n K)} (htI : t ∈ inner (projectiveSL n K)) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(H ⊓ centralizer {t}) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut' _
  obtain ⟨s, hst, hss, hs1⟩ := exists_involution_rep hn htI ht
  set N := (s : Matrix (Fin n) (Fin n) K) - 1 with hNdef
  have hNN : N * N = 0 := sub_one_mul_sub_one_eq_zero hss
  have hN0 : N ≠ 0 := by
    intro h
    apply hs1
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  set W := LinearMap.range (mulVecLin N) with hWdef
  set L := LinearMap.ker (mulVecLin N) with hLdef
  have hWL : W ≤ L := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hNN, zero_mulVec]
  obtain ⟨v₁, hv₁⟩ : ∃ v, N *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hN0
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, hall v, map_zero, LinearMap.zero_apply]
  have hW : W ≠ ⊥ := by
    intro h
    apply hv₁
    have hmem : N *ᵥ v₁ ∈ W := ⟨v₁, rfl⟩
    rw [h] at hmem
    exact (Submodule.mem_bot K).mp hmem
  have hL : L ≠ ⊤ := by
    intro h
    apply hv₁
    have hmem : v₁ ∈ L := h ▸ Submodule.mem_top
    exact hmem
  obtain ⟨-, -, hUp, hιI, hιapp, -, hnormE, -, hcent2⟩ :=
    even_linear_flag_kernel_projective_centralizer hn hf hK hW hWL hL
  have hus : ∀ u ∈ flagKernel W L hWL, (u : Matrix (Fin n) (Fin n) K) *
      (s : Matrix (Fin n) (Fin n) K) = (s : Matrix (Fin n) (Fin n) K) * u := by
    intro u hu
    obtain ⟨hu1, -, hu3⟩ := hu
    have huN : (u : Matrix (Fin n) (Fin n) K) * N = N := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec]
      have h := hu1 (N *ᵥ v) ⟨v, rfl⟩
      rwa [sub_mulVec, one_mulVec, sub_eq_zero] at h
    have hNu : N * (u : Matrix (Fin n) (Fin n) K) = N := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec,
        mulVec_eq_add_sub_one (u : Matrix (Fin n) (Fin n) K) v, mulVec_add]
      have h : N *ᵥ (((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v) = 0 := hu3 v
      rw [h, add_zero]
    have hs : (s : Matrix (Fin n) (Fin n) K) = 1 + N := by rw [hNdef, add_sub_cancel]
    rw [hs, Matrix.mul_add, Matrix.add_mul, huN, hNu, Matrix.mul_one, Matrix.one_mul]
  have hιX : (flagKernelInner W L hWL).range ≤ H ⊓ centralizer {t} := by
    rintro _ ⟨u, rfl⟩
    refine mem_inf.mpr ⟨hH (hιI ⟨u, rfl⟩), ?_⟩
    rw [mem_centralizer_singleton_iff, hιapp, ← hst, ← map_mul, ← map_mul]
    congr 1
    exact Units.ext (hus u u.2)
  have hnormT : ∀ (A : GL (Fin n) K) (φ : K ≃+* K),
      conjAut n K A * fieldAut n K φ * t = t * (conjAut n K A * fieldAut n K φ) →
      conjAut n K A * fieldAut n K φ ∈
        normalizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K))) := by
    intro A φ hcomm
    have h1 : conjAut n K (A * GeneralLinearGroup.map (φ : K →+* K) s * A⁻¹) =
        conjAut n K s := by
      rw [← conj_conjAut_fieldAut, hst, hcomm]
      group
    obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hn _ _).mp h1
    have hsq : (A * GeneralLinearGroup.map (φ : K →+* K) s * A⁻¹) *
        (A * GeneralLinearGroup.map (φ : K →+* K) s * A⁻¹) = 1 := by
      calc (A * GeneralLinearGroup.map (φ : K →+* K) s * A⁻¹) *
          (A * GeneralLinearGroup.map (φ : K →+* K) s * A⁻¹)
          = A * GeneralLinearGroup.map (φ : K →+* K) (s * s) * A⁻¹ := by
            rw [map_mul]
            group
        _ = 1 := by rw [hss, map_one, mul_one, mul_inv_cancel]
    have hcc : c * c = 1 := by
      rw [hc] at hsq
      have hcomm' := GeneralLinearGroup.scalar_commute c s
      have h2 : GeneralLinearGroup.scalar (Fin n) (c * c) = 1 := by
        rw [← hsq, map_mul]
        calc GeneralLinearGroup.scalar (Fin n) c * GeneralLinearGroup.scalar (Fin n) c
            = s * s * (GeneralLinearGroup.scalar (Fin n) c *
              GeneralLinearGroup.scalar (Fin n) c) := by rw [hss, one_mul]
          _ = s * (s * GeneralLinearGroup.scalar (Fin n) c) *
              GeneralLinearGroup.scalar (Fin n) c := by group
          _ = s * (GeneralLinearGroup.scalar (Fin n) c * s) *
              GeneralLinearGroup.scalar (Fin n) c := by rw [hcomm']
          _ = s * GeneralLinearGroup.scalar (Fin n) c *
              (s * GeneralLinearGroup.scalar (Fin n) c) := by group
      have h3 := congrArg (fun g : GL (Fin n) K =>
        (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h2
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, Units.val_one,
        one_apply_eq] at h3
      exact Units.ext (by rw [h3, Units.val_one])
    rw [units_eq_one_of_mul_self hcc, map_one, mul_one] at hc
    have hmat : (A : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K).map φ =
        (s : Matrix (Fin n) (Fin n) K) * A := by
      have h' : (A : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K).map φ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (s : Matrix (Fin n) (Fin n) K) :=
        congrArg Units.val hc
      calc (A : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K).map φ
          = (A : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K).map φ *
            (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
            rw [inv_mul_self_val, Matrix.mul_one]
        _ = (A : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K).map φ *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A := by
            simp only [Matrix.mul_assoc]
        _ = (s : Matrix (Fin n) (Fin n) K) * A := by rw [h']
    have hTN : ∀ v, semilin A φ (N *ᵥ v) = N *ᵥ semilin A φ v := by
      intro v
      rw [hNdef, sub_mulVec, one_mulVec, semilin_sub, sub_mulVec, one_mulVec, semilin_mulVec, hmat,
        ← mulVec_mulVec]
      rfl
    refine ((hnormE A φ ?_ ?_).2)
    · rintro _ ⟨v, rfl⟩
      exact ⟨semilin A φ v, (hTN v).symm⟩
    · intro x hx
      have hx' : N *ᵥ x = 0 := hx
      show N *ᵥ semilin A φ x = 0
      rw [← hTN, hx', semilin_zero]
  have hRp : IsPGroup 2 (flagKernelInner W L hWL).range :=
    hUp.of_surjective _ (flagKernelInner W L hWL).rangeRestrict_surjective
  apply oddCore_eq_bot_of_twoSubgroup hιX hRp
  · intro q hq r hr
    have hqodd : Odd (orderOf (q : MulAut (projectiveSL n K))) := by
      rw [Subgroup.orderOf_coe]
      exact odd_orderOf_of_mem_oddCore hq
    obtain ⟨A, φ, hAφ⟩ := mem_semilinearAutGroup_iff.mp (mem_semilinearAutGroup_of_odd hn hqodd)
    have hqt : (q : MulAut (projectiveSL n K)) * t = t * q :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp q.2).2
    rw [hAφ] at hqt ⊢
    exact (mem_normalizer_iff.mp (hnormT A φ hqt) r).mp hr
  · intro q hq hcomm
    have hqodd : Odd (orderOf (q : MulAut (projectiveSL n K))) := by
      rw [Subgroup.orderOf_coe]
      exact odd_orderOf_of_mem_oddCore hq
    have hqC : (q : MulAut (projectiveSL n K)) ∈ semilinearAutGroup n K ⊓
        centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K))) :=
      mem_inf.mpr ⟨mem_semilinearAutGroup_of_odd hn hqodd,
        mem_centralizer_iff.mpr fun r hr => (hcomm r hr).symm⟩
    obtain ⟨k, hk⟩ := hcent2 ⟨_, hqC⟩
    refine ⟨k, ?_⟩
    have h := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, OneMemClass.coe_one] at h

end CFSG.ComponentClassification.UnbalancedCatalog
