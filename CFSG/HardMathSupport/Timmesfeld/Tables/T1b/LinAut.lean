module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CyclicArith
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
import CFSG.GH74.GLS.Stage4.T2F1LocH90
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Open

theorem card_le_mul_card_inf_of_zpowers {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] {p : ℕ} (hp : p.Prime) (E : Subgroup G) (hE : IsElemAbelian p E) (g : G)
    (hg : ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ N) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ N) := by
  let φ : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hker : Nat.card φ.ker = Nat.card ↥(E ⊓ N) := by
    have : φ.ker = (E ⊓ N).subgroupOf E := by
      ext x
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card φ.range ≤ p := by
    set C : Subgroup (G ⧸ N) := Subgroup.zpowers (QuotientGroup.mk g : G ⧸ N) with hC
    have hle : φ.range ≤ C := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨k, hk⟩ := hg x x.2
      have h1 : (QuotientGroup.mk (g ^ k * (x : G)) : G ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hk
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
      have h2 : φ x = ((QuotientGroup.mk g : G ⧸ N) ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
    let R : Subgroup C := φ.range.subgroupOf C
    have hR : Nat.card R = Nat.card φ.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    obtain ⟨g', hg'⟩ := IsCyclic.exists_generator (α := R)
    have h1 : Nat.card R = orderOf g' := (orderOf_eq_card_of_forall_mem_zpowers hg').symm
    have h2 : g' ^ p = 1 := by
      obtain ⟨x, hx⟩ : (((g' : C) : G ⧸ N)) ∈ φ.range := g'.2
      have hxp : x ^ p = 1 := Subtype.ext (hE.2 x x.2)
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hx, ← map_pow, hxp, map_one]
    rw [← hR, h1]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one h2)
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card ↥(E ⊓ N) * p := by rw [hker]; exact Nat.mul_le_mul_left _ hrange
    _ = p * Nat.card ↥(E ⊓ N) := mul_comm _ _

theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G} (h : A ≤ B)
    (hB : IsElemAbelian p B) : IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB h

instance conjRange_normal (X : Type*) [Group X] :
    ((MulAut.conj : X →* MulAut X).range).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨x, rfl⟩ φ
  refine ⟨φ x, ?_⟩
  ext z
  simp [MulAut.conj_apply]

theorem mem_of_odd_pow_mem_of_index_le_two {Γ : Type*} [Group Γ] [Finite Γ] (E : Subgroup Γ)
    (h : E.index ≤ 2) {α : Γ} {N : ℕ} (hN : Odd N) (hα : α ^ N ∈ E) : α ∈ E := by
  have h0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_cases h1 : E.index = 1
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top α
  · have h2 : E.index = 2 := by omega
    obtain ⟨m, rfl⟩ := hN
    have hsq : α * α ∈ E := Subgroup.mul_self_mem_of_index_two h2 α
    have : α = ((α * α) ^ m)⁻¹ * α ^ (2 * m + 1) := by
      rw [pow_succ, pow_mul, sq, ← mul_assoc]
      group
    rw [this]
    exact mul_mem (inv_mem (pow_mem hsq m)) hα

section Matrices

variable {K : Type} [Field K] {n : ℕ}

theorem conjAut_eq_one_iff_scalar [Finite K] (hn : 3 ≤ n) (A : GL (Fin n) K) :
    conjAut n K A = 1 ↔ ∃ u : Kˣ, A = GeneralLinearGroup.scalar (Fin n) u := by
  constructor
  · intro h
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by rw [map_one, mul_one, h])
    exact ⟨c, hc.symm⟩
  · rintro ⟨u, rfl⟩
    exact conjAut_scalar u

theorem det_scalar_gl (u : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) u) = u ^ n := by
  ext
  simp [GeneralLinearGroup.scalar]

theorem conjAut_mem_inner_of_det_eq_pow [Finite K] (A : GL (Fin n) K) (μ : Kˣ)
    (h : GeneralLinearGroup.det A = μ ^ n) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_range_conj_of_det_eq_pow h

theorem isCyclic_linearD_quotient [Finite K] (_hn : 3 ≤ n) :
    IsCyclic (linearAutGroup n K ⧸
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range.subgroupOf
        (linearAutGroup n K)) := by
  set I := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hI
  set I' := I.subgroupOf (linearAutGroup n K) with hI'
  let Θ : GL (Fin n) K →* linearAutGroup n K ⧸ I' :=
    (QuotientGroup.mk' I').comp
      ((conjAut n K).codRestrict (linearAutGroup n K) conjAut_mem_linearAutGroup)
  let θ : GL (Fin n) K →* Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range :=
    (QuotientGroup.mk' _).comp GeneralLinearGroup.det
  have hΘsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨⟨d, hd⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hd
    exact ⟨A, rfl⟩
  have hker : θ.ker ≤ Θ.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    have h1 : GeneralLinearGroup.det A ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
      (QuotientGroup.eq_one_iff _).1 hA
    obtain ⟨μ, hμ⟩ := h1
    show QuotientGroup.mk' I' _ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact conjAut_mem_inner_of_det_eq_pow A μ (by simpa using hμ.symm)
  have : IsCyclic (GL (Fin n) K ⧸ θ.ker) :=
    isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange θ).symm
      (QuotientGroup.quotientKerEquivRange θ).symm.surjective
  refine isCyclic_of_surjective (QuotientGroup.lift θ.ker Θ hker) fun y => ?_
  obtain ⟨A, rfl⟩ := hΘsurj y
  exact ⟨QuotientGroup.mk A, rfl⟩

theorem exists_det_eq_pow_of_commute [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (hpK : p ∣ Nat.card K - 1) (hg : ¬ p ^ 2 ∣ Nat.gcd n (Nat.card K - 1))
    (σ : K ≃+* K) (hσ : orderOf σ = p) (A : GL (Fin n) K)
    (hcomm : fieldAut n K σ * conjAut n K A = conjAut n K A * fieldAut n K σ)
    (hA : conjAut n K A ^ p = 1) :
    ∃ μ : Kˣ, GeneralLinearGroup.det A = μ ^ n := by
  classical
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hn0 : 0 < n := by omega
  have h1 : conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) = conjAut n K A := by
    rw [← htrans.2.2.1, hcomm, mul_inv_cancel_right]
  have h2 : conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A * A⁻¹) = 1 := by
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff_scalar hn _).1 h2
  have hσA : GeneralLinearGroup.map (σ : K →+* K) A = GeneralLinearGroup.scalar (Fin n) u * A := by
    rw [← hu, inv_mul_cancel_right]
  have hM : (A : Matrix (Fin n) (Fin n) K).map σ = (u : K) • (A : Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hσA
    ext i j
    have h := congrFun (congrFun this i) j
    simpa [GeneralLinearGroup.map, GeneralLinearGroup.scalar, Matrix.diagonal_mul] using h
  have hent : ∀ i j, σ ((A : Matrix (Fin n) (Fin n) K) i j) = u * (A : Matrix (Fin n) (Fin n) K) i j :=
    fun i j => by simpa using congrFun (congrFun hM i) j
  have hit : ∀ k i j, (σ ^ k) ((A : Matrix (Fin n) (Fin n) K) i j) =
      (∏ l ∈ Finset.range k, (σ ^ l) (u : K)) * (A : Matrix (Fin n) (Fin n) K) i j := by
    intro k i j
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : (σ ^ (k + 1)) ((A : Matrix (Fin n) (Fin n) K) i j) =
          σ ((σ ^ k) ((A : Matrix (Fin n) (Fin n) K) i j)) := by
        rw [pow_succ']
        rfl
      have e2 : ∏ l ∈ Finset.range (k + 1), (σ ^ l) (u : K) =
          σ (∏ l ∈ Finset.range k, (σ ^ l) (u : K)) * u := by
        rw [Finset.prod_range_succ', map_prod]
        simp [pow_succ']
      rw [e1, ih, map_mul, hent, e2]
      ring
  obtain ⟨i, j, hij⟩ : ∃ i j, (A : Matrix (Fin n) (Fin n) K) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : (A : Matrix (Fin n) (Fin n) K) = 0 := by
      ext i j
      exact hcon i j
    have h1 : ((A * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [mul_inv_cancel]
      rfl
    rw [Units.val_mul, h0, zero_mul] at h1
    have := congrFun (congrFun h1 ⟨0, hn0⟩) ⟨0, hn0⟩
    simp at this
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hN : ∏ l ∈ Finset.range p, (σ ^ l) (u : K) = 1 := by
    have := hit p i j
    rw [hσp] at this
    have h3 : (1 : K ≃+* K) ((A : Matrix (Fin n) (Fin n) K) i j) =
        (A : Matrix (Fin n) (Fin n) K) i j := rfl
    rw [h3] at this
    have h4 : (1 : K) * (A : Matrix (Fin n) (Fin n) K) i j =
        (∏ l ∈ Finset.range p, (σ ^ l) (u : K)) * (A : Matrix (Fin n) (Fin n) K) i j := by
      rw [one_mul]
      exact this
    exact (mul_right_cancel₀ hij h4).symm
  obtain ⟨y, hy0, hy⟩ := CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField σ hσ hN
  set d : K := (A : Matrix (Fin n) (Fin n) K).det with hd
  have hdU : ((GeneralLinearGroup.det A : Kˣ) : K) = d := by
    simp [hd]
  have hd0 : d ≠ 0 := by
    rw [← hdU]
    exact Units.ne_zero _
  have hσd : σ d = (u : K) ^ n * d := by
    have := RingHom.map_det (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K)
    rw [RingHom.mapMatrix_apply] at this
    change σ d = _ at this
    rw [this]
    have h5 : (A : Matrix (Fin n) (Fin n) K).map (σ : K →+* K) =
        (u : K) • (A : Matrix (Fin n) (Fin n) K) := hM
    rw [h5, Matrix.det_smul, Fintype.card_fin]
  have hfix : σ (d * y ^ n) = d * y ^ n := by
    rw [map_mul, map_pow, hσd]
    calc (u : K) ^ n * d * σ y ^ n = d * ((u : K) * σ y) ^ n := by ring
      _ = d * y ^ n := by rw [hy]
  obtain ⟨ν, hν⟩ := fixed_unit_isPow hp hp2 σ hσ hpK (d * y ^ n) hfix
    (mul_ne_zero hd0 (pow_ne_zero _ hy0))
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero hd0 (pow_ne_zero _ hy0) hν.symm
  set ν' : Kˣ := Units.mk0 ν hν0 with hν'
  set y' : Kˣ := Units.mk0 y hy0 with hy'
  set dU : Kˣ := GeneralLinearGroup.det A with hdU'
  have hdy : dU * y' ^ n = ν' ^ p := by
    apply Units.ext
    simp [hdU, hν', hy', hν]
  obtain ⟨w, hw⟩ : ∃ w : Kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) w := by
    have : conjAut n K (A ^ p) = 1 := by rw [map_pow]; exact hA
    exact (conjAut_eq_one_iff_scalar hn _).1 this
  have hdw : dU ^ p = w ^ n := by
    have := congrArg GeneralLinearGroup.det hw
    rwa [map_pow, det_scalar_gl] at this
  have hsq : ν' ^ (p ^ 2) = (w * y' ^ p) ^ n := by
    calc ν' ^ (p ^ 2) = (ν' ^ p) ^ p := by rw [← pow_mul, sq]
      _ = (dU * y' ^ n) ^ p := by rw [hdy]
      _ = dU ^ p * (y' ^ p) ^ n := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n p]
      _ = (w * y' ^ p) ^ n := by rw [hdw, mul_pow]
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_sq_eq (Z := Kˣ) hp (by rwa [Nat.card_units]) hsq
  refine ⟨μ * y'⁻¹, ?_⟩
  rw [mul_pow, inv_pow]
  apply eq_mul_inv_of_mul_eq
  rw [hdy, hμ]

end Matrices


section Aut

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linearAutGroup_normal (hn : 3 ≤ n) : (linearAutGroup n K).Normal :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_normal_of_three_le hn

theorem mem_semilinearAutGroup_of_pow_eq_one (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : MulAut (projectiveSL n K)} (hx : x ^ p = 1) : x ∈ semilinearAutGroup n K :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2) hx

theorem card_le_mul_card_inf_linearD (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (projectiveSL n K))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ linearAutGroup n K) := by
  have : Finite (MulAut (projectiveSL n K)) :=
    Finite.of_injective (fun α : MulAut (projectiveSL n K) => (α : projectiveSL n K → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  have := linearAutGroup_normal (K := K) hn
  obtain ⟨-, -, -, -, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  exact card_le_mul_card_inf_of_zpowers (linearAutGroup n K) hp E hE g fun x hx =>
    hg x (mem_semilinearAutGroup_of_pow_eq_one hn hp hp2 (hE.2 x hx))

theorem card_le_pow_projectiveSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (E : Subgroup (MulAut (projectiveSL n K)))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ n := by
  have h1 := card_le_mul_card_inf_linearD hn hp hp2 E hE
  have hED : IsElemAbelian p (E ⊓ linearAutGroup n K) := isElemAbelian_of_le inf_le_left hE
  let ρ : (⊤ : Subgroup (GL (Fin n) K)) →* MulAut (projectiveSL n K) :=
    (conjAut n K).comp (⊤ : Subgroup (GL (Fin n) K)).subtype
  have h2 : Nat.card ↥(E ⊓ linearAutGroup n K) ≤ p ^ (n - 1) :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel hp hp2
      (by rwa [Nat.card_units]) (by omega) ⊤ ρ
      (fun A => by
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, conjAut_eq_one_iff_scalar hn]
        exact (CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff).symm)
      _ (fun y hy => by
        obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hy.2
        exact ⟨⟨A, trivial⟩, hA⟩) hED
  calc Nat.card E ≤ p * Nat.card ↥(E ⊓ linearAutGroup n K) := h1
    _ ≤ p * p ^ (n - 1) := Nat.mul_le_mul_left _ h2
    _ = p ^ n := by
      rw [← pow_succ']
      congr 1
      omega

theorem card_le_mul_card_inf_inner_of_le (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (E : Subgroup (MulAut (projectiveSL n K))) (hE : IsElemAbelian p E)
    (hED : E ≤ linearAutGroup n K) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) := by
  have : Finite (MulAut (projectiveSL n K)) :=
    Finite.of_injective (fun α : MulAut (projectiveSL n K) => (α : projectiveSL n K → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨γ, hγ⟩ := (isCyclic_linearD_quotient (K := K) hn).exists_generator
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective γ
  refine card_le_mul_card_inf_of_zpowers _ hp E hE (g₀ : MulAut (projectiveSL n K)) fun x hx => ?_
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hγ (QuotientGroup.mk ⟨x, hED hx⟩))
  refine ⟨-j, ?_⟩
  have h1 : (QuotientGroup.mk (g₀ ^ (-j) * (⟨x, hED hx⟩ : linearAutGroup n K)) :
      linearAutGroup n K ⧸ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range.subgroupOf
        (linearAutGroup n K)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hj, _root_.zpow_neg, inv_mul_cancel]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem inf_linearD_le_inner_of_not_le (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hg : ¬ p ^ 2 ∣ Nat.gcd n (Nat.card K - 1))
    (E : Subgroup (MulAut (projectiveSL n K))) (hE : IsElemAbelian p E)
    (hnle : ¬ E ≤ linearAutGroup n K) :
    E ⊓ linearAutGroup n K ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxE, hxD⟩ := Set.not_subset.1 hnle
  have hxp : x ^ p = 1 := hE.2 x hxE
  have hx1 : x ≠ 1 := fun h => hxD (h ▸ one_mem _)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxS : x ∈ semilinearAutGroup n K := mem_semilinearAutGroup_of_pow_eq_one hn hp hp2 hxp
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, hchar, f, hℓ, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨-, σ, hσ, ⟨h, hh, hxh⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ f.pos hn hK hp x hxS hxD hord
  obtain ⟨M, rfl⟩ := mem_linearAutGroup_iff.mp hh
  rintro y ⟨hyE, hyD⟩
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hyD
  have hxy : x * conjAut n K A = conjAut n K A * x :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hxE⟩ : E) ⟨conjAut n K A, hyE⟩)
  have hcomm : fieldAut n K σ * conjAut n K (M⁻¹ * A * M) =
      conjAut n K (M⁻¹ * A * M) * fieldAut n K σ := by
    rw [map_mul, map_mul, map_inv]
    set c := conjAut n K M
    set a := conjAut n K A
    set s := fieldAut n K σ
    have hx : x = c * s * c⁻¹ := hxh
    rw [hx] at hxy
    calc s * (c⁻¹ * a * c) = c⁻¹ * ((c * s * c⁻¹) * a) * c := by group
      _ = c⁻¹ * (a * (c * s * c⁻¹)) * c := by rw [hxy]
      _ = c⁻¹ * a * c * s := by group
  have hpow : conjAut n K (M⁻¹ * A * M) ^ p = 1 := by
    rw [map_mul, map_mul, map_inv]
    have h1 : (conjAut n K M)⁻¹ * conjAut n K A * conjAut n K M =
        (conjAut n K M)⁻¹ * conjAut n K A * ((conjAut n K M)⁻¹)⁻¹ := by rw [inv_inv]
    rw [h1, conj_pow, hE.2 _ hyE, mul_one, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := exists_det_eq_pow_of_commute hp hp2 hn hpK hg σ hσ _ hcomm hpow
  refine conjAut_mem_inner_of_det_eq_pow A μ ?_
  rw [← hμ, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

theorem card_le_mul_card_inf_inner (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hg : ¬ p ^ 2 ∣ Nat.gcd n (Nat.card K - 1))
    (E : Subgroup (MulAut (projectiveSL n K))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) := by
  by_cases hle : E ≤ linearAutGroup n K
  · exact card_le_mul_card_inf_inner_of_le hn hp E hE hle
  · have h1 := card_le_mul_card_inf_linearD hn hp hp2 E hE
    have h2 := inf_linearD_le_inner_of_not_le hn hp hp2 hpK hg E hE hle
    refine h1.trans (Nat.mul_le_mul_left _ ?_)
    exact Nat.card_mono (Set.toFinite _) (SetLike.coe_subset_coe.2 (le_inf inf_le_left h2))

theorem meets_inner_projectiveSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hg : ¬ p ^ 2 ∣ Nat.gcd n (Nat.card K - 1))
    (D : Subgroup (MulAut (projectiveSL n K))) (hD : IsElemAbelian p D) (hc : Nat.card D = p ^ 2) :
    ∃ x ∈ D ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : D ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hcon x hx
  have h1 := card_le_mul_card_inf_inner hn hp hp2 hpK hg D hD
  rw [hbot, Subgroup.card_bot, hc, mul_one] at h1
  have : p * p ≤ p := by rwa [← sq]
  have := hp.one_lt
  nlinarith

end Aut

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
