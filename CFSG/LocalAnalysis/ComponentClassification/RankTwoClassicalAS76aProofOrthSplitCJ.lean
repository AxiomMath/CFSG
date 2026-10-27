module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCType
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Order

variable {G : Type} [Group G] [Finite G]

theorem natCard_of_regularOn {A J : Subgroup G} {n : ℕ} {p : G} (hpJ : p ∈ J) (hp1 : p ≠ 1)
    (hreg : RegularOn A J (nonidentity J)) (haut : AutCyclic A J n) : Nat.card J = n + 1 := by
  classical
  set Nn := A ⊓ normalizer (J : Set G) with hNn
  set C := A ⊓ centralizer (J : Set G) with hC
  set L := C.subgroupOf Nn with hL
  have hkey : ∀ a b : Nn, (a : G) * p * (a : G)⁻¹ = (b : G) * p * (b : G)⁻¹ ↔ a⁻¹ * b ∈ L := by
    intro a b
    rw [hL, mem_subgroupOf]
    constructor
    · intro h
      have hfix : ((a⁻¹ * b : Nn) : G) * p * ((a⁻¹ * b : Nn) : G)⁻¹ = p := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (a : G)⁻¹ * b * p * ((a : G)⁻¹ * b)⁻¹ = (a : G)⁻¹ * (b * p * (b : G)⁻¹) * a := by
              group
          _ = p := by rw [← h]; group
      exact ⟨(a⁻¹ * b).2.1, hreg.2 _ (a⁻¹ * b).2 p ⟨hpJ, hp1⟩ hfix⟩
    · intro h
      have h1 := mem_centralizer_iff.mp h.2 p hpJ
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (a : G) * p * (a : G)⁻¹ = (a : G) * (((a : G)⁻¹ * b) * p) * ((a : G)⁻¹ * b)⁻¹ *
            (a : G)⁻¹ := by rw [← h1]; group
        _ = (b : G) * p * (b : G)⁻¹ := by group
  set g : Nn ⧸ L → G := Quotient.lift (fun a : Nn => (a : G) * p * (a : G)⁻¹)
    (fun a b hab => (hkey a b).2 (QuotientGroup.leftRel_apply.mp hab)) with hg
  have hginj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((hkey a b).1 hxy)
  have hrange : Set.range g = nonidentity J := by
    ext j
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with | H a => ?_
      refine ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.mp a.2.2 p).mp hpJ
      · intro h1
        apply hp1
        have h2 : (a : G) * p * (a : G)⁻¹ = 1 := h1
        calc p = (a : G)⁻¹ * ((a : G) * p * (a : G)⁻¹) * a := by group
          _ = 1 := by rw [h2]; group
    · intro hj
      obtain ⟨a, ha, hap⟩ := hreg.1 p ⟨hpJ, hp1⟩ j hj
      exact ⟨QuotientGroup.mk ⟨a, ha⟩, hap⟩
  have hcard : Nat.card (nonidentity J) = n := by
    rw [← hrange, Nat.card_range_of_injective hginj, ← haut.1]
    rfl
  have hJset : (J : Set G) = insert 1 (nonidentity J) := by
    ext j
    simp only [Set.mem_insert_iff, SetLike.mem_coe, Set.mem_ofPred_eq]
    constructor
    · intro hj
      by_cases h1 : j = 1
      · exact Or.inl h1
      · exact Or.inr ⟨hj, h1⟩
    · rintro (rfl | ⟨hj, -⟩)
      · exact one_mem J
      · exact hj
  have hfin : (nonidentity J).Finite := Set.toFinite _
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hJset,
    Set.ncard_insert_of_notMem (fun h => h.2 rfl) hfin, ← Nat.card_coe_set_eq, hcard]

omit [Finite G] in
theorem le_pCoreIn_of_central {S H : Subgroup G} (hSH : S ≤ H)
    (hcent : ∀ s ∈ S, ∀ h ∈ H, s * h = h * s) (h2 : ∀ s ∈ S, s ^ 2 = 1) :
    S ≤ CFSG.ABGTheoremB.pCoreIn 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (S.subgroupOf H) := fun s => ⟨1, by
    have h := h2 _ (mem_subgroupOf.mp s.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h⟩
  have hn : (S.subgroupOf H).Normal := ⟨fun s hs h => by
    rw [mem_subgroupOf] at hs ⊢
    have h1 := hcent _ hs h h.2
    have e : (h : G) * s * (h : G)⁻¹ = s := by
      calc (h : G) * s * (h : G)⁻¹ = s * h * (h : G)⁻¹ := by rw [h1]
        _ = s := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact hs⟩
  have hle : S.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hn, hp⟩
  intro s hs
  exact ⟨⟨s, hSH hs⟩, hle hs, rfl⟩

end Order

section Matrices

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem Represents.mul_comm_of_commute [CharP K 2] {x p : G} {X M : GL ι K}
    (hx : Represents e x X) (hp : Represents e p M) (hM2 : M ^ 2 = 1) (hxp : x * p = p * x) :
    (X : Matrix ι ι K) * M = M * X := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  have h1 : Represents e (p * x) (X * M) := hxp ▸ hx.mul hp
  obtain ⟨c, hc⟩ := (hp.mul hx).exists_scalar h1
  have hcm : (X : Matrix ι ι K) * M = (c : K) • ((M : Matrix ι ι K) * X) := by
    have h := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hc
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one]
  have hM2' : (M : Matrix ι ι K) * M = 1 := by
    have h := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hM2
    simpa [sq] using h
  have hX : (X : Matrix ι ι K) = (c : K) ^ 2 • (X : Matrix ι ι K) := by
    calc (X : Matrix ι ι K) = X * M * M := by rw [mul_assoc, hM2', mul_one]
      _ = ((c : K) • ((M : Matrix ι ι K) * X)) * M := by rw [hcm]
      _ = (c : K) • ((M : Matrix ι ι K) * (X * M)) := by rw [Matrix.smul_mul, mul_assoc]
      _ = (c : K) • ((M : Matrix ι ι K) * ((c : K) • ((M : Matrix ι ι K) * X))) := by rw [hcm]
      _ = (c : K) ^ 2 • (X : Matrix ι ι K) := by
          rw [Matrix.mul_smul, ← mul_assoc, hM2', one_mul, smul_smul, pow_two]
  have hc2 : (c : K) ^ 2 = 1 := by
    obtain ⟨i⟩ := hι
    have hXi : ∃ j, (X : Matrix ι ι K) i j ≠ 0 := by
      by_contra! h0
      have h := congrFun (congrFun (congrArg (fun Y : GL ι K => (Y : Matrix ι ι K))
        (mul_inv_cancel X)) i) i
      simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, h0, zero_mul,
        Finset.sum_const_zero, Matrix.one_apply_eq] at h
      exact zero_ne_one h
    obtain ⟨j, hj⟩ := hXi
    have h := congrFun (congrFun hX i) j
    rw [Matrix.smul_apply, smul_eq_mul] at h
    exact (mul_eq_right₀ hj).mp h.symm
  have hc1 : (c : K) = 1 := by
    have h : ((c : K) + 1) ^ 2 = 0 := by rw [CharTwo.add_sq, hc2, one_pow, CharTwo.add_self_eq_zero]
    have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [← CharTwo.sub_eq_add] at h'
    exact sub_eq_zero.mp h'
  rw [hcm, hc1, one_smul]

theorem splitAt_of_lifts [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {F : Type} [Field F]
    [Finite F] (W₁ W₂ : F → GL ι K) (hH₁ : ∀ a, W₁ a ∈ H) (hH₂ : ∀ a, W₂ a ∈ H)
    (hW₁ : ∀ a b, W₁ (a + b) = W₁ a * W₁ b) (hW₂ : ∀ a b, W₂ (a + b) = W₂ a * W₂ b)
    (hsq₁ : ∀ a, W₁ a ^ 2 = 1) (hsq₂ : ∀ a, W₂ a ^ 2 = 1)
    (hcomm : ∀ a b, W₁ a * W₂ b = W₂ b * W₁ a)
    (hsc₁ : ∀ a (c : Kˣ), W₁ a = Matrix.GeneralLinearGroup.scalar ι c → a = 0)
    (hsc₂ : ∀ a (c : Kˣ), W₂ a = Matrix.GeneralLinearGroup.scalar ι c → a = 0)
    (hinf : ∀ a b (c : Kˣ), W₂ b = W₁ a * Matrix.GeneralLinearGroup.scalar ι c → a = 0)
    {J : Subgroup G} (hJ : ∀ j, j ∈ J ↔ ∃ d, j ^ 2 = 1 ∧ Represents e j (W₁ d * W₂ d))
    (hD : ∀ c : F, c ≠ 0 → ∃ D ∈ H, ∀ x, D⁻¹ * W₁ x * D = W₁ x ∧ D⁻¹ * W₂ x * D = W₂ (c * x))
    (P₁ P₂ : G → Prop)
    (hP₁ : ∀ a : F, a ≠ 0 → ∀ x : G, orderOf x = 2 → Represents e x (W₁ a) → P₁ x)
    (hP₂ : ∀ a : F, a ≠ 0 → ∀ x : G, orderOf x = 2 → Represents e x (W₂ a) → P₂ x) :
    SplitAt A J (Nat.card F) P₁ P₂ := by
  classical
  choose ι₁ hι₁2 hι₁ using fun d : F => exists_represents_sq_eq_one (e := e) hZ (hH₁ d) (hsq₁ d)
  choose ι₂ hι₂2 hι₂ using fun d : F => exists_represents_sq_eq_one (e := e) hZ (hH₂ d) (hsq₂ d)
  have hι₁2' : ∀ d, ι₁ d ^ 2 ^ 1 = 1 := fun d => by rw [pow_one]; exact hι₁2 d
  have hι₂2' : ∀ d, ι₂ d ^ 2 ^ 1 = 1 := fun d => by rw [pow_one]; exact hι₂2 d
  have hcomm₁ : ∀ x y, ι₁ x * ι₁ y = ι₁ y * ι₁ x := fun x y =>
    commute_of_represents hZ (hι₁ x) (hι₁ y) (hι₁2 y) (by rw [← hW₁, ← hW₁, add_comm])
  have hcomm₂ : ∀ x y, ι₂ x * ι₂ y = ι₂ y * ι₂ x := fun x y =>
    commute_of_represents hZ (hι₂ x) (hι₂ y) (hι₂2 y) (by rw [← hW₂, ← hW₂, add_comm])
  have hcomm12 : ∀ x y, Commute (ι₁ x) (ι₂ y) := fun x y =>
    commute_of_represents hZ (hι₁ x) (hι₂ y) (hι₂2 y) (hcomm x y)
  have hadd₁ : ∀ x y, ι₁ (x + y) = ι₁ x * ι₁ y := by
    intro x y
    have hrep : Represents e (ι₁ x * ι₁ y) (W₁ (x + y)) := by
      rw [hW₁]
      exact (hι₁ x).mul (hι₁ y)
    have hsq : (ι₁ x * ι₁ y) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (ι₁ x) (ι₁ y) from hcomm₁ x y).mul_pow, hι₁2, hι₁2, one_mul]
    exact eq_of_represents hZ (hι₁ (x + y)) hrep (hι₁2' _) hsq
  have hadd₂ : ∀ x y, ι₂ (x + y) = ι₂ x * ι₂ y := by
    intro x y
    have hrep : Represents e (ι₂ x * ι₂ y) (W₂ (x + y)) := by
      rw [hW₂]
      exact (hι₂ x).mul (hι₂ y)
    have hsq : (ι₂ x * ι₂ y) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (ι₂ x) (ι₂ y) from hcomm₂ x y).mul_pow, hι₂2, hι₂2, one_mul]
    exact eq_of_represents hZ (hι₂ (x + y)) hrep (hι₂2' _) hsq
  have hinj₁ : ∀ x, ι₁ x = 1 → x = 0 := by
    intro x hx
    have h1 : Represents e (1 : G) (W₁ x) := hx ▸ hι₁ x
    obtain ⟨c, hc⟩ := represents_one.exists_scalar h1
    rw [one_mul] at hc
    exact hsc₁ x c hc
  have hinj₂ : ∀ x, ι₂ x = 1 → x = 0 := by
    intro x hx
    have h1 : Represents e (1 : G) (W₂ x) := hx ▸ hι₂ x
    obtain ⟨c, hc⟩ := represents_one.exists_scalar h1
    rw [one_mul] at hc
    exact hsc₂ x c hc
  have hsqd : ∀ d, (ι₁ d * ι₂ d) ^ 2 = 1 := fun d => by
    rw [(hcomm12 d d).mul_pow, hι₁2, hι₂2, one_mul]
  refine ⟨F, inferInstance, inferInstance, ι₁, ι₂, rfl,
    { map_add₁ := hadd₁
      map_add₂ := hadd₂
      inj₁ := hinj₁
      inj₂ := hinj₂
      mem₁ := fun x => (hι₁ x).1
      mem₂ := fun x => (hι₂ x).1
      comm := hcomm12
      inf := ?_
      mem_iff := ?_
      prop₁ := fun x hx => hP₁ x hx _ (orderOf_eq_prime (hι₁2 x) fun h => hx (hinj₁ x h)) (hι₁ x)
      prop₂ := fun x hx => hP₂ x hx _ (orderOf_eq_prime (hι₂2 x) fun h => hx (hinj₂ x h)) (hι₂ x)
      scalar := ?_ }⟩
  · intro x y hxy
    have h1 : Represents e (ι₂ y) (W₁ x) := hxy ▸ hι₁ x
    obtain ⟨c, hc⟩ := h1.exists_scalar (hι₂ y)
    exact hinf x y c hc
  · intro j
    rw [hJ]
    constructor
    · rintro ⟨d, hj2, hj⟩
      refine ⟨d, eq_of_represents hZ hj ((hι₁ d).mul (hι₂ d)) (k := 1) (by rw [pow_one]; exact hj2)
        (k' := 1) (by rw [pow_one]; exact hsqd d)⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, hsqd d, (hι₁ d).mul (hι₂ d)⟩
  · intro c hc
    obtain ⟨D, hDH, hDW⟩ := hD c hc
    obtain ⟨a, haD⟩ := exists_represents_of_mem (e := e) hDH
    refine ⟨a, haD.1, fun x => ⟨?_, ?_⟩⟩
    · have hrep : Represents e (a⁻¹ * ι₁ x * a) (W₁ x) := by
        have h := (hι₁ x).conj haD.inv
        rw [inv_inv, inv_inv, (hDW x).1] at h
        exact h
      have hsq : (a⁻¹ * ι₁ x * a) ^ 2 ^ 1 = 1 := by
        rw [pow_one, show a⁻¹ * ι₁ x * a = a⁻¹ * ι₁ x * a⁻¹⁻¹ by rw [inv_inv], conj_pow, hι₁2,
          mul_one, mul_inv_cancel]
      exact eq_of_represents hZ hrep (hι₁ x) hsq (hι₁2' x)
    · have hrep : Represents e (a⁻¹ * ι₂ x * a) (W₂ (c * x)) := by
        have h := (hι₂ x).conj haD.inv
        rw [inv_inv, inv_inv, (hDW x).2] at h
        exact h
      have hsq : (a⁻¹ * ι₂ x * a) ^ 2 ^ 1 = 1 := by
        rw [pow_one, show a⁻¹ * ι₂ x * a = a⁻¹ * ι₂ x * a⁻¹⁻¹ by rw [inv_inv], conj_pow, hι₂2,
          mul_one, mul_inv_cancel]
      exact eq_of_represents hZ hrep (hι₂ (c * x)) hsq (hι₂2' _)

theorem eq_zero_of_sqZeroGL_eq_scalar {T : Matrix ι ι K} (hT : T * T = 0) {c : Kˣ}
    (h : sqZeroGL T hT = Matrix.GeneralLinearGroup.scalar ι c) : T = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  obtain ⟨i⟩ := hι
  have h2 : (1 : Matrix ι ι K) + T = (c : K) • 1 := by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) h
    simp only [coe_sqZeroGL, Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [h1, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h3 : T = ((c : K) - 1) • (1 : Matrix ι ι K) := by
    rw [sub_smul, one_smul, ← h2, add_sub_cancel_left]
  have h4 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
    have h5 := hT
    rw [h3, smul_mul_smul_comm, one_mul] at h5
    have h6 := congrFun (congrFun h5 i) i
    simpa using h6
  have h7 : (c : K) - 1 = 0 := mul_self_eq_zero.mp h4
  rw [h3, h7, zero_smul]

end Matrices

section Beta

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ι K : Type} [Fintype ι]
  [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

theorem exists_beta_jGroup (Q : QuadraticForm K (ι → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega ⇑Q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} (hp2 : orderOf p = 2) {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hev : Even (commRank M)) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (((M : Matrix ι ι K) - 1) *ᵥ v))
    (hreg : RegularOn A (jGroup A p) (nonidentity (jGroup A p)))
    (haut : AutCyclic A (jGroup A p) (Nat.card K - 1)) :
    ∃ W : K → GL ι K,
      (∀ d, (W d : Matrix ι ι K) = 1 + betaT Q.polarBilin ((M : Matrix ι ι K) - 1) z d) ∧
      ∀ j, j ∈ jGroup A p ↔ ∃ d, j ^ 2 = 1 ∧ Represents e j (W d) := by
  classical
  set N := (M : Matrix ι ι K) - 1 with hNdef
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hMiso : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v := statedOmega_isometry hpM.2.1
  have hiso : ∀ v, Q (v + N *ᵥ v) = Q v := fun v => by
    have h1 : v + N *ᵥ v = (M : Matrix ι ι K) *ᵥ v := by
      rw [hMN, Matrix.add_mulVec, Matrix.one_mulVec]
    rw [h1]
    exact hMiso v
  have hN : N * N = 0 := sub_one_mul_self_eq_zero hM2
  have hNz := mulVec_sqrt_vector hQ hN hiso hz
  obtain ⟨z', hz'⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  have hQz := quad_eq_zero_of_sqrt_vector hQ hMiso hN hev hz
  set T := betaT Q.polarBilin N z with hTdef
  set W : K → GL ι K := fun d => sqZeroGL (T d) (betaT_mul_self hN hz hNz d) with hWdef
  have hWc : ∀ d, (W d : Matrix ι ι K) = 1 + T d := fun d => rfl
  have hrank : ∀ d, d ≠ 0 → (T d).rank = N.rank := fun d hd => rank_betaT hN hiso hz hz' hQz hd
  have hWH : ∀ d, W d ∈ StatedOmega ⇑Q := by
    intro d
    refine mem_statedOmega_of Q hQ hT (fun v => ?_) ?_
    · rw [hWc]
      exact betaT_isometry hN hz hiso hQz d v
    · rw [commRank_sqZeroGL]
      by_cases hd : d = 0
      · have h0 : T d = 0 := by simp [hTdef, betaT, hd]
        rw [h0, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · rw [hrank d hd]
        exact hev
  have hTadd : ∀ a b, T a + T b = T (a + b) := fun a b => betaT_add a b
  have hTmul : ∀ a b, T a * T b = 0 := betaT_mul hN hz hNz
  have hWmul : ∀ a b, W (a + b) = W a * W b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hWc, hWc, hWc, ← hTadd, add_mul, one_mul, mul_add, mul_one, hTmul,
      add_zero]
    abel
  have hWsq : ∀ d, W d ^ 2 = 1 := fun d => sqZeroGL_sq _ _
  have hW1 : W 1 = M := by
    apply Units.ext
    rw [hWc, hMN]
    simp [hTdef, betaT, CharTwo.add_self_eq_zero]
  choose β hβ2 hβ using fun d : K => exists_represents_sq_eq_one (e := e) hZ (hWH d) (hWsq d)
  have hβ2' : ∀ d, β d ^ 2 ^ 1 = 1 := fun d => by rw [pow_one]; exact hβ2 d
  have hp2' : p ^ 2 ^ 1 = 1 := by rw [pow_one, ← hp2]; exact pow_orderOf_eq_one p
  have hβ1 : β 1 = p := eq_of_represents hZ (hβ 1) (hW1 ▸ hpM) (hβ2' 1) hp2'
  have hβcomm : ∀ a b, β a * β b = β b * β a := fun a b =>
    commute_of_represents hZ (hβ a) (hβ b) (hβ2 b) (by rw [← hWmul, ← hWmul, add_comm])
  have hβadd : ∀ a b, β (a + b) = β a * β b := by
    intro a b
    have hrep : Represents e (β a * β b) (W (a + b)) := by
      rw [hWmul]
      exact (hβ a).mul (hβ b)
    have hsq : (β a * β b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (β a) (β b) from hβcomm a b).mul_pow, hβ2, hβ2, one_mul]
    exact eq_of_represents hZ (hβ (a + b)) hrep (hβ2' _) hsq
  have hβ0 : β 0 = 1 := by
    have h := hβadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  set φ : Multiplicative K →* G :=
    { toFun := fun d => β (Multiplicative.toAdd d)
      map_one' := hβ0
      map_mul' := fun a b => hβadd _ _ } with hφ
  have hkey : ∀ x ∈ A ⊓ centralizer ({p} : Set G), ∀ d, x * β d = β d * x := by
    intro x hx d
    obtain ⟨X, hX⟩ := exists_represents e hx.1
    have hxp : x * p = p * x := mem_centralizer_singleton_iff.mp hx.2
    have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hXM := hX.mul_comm_of_commute hpM hM2' hxp
    have hXN : (X : Matrix ι ι K) * N = N * X := by
      rw [hNdef, mul_sub, sub_mul, hXM, mul_one, one_mul]
    have hXT := commute_betaT hz hQ (statedOmega_isometry hX.2.1) hXN d
    have hXW : X * W d = W d * X := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hWc, mul_add, add_mul, mul_one, one_mul, hXT]
    exact commute_of_represents hZ hX (hβ d) (hβ2 d) hXW
  have hpC : p ∈ A ⊓ centralizer ({p} : Set G) := ⟨hpM.1, mem_centralizer_singleton_iff.mpr rfl⟩
  have hJ₀C : φ.range ≤ A ⊓ centralizer ({p} : Set G) := by
    rintro _ ⟨d, rfl⟩
    refine ⟨(hβ _).1, mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hkey p hpC _).symm
  have hJ₀J : φ.range ≤ jGroup A p := by
    intro y hy
    refine ⟨?_, ?_⟩
    · refine le_pCoreIn_of_central hJ₀C ?_ ?_ hy
      · rintro _ ⟨d, rfl⟩ h hh
        exact (hkey h hh _).symm
      · rintro _ ⟨d, rfl⟩
        exact hβ2 _
    · show y ∈ centralizer (conjCommuting A p)
      rw [mem_centralizer_iff]
      rintro w ⟨b, hb, rfl, hcomm⟩
      obtain ⟨d, rfl⟩ := hy
      have hw : b * p * b⁻¹ ∈ A ⊓ centralizer ({p} : Set G) :=
        Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hb hpM.1) (A.inv_mem hb),
          mem_centralizer_singleton_iff.mpr hcomm.eq⟩
      exact hkey _ hw _
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : Represents e (1 : G) (W (Multiplicative.toAdd d)) := hd ▸ hβ _
    obtain ⟨c, hc⟩ := represents_one.exists_scalar h1
    rw [one_mul] at hc
    have hT0 := eq_zero_of_sqZeroGL_eq_scalar _ hc
    by_contra hd1
    have hd0 : Multiplicative.toAdd d ≠ 0 := fun h => hd1 (by rw [← ofAdd_toAdd d, h, ofAdd_zero])
    have h2 := hrank _ hd0
    rw [hT0, Matrix.rank_zero] at h2
    exact commRank_ne_zero hM2 h2.symm
  have hcardJ₀ : Nat.card φ.range = Nat.card K := by
    have h1 : Nat.card φ.range = Nat.card (Set.range φ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_range)
    rw [h1, Nat.card_range_of_injective hφinj]
    rfl
  have hpJ : p ∈ jGroup A p := hJ₀J ⟨Multiplicative.ofAdd 1, hβ1⟩
  have hp1 : p ≠ 1 := fun h => by rw [h, orderOf_one] at hp2; omega
  have hcardJ : Nat.card (jGroup A p) = Nat.card K := by
    rw [natCard_of_regularOn hpJ hp1 hreg haut]
    have := Nat.card_pos (α := K)
    omega
  have hJ : φ.range = jGroup A p := Subgroup.eq_of_le_of_card_ge hJ₀J (by rw [hcardJ, hcardJ₀])
  refine ⟨W, hWc, fun j => ?_⟩
  rw [← hJ]
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨_, hβ2 _, hβ _⟩
  · rintro ⟨d, hj2, hj⟩
    refine ⟨Multiplicative.ofAdd d, ?_⟩
    exact eq_of_represents hZ (hβ d) hj (hβ2' d) (k' := 1) (by rw [pow_one]; exact hj2)

end Beta

end CFSG.ComponentClassification.RankTwoClassical
