module

public import CFSG.LieType.HighestRoot.CentSpinBasic
public import CFSG.LieType.HighestRoot.CentLinear

public section

namespace CFSG.LieType.HighestRoot

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Complements

variable {K : Type} [Field K] [Finite K] {G : Type*} [Group G]

theorem commute_of_normal_of_card_eq_three (hK : Nat.card K = 3) {z : G} (hz : orderOf z = 2)
    {Cc L : Subgroup G} (hCc : Cc ≤ Subgroup.centralizer ({z} : Set G))
    (hCcn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Cc : Set G))
    (hzCc : z ∉ Cc) (hL : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLe : Nonempty (L ≃* SL(2, K))) (hzL : z ∈ L) : ∀ x ∈ L, ∀ y ∈ Cc, Commute x y := by
  obtain ⟨e⟩ := hLe
  have hzL' : orderOf (⟨z, hzL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz
  have hdisj : ∀ y ∈ L, y ∈ Cc → y = 1 := by
    intro y hyL hyC
    have hNn : (Cc.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hCcn (hL g.2)) n).1 hn⟩
    by_cases hNZ : Cc.subgroupOf L ≤ Subgroup.center L
    · have hc := (mem_center_iff_of_mulEquiv hK e _).1
        (hNZ (show (⟨y, hyL⟩ : L) ∈ Cc.subgroupOf L from hyC))
      rcases hc with h1 | h1
      · have : (⟨y, hyL⟩ : L) = 1 :=
          (e.trans (slEquivSL23 hK)).injective (by rw [h1, map_one])
        exact congrArg Subtype.val this
      · exfalso
        have hy2 : orderOf (⟨y, hyL⟩ : L) = 2 := by
          rw [← orderOf_injective (e.trans (slEquivSL23 hK)).toMonoidHom
            (e.trans (slEquivSL23 hK)).injective]
          simp only [MulEquiv.coe_toMonoidHom]
          rw [h1, orderOf_neg_one_SL23]
        have hyz : y = z := congrArg Subtype.val (eq_of_orderOf_eq_two_of_mulEquiv hK e hy2 hzL')
        exact hzCc (hyz ▸ hyC)
    · exfalso
      have h8 := eight_le_card_of_normal hK e _ hNZ
      have h24 := card_eq_24 hK e
      have : Finite L := Nat.finite_of_card_ne_zero (by omega)
      have hdvd : Nat.card (Cc.subgroupOf L) ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card _
      have h2 : 2 ∣ Nat.card (Cc.subgroupOf L) := by
        obtain ⟨k, hk⟩ := hdvd
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | hk4
        · omega
        · exact ⟨12, by omega⟩
        · exact ⟨6, by omega⟩
        · exact ⟨4, by omega⟩
        · nlinarith
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hw' : orderOf (w : L) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact hw
      have hwz : ((w : L) : G) = z :=
        congrArg Subtype.val (eq_of_orderOf_eq_two_of_mulEquiv hK e hw' hzL')
      have hwC : ((w : L) : G) ∈ Cc := Subgroup.mem_subgroupOf.1 w.2
      rw [hwz] at hwC
      exact hzCc hwC
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ L := by
    have : y * x⁻¹ * y⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hLn (hCc hy)) _).1 (inv_mem hx)
    rw [mul_assoc, mul_assoc]
    exact mul_mem hx (by rwa [← mul_assoc])
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ Cc :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 (hCcn (hL hx)) y).1 hy) (inv_mem hy)
  have h3' := hdisj _ h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3'
  exact h3'

theorem eq_of_normal_of_orderOf_three_of_two (hK : Nat.card K = 3) {z : G} (hz : orderOf z = 2)
    {R C₁ C₂ L : Subgroup G} (hR : Nonempty (R ≃* SL(2, K)))
    (hC₁ : C₁ ≤ Subgroup.centralizer ({z} : Set G))
    (hC₁n : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (C₁ : Set G))
    (hzC₁ : z ∉ C₁) (hC₂ : C₂ ≤ Subgroup.centralizer ({z} : Set G))
    (hC₂n : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (C₂ : Set G))
    (hzC₂ : z ∉ C₂)
    (h3 : ∀ x ∈ Subgroup.centralizer ({z} : Set G), orderOf x = 3 →
      (∀ y ∈ C₁, Commute x y) → (∀ y ∈ C₂, Commute x y) → x ∈ R)
    (hL : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLe : Nonempty (L ≃* SL(2, K))) (hzL : z ∈ L) : L = R := by
  have hc₁ := commute_of_normal_of_card_eq_three hK hz hC₁ hC₁n hzC₁ hL hLn hLe hzL
  have hc₂ := commute_of_normal_of_card_eq_three hK hz hC₂ hC₂n hzC₂ hL hLn hLe hzL
  obtain ⟨e⟩ := hLe
  obtain ⟨eR⟩ := hR
  have hLR : L ≤ R := by
    intro x hx
    have hx' : (⟨x, hx⟩ : L) ∈ Subgroup.closure {y : L | orderOf y = 3} := by
      rw [closure_orderOf_three_eq_top_of_mulEquiv hK e]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure {y : L | orderOf y = 3} ≤ R.comap L.subtype := by
      rw [Subgroup.closure_le]
      intro y hy
      have hy3 : orderOf (y : G) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact hy
      exact h3 y (hL y.2) hy3 (fun c hc => hc₁ y y.2 c hc) (fun c hc => hc₂ y y.2 c hc)
    exact hle hx'
  have hRfin : Finite R := Nat.finite_of_card_ne_zero (by rw [card_eq_24 hK eR]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hLR (by rw [card_eq_24 hK eR, card_eq_24 hK e])

end Complements

section Scalar

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem commute_eichler_identity (M : V →ₗ[K] V) (u w : V) (a : K)
    (h : ∀ x, M (x + polar Q x u • (a • w) - polar Q x (a • w) • u -
        (Q (a • w) * polar Q x u) • u) =
      M x + polar Q (M x) u • (a • w) - polar Q (M x) (a • w) • u -
        (Q (a • w) * polar Q (M x) u) • u) (x : V) :
    a • (polar Q x u • M w - polar Q x w • M u - polar Q (M x) u • w + polar Q (M x) w • u) +
      (a ^ 2 * Q w) • (polar Q (M x) u • u - polar Q x u • M u) = 0 := by
  have hx := h x
  simp only [map_add, map_sub, map_smul, polar_smul_right_eq, map_smul_eq_sq] at hx
  linear_combination (norm := module) hx

theorem exists_smul_of_commute_eichler {U : Submodule K V} (P : HypPair Q) (heU : P.e ∈ U)
    (hfU : P.f ∈ U) {w₀ : V} (hw₀U : w₀ ∈ U) (hw₀ : w₀ ∈ P.perp) (hQw₀ : Q w₀ ≠ 0) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (M : V →ₗ[K] V)
    (hM : ∀ u, (u = P.e ∨ u = P.f) → ∀ w ∈ U, w ∈ P.perp → ∀ a : K, ∀ x,
      M (x + polar Q x u • (a • w) - polar Q x (a • w) • u - (Q (a • w) * polar Q x u) • u) =
        M x + polar Q (M x) u • (a • w) - polar Q (M x) (a • w) • u -
          (Q (a • w) * polar Q (M x) u) • u) :
    ∃ l : K, ∀ x ∈ U, M x = l • x := by
  have hc2 : c - c ^ 2 ≠ 0 := by
    rw [show c - c ^ 2 = c * (1 - c) by ring]
    exact mul_ne_zero hc0 (sub_ne_zero.mpr hc1.symm)
  have hcc : (c - c ^ 2) * Q w₀ ≠ 0 := mul_ne_zero hc2 hQw₀
  have key : ∀ u, (u = P.e ∨ u = P.f) →
      (∀ x, polar Q (M x) u • u = polar Q x u • M u) ∧
      ∀ w ∈ U, w ∈ P.perp → ∀ x,
        polar Q x u • M w - polar Q x w • M u - polar Q (M x) u • w + polar Q (M x) w • u = 0 := by
    intro u hu
    have hY : ∀ x, polar Q (M x) u • u - polar Q x u • M u = 0 := by
      intro x
      have h1 := commute_eichler_identity M u w₀ 1 (hM u hu w₀ hw₀U hw₀ 1) x
      have h2 := commute_eichler_identity M u w₀ c (hM u hu w₀ hw₀U hw₀ c) x
      have h3 : ((c - c ^ 2) * Q w₀) • (polar Q (M x) u • u - polar Q x u • M u) = 0 := by
        linear_combination (norm := module) c • h1 - h2
      exact (smul_eq_zero.mp h3).resolve_left hcc
    refine ⟨fun x => sub_eq_zero.mp (hY x), fun w hwU hw x => ?_⟩
    have h1 := commute_eichler_identity M u w 1 (hM u hu w hwU hw 1) x
    rwa [hY x, smul_zero, add_zero, one_smul] at h1
  obtain ⟨hYe, hXe⟩ := key P.e (Or.inl rfl)
  obtain ⟨hYf, -⟩ := key P.f (Or.inr rfl)
  set l := polar Q (M P.f) P.e with hl
  have hMe : M P.e = l • P.e := by
    have := hYe P.f
    rw [P.polar_fe, one_smul] at this
    exact this.symm
  have hMf : M P.f = l • P.f := by
    have := hYf P.e
    rw [P.polar_ef, one_smul, hMe, polar_smul_left_eq, P.polar_ef, mul_one] at this
    exact this.symm
  have hMw : ∀ w ∈ U, w ∈ P.perp → M w = l • w := by
    intro w hwU hw
    have hwf := (HypPair.mem_perp.mp hw).2
    have := hXe w hwU hw P.f
    rw [P.polar_fe, hwf, ← hl, hMf, polar_smul_left_eq, hwf, mul_zero, one_smul, zero_smul,
      sub_zero, zero_smul, add_zero, sub_eq_zero] at this
    exact this
  refine ⟨l, fun x hx => ?_⟩
  have hpU : P.proj x ∈ U := by
    rw [HypPair.proj]
    exact U.sub_mem (U.sub_mem hx (U.smul_mem _ heU)) (U.smul_mem _ hfU)
  rw [P.eq_add_proj x, map_add, map_add, map_smul, map_smul, hMe, hMf,
    hMw _ hpU (P.proj_mem_perp x), smul_add, smul_add, smul_comm l _ P.e, smul_comm l _ P.f]

theorem eq_mul_of_forall_specialLinear {T : Module.End K (Matrix (Fin 2) (Fin 2) K)}
    {A : Matrix (Fin 2) (Fin 2) K} (h : ∀ B : SL(2, K), T B = A * B)
    (X : Matrix (Fin 2) (Fin 2) K) : T X = A * X := by
  have h1 : T 1 = A * 1 := by
    have := h 1
    rwa [Matrix.SpecialLinearGroup.coe_one] at this
  have hU : T !![1, 1; 0, 1] = A * !![1, 1; 0, 1] := by
    have := h (upperSL2 1)
    rwa [coe_upperSL2] at this
  have hL : T !![1, 0; 1, 1] = A * !![1, 0; 1, 1] := by
    have := h (lowerSL2 1)
    rwa [coe_lowerSL2] at this
  have hUL : T !![2, 1; 1, 1] = A * !![2, 1; 1, 1] := by
    have e : ((upperSL2 (1 : K) * lowerSL2 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        !![2, 1; 1, 1] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2, coe_lowerSL2]
      ext a b
      fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    have := h (upperSL2 1 * lowerSL2 1)
    rwa [e] at this
  have hX : X = X 0 0 • (!![2, 1; 1, 1] - !![1, 1; 0, 1] - !![1, 0; 1, 1] + 1) +
      X 0 1 • (!![1, 1; 0, 1] - 1) + X 1 0 • (!![1, 0; 1, 1] - 1) +
      X 1 1 • (1 - (!![2, 1; 1, 1] - !![1, 1; 0, 1] - !![1, 0; 1, 1] + 1)) := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num
  rw [hX]
  simp only [map_add, map_sub, map_smul, hU, hL, hUL, h1, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_smul]

end Scalar

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
  (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)

@[expose] noncomputable def planeFixer : Subgroup (spinGroup Q) where
  carrier := {y | y * F₀.longSL2 hij s t (-1) = F₀.longSL2 hij s t (-1) * y ∧
    ∀ v ∈ (F₀.toFrame hij s t).span, spinAction Q y v = v}
  mul_mem' := by
    rintro y y' ⟨hy, hyv⟩ ⟨hy', hy'v⟩
    refine ⟨by rw [mul_assoc, hy', ← mul_assoc, hy, mul_assoc], fun v hv => ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, hy'v v hv, hyv v hv]
  one_mem' := ⟨by rw [one_mul, mul_one], fun v _ => by rw [map_one]; rfl⟩
  inv_mem' := by
    rintro y ⟨hy, hyv⟩
    refine ⟨?_, fun v hv => ?_⟩
    · calc y⁻¹ * F₀.longSL2 hij s t (-1) = y⁻¹ * (F₀.longSL2 hij s t (-1) * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * F₀.longSL2 hij s t (-1)) * y⁻¹ := by rw [hy]
        _ = F₀.longSL2 hij s t (-1) * y⁻¹ := by group
    · calc spinAction Q y⁻¹ v = spinAction Q y⁻¹ (spinAction Q y v) := by rw [hyv v hv]
        _ = v := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_planeFixer {y : spinGroup Q} :
    y ∈ planeFixer F₀ hij s t ↔ y * F₀.longSL2 hij s t (-1) = F₀.longSL2 hij s t (-1) * y ∧
      ∀ v ∈ (F₀.toFrame hij s t).span, spinAction Q y v = v := Iff.rfl

theorem planeFixer_le_centralizer :
    planeFixer F₀ hij s t ≤ Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)) :=
  fun _ hy => Subgroup.mem_centralizer_singleton_iff.mpr hy.1

theorem commute_La_of_mem_centralizer {c : spinGroup Q}
    (hc : c ∈ Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q))) :
    spinAction Q c * (F₀.toFrame hij s t).La (-1) =
      (F₀.toFrame hij s t).La (-1) * spinAction Q c := by
  rw [← spinAction_longSL2, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]

theorem conj_mem_planeFixer (h2 : (2 : K) ≠ 0) {c : spinGroup Q}
    (hc : c ∈ Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)))
    {y : spinGroup Q} (hy : y ∈ planeFixer F₀ hij s t) : c * y * c⁻¹ ∈ planeFixer F₀ hij s t := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mp (mul_mem (mul_mem hc
    (planeFixer_le_centralizer F₀ hij s t hy)) (inv_mem hc)), fun v hv => ?_⟩
  have hg' := commute_La_of_mem_centralizer F₀ hij s t (inv_mem hc)
  have hv' := Frame.map_mem_span h2 hg' hv
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hy.2 _ hv',
    ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem centralizer_le_normalizer_planeFixer (h2 : (2 : K) ≠ 0) :
    Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)) ≤
      Subgroup.normalizer (planeFixer F₀ hij s t : Set (spinGroup Q)) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_planeFixer F₀ hij s t h2 hc hy, fun hy => ?_⟩
  have := conj_mem_planeFixer F₀ hij s t h2 (inv_mem hc) hy
  rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at this

theorem longSL2_neg_one_notMem_planeFixer (h2 : (2 : K) ≠ 0) :
    F₀.longSL2 hij s t (-1) ∉ planeFixer F₀ hij s t := by
  intro h
  have hmem : (F₀.toFrame hij s t).e₁ ∈ (F₀.toFrame hij s t).span :=
    ⟨_, (Frame.e₁_eq_incl (F₀.toFrame hij s t)).symm⟩
  have h1 := h.2 _ hmem
  rw [spinAction_longSL2, (Frame.mem_span_iff_inv _ h2).mp hmem] at h1
  have h0 : (2 : K) • (F₀.toFrame hij s t).e₁ = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    exact neg_add_cancel _
  exact hypFrame_vec_ne_zero F₀ i s ((smul_eq_zero.mp h0).resolve_left h2)

theorem polar_eq_zero_of_mem_perp {x : V} (hx : x ∈ (F₀.toFrame hij s t).perp) :
    polar Q x (F₀.vec i s) = 0 ∧ polar Q x (F₀.vec i (!s)) = 0 ∧
      polar Q x (F₀.vec j t) = 0 ∧ polar Q x (F₀.vec j (!t)) = 0 := by
  rw [Frame.mem_perp_iff_forall_incl] at hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hx !![1, 0; 0, 0]
    rwa [← Frame.e₁_eq_incl] at this
  · have := hx !![0, 0; 0, 1]
    rwa [← Frame.f₁_eq_incl] at this
  · have := hx !![0, -1; 0, 0]
    rwa [← Frame.e₂_eq_incl] at this
  · have := hx !![0, 0; 1, 0]
    rwa [← Frame.f₂_eq_incl] at this

theorem rootElt_mem_planeFixer {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (huP : u ∈ (F₀.toFrame hij s t).perp) (hwP : w ∈ (F₀.toFrame hij s t).perp)
    {y : spinGroup Q} (hy : (y : CliffordAlgebra Q) = 1 + ι Q w * ι Q u) :
    y ∈ planeFixer F₀ hij s t := by
  obtain ⟨hu1, hu2, hu3, hu4⟩ := polar_eq_zero_of_mem_perp F₀ hij s t huP
  obtain ⟨hw1, hw2, hw3, hw4⟩ := polar_eq_zero_of_mem_perp F₀ hij s t hwP
  have hX : Commute (ι Q w * ι Q u) (F₀.longPair hij s t).X :=
    commute_ι_mul_ι Q hw1 hw3 hu1 hu3
  have hY : Commute (ι Q w * ι Q u) (F₀.longPair hij s t).Y :=
    commute_ι_mul_ι Q hw4 hw2 hu4 hu2
  have hS : Commute (ι Q w * ι Q u) ((F₀.longPair hij s t).X * (F₀.longPair hij s t).Y +
      (F₀.longPair hij s t).Y * (F₀.longPair hij s t).X) :=
    (hX.mul_right hY).add_right (hY.mul_right hX)
  refine ⟨Subtype.ext ?_, fun v hv => ?_⟩
  · rw [Submonoid.coe_mul, Submonoid.coe_mul, hy, coe_longSL2_neg_one]
    exact ((Commute.one_left _).add_left ((Commute.one_right _).sub_right (hS.smul_right _))).eq
  · obtain ⟨X, rfl⟩ := hv
    have h1 : polar Q ((F₀.toFrame hij s t).incl X) u = 0 := by
      rw [polar_comm]
      exact (Frame.mem_perp_iff_forall_incl _).mp huP X
    have h2 : polar Q ((F₀.toFrame hij s t).incl X) w = 0 := by
      rw [polar_comm]
      exact (Frame.mem_perp_iff_forall_incl _).mp hwP X
    rw [spinAction_apply_of_coe_eq Q hu huw hy, h1, h2, zero_smul, zero_smul, mul_zero,
      zero_smul, add_zero, sub_zero, sub_zero]

theorem swap_La_incl (fr : Frame Q) (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    fr.swap.La A (fr.incl X) = fr.incl (X * sigmaLin (A : Matrix (Fin 2) (Fin 2) K)) := by
  rw [Frame.La_swap_apply, Frame.embLin_apply_eq, Frame.coords_incl, sub_self, add_zero]
  rfl

theorem mem_range_longSL2_of_orderOf_eq_three [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : Q.Nondegenerate) {l : Fin m} (hli : l ≠ i) (hlj : l ≠ j) {w₀ : V}
    (hw₀ : ∀ r, polar Q (F₀.vec i r) w₀ = 0 ∧ polar Q (F₀.vec j r) w₀ = 0 ∧
      polar Q (F₀.vec l r) w₀ = 0) (hQw₀ : Q w₀ ≠ 0) {x : spinGroup Q}
    (hx : x ∈ Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)))
    (h3 : orderOf x = 3) (hc₁ : ∀ y ∈ (F₀.longSL2 hij s (!t)).range, Commute x y)
    (hc₂ : ∀ y ∈ planeFixer F₀ hij s t, Commute x y) : x ∈ (F₀.longSL2 hij s t).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_eq_three hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Nontrivial V := ⟨⟨F₀.vec i s, 0, hypFrame_vec_ne_zero F₀ i s⟩⟩
  have hgO : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)
  have hg := commute_La_of_mem_centralizer F₀ hij s t hx
  have hx3 : x ^ 3 = 1 := h3 ▸ pow_orderOf_eq_one x
  have hperp : ∀ v : V, (∀ r, polar Q (F₀.vec i r) v = 0 ∧ polar Q (F₀.vec j r) v = 0) →
      v ∈ (F₀.toFrame hij s t).perp := by
    intro v hv
    rw [Frame.mem_perp_iff]
    have e1 := (hv s).1
    have e2 := (hv (!s)).1
    have e3 := (hv t).2
    have e4 := (hv (!t)).2
    rw [polar_comm] at e1 e2 e3 e4
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Frame.coords_apply, HypFrame.toFrame, e1, e2, e3, e4]
  have hlP : ∀ r, F₀.vec l r ∈ (F₀.toFrame hij s t).perp := fun r => hperp _ fun r' =>
    ⟨F₀.polar_vec_of_ne hli.symm r' r, F₀.polar_vec_of_ne hlj.symm r' r⟩
  have hw₀U : w₀ ∈ (F₀.toFrame hij s t).perp := hperp _ fun r => ⟨(hw₀ r).1, (hw₀ r).2.1⟩
  let P : HypPair Q := ⟨F₀.vec l true, F₀.vec l false, F₀.map_vec l true, F₀.map_vec l false,
    F₀.polar_vec_not l true⟩
  have hw₀P : w₀ ∈ P.perp := HypPair.mem_perp.mpr ⟨(hw₀ true).2.2, (hw₀ false).2.2⟩
  have hQa : Q (F₀.vec i s + F₀.vec i (!s)) = 1 := by
    rw [QuadraticMap.map_add Q, F₀.map_vec, F₀.map_vec, F₀.polar_vec_not, zero_add, zero_add]
  have hpa : ∀ v ∈ (F₀.toFrame hij s t).perp, polar Q v (F₀.vec i s + F₀.vec i (!s)) = 0 :=
    fun v hv => by
      obtain ⟨h1, h2, -, -⟩ := polar_eq_zero_of_mem_perp F₀ hij s t hv
      rw [polar_add_right, h1, h2, add_zero]
  have hc1 : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  obtain ⟨μ, hμ⟩ := exists_smul_of_commute_eichler (U := (F₀.toFrame hij s t).perp) P
    (hlP true) (hlP false) hw₀U hw₀P hQw₀ (neg_ne_zero.mpr one_ne_zero) hc1
    (spinAction Q x : V →ₗ[K] V) (fun u hu w hwU hwP a v => by
      have huU : u ∈ (F₀.toFrame hij s t).perp := by
        rcases hu with rfl | rfl
        · exact hlP true
        · exact hlP false
      have hu0 : Q u = 0 := by
        rcases hu with rfl | rfl
        · exact F₀.map_vec l true
        · exact F₀.map_vec l false
      have huw : polar Q u w = 0 := by
        rcases hu with rfl | rfl
        · exact (HypPair.mem_perp.mp hwP).1
        · exact (HypPair.mem_perp.mp hwP).2
      have huw' : polar Q u (a • w) = 0 := by rw [polar_smul_right_eq, huw, mul_zero]
      have hmem := one_add_smul_ι_mul_ι_mem_spinGroup Q hu0 huw (hpa u huU) (hpa w hwU)
        (by rw [hQa]; exact isUnit_one) a
      have hcoe : ((⟨_, hmem⟩ : spinGroup Q) : CliffordAlgebra Q) =
          1 + ι Q (a • w) * ι Q u := by
        show 1 + a • (ι Q w * ι Q u) = _
        rw [map_smul, smul_mul_assoc]
      have hy := rootElt_mem_planeFixer F₀ hij s t hu0 huw' huU
        ((F₀.toFrame hij s t).perp.smul_mem a hwU) hcoe
      have hcomm := congrArg (fun g : spinGroup Q => spinAction Q g v) (hc₂ _ hy).eq
      simp only [map_mul, LinearEquiv.mul_apply] at hcomm
      rw [spinAction_apply_of_coe_eq Q hu0 huw' hcoe, spinAction_apply_of_coe_eq Q hu0 huw' hcoe]
        at hcomm
      simpa only [LinearEquiv.coe_coe] using hcomm)
  have hμ1 : μ = 1 := by
    have he := hμ _ (hlP true)
    simp only [LinearEquiv.coe_coe] at he
    have h3e : spinAction Q (x ^ 3) (F₀.vec l true) = μ ^ 3 • F₀.vec l true := by
      simp only [pow_three, map_mul, LinearEquiv.mul_apply, he, map_smul, smul_smul, mul_assoc]
    rw [hx3, map_one] at h3e
    have h3e' : F₀.vec l true = μ ^ 3 • F₀.vec l true := h3e
    have h0 : (μ ^ 3 - 1) • F₀.vec l true = 0 := by
      rw [sub_smul, one_smul, ← h3e', sub_self]
    exact eq_one_of_pow_three_eq_one hK
      (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right (hypFrame_vec_ne_zero F₀ l true)))
  have hTB : ∀ (X : Matrix (Fin 2) (Fin 2) K) (B : SL(2, K)),
      (F₀.toFrame hij s t).transport (spinAction Q x) (X * B) =
        (F₀.toFrame hij s t).transport (spinAction Q x) X * B := by
    intro X B
    have hcomm := congrArg (fun g : spinGroup Q => spinAction Q g ((F₀.toFrame hij s t).incl X))
      (hc₁ _ ⟨Frame.sigmaSL B, rfl⟩).eq
    simp only [map_mul, LinearEquiv.mul_apply, spinAction_longSL2, toFrame_not] at hcomm
    rw [swap_La_incl, ← Frame.incl_transport h2 hg, ← Frame.incl_transport h2 hg, swap_La_incl,
      Frame.coe_sigmaSL, sigmaLin_sigmaLin] at hcomm
    have := congrArg (F₀.toFrame hij s t).coords hcomm
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  have hTX := eq_mul_of_forall_specialLinear (fun B => by
    simpa only [Matrix.one_mul] using hTB 1 B)
  have hdet : ((F₀.toFrame hij s t).transport (spinAction Q x) 1).det = 1 := by
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (Frame.transportEquiv_mem_orthogonalGroup h2 hgO hg) 1
    rwa [detQ_apply, detQ_apply, Frame.transportEquiv_apply, Matrix.det_one] at this
  set A : SL(2, K) := ⟨(F₀.toFrame hij s t).transport (spinAction Q x) 1, hdet⟩ with hA
  have hπ : spinAction Q x = spinAction Q (F₀.longSL2 hij s t A) := by
    rw [spinAction_longSL2]
    refine LinearEquiv.ext fun v => ?_
    have hr : v - (F₀.toFrame hij s t).incl ((F₀.toFrame hij s t).coords v) ∈
        (F₀.toFrame hij s t).perp := by
      rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
    have hv : v = (F₀.toFrame hij s t).incl ((F₀.toFrame hij s t).coords v) +
        (v - (F₀.toFrame hij s t).incl ((F₀.toFrame hij s t).coords v)) := by abel
    have hμr := hμ _ hr
    simp only [LinearEquiv.coe_coe] at hμr
    rw [Frame.La_apply]
    conv_lhs => rw [hv]
    rw [map_add, ← Frame.incl_transport h2 hg, hTX, hμr, hμ1, one_smul, map_sub]
    show _ = v + ((F₀.toFrame hij s t).incl
      ((F₀.toFrame hij s t).transport (spinAction Q x) 1 * (F₀.toFrame hij s t).coords v) -
        (F₀.toFrame hij s t).incl ((F₀.toFrame hij s t).coords v))
    abel
  have hsq := mul_self_eq_of_spinAction_eq hQ hπ
  have hx4 : x = (x * x) * (x * x) := by
    calc x = x * x ^ 3 := by rw [hx3, mul_one]
      _ = (x * x) * (x * x) := by rw [pow_three]; simp only [mul_assoc]
  rw [hx4, hsq, ← map_mul, ← map_mul]
  exact ⟨_, rfl⟩

theorem centralizerCondition_longSL2 [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : Q.Nondegenerate) {l : Fin m} (hli : l ≠ i) (hlj : l ≠ j) {w₀ : V}
    (hw₀ : ∀ r, polar Q (F₀.vec i r) w₀ = 0 ∧ polar Q (F₀.vec j r) w₀ = 0 ∧
      polar Q (F₀.vec l r) w₀ = 0) (hQw₀ : Q w₀ ≠ 0) :
    CentralizerCondition K (F₀.longSL2 hij s t).range := by
  intro z hz hz2
  obtain rfl := eq_of_mem_range_longSL2_of_orderOf_eq_two F₀ hij s t h2 hz hz2
  refine ⟨centralizer_le_normalizer_longSL2 F₀ hij s t h2 hQ, fun hK L hLc hLn hLe hzL => ?_⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  refine eq_of_normal_of_orderOf_three_of_two hK hz2 (nonempty_mulEquiv_range_longSL2 F₀ hij s t)
    (C₁ := (F₀.longSL2 hij s (!t)).range) (C₂ := planeFixer F₀ hij s t) ?_ ?_ ?_
    (planeFixer_le_centralizer F₀ hij s t) (centralizer_le_normalizer_planeFixer F₀ hij s t h2)
    (longSL2_neg_one_notMem_planeFixer F₀ hij s t h2)
    (fun x hx h3 hc₁ hc₂ =>
      mem_range_longSL2_of_orderOf_eq_three F₀ hij s t hK hQ hli hlj hw₀ hQw₀ hx h3 hc₁ hc₂)
    hLc hLn hLe hzL
  · rw [← centralizer_longSL2_not_neg_one F₀ hij s t]
    rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp ((CFSG.ClassicalInvolution.mem_center_sl2_iff (-1)).mpr
        (Or.inr rfl)) B]
  · rw [← centralizer_longSL2_not_neg_one F₀ hij s t]
    exact centralizer_le_normalizer_longSL2 F₀ hij s (!t) h2 hQ
  · intro h
    have := eq_of_mem_range_longSL2_of_orderOf_eq_two F₀ hij s (!t) h2 h hz2
    exact coe_ne_neg_coe h2 _ ((congrArg Subtype.val this).trans
      (coe_longSL2_not_neg_one F₀ hij s t))

end CFSG.LieType.HighestRoot
