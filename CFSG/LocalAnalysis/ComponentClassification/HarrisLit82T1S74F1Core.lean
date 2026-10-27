module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1Rad

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section Core

variable {G : Type*} [Group G] {C : Subgroup G}

theorem oddCoreOf_le : oddCoreOf C ≤ C := map_subtype_le _

theorem conj_mem_oddCoreOf {c x : G} (hc : c ∈ C) (hx : x ∈ oddCoreOf C) :
    c * x * c⁻¹ ∈ oddCoreOf C := by
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (pPrimeCore_normal (p := 2) (G := C)).conj_mem y hy ⟨c, hc⟩, rfl⟩

theorem le_oddCoreOf {N : Subgroup G} (hNC : N ≤ C)
    (hN : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf C := by
  have hn : (N.subgroupOf C).Normal := ⟨fun n hn g => hN g g.2 n hn⟩
  have hcard : Nat.card (N.subgroupOf C) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv
  have hle : N.subgroupOf C ≤ pPrimeCore 2 C :=
    le_sSup ⟨hn, Nat.coprime_two_left.mpr (by rw [hcard]; exact hodd)⟩
  intro x hx
  exact ⟨⟨x, hNC hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

variable [Finite G]

theorem odd_card_oddCoreOf : Odd (Nat.card (oddCoreOf C)) := by
  show Odd (Nat.card ((pPrimeCore 2 C).map C.subtype))
  rw [card_map_of_injective C.subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))

theorem odd_orderOf_of_mem_oddCoreOf {x : G} (hx : x ∈ oddCoreOf C) : Odd (orderOf x) :=
  odd_card_oddCoreOf.of_dvd_nat ((oddCoreOf C).orderOf_dvd_natCard hx)

end Core

section Frame

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem La_swap_incl (F : Frame Q) (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    F.swap.La A (F.incl X) = F.incl (X * sigmaLin (A : Matrix (Fin 2) (Fin 2) K)) := by
  rw [Frame.La_swap_apply, Frame.embLin_apply_eq, Frame.coords_incl, sub_self, add_zero]
  rfl

theorem eq_smul_one_of_commute {A : Matrix (Fin 2) (Fin 2) K}
    (hU : A * !![1, 1; 0, 1] = !![1, 1; 0, 1] * A)
    (hL : A * !![1, 0; 1, 1] = !![1, 0; 1, 1] * A) :
    A = A 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have u00 : A 0 0 = A 0 0 + A 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 0
  have u01 : A 0 0 + A 0 1 = A 0 1 + A 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 1
  have l00 : A 0 0 + A 0 1 = A 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hL 0) 0
  have h10 : A 1 0 = 0 := by linear_combination -u00
  have h01 : A 0 1 = 0 := by linear_combination l00
  have h11 : A 1 1 = A 0 0 := by linear_combination -u01
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h10, h01, h11]

theorem eq_smul_of_forall_specialLinear {T : Module.End K (Matrix (Fin 2) (Fin 2) K)} {μ : K}
    (h : ∀ B : SL(2, K), T B = μ • (B : Matrix (Fin 2) (Fin 2) K))
    (X : Matrix (Fin 2) (Fin 2) K) : T X = μ • X := by
  have h1 : T 1 = μ • 1 := by
    have := h 1
    rwa [Matrix.SpecialLinearGroup.coe_one] at this
  have hU : T !![1, 1; 0, 1] = μ • !![1, 1; 0, 1] := by
    have := h (upperSL2 1)
    rwa [coe_upperSL2] at this
  have hL : T !![1, 0; 1, 1] = μ • !![1, 0; 1, 1] := by
    have := h (lowerSL2 1)
    rwa [coe_lowerSL2] at this
  have hUL : T !![2, 1; 1, 1] = μ • !![2, 1; 1, 1] := by
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
  simp only [map_add, map_sub, map_smul, hU, hL, hUL, h1]
  module

theorem det_transportEquiv_ne_neg_one {F : Frame Q} (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g * F.La (-1) = F.La (-1) * g) (hodd : Odd (orderOf g)) :
    LinearEquiv.det (Frame.transportEquiv h2 hg) ≠ -1 := by
  intro hd
  have hpow : ∀ n : ℕ, F.transport (g ^ n) = F.transport g ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Frame.transport_one]
    | succ n ih => rw [pow_succ, pow_succ, Frame.transport_mul h2 hg, ih]
  have hT : ((Frame.transportEquiv h2 hg :
      Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) = F.transport g :=
    LinearMap.ext fun _ => rfl
  have hdet : LinearMap.det (F.transport g) = -1 := by
    rw [← hT, ← LinearEquiv.coe_det, hd, Units.val_neg, Units.val_one]
  have h1 : LinearMap.det (F.transport g) ^ orderOf g = 1 := by
    rw [← map_pow LinearMap.det, ← hpow, pow_orderOf_eq_one, Frame.transport_one, map_one]
  rw [hdet, hodd.neg_one_pow] at h1
  exact h2 (by linear_combination -h1)

theorem exists_smul_of_commute_La (F : Frame Q) (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : g * F.La (-1) = F.La (-1) * g)
    (hL : ∀ A, g * F.La A = F.La A * g) (hR : ∀ A, g * F.swap.La A = F.swap.La A * g) :
    ∃ μ : K, μ * μ = 1 ∧ ∀ X, g (F.incl X) = μ • F.incl X := by
  have hTL : ∀ (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      F.transport g ((A : Matrix (Fin 2) (Fin 2) K) * X) =
        (A : Matrix (Fin 2) (Fin 2) K) * F.transport g X := by
    intro A X
    have h := LinearEquiv.congr_fun (hL A) (F.incl X)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply_incl,
      ← Frame.incl_transport h2 hg, ← Frame.incl_transport h2 hg, Frame.La_apply_incl] at h
    simpa only [Frame.coords_incl] using congrArg F.coords h
  have hTR : ∀ (B : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      F.transport g (X * (B : Matrix (Fin 2) (Fin 2) K)) =
        F.transport g X * (B : Matrix (Fin 2) (Fin 2) K) := by
    intro B X
    have h := LinearEquiv.congr_fun (hR (Frame.sigmaSL B)) (F.incl X)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_swap_incl,
      ← Frame.incl_transport h2 hg, ← Frame.incl_transport h2 hg, La_swap_incl,
      Frame.coe_sigmaSL, sigmaLin_sigmaLin] at h
    simpa only [Frame.coords_incl] using congrArg F.coords h
  have hcomm : ∀ B : SL(2, K), F.transport g 1 * (B : Matrix (Fin 2) (Fin 2) K) =
      (B : Matrix (Fin 2) (Fin 2) K) * F.transport g 1 := fun B => by
    have e1 := hTR B 1
    have e2 := hTL B 1
    rw [Matrix.one_mul] at e1
    rw [Matrix.mul_one] at e2
    exact e1.symm.trans e2
  have hU := hcomm (upperSL2 1)
  have hL' := hcomm (lowerSL2 1)
  rw [coe_upperSL2] at hU
  rw [coe_lowerSL2] at hL'
  obtain ⟨μ, hμ1⟩ : ∃ μ : K, F.transport g 1 = μ • (1 : Matrix (Fin 2) (Fin 2) K) :=
    ⟨_, eq_smul_one_of_commute hU hL'⟩
  have hTX : ∀ X, F.transport g X = μ • X := eq_smul_of_forall_specialLinear fun B => by
    have e1 := hTR B 1
    rw [Matrix.one_mul, hμ1, Matrix.smul_mul, Matrix.one_mul] at e1
    exact e1
  have hgW : ∀ X, g (F.incl X) = μ • F.incl X := fun X => by
    rw [← Frame.incl_transport h2 hg, hTX, map_smul]
  refine ⟨μ, ?_, hgW⟩
  have h1 := map_of_mem hgO (F.incl 1)
  rw [hgW, QuadraticMap.map_smul, F.Q_incl, Matrix.det_one, smul_eq_mul, mul_one] at h1
  exact h1

theorem commute_La_of_mem_oddCoreOf [Finite K] {G : Type*} [Group G] [Finite G]
    {C : Subgroup G} (ρ : G →* (V ≃ₗ[K] V)) (F : Frame Q) (j : SL(2, K) →* G)
    (hjC : ∀ A, j A ∈ C) (hjρ : ∀ A, ρ (j A) = F.La A) (hK : Odd (Nat.card K))
    (h3 : 3 ≤ Nat.card K) {l : G} (hl : l ∈ oddCoreOf C)
    (hconj : ∀ A, ρ l * F.La A * (ρ l)⁻¹ ∈ F.La.range) (A : SL(2, K)) :
    ρ l * F.La A = F.La A * ρ l := by
  have hN : (((oddCoreOf C).map ρ).comap F.La).Normal := ⟨fun A hA B => by
    obtain ⟨o, ho, hoA⟩ := mem_map.mp (mem_comap.mp hA)
    refine mem_comap.mpr (mem_map.mpr ⟨j B * o * (j B)⁻¹, conj_mem_oddCoreOf (hjC B) ho, ?_⟩)
    simp only [map_mul, map_inv, hjρ, hoA]⟩
  have hNodd : Odd (Nat.card (((oddCoreOf C).map ρ).comap F.La)) := by
    have e1 : Nat.card ((((oddCoreOf C).map ρ).comap F.La).map F.La) =
        Nat.card (((oddCoreOf C).map ρ).comap F.La) := card_map_of_injective F.La_injective
    have e2 := card_dvd_of_le (map_comap_le F.La ((oddCoreOf C).map ρ))
    have e3 := card_map_dvd (H := oddCoreOf C) ρ
    rw [← e1]
    exact (odd_card_oddCoreOf.of_dvd_nat e3).of_dvd_nat e2
  have hbot := CFSG.Semidihedral.OddLinearNormals.normal_odd_specialLinear_eq_bot K hK h3 _ hN
    hNodd
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp (hconj A)
  have hBA : B * A⁻¹ ∈ ((oddCoreOf C).map ρ).comap F.La := by
    refine mem_comap.mpr (mem_map.mpr ⟨l * (j A * l⁻¹ * (j A)⁻¹),
      mul_mem hl (conj_mem_oddCoreOf (hjC A) (inv_mem hl)), ?_⟩)
    simp only [map_mul, map_inv, hjρ, hB, mul_assoc]
  rw [hbot, mem_bot, mul_inv_eq_one] at hBA
  rw [hBA] at hB
  exact mul_inv_eq_iff_eq_mul.mp hB.symm

end Frame

section FourT

variable {K : Type} [Field K]

theorem mem_fourT_of_spinAction_eq (h2 : (2 : K) ≠ 0) {y : spinGroup (quadOdd 3 K)}
    (hy : spinAction (quadOdd 3 K) y = (frame01 K).La (-1)) : y ∈ fourT K := by
  have h1 : spinAction (quadOdd 3 K) (y * (tSeven K)⁻¹) = 1 := by
    rw [map_mul, map_inv, hy, spinAction_tSeven, mul_inv_cancel]
  have ht : tSeven K ∈ fourT K := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hz : spinZ K ∈ fourT K := subset_closure (Set.mem_insert _ _)
  rcases eq_one_or_eq_spinZ h2 h1 with h | h
  · rw [mul_inv_eq_one.mp h]
    exact ht
  · have e : y = spinZ K * tSeven K := by rw [← h, inv_mul_cancel_right]
    rw [e]
    exact mul_mem hz ht

theorem conj_mem_fourT (h2 : (2 : K) ≠ 0) {l : spinGroup (quadOdd 3 K)}
    (hl : spinAction (quadOdd 3 K) l * (frame01 K).La (-1) =
      (frame01 K).La (-1) * spinAction (quadOdd 3 K) l) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ fourT K) : l * x * l⁻¹ ∈ fourT K := by
  induction hx using closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [← spinZ_commute l, mul_inv_cancel_right]
      exact subset_closure (Set.mem_insert _ _)
    · refine mem_fourT_of_spinAction_eq h2 ?_
      rw [map_mul, map_mul, map_inv, spinAction_tSeven, hl, mul_inv_cancel_right]
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul a b _ _ iha ihb =>
    rw [show l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) by group]
    exact mul_mem iha ihb
  | inv a _ iha =>
    rw [show l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ by group]
    exact inv_mem iha

theorem mem_normalizer_fourT (h2 : (2 : K) ≠ 0) {l : spinGroup (quadOdd 3 K)}
    (hl : spinAction (quadOdd 3 K) l * (frame01 K).La (-1) =
      (frame01 K).La (-1) * spinAction (quadOdd 3 K) l) :
    l ∈ normalizer (fourT K : Set (spinGroup (quadOdd 3 K))) := by
  have hl' : spinAction (quadOdd 3 K) l⁻¹ * (frame01 K).La (-1) =
      (frame01 K).La (-1) * spinAction (quadOdd 3 K) l⁻¹ := by
    rw [map_inv]
    exact Frame.inv_commute_La hl
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => conj_mem_fourT h2 hl hx, fun hx => ?_⟩
  have := conj_mem_fourT h2 hl' hx
  rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at this

end FourT

end CFSG.ComponentClassification.HarrisLit.T1.S74
