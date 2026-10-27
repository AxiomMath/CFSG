module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapD
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AP

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix Pointwise

namespace Sec8

open Sec7

namespace GapNH

theorem two_mul_eq_iff : ∀ x y : ZMod 4, 2 * x = 2 * y ↔ r2 x = r2 y := by decide

theorem exists_half : ∀ x : ZMod 4, r2 x = 0 → ∃ y : ZMod 4, x = 2 * y := by decide

theorem exists_add_self : ∀ x : ZMod 4, 2 * x = 0 → ∃ s : ZMod 4, x = s + s := by decide

theorem four_eq_zero : (2 * 2 : ZMod 4) = 0 := by decide

theorem redM_sub (M N : Matrix (Fin 3) (Fin 3) (ZMod 4)) : redM (M - N) = redM M - redM N :=
  Matrix.map_sub r2 (map_sub r2) M N

theorem exists_two_smul {M : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : redM M = 1) :
    ∃ W : Matrix (Fin 3) (Fin 3) (ZMod 4), M = 1 + (2 : ZMod 4) • W := by
  have h0 : redM (M - 1) = 0 := by rw [redM_sub, h, redM_one, sub_self]
  have hij : ∀ i j, ∃ y : ZMod 4, (M - 1) i j = 2 * y := fun i j =>
    exists_half _ (congrFun (congrFun h0 i) j)
  choose W hW using hij
  refine ⟨Matrix.of W, ?_⟩
  ext i j
  have := hW i j
  rw [Matrix.sub_apply] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← this]
  ring

theorem mul_two_smul (W W' : Matrix (Fin 3) (Fin 3) (ZMod 4)) :
    (1 + (2 : ZMod 4) • W) * (1 + (2 : ZMod 4) • W') = 1 + (2 : ZMod 4) • (W + W') := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    four_eq_zero, zero_smul, add_zero, smul_add]
  abel

theorem conj_two_smul {K K' : Matrix (Fin 3) (Fin 3) (ZMod 4)} (hK : K * K' = 1)
    (W : Matrix (Fin 3) (Fin 3) (ZMod 4)) :
    K * (1 + (2 : ZMod 4) • W) * K' = 1 + (2 : ZMod 4) • (K * W * K') := by
  rw [mul_add, mul_one, add_mul, hK, mul_smul_comm, smul_mul_assoc]

theorem redM_eq_zero_of {Z : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : 1 + (2 : ZMod 4) • Z = 1) :
    redM Z = 0 := by
  have h2 : (2 : ZMod 4) • Z = 0 := add_left_cancel (h.trans (add_zero 1).symm)
  ext i j
  have := congrFun (congrFun h2 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
  exact (r2_eq_zero_iff _).mpr this

theorem redM_eq_one_of {Z : Matrix (Fin 3) (Fin 3) (ZMod 4)} (h : 1 + (2 : ZMod 4) • Z = -1) :
    redM Z = 1 := by
  have h2 : (2 : ZMod 4) • Z = (2 : ZMod 4) • 1 := by
    have e : (2 : ZMod 4) • (1 : Matrix (Fin 3) (Fin 3) (ZMod 4)) = -1 - 1 := by
      rw [show (2 : ZMod 4) = -1 - 1 by decide, sub_smul, neg_smul, one_smul]
    rw [e, ← h]
    abel
  ext i j
  have := congrFun (congrFun h2 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at this
  rw [show redM Z i j = r2 (Z i j) from rfl, (two_mul_eq_iff _ _).mp this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem redM_add (M N : Matrix (Fin 3) (Fin 3) (ZMod 4)) : redM (M + N) = redM M + redM N :=
  Matrix.map_add r2 (map_add r2) M N

theorem comm_of_redM {M N : Matrix (Fin 3) (Fin 3) (ZMod 4)} (hM : redM M = 1)
    (hN : redM N = 1) : M * N = N * M := by
  obtain ⟨W, rfl⟩ := exists_two_smul hM
  obtain ⟨W', rfl⟩ := exists_two_smul hN
  rw [mul_two_smul, mul_two_smul, add_comm W]

theorem add_conj_ne_one (X Kb Kb' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : Kb' * Kb = 1) :
    X + Kb * X * Kb' ≠ 1 := by
  intro hX
  have := congrArg Matrix.trace hX
  rw [Matrix.trace_add, Matrix.trace_mul_cycle, h, one_mul, Matrix.trace_one,
    Fintype.card_fin] at this
  revert this
  generalize X.trace = τ
  revert τ
  decide

theorem comm_of_add {X Kb Kb' : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : Kb' * Kb = 1)
    (hX : X + Kb * X * Kb' = 0 ∨ X + Kb * X * Kb' = 1) : Kb * X = X * Kb := by
  rcases hX with hX | hX
  · have hneg : -X = X := by
      ext i j
      rw [Matrix.neg_apply]
      generalize X i j = a
      revert a
      decide
    have h1 : Kb * X * Kb' = X := by
      have := eq_neg_of_add_eq_zero_right hX
      rwa [hneg] at this
    calc Kb * X = Kb * X * (Kb' * Kb) := by rw [h, mul_one]
      _ = Kb * X * Kb' * Kb := by rw [mul_assoc (Kb * X)]
      _ = X * Kb := by rw [h1]
  · exact absurd hX (add_conj_ne_one X Kb Kb' h)

theorem entries_of_comm (X : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hK : blk 0 1 1 1 * X = X * blk 0 1 1 1) (hU : blk 1 1 0 1 * X = X * blk 1 1 0 1) :
    X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 1 1 = X 0 0 := by
  have eK : ∀ i j, (blk 0 1 1 1 * X) i j = (X * blk 0 1 1 1) i j := fun i j => by rw [hK]
  have eU : ∀ i j, (blk 1 1 0 1 * X) i j = (X * blk 1 1 0 1) i j := fun i j => by rw [hU]
  have u00 := eU 0 0
  have u01 := eU 0 1
  have u02 := eU 0 2
  have u21 := eU 2 1
  have k00 := eK 0 0
  have k12 := eK 1 2
  have k20 := eK 2 0
  have k21 := eK 2 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, blk] at u00 u01 u02 u21 k00 k12 k20 k21
  refine ⟨by rw [← k00, u00], k12, u00, u02, u21, by rw [← k20, u21], ?_⟩
  linear_combination u01

theorem diag_cases : ∀ a b : ZMod 4,
    (!![1 + 2 * a, 0, 0; 0, 1 + 2 * a, 0; 0, 0, 1 + 2 * b] = 1 ∨
      !![1 + 2 * a, 0, 0; 0, 1 + 2 * a, 0; 0, 0, 1 + 2 * b] = -1 ∨
      !![1 + 2 * a, 0, 0; 0, 1 + 2 * a, 0; 0, 0, 1 + 2 * b] = Dmat ∨
      !![1 + 2 * a, 0, 0; 0, 1 + 2 * a, 0; 0, 0, 1 + 2 * b] = -Dmat) := by
  decide

theorem mem_four {W : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (hK : blk 0 1 1 1 * redM W = redM W * blk 0 1 1 1)
    (hU : blk 1 1 0 1 * redM W = redM W * blk 1 1 0 1) :
    1 + (2 : ZMod 4) • W = 1 ∨ 1 + (2 : ZMod 4) • W = -1 ∨ 1 + (2 : ZMod 4) • W = Dmat ∨
      1 + (2 : ZMod 4) • W = -Dmat := by
  obtain ⟨h01, h02, h10, h12, h20, h21, h11⟩ := entries_of_comm (redM W) hK hU
  have z : ∀ i j, redM W i j = 0 → 2 * W i j = 0 := fun i j h => (r2_eq_zero_iff _).mp h
  have e11 : 2 * W 1 1 = 2 * W 0 0 := (two_mul_eq_iff _ _).mpr h11
  have e : 1 + (2 : ZMod 4) • W =
      !![1 + 2 * W 0 0, 0, 0; 0, 1 + 2 * W 0 0, 0; 0, 0, 1 + 2 * W 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [z _ _ h01, z _ _ h02, z _ _ h10, z _ _ h12, z _ _ h20, z _ _ h21, e11]
  rw [e]
  exact diag_cases _ _

theorem redM_Umat : redM Umat = blk 1 1 0 1 := by decide

theorem redM_Umat_ne : redM Umat ≠ 1 := by decide

theorem redM_neg_Umat_ne : redM (-Umat) ≠ 1 := by decide

theorem blk_sq : blk 1 1 1 0 * blk 1 1 1 0 = blk 0 1 1 1 := by decide

theorem exists_conj_le_of_max {X : Type} [Group X] [Finite X] {K P R : Subgroup X} (hPK : P ≤ K)
    (hRK : R ≤ K) (hP : IsPGroup 2 P) (hR : IsPGroup 2 R)
    (hmax : ∀ R : Subgroup X, IsPGroup 2 R → P ≤ R → R ≤ K → R = P) :
    ∃ k ∈ K, ∀ x ∈ R, k⁻¹ * x * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' : Sylow 2 K :=
    { toSubgroup := P.subgroupOf K
      isPGroup' := hP.comap_subtype
      is_maximal' := fun {R₁} hR₁ hle => by
        have hR' : IsPGroup 2 (R₁.map K.subtype) := hR₁.map _
        have hPR : P ≤ R₁.map K.subtype := fun x hx => ⟨⟨x, hPK hx⟩, hle hx, rfl⟩
        have h := hmax _ hR' hPR (map_subtype_le R₁)
        ext x
        constructor
        · intro hx
          have : (x : X) ∈ R₁.map K.subtype := ⟨x, hx, rfl⟩
          rw [h] at this
          exact this
        · intro hx
          exact hle hx }
  obtain ⟨Q', hQ'⟩ := (hR.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P' Q'
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h1 : (⟨x, hRK hx⟩ : K) ∈ (Q' : Subgroup K) :=
    hQ' (show (⟨x, hRK hx⟩ : K) ∈ R.subgroupOf K from hx)
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨b, hb, hbx⟩ := h1
  rw [MulAut.smul_def, MulAut.conj_apply] at hbx
  have hb' : ((b : K) : X) ∈ P := hb
  have hkx : (k : X)⁻¹ * x * k = b := by
    have := congrArg Subtype.val hbx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    group
  rw [hkx]
  exact hb'

end GapNH

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

theorem redM_mat_inv {x : X} (hx : x ∈ A.NA) (h : redM (A.mat ⟨x, hx⟩) = 1) :
    redM (A.mat ⟨x⁻¹, inv_mem hx⟩) = 1 := by
  have h1 : A.mat ⟨x⁻¹, inv_mem hx⟩ * A.mat ⟨x, hx⟩ = 1 := by
    rw [← A.mat_mul, show (⟨x⁻¹, inv_mem hx⟩ : A.NA) * ⟨x, hx⟩ = 1 from
      Subtype.ext (inv_mul_cancel x), A.mat_one]
  have := congrArg redM h1
  rwa [redM_mul, h, mul_one, redM_one] at this

theorem mat_mul_inv (n : A.NA) : A.mat n * A.mat n⁻¹ = 1 := by
  rw [← A.mat_mul, mul_inv_cancel, A.mat_one]

theorem mat_inv_mul (n : A.NA) : A.mat n⁻¹ * A.mat n = 1 := by
  rw [← A.mat_mul, inv_mul_cancel, A.mat_one]

@[expose] noncomputable def G0 : Subgroup X where
  carrier := {g | ∃ h : g ∈ A.NA, redM (A.mat ⟨g, h⟩) = 1}
  mul_mem' := by
    rintro a b ⟨ha, hma⟩ ⟨hb, hmb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show (⟨a * b, mul_mem ha hb⟩ : A.NA) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, A.mat_mul,
      redM_mul, hma, hmb, mul_one]
  one_mem' := ⟨one_mem _, by
    rw [show (⟨1, one_mem _⟩ : A.NA) = 1 from rfl, A.mat_one, redM_one]⟩
  inv_mem' := by
    rintro a ⟨ha, hma⟩
    exact ⟨inv_mem ha, A.redM_mat_inv ha hma⟩

theorem G0_le_NA : A.G0 ≤ A.NA := fun _ ⟨h, _⟩ => h

theorem conj_mem_G0 {n : X} (hn : n ∈ A.NA) {g : X} (hg : g ∈ A.G0) : n * g * n⁻¹ ∈ A.G0 := by
  obtain ⟨hgN, hm⟩ := hg
  refine ⟨mul_mem (mul_mem hn hgN) (inv_mem hn), ?_⟩
  rw [show (⟨n * g * n⁻¹, mul_mem (mul_mem hn hgN) (inv_mem hn)⟩ : A.NA) =
      ⟨n, hn⟩ * ⟨g, hgN⟩ * ⟨n, hn⟩⁻¹ from rfl, A.mat_mul, A.mat_mul, redM_mul, redM_mul, hm,
    mul_one, ← redM_mul, A.mat_mul_inv, redM_one]

end BData

namespace BData.Syl

variable {A : BData S F T₁} (Y : A.Syl)

theorem mat_pm_of_InVQ2 (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P)
    (hred : redM (A.mat ⟨p, Y.mem_NA hp⟩) = 1) (h : Y.InVQ2 (qxOf S p)) :
    A.mat ⟨p, Y.mem_NA hp⟩ = 1 ∨ A.mat ⟨p, Y.mem_NA hp⟩ = -1 := by
  obtain ⟨q, hq, hqp⟩ := Y.mem_QS₁_of_qx hnc hp h
  have hqN : q ∈ A.NA := Y.mem_NA (mem_inf.mp hq).1
  have hN : q * p ∈ A.NA := mul_mem hqN (Y.mem_NA hp)
  have hm := A.mat_S₁ hqp hN
  have heq : A.mat ⟨q * p, hN⟩ = A.mat ⟨p, Y.mem_NA hp⟩ := by
    rw [show (⟨q * p, hN⟩ : A.NA) = ⟨q, hqN⟩ * ⟨p, Y.mem_NA hp⟩ from rfl, A.mat_mul,
      (A.mat_eq_one_iff _).mpr (mem_inf.mp hq).2, one_mul]
  rw [heq] at hm
  simp only [BData.L4set, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · rw [h1] at hred; exact absurd hred GapNH.redM_Umat_ne
  · rw [h1] at hred; exact absurd hred GapNH.redM_neg_Umat_ne

theorem exists_gen (hnc : ¬ SubConj F.E₁ F.E₂) :
    ∃ g ∈ Y.Q, ∀ q ∈ Y.Q, ∃ w ∈ A.VV, ∃ n : ℤ, q = w * g ^ n := by
  have := Y.isCyclic_QV hnc
  obtain ⟨gb, hgb⟩ := IsCyclic.exists_generator (α := Y.QV)
  obtain ⟨r, hr, hrg⟩ := gb.2
  refine ⟨(r : X), hr, fun q hq => ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hgb ⟨Y.pi ⟨q, Y.Q_le_R hq⟩, Y.mem_QV_of hq⟩)
  have h1 : Y.pi (r ^ n) = Y.pi ⟨q, Y.Q_le_R hq⟩ := by
    rw [map_zpow, hrg, ← SubgroupClass.coe_zpow]
    exact congrArg Subtype.val hn
  rw [pi_eq_iff, SubgroupClass.coe_zpow] at h1
  refine ⟨((r : X) ^ n)⁻¹ * q, h1, n, ?_⟩
  have hc := Y.VV_central (zpow_mem (show (r : X) ∈ Y.Q from hr) n) h1
  calc q = (r : X) ^ n * (((r : X) ^ n)⁻¹ * q) := by group
    _ = ((r : X) ^ n)⁻¹ * q * (r : X) ^ n := hc

theorem InVQ2_of_even {g : X} (hg : g ∈ Y.Q) {w : X} (hw : w ∈ A.VV) {n : ℤ} (hn : Even n) :
    Y.InVQ2 (w * g ^ n) := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨w, hw, g ^ m, zpow_mem hg m, by rw [zpow_add, pow_two]⟩

theorem InVQ2_mul (hnc : ¬ SubConj F.E₁ F.E₂) {q q' : X} (hq : q ∈ Y.Q) (hq' : q' ∈ Y.Q)
    (h : ¬ Y.InVQ2 q) (h' : ¬ Y.InVQ2 q') : Y.InVQ2 (q * q') := by
  obtain ⟨g, hg, hgen⟩ := Y.exists_gen hnc
  obtain ⟨w, hw, n, rfl⟩ := hgen q hq
  obtain ⟨w', hw', n', rfl⟩ := hgen q' hq'
  have hn : ¬ Even n := fun he => h (Y.InVQ2_of_even hg hw he)
  have hn' : ¬ Even n' := fun he => h' (Y.InVQ2_of_even hg hw' he)
  rw [Int.not_even_iff_odd] at hn hn'
  have hc : g ^ n * w' = w' * g ^ n := Y.VV_central (zpow_mem hg n) hw'
  have e : w * g ^ n * (w' * g ^ n') = (w * w') * g ^ (n + n') := by
    calc w * g ^ n * (w' * g ^ n') = w * (g ^ n * w') * g ^ n' := by group
      _ = w * (w' * g ^ n) * g ^ n' := by rw [hc]
      _ = (w * w') * g ^ (n + n') := by rw [zpow_add]; group
  rw [e]
  exact Y.InVQ2_of_even hg (mul_mem hw hw') (hn.add_odd hn')

theorem InVQ2_conj (hnc : ¬ SubConj F.E₁ F.E₂) {x : X} (hx : x ∈ Y.P)
    (hred : redM (A.mat ⟨x, Y.mem_NA hx⟩) = 1) {q : X} (h : Y.InVQ2 q) :
    Y.InVQ2 (x * q * x⁻¹) := by
  obtain ⟨w, hw, q₁, hq₁, rfl⟩ := h
  obtain ⟨v, hv2, rfl⟩ := hw
  set M := A.mat ⟨x, Y.mem_NA hx⟩ with hM
  have hconj : x * A.Φ v * x⁻¹ = A.Φ (M *ᵥ v) := A.conj_Φ ⟨x, Y.mem_NA hx⟩ v
  have hoff : ∀ j, j ≠ 2 → 2 * M 2 j = 0 := fun j hj => (r2_eq_zero_iff _).mp (by
    have := congrFun (congrFun hred 2) j
    rw [show redM M 2 j = r2 (M 2 j) from rfl, Matrix.one_apply_ne (Ne.symm hj)] at this
    exact this)
  have hu2 : 2 * (M *ᵥ v) 2 = 0 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2, mul_zero, add_zero]
    linear_combination (v 0) * hoff 0 (by decide) + (v 1) * hoff 1 (by decide)
  obtain ⟨s, hs⟩ := GapNH.exists_add_self _ hu2
  have hsplit : A.Φ (M *ᵥ v) = A.Φ ![(M *ᵥ v) 0, (M *ᵥ v) 1, 0] * A.Φ ![0, 0, s] ^ 2 := by
    rw [pow_two, ← A.Φ_add, ← A.Φ_add]
    congr 1
    funext i
    fin_cases i
    · simp
    · simp
    · simp [hs]
  have hcQ : A.Φ ![0, 0, s] ∈ Y.Q := Y.AA_le_Q (A.Φ_mem _)
  have hq₁' : x * q₁ * x⁻¹ ∈ Y.Q := Y.conj_mem_Q hx hq₁
  refine ⟨A.Φ ![(M *ᵥ v) 0, (M *ᵥ v) 1, 0], ⟨_, rfl, rfl⟩, A.Φ ![0, 0, s] * (x * q₁ * x⁻¹),
    mul_mem hcQ hq₁', ?_⟩
  have hc : Commute (A.Φ ![0, 0, s]) (x * q₁ * x⁻¹) := Y.Q_comm hnc hcQ hq₁'
  calc x * (A.Φ v * q₁ ^ 2) * x⁻¹ = (x * A.Φ v * x⁻¹) * (x * q₁ * x⁻¹) ^ 2 := by
        rw [pow_two, pow_two]; group
    _ = A.Φ ![(M *ᵥ v) 0, (M *ᵥ v) 1, 0] * (A.Φ ![0, 0, s] ^ 2 * (x * q₁ * x⁻¹) ^ 2) := by
        rw [hconj, hsplit, mul_assoc]
    _ = A.Φ ![(M *ᵥ v) 0, (M *ᵥ v) 1, 0] * (A.Φ ![0, 0, s] * (x * q₁ * x⁻¹)) ^ 2 := by
        rw [hc.mul_pow]

theorem qxOf_mul (x y : X) : qxOf S (x * y) = qxOf S x * (x * qxOf S y * x⁻¹) := by
  simp only [qxOf]
  group

theorem mat_mul_pm (hnc : ¬ SubConj F.E₁ F.E₂) {p p' : X} (hp : p ∈ Y.P) (hp' : p' ∈ Y.P)
    (hr : redM (A.mat ⟨p, Y.mem_NA hp⟩) = 1) (hr' : redM (A.mat ⟨p', Y.mem_NA hp'⟩) = 1)
    (hne : ¬ (A.mat ⟨p, Y.mem_NA hp⟩ = 1 ∨ A.mat ⟨p, Y.mem_NA hp⟩ = -1))
    (hne' : ¬ (A.mat ⟨p', Y.mem_NA hp'⟩ = 1 ∨ A.mat ⟨p', Y.mem_NA hp'⟩ = -1)) :
    A.mat ⟨p * p', Y.mem_NA (mul_mem hp hp')⟩ = 1 ∨
      A.mat ⟨p * p', Y.mem_NA (mul_mem hp hp')⟩ = -1 := by
  have h1 : ¬ Y.InVQ2 (qxOf S p) := fun h => hne (Y.mat_pm_of_InVQ2 hnc hp hr h)
  have h2 : ¬ Y.InVQ2 (p * qxOf S p' * p⁻¹) := by
    intro h
    apply hne'
    refine Y.mat_pm_of_InVQ2 hnc hp' hr' ?_
    have := Y.InVQ2_conj hnc (inv_mem hp) (A.redM_mat_inv (Y.mem_NA hp) hr) h
    rwa [show p⁻¹ * (p * qxOf S p' * p⁻¹) * p⁻¹⁻¹ = qxOf S p' by group] at this
  have hmul := Y.InVQ2_mul hnc (Y.qx_mem_Q hp) (Y.conj_mem_Q hp (Y.qx_mem_Q hp')) h1 h2
  rw [← qxOf_mul] at hmul
  have hrr : redM (A.mat ⟨p * p', Y.mem_NA (mul_mem hp hp')⟩) = 1 := by
    rw [show (⟨p * p', Y.mem_NA (mul_mem hp hp')⟩ : A.NA) = ⟨p, Y.mem_NA hp⟩ *
      ⟨p', Y.mem_NA hp'⟩ from rfl, A.mat_mul, redM_mul, hr, hr', mul_one]
  exact Y.mat_pm_of_InVQ2 hnc (mul_mem hp hp') hrr hmul

theorem max_G0 {R : Subgroup X} (hR : IsPGroup 2 R) (hle : Y.P ⊓ A.G0 ≤ R) (hRG : R ≤ A.G0) :
    R = Y.P ⊓ A.G0 := by
  obtain ⟨g, hg, hgR⟩ := GapNH.exists_conj_le_of_max Y.le_NA (hRG.trans A.G0_le_NA)
    Y.isPGroup hR Y.maximal
  have hmap : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ Y.P ⊓ A.G0 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := A.conj_mem_G0 (inv_mem hg) (hRG hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inv_inv] at h1 ⊢
    exact mem_inf.mpr ⟨hgR x hx, h1⟩
  have hcard : Nat.card R ≤ Nat.card (Y.P ⊓ A.G0 : Subgroup X) := by
    rw [← card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective]
    exact card_le_of_le hmap
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_conj_G0 {n : X} (hn : n ∈ A.NA) {p : X} (hp : p ∈ Y.P ⊓ A.G0) :
    ∃ x ∈ A.G0, x⁻¹ * (n * p * n⁻¹) * x ∈ Y.P ⊓ A.G0 := by
  have hP : IsPGroup 2 (Y.P ⊓ A.G0 : Subgroup X) := Y.isPGroup.to_le inf_le_left
  obtain ⟨x, hx, hxQ⟩ := exists_conj_of_max (K := A.G0) (P := Y.P ⊓ A.G0)
    (Q := (Y.P ⊓ A.G0).map (MulAut.conj n).toMonoidHom) inf_le_right
    (by rintro _ ⟨g, hg, rfl⟩; exact A.conj_mem_G0 hn (mem_inf.mp hg).2) hP (hP.map _)
    (fun R hR hle hRG => Y.max_G0 hR hle hRG)
    (card_map_of_injective (MulAut.conj n).injective)
  exact ⟨x, hx, (hxQ _).mp ⟨p, hp, by simp⟩⟩

theorem exists_conj_mat {n : X} (hn : n ∈ A.NA) {p : X} (hp : p ∈ Y.P)
    (hr : redM (A.mat ⟨p, Y.mem_NA hp⟩) = 1) :
    ∃ p', ∃ hp' : p' ∈ Y.P, A.mat ⟨p', Y.mem_NA hp'⟩ =
      A.mat ⟨n, hn⟩ * A.mat ⟨p, Y.mem_NA hp⟩ * A.mat ⟨n, hn⟩⁻¹ := by
  obtain ⟨x, ⟨hxN, hxr⟩, hx⟩ := Y.exists_conj_G0 hn (mem_inf.mpr ⟨hp, Y.mem_NA hp, hr⟩)
  refine ⟨_, (mem_inf.mp hx).1, ?_⟩
  set N : A.NA := ⟨n, hn⟩ * ⟨p, Y.mem_NA hp⟩ * ⟨n, hn⟩⁻¹ with hN
  have hNr : redM (A.mat N) = 1 := by
    rw [hN, A.mat_mul, A.mat_mul, redM_mul, redM_mul, hr, mul_one, ← redM_mul, A.mat_mul_inv,
      redM_one]
  have hxr' := A.redM_mat_inv hxN hxr
  rw [show (⟨x⁻¹ * (n * p * n⁻¹) * x, Y.mem_NA (mem_inf.mp hx).1⟩ : A.NA) =
      ⟨x⁻¹, inv_mem hxN⟩ * N * ⟨x, hxN⟩ from rfl, A.mat_mul, A.mat_mul,
    GapNH.comm_of_redM hxr' hNr, mul_assoc, ← A.mat_mul,
    show (⟨x⁻¹, inv_mem hxN⟩ * ⟨x, hxN⟩ : A.NA) = 1 from Subtype.ext (inv_mul_cancel x),
    A.mat_one, mul_one, hN, A.mat_mul, A.mat_mul]

theorem comm_of_conj (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P)
    (hr : redM (A.mat ⟨p, Y.mem_NA hp⟩) = 1)
    (hne : ¬ (A.mat ⟨p, Y.mem_NA hp⟩ = 1 ∨ A.mat ⟨p, Y.mem_NA hp⟩ = -1)) {n : X}
    (hn : n ∈ A.NA) {W : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (hW : A.mat ⟨p, Y.mem_NA hp⟩ = 1 + (2 : ZMod 4) • W) :
    redM (A.mat ⟨n, hn⟩) * redM W = redM W * redM (A.mat ⟨n, hn⟩) := by
  obtain ⟨p', hp', hmat⟩ := Y.exists_conj_mat hn hp hr
  set K := A.mat ⟨n, hn⟩ with hK
  set K' := A.mat ⟨n, hn⟩⁻¹ with hK'
  have hKK' : K * K' = 1 := A.mat_mul_inv _
  have hK'K : K' * K = 1 := A.mat_inv_mul _
  have hr' : redM (A.mat ⟨p', Y.mem_NA hp'⟩) = 1 := by
    rw [hmat, redM_mul, redM_mul, hr, mul_one, ← redM_mul, hKK', redM_one]
  have hne' : ¬ (A.mat ⟨p', Y.mem_NA hp'⟩ = 1 ∨ A.mat ⟨p', Y.mem_NA hp'⟩ = -1) := by
    intro h
    apply hne
    have e : A.mat ⟨p, Y.mem_NA hp⟩ = K' * (K * A.mat ⟨p, Y.mem_NA hp⟩ * K') * K := by
      rw [show K' * (K * A.mat ⟨p, Y.mem_NA hp⟩ * K') * K =
        (K' * K) * A.mat ⟨p, Y.mem_NA hp⟩ * (K' * K) by noncomm_ring, hK'K, one_mul, mul_one]
    rw [hmat] at h
    rcases h with h | h
    · left; rw [e, h, mul_one, hK'K]
    · right; rw [e, h, mul_neg, mul_one, neg_mul, hK'K]
  have hprod := Y.mat_mul_pm hnc hp hp' hr hr' hne hne'
  have e2 : A.mat ⟨p * p', Y.mem_NA (mul_mem hp hp')⟩ =
      1 + (2 : ZMod 4) • (W + K * W * K') := by
    rw [show (⟨p * p', Y.mem_NA (mul_mem hp hp')⟩ : A.NA) = ⟨p, Y.mem_NA hp⟩ *
      ⟨p', Y.mem_NA hp'⟩ from rfl, A.mat_mul, hmat, hW, GapNH.conj_two_smul hKK',
      GapNH.mul_two_smul]
  rw [e2] at hprod
  have hX : redM W + redM K * redM W * redM K' = 0 ∨
      redM W + redM K * redM W * redM K' = 1 := by
    rw [← redM_mul, ← redM_mul, ← GapNH.redM_add]
    rcases hprod with h | h
    · exact Or.inl (GapNH.redM_eq_zero_of h)
    · exact Or.inr (GapNH.redM_eq_one_of h)
  exact GapNH.comm_of_add (by rw [← redM_mul, hK'K, redM_one]) hX

theorem mat_mem_of_redM (hnc : ¬ SubConj F.E₁ F.E₂) {p : X} (hp : p ∈ Y.P)
    (hr : redM (A.mat ⟨p, Y.mem_NA hp⟩) = 1) :
    A.mat ⟨p, Y.mem_NA hp⟩ = 1 ∨ A.mat ⟨p, Y.mem_NA hp⟩ = -1 ∨
      A.mat ⟨p, Y.mem_NA hp⟩ = Dmat ∨ A.mat ⟨p, Y.mem_NA hp⟩ = -Dmat := by
  by_cases hpm : A.mat ⟨p, Y.mem_NA hp⟩ = 1 ∨ A.mat ⟨p, Y.mem_NA hp⟩ = -1
  · rcases hpm with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨W, hW⟩ := GapNH.exists_two_smul hr
  obtain ⟨δ, hδ, hz⟩ := A.exists_kappa
  have hK := Y.comm_of_conj hnc hp hr hpm (A.D₁₁_le_NA hδ) hW
  have hU := Y.comm_of_conj hnc hp hr hpm A.u_mem_NA hW
  rw [A.mat_u, GapNH.redM_Umat] at hU
  have hK' : blk 0 1 1 1 * redM W = redM W * blk 0 1 1 1 := by
    rcases A.kbar_cases hδ hz with h | h <;> rw [h] at hK
    · exact hK
    · rw [← GapNH.blk_sq, mul_assoc, hK, ← mul_assoc, hK, mul_assoc]
  rw [hW]
  exact GapNH.mem_four hK' hU

end BData.Syl

end Sec8

end CFSG.ComponentClassification.HSFLit
