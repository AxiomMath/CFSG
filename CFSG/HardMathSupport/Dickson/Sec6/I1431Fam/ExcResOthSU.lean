module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthV
public import CFSG.ClassicalInvolution.Phan.CenterScalars

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open Matrix
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Basic

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem excOth_center_smul (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n) {z : SUid σ n}
    (hz : z ∈ Subgroup.center (SUid σ n)) : ∃ μ : K, ∀ v : Fin n → K, z • v = μ • v := by
  rw [CFSG.ClassicalInvolution.Phan.center_SUid_eq hσ hn, Subgroup.mem_subgroupOf] at hz
  obtain ⟨μ, hμ⟩ := hz
  refine ⟨μ, fun v => ?_⟩
  rw [smul_def, ← hμ]
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

@[expose] noncomputable def excOth_dg {n : ℕ} (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) : SUid σ n :=
  mkSU σ (Matrix.diagonal d) (by rw [Matrix.det_diagonal]; exact hdet) (fun x y => by
    simp only [herm_def, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (σ (x i) * y i) * hd i)

theorem excOth_dg_smul {n : ℕ} (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) (v : Fin n → K) :
    excOth_dg d hd hdet • v = fun i => d i * v i := by
  funext i
  rw [excOth_dg, mkSU_smul, Matrix.mulVec_diagonal]

theorem excOth_dg_commute_tv (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {d : Fin n → K}
    {hd : ∀ i, σ (d i) * d i = 1} {hdet : ∏ i, d i = 1} {a : Fin n → K}
    (ha : herm σ a a = 0) {c : K} (hc : c + σ c = 0) {l : K} (hl : ∀ i, a i ≠ 0 → d i = l) :
    excOth_dg d hd hdet * tv hσ ha hc = tv hσ ha hc * excOth_dg d hd hdet := by
  apply ext_smul
  intro v
  have h1 : excOth_dg d hd hdet • a = l • a := by
    rw [excOth_dg_smul]
    funext i
    by_cases hai : a i = 0
    · simp [hai]
    · simp [hl i hai]
  have h2 : herm σ a (excOth_dg d hd hdet • v) = l * herm σ a v := by
    rw [excOth_dg_smul, herm_def, herm_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hai : a i = 0
    · simp [hai]
    · rw [hl i hai]; ring
  rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, h2, smul_comm _ (c * herm σ a v) a, h1,
    smul_smul]
  congr 2
  ring

theorem excOth_comm_smul_fix {G : Type*} [Group G] {V : Type*} [MulAction G V] {g h : G} {w : V}
    (hg : g • w = w) (hh : h • w = w) : ⁅g, h⁆ • w = w := by
  rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, inv_smul_eq_iff.2 hh.symm,
    inv_smul_eq_iff.2 hg.symm, hh, hg]

@[expose] def excOth_traceZero (σ : K ≃+* K) : AddSubgroup K where
  carrier := {s | s + σ s = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    linear_combination ha + hb
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq, map_neg] at *
    linear_combination -ha

theorem excOth_mem_traceZero {s : K} : s ∈ excOth_traceZero σ ↔ s + σ s = 0 := Iff.rfl

@[expose] noncomputable def excOth_tvHom (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a : Fin n → K}
    (ha : herm σ a a = 0) : Multiplicative (excOth_traceZero σ) →* SUid σ n :=
  MonoidHom.mk' (fun s => tv hσ ha (excOth_mem_traceZero.1 (Multiplicative.toAdd s).2))
    (fun s t =>
    (tv_mul_tv hσ ha (excOth_mem_traceZero.1 (Multiplicative.toAdd s).2)
      (excOth_mem_traceZero.1 (Multiplicative.toAdd t).2)
      (excOth_mem_traceZero.1 (Multiplicative.toAdd (s * t)).2)).symm)

end Basic

section CaseA

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def excOth_e2 (K : Type) [Field K] (m : ℕ) : Fin (m + 1 + 2) → K :=
  Pi.single (Fin.succ (Fin.succ (0 : Fin (m + 1)))) 1

theorem excOth_e2_zero (m : ℕ) : (excOth_e2 K m) 0 = 0 :=
  Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm _

theorem excOth_e2_one (m : ℕ) : (excOth_e2 K m) 1 = 0 :=
  Pi.single_eq_of_ne (WittData.succ_succ_ne_one (m := m + 1) 0).symm _

theorem excOth_e2_self (m : ℕ) : (excOth_e2 K m) (Fin.succ (Fin.succ 0)) = 1 :=
  Pi.single_eq_same _ _

theorem excOth_herm_hypA_e2 (W : WittData σ) (m : ℕ) :
    herm σ (W.hypA (m + 1)) (excOth_e2 K m) = 0 := by
  rw [W.herm_hypA_left, excOth_e2_zero, excOth_e2_one]
  simp

theorem excOth_herm_hypB_e2 (W : WittData σ) (m : ℕ) :
    herm σ (W.hypB (m + 1)) (excOth_e2 K m) = 0 := by
  rw [W.herm_hypB_left, excOth_e2_zero, excOth_e2_one]
  simp

theorem excOth_hypB_ne_zero (W : WittData σ) (m : ℕ) : W.hypB (m + 1) ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [W.hypB_zero] at this
  exact inv_ne_zero W.one_sub_ω_ne_zero this

@[expose] noncomputable def excOth_tA (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ)
    {s : K} (hs : s + σ s = 0) : SUid σ (m + 1 + 2) :=
  tv hσ.invol (W.herm_hypA_hypA (m := m + 1)) hs

@[expose] noncomputable def excOth_tB (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ)
    {t : K} (ht : t + σ t = 0) : SUid σ (m + 1 + 2) :=
  tv hσ.invol (W.herm_hypB_hypB (m := m + 1)) ht

theorem excOth_tA_smul (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ) {s : K}
    (hs : s + σ s = 0) (v : Fin (m + 1 + 2) → K) :
    excOth_tA W m hσ hs • v = v + (s * herm σ (W.hypA (m + 1)) v) • W.hypA (m + 1) :=
  tv_smul hσ.invol _ hs v

theorem excOth_tB_smul (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ) {t : K}
    (ht : t + σ t = 0) (v : Fin (m + 1 + 2) → K) :
    excOth_tB W m hσ ht • v = v + (t * herm σ (W.hypB (m + 1)) v) • W.hypB (m + 1) :=
  tv_smul hσ.invol _ ht v

theorem excOth_tA_fix_e2 (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ) {s : K}
    (hs : s + σ s = 0) : excOth_tA W m hσ hs • excOth_e2 K m = excOth_e2 K m := by
  rw [excOth_tA_smul, excOth_herm_hypA_e2, mul_zero, zero_smul, add_zero]

theorem excOth_tB_fix_e2 (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ) {t : K}
    (ht : t + σ t = 0) : excOth_tB W m hσ ht • excOth_e2 K m = excOth_e2 K m := by
  rw [excOth_tB_smul, excOth_herm_hypB_e2, mul_zero, zero_smul, add_zero]

theorem excOth_tA_tB_ne (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ) {s t : K}
    (hs : s + σ s = 0) (ht : t + σ t = 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    excOth_tA W m hσ hs * excOth_tB W m hσ ht ≠ excOth_tB W m hσ ht * excOth_tA W m hσ hs := by
  intro h
  have h1 := congrArg (fun g : SUid σ (m + 1 + 2) => g • W.hypB (m + 1)) h
  have hbb : herm σ (W.hypB (m + 1)) (W.hypB (m + 1)) = 0 := W.herm_hypB_hypB
  have hab : herm σ (W.hypA (m + 1)) (W.hypB (m + 1)) = 1 := W.herm_hypA_hypB
  have hba : herm σ (W.hypB (m + 1)) (W.hypA (m + 1)) = 1 := W.herm_hypB_hypA hσ.invol
  have e1 : (excOth_tA W m hσ hs * excOth_tB W m hσ ht) • W.hypB (m + 1) =
      W.hypB (m + 1) + s • W.hypA (m + 1) := by
    rw [mul_smul, excOth_tB_smul, hbb, mul_zero, zero_smul, add_zero, excOth_tA_smul, hab,
      mul_one]
  have e2 : (excOth_tB W m hσ ht * excOth_tA W m hσ hs) • W.hypB (m + 1) =
      W.hypB (m + 1) + s • W.hypA (m + 1) + (s * t) • W.hypB (m + 1) := by
    rw [mul_smul, excOth_tA_smul, hab, mul_one, excOth_tB_smul, herm_add_right, herm_smul_right,
      hbb, hba, mul_one, zero_add]
    congr 2
    ring
  rw [e1, e2] at h1
  have h3 : (s * t) • W.hypB (m + 1) = 0 := add_eq_left.1 h1.symm
  exact excOth_hypB_ne_zero W m ((smul_eq_zero.1 h3).resolve_left (mul_ne_zero hs0 ht0))

theorem excOth_comm_not_central (W : WittData σ) (m : ℕ) (hσ : IsUnitaryInvolution σ) {s t : K}
    (hs : s + σ s = 0) (ht : t + σ t = 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    ⁅excOth_tA W m hσ hs, excOth_tB W m hσ ht⁆ ∉ Subgroup.center (SUid σ (m + 1 + 2)) := by
  intro hz
  obtain ⟨μ, hμ⟩ := excOth_center_smul hσ (by omega) hz
  have hfix : ⁅excOth_tA W m hσ hs, excOth_tB W m hσ ht⁆ • excOth_e2 K m = excOth_e2 K m :=
    excOth_comm_smul_fix (excOth_tA_fix_e2 W m hσ hs) (excOth_tB_fix_e2 W m hσ ht)
  have hμ1 : μ = 1 := by
    have h1 := congrFun ((hμ (excOth_e2 K m)).symm.trans hfix) (Fin.succ (Fin.succ 0))
    rw [Pi.smul_apply, smul_eq_mul, excOth_e2_self, mul_one] at h1
    exact h1
  have hone : ⁅excOth_tA W m hσ hs, excOth_tB W m hσ ht⁆ = 1 := by
    apply ext_smul
    intro v
    rw [hμ v, hμ1, one_smul, one_smul]
  exact excOth_tA_tB_ne W m hσ hs ht hs0 ht0 (commutatorElement_eq_one_iff_mul_comm.1 hone)

@[expose] def excOth_dA (l : K) (m : ℕ) : Fin (m + 1 + 2) → K :=
  Fin.cons l (Fin.cons l (Fin.cons (l ^ 2)⁻¹ (fun _ : Fin m => (1 : K))))

theorem excOth_dA_zero (l : K) (m : ℕ) : excOth_dA l m 0 = l := rfl

theorem excOth_dA_two (l : K) (m : ℕ) : excOth_dA l m (Fin.succ (Fin.succ 0)) = (l ^ 2)⁻¹ := rfl

theorem excOth_dA_norm {l : K} (hl : σ l * l = 1) (m : ℕ) :
    ∀ i, σ (excOth_dA l m i) * excOth_dA l m i = 1 := by
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i) i
  · exact hl
  · exact hl
  · rw [excOth_dA_two, map_inv₀, map_pow, ← mul_inv, ← mul_pow, hl]
    simp
  · simp [excOth_dA]

theorem excOth_dA_prod {l : K} (hl : σ l * l = 1) (m : ℕ) : ∏ i, excOth_dA l m i = 1 := by
  have : l ≠ 0 := by
    intro h; rw [h, mul_zero] at hl; exact zero_ne_one hl
  simp [excOth_dA, Fin.prod_univ_succ]
  field_simp

theorem excOth_dA_support_A (W : WittData σ) (l : K) (m : ℕ) :
    ∀ i, W.hypA (m + 1) i ≠ 0 → excOth_dA l m i = l := by
  intro i hi
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => exact absurd (W.hypA_succ_succ k) hi

theorem excOth_dA_support_B (W : WittData σ) (l : K) (m : ℕ) :
    ∀ i, W.hypB (m + 1) i ≠ 0 → excOth_dA l m i = l := by
  intro i hi
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => exact absurd (W.hypB_succ_succ k) hi

@[expose] noncomputable def excOth_cA {l : K} (hl : σ l * l = 1) (m : ℕ) : SUid σ (m + 1 + 2) :=
  excOth_dg (excOth_dA l m) (excOth_dA_norm hl m) (excOth_dA_prod hl m)

theorem excOth_cA_not_central (hσ : IsUnitaryInvolution σ) {l : K} (hl : σ l * l = 1)
    (hl3 : l ^ 3 ≠ 1) (m : ℕ) : excOth_cA hl m ∉ Subgroup.center (SUid σ (m + 1 + 2)) := by
  intro hz
  obtain ⟨μ, hμ⟩ := excOth_center_smul hσ (by omega) hz
  have hl0 : l ≠ 0 := by
    intro h; rw [h, mul_zero] at hl; exact zero_ne_one hl
  have h0 := congrFun (hμ (Pi.single 0 1)) 0
  have h2 := congrFun (hμ (excOth_e2 K m)) (Fin.succ (Fin.succ 0))
  rw [excOth_cA, excOth_dg_smul] at h0 h2
  simp only [excOth_dA_zero, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at h0
  simp only [excOth_dA_two, excOth_e2_self, Pi.smul_apply, smul_eq_mul, mul_one] at h2
  apply hl3
  rw [← h0] at h2
  field_simp at h2
  linear_combination -h2

theorem excOth_caseA [Finite K] (hσ : IsUnitaryInvolution σ) (W : WittData σ) (m : ℕ) {l : K}
    (hl : σ l * l = 1) (hl3 : l ^ 3 ≠ 1) {ω : K} (hωσ : σ ω = ω) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {F : Type} [Field F]
    (φ : (↥(SUid σ (m + 1 + 2)) ⧸ Subgroup.center ↥(SUid σ (m + 1 + 2))) ≃*
      StatedProj (StatedSL 2 F)) : False := by
  classical
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hωτ : ω * τ + σ (ω * τ) = 0 := by
    rw [map_mul, hωσ]
    linear_combination ω * hτ
  have hcard : 3 ≤ Nat.card (Multiplicative (excOth_traceZero σ)) := by
    rw [Nat.card_congr Multiplicative.toAdd]
    let f : Fin 3 → excOth_traceZero σ := ![0, ⟨τ, hτ⟩, ⟨ω * τ, hωτ⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have h01 : (0 : excOth_traceZero σ) ≠ ⟨τ, hτ⟩ := fun h => hτ0 (congrArg Subtype.val h).symm
      have h02 : (0 : excOth_traceZero σ) ≠ ⟨ω * τ, hωτ⟩ := fun h =>
        mul_ne_zero hω0 hτ0 (congrArg Subtype.val h).symm
      have h12 : (⟨τ, hτ⟩ : excOth_traceZero σ) ≠ ⟨ω * τ, hωτ⟩ := fun h =>
        hω1 (mul_right_cancel₀ hτ0 ((congrArg Subtype.val h).symm.trans (one_mul τ).symm))
      fin_cases i <;> fin_cases j <;> simp only [f] at hij <;> first | rfl | (exfalso; simp_all) 
    calc 3 = Nat.card (Fin 3) := by simp
      _ ≤ _ := Nat.card_le_card_of_injective f hf
  have hxy : ∀ s t : Multiplicative (excOth_traceZero σ), s ≠ 1 → t ≠ 1 →
      ⁅excOth_tvHom hσ.invol (W.herm_hypA_hypA (m := m + 1)) s,
        excOth_tvHom hσ.invol (W.herm_hypB_hypB (m := m + 1)) t⁆ ∉
          Subgroup.center (SUid σ (m + 1 + 2)) := by
    intro s t hs ht
    have hs0 : (Multiplicative.toAdd s).1 ≠ 0 := fun h =>
      hs (Multiplicative.toAdd.injective (Subtype.ext h))
    have ht0 : (Multiplicative.toAdd t).1 ≠ 0 := fun h =>
      ht (Multiplicative.toAdd.injective (Subtype.ext h))
    exact excOth_comm_not_central W m hσ (excOth_mem_traceZero.1 (Multiplicative.toAdd s).2)
      (excOth_mem_traceZero.1 (Multiplicative.toAdd t).2) hs0 ht0
  refine excTL_false_of_heis φ hcard (excOth_tvHom hσ.invol (W.herm_hypA_hypA (m := m + 1)))
    (excOth_tvHom hσ.invol (W.herm_hypB_hypB (m := m + 1))) (excOth_cA hl m)
    (excOth_cA_not_central hσ hl hl3 m) (fun s => ?_) (fun t => ?_) hxy
  · exact (excOth_dg_commute_tv hσ.invol (W.herm_hypA_hypA (m := m + 1))
      (excOth_mem_traceZero.1 (Multiplicative.toAdd s).2) (excOth_dA_support_A W l m)
      (d := excOth_dA l m) (hd := excOth_dA_norm hl m) (hdet := excOth_dA_prod hl m)).symm
  · exact (excOth_dg_commute_tv hσ.invol (W.herm_hypB_hypB (m := m + 1))
      (excOth_mem_traceZero.1 (Multiplicative.toAdd t).2) (excOth_dA_support_B W l m)
      (d := excOth_dA l m) (hd := excOth_dA_norm hl m) (hdet := excOth_dA_prod hl m)).symm

end CaseA

section Dihedral

theorem excOth_dihedral_pair {G : Type*} [Group G] {F : Type} [Field F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F)) {c a₁ a₂ m₁ m₂ : G}
    (hc : c ∉ Subgroup.center G) (hca₁ : Commute a₁ c) (hca₂ : Commute a₂ c)
    (hcm₁ : Commute m₁ c) (hcm₂ : Commute m₂ c) (h₁ : m₁ * a₁ * m₁⁻¹ = a₁⁻¹)
    (h₂ : m₂ * a₂ * m₂⁻¹ = a₂⁻¹) (h₁₂ : Commute m₂ a₁)
    (hn₁ : a₁⁻¹ ^ 4 ∉ Subgroup.center G) (hn₂ : a₂⁻¹ ^ 4 ∉ Subgroup.center G) : False := by
  classical
  set C : Subgroup G := Subgroup.centralizer {c} with hC
  have hmem : ∀ x : G, Commute x c → x ∈ C := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact hx.symm.eq
  obtain ⟨K₀, hK₀, hcomm⟩ := excOth_index_two φ C.subtype c hc (fun a =>
    (Subgroup.mem_centralizer_iff.1 a.2 c (Set.mem_singleton c)).symm)
  let A1 : C := ⟨a₁, hmem a₁ hca₁⟩
  let A2 : C := ⟨a₂, hmem a₂ hca₂⟩
  let M1 : C := ⟨m₁, hmem m₁ hcm₁⟩
  let M2 : C := ⟨m₂, hmem m₂ hcm₂⟩
  have hsq : ∀ x : C, x ^ 2 ∈ K₀ := by
    intro x
    have hx : x ∈ K₀ → x ^ 2 ∈ K₀ := fun h => by
      rw [pow_two]
      exact K₀.mul_mem h h
    rcases hK₀ 1 x (x ^ 2) with h | h | h
    · rw [inv_one, one_mul] at h
      exact hx h
    · rwa [inv_one, one_mul] at h
    · apply hx
      have : x⁻¹ * x ^ 2 = x := by group
      rwa [this] at h
  have E : m₁ * a₁⁻¹ * m₁⁻¹ = a₁ := by
    calc m₁ * a₁⁻¹ * m₁⁻¹ = (m₁ * a₁ * m₁⁻¹)⁻¹ := by group
      _ = (a₁⁻¹)⁻¹ := by rw [h₁]
      _ = a₁ := inv_inv a₁
  have h₁' : m₁⁻¹ * a₁ * m₁ = a₁⁻¹ := by
    calc m₁⁻¹ * a₁ * m₁ = m₁⁻¹ * (m₁ * a₁⁻¹ * m₁⁻¹) * m₁ := by rw [E]
      _ = a₁⁻¹ := by group
  have e1 : ⁅m₁, a₁ ^ 2⁆ = a₁⁻¹ ^ 4 := by
    have : m₁ * a₁ ^ 2 * m₁⁻¹ = (a₁⁻¹) ^ 2 := by rw [← h₁, pow_two, pow_two]; group
    rw [commutatorElement_def, this]
    group
  have e2 : ⁅m₂, a₂ ^ 2⁆ = a₂⁻¹ ^ 4 := by
    have : m₂ * a₂ ^ 2 * m₂⁻¹ = (a₂⁻¹) ^ 2 := by rw [← h₂, pow_two, pow_two]; group
    rw [commutatorElement_def, this]
    group
  have e3 : ⁅m₁⁻¹ * m₂, a₁ ^ 2⁆ = a₁⁻¹ ^ 4 := by
    have h3 : m₂ * a₁ ^ 2 * m₂⁻¹ = a₁ ^ 2 := mul_inv_eq_iff_eq_mul.2 (h₁₂.pow_right 2).eq
    have h4 : m₁⁻¹ * a₁ ^ 2 * m₁ = (a₁⁻¹) ^ 2 := by rw [← h₁', pow_two, pow_two]; group
    calc ⁅m₁⁻¹ * m₂, a₁ ^ 2⁆ = m₁⁻¹ * (m₂ * a₁ ^ 2 * m₂⁻¹) * m₁ * (a₁ ^ 2)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a₁⁻¹ ^ 4 := by rw [h3, h4]; group
  have hA1 := hsq A1
  have hA2 := hsq A2
  rcases hK₀ 1 M1 M2 with h | h | h
  · rw [inv_one, one_mul] at h
    have := hcomm M1 h (A1 ^ 2) hA1
    apply hn₁
    rw [← e1]
    exact this
  · rw [inv_one, one_mul] at h
    have := hcomm M2 h (A2 ^ 2) hA2
    apply hn₂
    rw [← e2]
    exact this
  · have := hcomm (M1⁻¹ * M2) h (A1 ^ 2) hA1
    apply hn₁
    rw [← e3]
    exact this

end Dihedral

section CaseB

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] noncomputable def excOth_sw (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) : SUid σ n :=
  tv hσ.invol (a := Pi.single i 1 + Pi.single j 1)
    (by rw [herm_single_add_single hij 1, map_one, mul_one, one_add_one_eq_two, h2])
    (c := 1) (by rw [map_one, one_add_one_eq_two, h2])

theorem excOth_sw_smul (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (v : Fin n → K) :
    excOth_sw hσ h2 i j hij • v = fun k => v (Equiv.swap i j k) := by
  rw [excOth_sw, tv_smul]
  have hh : herm σ (Pi.single i 1 + Pi.single j 1) v = v i + v j := by
    rw [herm_add_left, herm_single_left, herm_single_left, map_one, one_mul, one_mul]
  funext k
  rw [Pi.add_apply, Pi.smul_apply, hh, one_mul, smul_eq_mul]
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hki : k = i
  · subst hki
    simp only [if_true, hij, hij.symm, if_false, Equiv.swap_apply_left]
    linear_combination (v k) * h2
  · by_cases hkj : k = j
    · subst hkj
      simp only [if_true, hij, hij.symm, if_false, Equiv.swap_apply_right]
      linear_combination (v k) * h2
    · simp only [hki, hkj, if_false, Equiv.swap_apply_of_ne_of_ne hki hkj]
      ring

theorem excOth_sw_mul_self (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) : excOth_sw hσ h2 i j hij * excOth_sw hσ h2 i j hij = 1 := by
  apply ext_smul
  intro v
  rw [mul_smul, excOth_sw_smul, excOth_sw_smul, one_smul]
  funext k
  simp

theorem excOth_dg_comm_dg {n : ℕ} (d d' : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) (hd' : ∀ i, σ (d' i) * d' i = 1) (hdet' : ∏ i, d' i = 1) :
    excOth_dg d hd hdet * excOth_dg d' hd' hdet' = excOth_dg d' hd' hdet' * excOth_dg d hd hdet := by
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, excOth_dg_smul, excOth_dg_smul, excOth_dg_smul, excOth_dg_smul]
  funext k
  ring

theorem excOth_dg_smul_single {n : ℕ} (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) (k : Fin n) :
    excOth_dg d hd hdet • (Pi.single k 1 : Fin n → K) = d k • (Pi.single k 1 : Fin n → K) := by
  rw [excOth_dg_smul]
  funext l
  by_cases hl : l = k
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]

theorem excOth_sw_comm_dg (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    (hs : ∀ k, d (Equiv.swap i j k) = d k) :
    excOth_sw hσ h2 i j hij * excOth_dg d hd hdet = excOth_dg d hd hdet * excOth_sw hσ h2 i j hij := by
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, excOth_sw_smul, excOth_dg_smul, excOth_dg_smul, excOth_sw_smul]
  funext k
  simp [hs k]

theorem excOth_sw_dg_inv (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    (hs : ∀ k, d (Equiv.swap i j k) * d k = 1) :
    excOth_sw hσ h2 i j hij * excOth_dg d hd hdet * (excOth_sw hσ h2 i j hij)⁻¹ =
      (excOth_dg d hd hdet)⁻¹ := by
  have hinv : (excOth_sw hσ h2 i j hij)⁻¹ = excOth_sw hσ h2 i j hij :=
    inv_eq_of_mul_eq_one_right (excOth_sw_mul_self hσ h2 i j hij)
  rw [hinv]
  refine eq_inv_of_mul_eq_one_left ?_
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, mul_smul, excOth_dg_smul, excOth_sw_smul, excOth_dg_smul,
    excOth_sw_smul, one_smul]
  funext k
  simp only [Equiv.swap_apply_self]
  have := hs k
  linear_combination (v k) * this

theorem excOth_pow_inv_smul_single {n : ℕ} (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) (k : Fin n) (N : ℕ) :
    ((excOth_dg d hd hdet)⁻¹ ^ N) • (Pi.single k 1 : Fin n → K) =
      ((d k)⁻¹ ^ N) • (Pi.single k 1 : Fin n → K) := by
  have hk : d k ≠ 0 := by
    intro h; have := hd k; rw [h, mul_zero] at this; exact zero_ne_one this
  have h1 : (excOth_dg d hd hdet)⁻¹ • (Pi.single k 1 : Fin n → K) =
      (d k)⁻¹ • (Pi.single k 1 : Fin n → K) := by
    rw [inv_smul_eq_iff, smul_comm, excOth_dg_smul_single, smul_smul, inv_mul_cancel₀ hk, one_smul]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, mul_smul, h1, smul_comm, ih, smul_smul, pow_succ]
    congr 1
    ring

@[expose] def excOth_wd {n : ℕ} (i j : Fin n) (x y : K) : Fin n → K :=
  fun k => if k = i then x else if k = j then y else 1

theorem excOth_wd_norm {n : ℕ} {i j : Fin n} {x y : K} (hx : σ x * x = 1) (hy : σ y * y = 1) :
    ∀ k, σ (excOth_wd i j x y k) * excOth_wd i j x y k = 1 := by
  intro k
  unfold excOth_wd
  split_ifs <;> simp [hx, hy]

theorem excOth_wd_prod {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x y : K) :
    ∏ k, excOth_wd i j x y k = x * y := by
  rw [Finset.prod_eq_mul i j hij]
  · simp [excOth_wd, hij.symm]
  · intro c _ hc
    simp [excOth_wd, hc.1, hc.2]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro h; exact absurd (Finset.mem_univ j) h

end CaseB

section CaseBMain

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem excOth_sq_eq_one {h2 : (2 : K) = 0} {ω : K} (h : ω ^ 2 = 1) : ω = 1 := by
  have h' : (ω - 1) ^ 2 = 0 := by linear_combination h + (1 - ω) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h')

theorem excOth_pow_four_eq_one {h2 : (2 : K) = 0} {ω : K} (h : ω ^ 4 = 1) : ω = 1 := by
  have h' : (ω - 1) ^ 4 = 0 := by
    linear_combination h + (-2 * ω ^ 3 + 3 * ω ^ 2 - 2 * ω + 1) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h')

theorem excOth_caseB (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) {n : ℕ} (hn : 3 ≤ n)
    {i0 i1 i2 i3 : Fin n} (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h03 : i0 ≠ i3) (h12 : i1 ≠ i2)
    (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) {ω : K} (hω : σ ω * ω = 1) (hω1 : ω ≠ 1) {F : Type}
    [Field F]
    (φ : (↥(SUid σ n) ⧸ Subgroup.center ↥(SUid σ n)) ≃* StatedProj (StatedSL 2 F)) : False := by
  classical
  have hω0 : ω ≠ 0 := by
    intro h; rw [h, mul_zero] at hω; exact zero_ne_one hω
  have hωi : σ ω⁻¹ * ω⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hω, inv_one]
  have nA1 := excOth_wd_norm (σ := σ) (i := i0) (j := i1) (x := ω) (y := ω⁻¹) hω hωi
  have pA1 : ∏ k, excOth_wd i0 i1 ω ω⁻¹ k = 1 := by
    rw [excOth_wd_prod h01, mul_inv_cancel₀ hω0]
  have nA2 := excOth_wd_norm (σ := σ) (i := i2) (j := i3) (x := ω) (y := ω⁻¹) hω hωi
  have pA2 : ∏ k, excOth_wd i2 i3 ω ω⁻¹ k = 1 := by
    rw [excOth_wd_prod h23, mul_inv_cancel₀ hω0]
  have nC : ∀ k, σ (excOth_wd i0 i1 ω ω k * excOth_wd i2 i3 ω⁻¹ ω⁻¹ k) *
      (excOth_wd i0 i1 ω ω k * excOth_wd i2 i3 ω⁻¹ ω⁻¹ k) = 1 := by
    intro k
    have e1 := excOth_wd_norm (σ := σ) (i := i0) (j := i1) hω hω k
    have e2 := excOth_wd_norm (σ := σ) (i := i2) (j := i3) hωi hωi k
    rw [map_mul]
    linear_combination (σ (excOth_wd i2 i3 ω⁻¹ ω⁻¹ k) * excOth_wd i2 i3 ω⁻¹ ω⁻¹ k) * e1 + e2
  have pC : ∏ k, (excOth_wd i0 i1 ω ω k * excOth_wd i2 i3 ω⁻¹ ω⁻¹ k) = 1 := by
    rw [Finset.prod_mul_distrib, excOth_wd_prod h01, excOth_wd_prod h23]
    field_simp
  set A1 : SUid σ n := excOth_dg _ nA1 pA1 with hA1
  set A2 : SUid σ n := excOth_dg _ nA2 pA2 with hA2
  set C : SUid σ n := excOth_dg _ nC pC with hC
  set M1 : SUid σ n := excOth_sw hσ h2 i0 i1 h01 with hM1
  set M2 : SUid σ n := excOth_sw hσ h2 i2 i3 h23 with hM2
  have h10 := h01.symm
  have h20 := h02.symm
  have h30 := h03.symm
  have h21 := h12.symm
  have h31 := h13.symm
  have h32 := h23.symm
  have sC1 : ∀ k, excOth_wd i0 i1 ω ω (Equiv.swap i0 i1 k) *
      excOth_wd i2 i3 ω⁻¹ ω⁻¹ (Equiv.swap i0 i1 k) =
        excOth_wd i0 i1 ω ω k * excOth_wd i2 i3 ω⁻¹ ω⁻¹ k := by
    intro k
    simp only [excOth_wd, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have sC2 : ∀ k, excOth_wd i0 i1 ω ω (Equiv.swap i2 i3 k) *
      excOth_wd i2 i3 ω⁻¹ ω⁻¹ (Equiv.swap i2 i3 k) =
        excOth_wd i0 i1 ω ω k * excOth_wd i2 i3 ω⁻¹ ω⁻¹ k := by
    intro k
    simp only [excOth_wd, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have sA1 : ∀ k, excOth_wd i0 i1 ω ω⁻¹ (Equiv.swap i0 i1 k) * excOth_wd i0 i1 ω ω⁻¹ k = 1 := by
    intro k
    simp only [excOth_wd, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have sA2 : ∀ k, excOth_wd i2 i3 ω ω⁻¹ (Equiv.swap i2 i3 k) * excOth_wd i2 i3 ω ω⁻¹ k = 1 := by
    intro k
    simp only [excOth_wd, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have sA12 : ∀ k, excOth_wd i0 i1 ω ω⁻¹ (Equiv.swap i2 i3 k) = excOth_wd i0 i1 ω ω⁻¹ k := by
    intro k
    simp only [excOth_wd, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have vC0 : (excOth_wd i0 i1 ω ω i0 * excOth_wd i2 i3 ω⁻¹ ω⁻¹ i0) = ω := by
    simp [excOth_wd, h01, h02, h03]
  have vC2 : (excOth_wd i0 i1 ω ω i2 * excOth_wd i2 i3 ω⁻¹ ω⁻¹ i2) = ω⁻¹ := by
    simp [excOth_wd, h20, h21]
  have vA1_2 : excOth_wd i0 i1 ω ω⁻¹ i2 = 1 := by simp [excOth_wd, h20, h21]
  have vA1_0 : excOth_wd i0 i1 ω ω⁻¹ i0 = ω := by simp [excOth_wd]
  have vA2_0 : excOth_wd i2 i3 ω ω⁻¹ i0 = 1 := by simp [excOth_wd, h02, h03]
  have vA2_2 : excOth_wd i2 i3 ω ω⁻¹ i2 = ω := by simp [excOth_wd]
  have hcNC : C ∉ Subgroup.center (SUid σ n) := by
    intro hz
    obtain ⟨μ, hμ⟩ := excOth_center_smul hσ hn hz
    have e0 := congrFun (hμ (Pi.single i0 1)) i0
    have e2 := congrFun (hμ (Pi.single i2 1)) i2
    rw [hC, excOth_dg_smul_single] at e0 e2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, vC0, vC2] at e0 e2
    have hsq : ω ^ 2 = 1 := by
      have h3 : ω⁻¹ = ω := e2.trans e0.symm
      have h4 := mul_inv_cancel₀ hω0
      rw [h3] at h4
      rw [pow_two]
      exact h4
    exact hω1 (excOth_sq_eq_one (h2 := h2) hsq)
  have hnc : ∀ (p q : Fin n) (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
      (hdet : ∏ i, d i = 1), d p = 1 → (d q)⁻¹ ^ 4 ≠ 1 →
      (excOth_dg d hd hdet)⁻¹ ^ 4 ∉ Subgroup.center (SUid σ n) := by
    intro p q d hd hdet hp hq hz
    obtain ⟨μ, hμ⟩ := excOth_center_smul hσ hn hz
    have ep := congrFun (hμ (Pi.single p 1)) p
    have eq' := congrFun (hμ (Pi.single q 1)) q
    rw [excOth_pow_inv_smul_single] at ep eq'
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, hp, inv_one,
      one_pow] at ep eq'
    exact hq (eq'.trans ep.symm)
  have hn₁ : A1⁻¹ ^ 4 ∉ Subgroup.center (SUid σ n) := by
    refine hnc i2 i0 _ nA1 pA1 vA1_2 ?_
    rw [vA1_0]
    intro h
    exact hω1 (excOth_pow_four_eq_one (h2 := h2) (by simpa using h))
  have hn₂ : A2⁻¹ ^ 4 ∉ Subgroup.center (SUid σ n) := by
    refine hnc i0 i2 _ nA2 pA2 vA2_0 ?_
    rw [vA2_2]
    intro h
    exact hω1 (excOth_pow_four_eq_one (h2 := h2) (by simpa using h))
  exact excOth_dihedral_pair φ hcNC
    (excOth_dg_comm_dg _ _ nA1 pA1 nC pC) (excOth_dg_comm_dg _ _ nA2 pA2 nC pC)
    (excOth_sw_comm_dg hσ h2 i0 i1 h01 _ nC pC sC1) (excOth_sw_comm_dg hσ h2 i2 i3 h23 _ nC pC sC2)
    (excOth_sw_dg_inv hσ h2 i0 i1 h01 _ nA1 pA1 sA1) (excOth_sw_dg_inv hσ h2 i2 i3 h23 _ nA2 pA2 sA2)
    (excOth_sw_comm_dg hσ h2 i2 i3 h23 _ nA1 pA1 sA12) hn₁ hn₂

end CaseBMain

end CFSG.HardMathSupport.Dickson.Sec6.I1431
