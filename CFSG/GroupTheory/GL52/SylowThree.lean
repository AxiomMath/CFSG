module

public import CFSG.GroupTheory.GL52.InvolutionsTransvection
public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.GL52.Simple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.GL52.OrderThreeConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix
open scoped Pointwise

@[expose] def syl3TbM : M5 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def syl3rM : M5 :=
  !![0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def syl3wM : M5 :=
  !![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

set_option maxRecDepth 100000 in
theorem syl3_facts : syl3TbM * syl3TbM ^ 2 = 1 ∧ syl3TbM ^ 3 = 1 ∧ syl3TbM ≠ 1 ∧
    ord3T2M * syl3TbM = syl3TbM * ord3T2M ∧
    (∀ i : Fin 3, ord3T2M ^ (i : ℕ) *ᵥ Pi.single 0 1 = Pi.single 0 1 → (i : ℕ) = 0) ∧
    syl3TbM *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  decide +kernel

@[expose] def syl3Tb : G52 :=
  mk5 syl3TbM (syl3TbM ^ 2) syl3_facts.1

theorem orderOf_syl3Tb : orderOf syl3Tb = 3 := by
  refine orderOf_eq_prime (Units.ext ?_) fun h => syl3_facts.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, syl3Tb, coe_mk5, Units.val_one]
    exact syl3_facts.2.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [syl3Tb] using this

theorem syl3_commute : ord3T2 * syl3Tb = syl3Tb * ord3T2 :=
  Units.ext syl3_facts.2.2.2.1

@[expose] def syl3R : Subgroup G52 :=
  Subgroup.zpowers ord3T2 ⊔ Subgroup.zpowers syl3Tb

theorem syl3_zpowers_le_normalizer :
    Subgroup.zpowers ord3T2 ≤ Subgroup.normalizer (Subgroup.zpowers syl3Tb : Set G52) := by
  rw [Subgroup.zpowers_le]
  refine mem_normalizer_zpowers_of_conj_mem ?_
  rw [syl3_commute, mul_inv_cancel_right]
  exact Subgroup.mem_zpowers _

theorem syl3_mem_R {g : G52} (hg : g ∈ syl3R) :
    ∃ i < 3, ∃ j < 3, g = ord3T2 ^ i * syl3Tb ^ j := by
  classical
  have hmul : (syl3R : Set G52) =
      (Subgroup.zpowers ord3T2 : Set G52) * (Subgroup.zpowers syl3Tb : Set G52) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ syl3_zpowers_le_normalizer
  have hg' : g ∈ (syl3R : Set G52) := hg
  rw [hmul] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_ord3T2] at ha
  rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_syl3Tb] at hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
  exact ⟨i, Finset.mem_range.1 hi, j, Finset.mem_range.1 hj, rfl⟩

theorem syl3_card_R : Nat.card syl3R = 9 := by
  have hcover : ∀ g ∈ syl3R, ∃ i < 3, (ord3T2 ^ i)⁻¹ * g ∈ Subgroup.zpowers syl3Tb := by
    intro g hg
    obtain ⟨i, hi, j, -, rfl⟩ := syl3_mem_R hg
    exact ⟨i, hi, by rw [inv_mul_cancel_left]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j⟩
  have hdisj : ∀ i < 3, ord3T2 ^ i ∈ Subgroup.zpowers syl3Tb → i = 0 := by
    intro i hi h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    refine syl3_facts.2.2.2.2.1 ⟨i, hi⟩ ?_
    have hfix : ((syl3Tb ^ k : G52) : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      have hpos : ∀ n : ℕ, ((syl3Tb ^ n : G52) : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
        intro n
        induction n with
        | zero => rw [pow_zero, Units.val_one, one_mulVec]
        | succ n ih =>
          rw [pow_succ, Units.val_mul, ← mulVec_mulVec]
          change ((syl3Tb ^ n : G52) : M5) *ᵥ (syl3TbM *ᵥ Pi.single 0 1) = _
          rw [syl3_facts.2.2.2.2.2, ih]
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]
        exact hpos n
      · rw [_root_.zpow_neg, zpow_natCast]
        conv_lhs => rw [← hpos n]
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [hk] at hfix
    simpa [ord3T2, Units.val_pow_eq_pow_val] using hfix
  have hle : Subgroup.zpowers syl3Tb ≤ syl3R := le_sup_right
  have hφ : ord3T2 ∈ syl3R := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  rw [card_eq_mul_of_cosets hle hφ hcover hdisj, Nat.card_zpowers, orderOf_syl3Tb]

theorem syl3_mul_eq (i j k l : ℕ) : ord3T2 ^ i * syl3Tb ^ j * (ord3T2 ^ k * syl3Tb ^ l) =
    ord3T2 ^ (i + k) * syl3Tb ^ (j + l) := by
  have hc : Commute ord3T2 syl3Tb := syl3_commute
  calc ord3T2 ^ i * syl3Tb ^ j * (ord3T2 ^ k * syl3Tb ^ l) =
      ord3T2 ^ i * (syl3Tb ^ j * ord3T2 ^ k) * syl3Tb ^ l := by group
    _ = ord3T2 ^ i * (ord3T2 ^ k * syl3Tb ^ j) * syl3Tb ^ l := by rw [(hc.pow_pow k j).eq]
    _ = ord3T2 ^ (i + k) * syl3Tb ^ (j + l) := by rw [pow_add, pow_add]; group

theorem syl3_R_comm : ∀ x ∈ syl3R, ∀ y ∈ syl3R, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, -, j, -, rfl⟩ := syl3_mem_R hx
  obtain ⟨k, -, l, -, rfl⟩ := syl3_mem_R hy
  rw [syl3_mul_eq, syl3_mul_eq, add_comm i k, add_comm j l]

theorem syl3_R_cube : ∀ x ∈ syl3R, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨i, -, j, -, rfl⟩ := syl3_mem_R hx
  have hc : Commute ord3T2 syl3Tb := syl3_commute
  have ha : ord3T2 ^ 3 = 1 := by rw [← orderOf_ord3T2]; exact pow_orderOf_eq_one _
  have hb : syl3Tb ^ 3 = 1 := by rw [← orderOf_syl3Tb]; exact pow_orderOf_eq_one _
  rw [(hc.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul,
    ha, hb, one_pow, one_pow, one_mul]

theorem syl3_ker_a : ∀ v : V5, (ord3T2M * ord3T2M + ord3T2M + 1) *ᵥ v = 0 →
    (syl3TbM + 1) *ᵥ v = 0 → v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 := by
  decide +kernel

theorem syl3_ker_b : ∀ v : V5, (syl3TbM * syl3TbM + syl3TbM + 1) *ᵥ v = 0 →
    (ord3T2M + 1) *ᵥ v = 0 → v 0 = 0 ∧ v 1 = 0 ∧ v 4 = 0 := by
  decide +kernel

theorem syl3_ker_4 : ∀ v : V5, (ord3T2M + 1) *ᵥ v = 0 → (syl3TbM + 1) *ᵥ v = 0 →
    v = 0 ∨ v = Pi.single 4 1 := by
  decide +kernel

theorem syl3_vec_facts :
    (ord3T2M * ord3T2M + ord3T2M + 1) *ᵥ Pi.single 0 1 = 0 ∧ (syl3TbM + 1) *ᵥ Pi.single 0 1 = 0 ∧
    (syl3TbM * syl3TbM + syl3TbM + 1) *ᵥ Pi.single 2 1 = 0 ∧ (ord3T2M + 1) *ᵥ Pi.single 2 1 = 0 ∧
    (ord3T2M + 1) *ᵥ Pi.single 4 1 = 0 ∧ (syl3TbM + 1) *ᵥ Pi.single 4 1 = 0 ∧
    ord3T2M *ᵥ Pi.single 0 1 = Pi.single 1 1 ∧ syl3TbM *ᵥ Pi.single 2 1 = Pi.single 3 1 := by
  decide +kernel

theorem syl3_orbit_a : ∀ v : V5, v ≠ 0 → v 2 = 0 → v 3 = 0 → v 4 = 0 →
    ∃ i : Fin 3, ord3T2M ^ (i : ℕ) *ᵥ Pi.single 0 1 = v := by
  decide +kernel

theorem syl3_orbit_b : ∀ v : V5, v ≠ 0 → v 0 = 0 → v 1 = 0 → v 4 = 0 →
    ∃ j : Fin 3, syl3TbM ^ (j : ℕ) *ᵥ Pi.single 2 1 = v := by
  decide +kernel

theorem syl3_fix_facts : ∀ j : Fin 3, syl3TbM ^ (j : ℕ) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
    ord3T2M ^ (j : ℕ) *ᵥ Pi.single 2 1 = Pi.single 2 1 ∧
    ord3T2M ^ (j : ℕ) *ᵥ Pi.single 4 1 = Pi.single 4 1 ∧
    syl3TbM ^ (j : ℕ) *ᵥ Pi.single 4 1 = Pi.single 4 1 := by
  decide +kernel

theorem syl3_eq_of_commute {A B : M5} (hAa : A * ord3T2M = ord3T2M * A)
    (hAb : A * syl3TbM = syl3TbM * A) (hBa : B * ord3T2M = ord3T2M * B)
    (hBb : B * syl3TbM = syl3TbM * B) (h0 : A *ᵥ Pi.single 0 1 = B *ᵥ Pi.single 0 1)
    (h2 : A *ᵥ Pi.single 2 1 = B *ᵥ Pi.single 2 1)
    (h4 : A *ᵥ Pi.single 4 1 = B *ᵥ Pi.single 4 1) : A = B := by
  obtain ⟨-, -, -, -, -, -, v1, v3⟩ := syl3_vec_facts
  have e1 : A *ᵥ Pi.single 1 1 = B *ᵥ Pi.single 1 1 := by
    rw [← v1, mulVec_comm hAa, mulVec_comm hBa, h0]
  have e3 : A *ᵥ Pi.single 3 1 = B *ᵥ Pi.single 3 1 := by
    rw [← v3, mulVec_comm hAb, mulVec_comm hBb, h2]
  refine ext_cols fun j => ?_
  fin_cases j
  exacts [h0, e1, h2, e3, h4]

theorem syl3_pow_matrix_a (i : ℕ) : ((ord3T2 ^ i : G52) : M5) = ord3T2M ^ i := by
  rw [Units.val_pow_eq_pow_val]
  rfl

theorem syl3_pow_matrix_b (j : ℕ) : ((syl3Tb ^ j : G52) : M5) = syl3TbM ^ j := by
  rw [Units.val_pow_eq_pow_val]
  rfl

theorem syl3_mem_R_of_commute {g : G52} (ha : g * ord3T2 = ord3T2 * g)
    (hb : g * syl3Tb = syl3Tb * g) : g ∈ syl3R := by
  obtain ⟨hPa0, hb0, hPb2, ha2, ha4, hb4, -, -⟩ := syl3_vec_facts
  have kA := syl3_ker_a
  have kB := syl3_ker_b
  have k4 := syl3_ker_4
  have hA : (g : M5) * ord3T2M = ord3T2M * (g : M5) := congrArg (fun x : G52 => (x : M5)) ha
  have hB : (g : M5) * syl3TbM = syl3TbM * (g : M5) := congrArg (fun x : G52 => (x : M5)) hb
  have hpoly : ∀ X : M5, (g : M5) * X = X * (g : M5) →
      (g : M5) * (X * X + X + 1) = (X * X + X + 1) * (g : M5) := by
    intro X hX
    simp only [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, hX]
    rw [mul_assoc, hX, ← mul_assoc]
  have hlin : ∀ X : M5, (g : M5) * X = X * (g : M5) →
      (g : M5) * (X + 1) = (X + 1) * (g : M5) := by
    intro X hX
    rw [mul_add, add_mul, hX, mul_one, one_mul]
  obtain ⟨c02, c03, c04⟩ := kA _ (by rw [← mulVec_comm (hpoly _ hA), hPa0, mulVec_zero])
    (by rw [← mulVec_comm (hlin _ hB), hb0, mulVec_zero])
  obtain ⟨c20, c21, c24⟩ := kB _ (by rw [← mulVec_comm (hpoly _ hB), hPb2, mulVec_zero])
    (by rw [← mulVec_comm (hlin _ hA), ha2, mulVec_zero])
  have g4 : (g : M5) *ᵥ Pi.single 4 1 = Pi.single 4 1 := by
    rcases k4 _ (by rw [← mulVec_comm (hlin _ hA), ha4, mulVec_zero])
        (by rw [← mulVec_comm (hlin _ hB), hb4, mulVec_zero]) with h | h
    · exact absurd (eq_zero_of_mulVec_eq_zero g h) (by decide)
    · exact h
  obtain ⟨i, hi⟩ := syl3_orbit_a _ (fun h => (by decide : (Pi.single 0 1 : V5) ≠ 0)
    (eq_zero_of_mulVec_eq_zero g h)) c02 c03 c04
  obtain ⟨j, hj⟩ := syl3_orbit_b _ (fun h => (by decide : (Pi.single 2 1 : V5) ≠ 0)
    (eq_zero_of_mulVec_eq_zero g h)) c20 c21 c24
  have hfix := syl3_fix_facts
  have heq : ord3T2 ^ (i : ℕ) * syl3Tb ^ (j : ℕ) = g := by
    refine Units.ext ?_
    rw [Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b]
    have hcab : ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ) = syl3TbM ^ (j : ℕ) * ord3T2M ^ (i : ℕ) := by
      have := (Commute.pow_pow (show Commute ord3T2M syl3TbM from syl3_facts.2.2.2.1) i j)
      exact this.eq
    refine syl3_eq_of_commute ?_ ?_ hA hB ?_ ?_ ?_
    · have h1 : Commute (ord3T2M ^ (i : ℕ)) ord3T2M := Commute.pow_left (Commute.refl _) _
      have h2 : Commute (syl3TbM ^ (j : ℕ)) ord3T2M :=
        Commute.pow_left (show Commute syl3TbM ord3T2M from syl3_facts.2.2.2.1.symm) _
      exact (h1.mul_left h2).eq
    · have h1 : Commute (ord3T2M ^ (i : ℕ)) syl3TbM :=
        Commute.pow_left (show Commute ord3T2M syl3TbM from syl3_facts.2.2.2.1) _
      have h2 : Commute (syl3TbM ^ (j : ℕ)) syl3TbM := Commute.pow_left (Commute.refl _) _
      exact (h1.mul_left h2).eq
    · rw [← mulVec_mulVec, (hfix j).1, hi]
    · rw [hcab, ← mulVec_mulVec, (hfix i).2.1, hj]
    · rw [← mulVec_mulVec, (hfix j).2.2.2, (hfix i).2.2.1, g4]
  rw [← heq]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))

theorem syl3_centralizer : Subgroup.centralizer (syl3R : Set G52) = syl3R := by
  refine le_antisymm (fun g hg => ?_) fun x hx y hy => (syl3_R_comm x hx y hy).symm
  have ha := Subgroup.mem_centralizer_iff.1 hg ord3T2
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hb := Subgroup.mem_centralizer_iff.1 hg syl3Tb
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  exact syl3_mem_R_of_commute ha.symm hb.symm

@[expose] def syl3DM : DihedralGroup 4 → M5
  | .r i => syl3rM ^ i.val
  | .sr i => syl3wM * syl3rM ^ i.val

set_option maxRecDepth 100000 in
theorem syl3DM_mul : ∀ x y : DihedralGroup 4, syl3DM (x * y) = syl3DM x * syl3DM y := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem syl3DM_inv : ∀ x : DihedralGroup 4, syl3DM x * syl3DM x⁻¹ = 1 := by
  decide +kernel

theorem syl3DM_one : syl3DM 1 = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem syl3DM_injective : ∀ x y : DihedralGroup 4, syl3DM x = syl3DM y → x = y := by
  decide +kernel

@[expose] def syl3DHom : DihedralGroup 4 →* G52 where
  toFun x := mk5 (syl3DM x) (syl3DM x⁻¹) (syl3DM_inv x)
  map_one' := Units.ext syl3DM_one
  map_mul' x y := Units.ext (syl3DM_mul x y)

theorem syl3DHom_injective : Function.Injective syl3DHom := fun x y h =>
  syl3DM_injective x y (congrArg (fun g : G52 => (g : M5)) h)

@[expose] def syl3T : Subgroup G52 :=
  syl3DHom.range

theorem syl3_card_T : Nat.card syl3T = 8 := by
  rw [syl3T, ← Nat.card_congr (MonoidHom.ofInjective syl3DHom_injective).toEquiv,
    Nat.card_eq_fintype_card, DihedralGroup.card]

set_option maxRecDepth 100000 in
theorem syl3_T_conj : ∀ x : DihedralGroup 4, ∃ i j k l : Fin 3,
    syl3DM x * ord3T2M * syl3DM x⁻¹ = ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ) ∧
    syl3DM x * syl3TbM * syl3DM x⁻¹ = ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem syl3_conj_pairs : ∀ i j k l : Fin 3,
    ((i : ℕ) = 0 ↔ (j : ℕ) ≠ 0) ∧ ((k : ℕ) = 0 ↔ (l : ℕ) ≠ 0) ∧ ((i : ℕ) = 0 ↔ (k : ℕ) ≠ 0) →
    ∃ x : DihedralGroup 4,
      syl3DM x * ord3T2M * syl3DM x⁻¹ = ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ) ∧
      syl3DM x * syl3TbM * syl3DM x⁻¹ = ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ) := by
  decide +kernel

theorem syl3_trace : ∀ i j : Fin 3,
    Matrix.trace (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) = 0 → ((i : ℕ) = 0 ↔ (j : ℕ) ≠ 0) := by
  decide +kernel

theorem syl3_trace_ab : Matrix.trace ord3T2M = 0 ∧ Matrix.trace syl3TbM = 0 := by
  decide +kernel

theorem syl3_trace_conj (g : G52) (A : M5) :
    Matrix.trace ((g : M5) * A * ((g⁻¹ : G52) : M5)) = Matrix.trace A := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul]

theorem syl3_mem_normalizer_of_map_le {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have heq : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge h ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g).injective hyx
    rwa [← this]

theorem syl3_conj_mem_R {g : G52} (ha : g * ord3T2 * g⁻¹ ∈ syl3R) (hb : g * syl3Tb * g⁻¹ ∈ syl3R) :
    g ∈ Subgroup.normalizer (syl3R : Set G52) := by
  refine syl3_mem_normalizer_of_map_le ?_
  rw [syl3R, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact sup_le ((Subgroup.zpowers_le).2 ha) ((Subgroup.zpowers_le).2 hb)

theorem syl3_T_le_normalizer : syl3T ≤ Subgroup.normalizer (syl3R : Set G52) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, j, k, l, h1, h2⟩ := syl3_T_conj x
  refine syl3_conj_mem_R ?_ ?_
  · have : syl3DHom x * ord3T2 * (syl3DHom x)⁻¹ = ord3T2 ^ (i : ℕ) * syl3Tb ^ (j : ℕ) :=
      Units.ext (by
        simp only [Units.val_mul]
        rw [syl3_pow_matrix_a, syl3_pow_matrix_b, ← h1]
        rfl)
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · have : syl3DHom x * syl3Tb * (syl3DHom x)⁻¹ = ord3T2 ^ (k : ℕ) * syl3Tb ^ (l : ℕ) :=
      Units.ext (by
        simp only [Units.val_mul]
        rw [syl3_pow_matrix_a, syl3_pow_matrix_b, ← h2]
        rfl)
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))

theorem syl3_not_both {g : G52} {X : Subgroup G52} (hX : Nat.card X = 3)
    (ha : g * ord3T2 * g⁻¹ ∈ X) (hb : g * syl3Tb * g⁻¹ ∈ X) : False := by
  have hle : syl3R.map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [syl3R, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le ((Subgroup.zpowers_le).2 ha) ((Subgroup.zpowers_le).2 hb)
  have := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, syl3_card_R, hX] at this
  norm_num at this

theorem syl3_normalizer_eq : syl3R ⊔ syl3T = Subgroup.normalizer (syl3R : Set G52) := by
  refine le_antisymm (sup_le Subgroup.le_normalizer syl3_T_le_normalizer) fun g hg => ?_
  have hmem : ∀ y ∈ syl3R, g * y * g⁻¹ ∈ syl3R := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  obtain ⟨i, hi, j, hj, hij⟩ :=
    syl3_mem_R (hmem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  obtain ⟨k, hk, l, hl, hkl⟩ :=
    syl3_mem_R (hmem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have htr : ∀ {y : G52} {a b : ℕ}, g * y * g⁻¹ = ord3T2 ^ a * syl3Tb ^ b →
      Matrix.trace (y : M5) = 0 → Matrix.trace (ord3T2M ^ a * syl3TbM ^ b) = 0 := by
    intro y a b h htr
    have := congrArg (fun x : G52 => Matrix.trace (x : M5)) h
    simp only [Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b] at this
    rw [← this, syl3_trace_conj, htr]
  have h1 := syl3_trace ⟨i, hi⟩ ⟨j, hj⟩ (htr hij syl3_trace_ab.1)
  have h2 := syl3_trace ⟨k, hk⟩ ⟨l, hl⟩ (htr hkl syl3_trace_ab.2)
  simp only at h1 h2
  have hcardA : Nat.card (Subgroup.zpowers ord3T2) = 3 := by
    rw [Nat.card_zpowers, orderOf_ord3T2]
  have hcardB : Nat.card (Subgroup.zpowers syl3Tb) = 3 := by
    rw [Nat.card_zpowers, orderOf_syl3Tb]
  have h3 : i = 0 ↔ k ≠ 0 := by
    constructor
    · intro hi0 hk0
      have hj0 : j ≠ 0 := h1.1 hi0
      have hl0 : l ≠ 0 := h2.1 hk0
      refine syl3_not_both (g := g) hcardB ?_ ?_
      · rw [hij, hi0, pow_zero, one_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · rw [hkl, hk0, pow_zero, one_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · intro hk0
      by_contra hi0
      have hj0 : j = 0 := by
        by_contra hj0
        exact hi0 (h1.2 hj0)
      have hl0 : l = 0 := by
        by_contra hl0
        exact hk0 (h2.2 hl0)
      refine syl3_not_both (g := g) hcardA ?_ ?_
      · rw [hij, hj0, pow_zero, mul_one]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · rw [hkl, hl0, pow_zero, mul_one]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨x, hx1, hx2⟩ := syl3_conj_pairs ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨l, hl⟩ ⟨h1, h2, h3⟩
  set t := syl3DHom x with ht
  have hta : t * ord3T2 * t⁻¹ = g * ord3T2 * g⁻¹ := by
    rw [hij]
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [syl3_pow_matrix_a, syl3_pow_matrix_b, ← hx1]
    rfl
  have htb : t * syl3Tb * t⁻¹ = g * syl3Tb * g⁻¹ := by
    rw [hkl]
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [syl3_pow_matrix_a, syl3_pow_matrix_b, ← hx2]
    rfl
  have hcomm : ∀ y : G52, t * y * t⁻¹ = g * y * g⁻¹ → t⁻¹ * g * y = y * (t⁻¹ * g) := by
    intro y hy
    calc t⁻¹ * g * y = t⁻¹ * (g * y * g⁻¹) * g := by group
      _ = t⁻¹ * (t * y * t⁻¹) * g := by rw [hy]
      _ = y * (t⁻¹ * g) := by group
  have hR := syl3_mem_R_of_commute (hcomm _ hta) (hcomm _ htb)
  have e : g = t * (t⁻¹ * g) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right ⟨x, rfl⟩) (Subgroup.mem_sup_left hR)

theorem syl3_R_inf_T : syl3R ⊓ syl3T = ⊥ := by
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [syl3_card_R, syl3_card_T]
  norm_num

theorem syl3_card_normalizer : Nat.card (Subgroup.normalizer (syl3R : Set G52)) = 72 := by
  rw [← syl3_normalizer_eq, inv_card_sup syl3_T_le_normalizer syl3_R_inf_T, syl3_card_R,
    syl3_card_T]

theorem syl3_quotient_equiv {N R T : Subgroup G52} [(R.subgroupOf N).Normal] (hRN : R ≤ N)
    (hTN : T ≤ N) (hcard : Nat.card N = Nat.card T * Nat.card R)
    (hcop : Nat.Coprime (Nat.card T) (Nat.card R)) :
    Nonempty (N ⧸ R.subgroupOf N ≃* T) := by
  have hT : Nat.card (T.subgroupOf N) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hR : Nat.card (R.subgroupOf N) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
  have hc : (T.subgroupOf N).IsComplement' (R.subgroupOf N) :=
    Subgroup.isComplement'_of_coprime (by rw [hT, hR, hcard]) (by rw [hT, hR]; exact hcop)
  exact ⟨hc.QuotientMulEquiv.trans (Subgroup.subgroupOfEquivOfLe hTN)⟩

theorem syl3_card_sylow (P : Sylow 3 G52) : Nat.card P = 9 := by
  have := card_sylow_of_card_eq_pow_mul (p := 3) (k := 2) (m := 1111040)
    (by rw [card_G52]; norm_num) (by norm_num) P
  rw [this]
  norm_num

theorem syl3_structure (R : Sylow 3 G52) :
    Nat.card R = 9 ∧ IsElementaryAbelian 3 R ∧
    Subgroup.centralizer (R : Set G52) = R ∧
    Nonempty (Subgroup.normalizer ((R : Subgroup G52) : Set G52) ⧸
      (R : Subgroup G52).subgroupOf (Subgroup.normalizer ((R : Subgroup G52) : Set G52)) ≃*
        DihedralGroup 4) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (by rw [syl3_card_R]; norm_num)
    (fun P => by rw [syl3_card_sylow P]; norm_num)
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q R
  rw [hQ] at hc
  set f := (MulAut.conj c).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj c).injective
  have hRs : ((R : Set G52)) = ((R : Subgroup G52) : Set G52) := rfl
  refine ⟨syl3_card_sylow R, ?_, ?_, ?_⟩
  ·
    have hRe : (R : Subgroup G52) = syl3R.map f := hc
    refine
      { is_comm := ⟨fun x y => Subtype.ext ?_⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_ }
    · have hx : (x : G52) ∈ syl3R.map f := hRe ▸ x.2
      have hy : (y : G52) ∈ syl3R.map f := hRe ▸ y.2
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      change (x : G52) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul, syl3_R_comm a ha b hb]
    · have hx : (x : G52) ∈ syl3R.map f := hRe ▸ x.2
      obtain ⟨a, ha, hax⟩ := hx
      change (x : G52) ^ 3 = 1
      rw [← hax, ← map_pow, syl3_R_cube a ha, map_one]
  · rw [hRs, hc, hf, centralizer_map_conj, syl3_centralizer]
  · have hinj' : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
    have hNeq : Subgroup.normalizer ((R : Subgroup G52) : Set G52) =
        (Subgroup.normalizer (syl3R : Set G52)).map (MulAut.conj c).toMonoidHom := by
      rw [hc, hf, normalizer_map_conj]
    have hTN : syl3T.map (MulAut.conj c).toMonoidHom ≤
        Subgroup.normalizer ((R : Subgroup G52) : Set G52) := by
      rw [hNeq]
      exact Subgroup.map_mono syl3_T_le_normalizer
    have hRN : (R : Subgroup G52) ≤ Subgroup.normalizer ((R : Subgroup G52) : Set G52) :=
      Subgroup.le_normalizer
    have hcardN : Nat.card (Subgroup.normalizer ((R : Subgroup G52) : Set G52)) = 72 := by
      rw [hNeq, Subgroup.card_map_of_injective hinj', syl3_card_normalizer]
    have hcardT : Nat.card (syl3T.map (MulAut.conj c).toMonoidHom) = 8 := by
      rw [Subgroup.card_map_of_injective hinj', syl3_card_T]
    have hcardR : Nat.card (R : Subgroup G52) = 9 := syl3_card_sylow R
    obtain ⟨e⟩ := syl3_quotient_equiv hRN hTN (by rw [hcardN, hcardT, hcardR])
      (by rw [hcardT, hcardR]; norm_num)
    exact ⟨e.trans ((Subgroup.equivMapOfInjective syl3T _ hinj').symm.trans
      (MonoidHom.ofInjective syl3DHom_injective).symm)⟩

end CFSG.GroupTheory.GL52
