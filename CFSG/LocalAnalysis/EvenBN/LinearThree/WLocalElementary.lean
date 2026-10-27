module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocalAbelian
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal

open Matrix
open scoped MatrixGroups

namespace WSetting

variable {G : Type*} [Group G] {K : Type*} [Field K] (S : WSetting G K)

noncomputable def nu (a : G) : Fin 2 → K := Classical.epsilon fun v => S.ι v = a

theorem ι_nu {a : G} (h : ∃ v, S.ι v = a) : S.ι (S.nu a) = a :=
  Classical.epsilon_spec h

theorem nu_ι (v : Fin 2 → K) : S.nu (S.ι v) = v :=
  S.ι_injective (S.ι_nu ⟨v, rfl⟩)

omit [Field K] in
theorem vec_add_self {K : Type*} [Ring K] [CharP K 2] (v : Fin 2 → K) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem ι_mul_self [CharP K 2] (v : Fin 2 → K) : S.ι v * S.ι v = 1 := by
  rw [← S.ι_add, vec_add_self, S.ι_zero]

noncomputable abbrev root (s : K) : G := S.lev (upper s)

noncomputable abbrev diag (l : Kˣ) : G := S.lev (dmat l)

theorem root_mul_self [CharP K 2] (s : K) : S.root s * S.root s = 1 := by
  rw [← map_mul, upper_mul_upper, CharTwo.add_self_eq_zero, upper_zero, map_one]

theorem root_comm (s s' : K) : S.root s * S.root s' = S.root s' * S.root s := by
  rw [← map_mul, ← map_mul, upper_mul_upper, upper_mul_upper, add_comm]

theorem diag_conj_root (l : Kˣ) (s : K) :
    S.diag l * S.root s * (S.diag l)⁻¹ = S.root ((l : K) ^ 2 * s) := by
  rw [← map_inv, ← map_mul, ← map_mul, dmat_conj_upper]

theorem ψ_root {a : G} (ha : a ∈ S.W) (s : K) :
    S.ψ (S.root s * a * (S.root s)⁻¹) = ![S.ψ a 0 + s * S.ψ a 1, S.ψ a 1] := by
  rw [S.lev_ψ _ _ ha, upper_mulVec]

theorem root_ι (s : K) (v : Fin 2 → K) :
    S.root s * S.ι v * (S.root s)⁻¹ = S.ι ![v 0 + s * v 1, v 1] := by
  rw [S.lev_ι, upper_mulVec]

theorem ψ_diag {a : G} (ha : a ∈ S.W) (l : Kˣ) :
    S.ψ (S.diag l * a * (S.diag l)⁻¹) = ![(l : K) * S.ψ a 0, ((l⁻¹ : Kˣ) : K) * S.ψ a 1] := by
  rw [S.lev_ψ _ _ ha, dmat_mulVec]

theorem diag_ι (l : Kˣ) (v : Fin 2 → K) :
    S.diag l * S.ι v * (S.diag l)⁻¹ = S.ι ![(l : K) * v 0, ((l⁻¹ : Kˣ) : K) * v 1] := by
  rw [S.lev_ι, dmat_mulVec]

def InY (a : G) : Prop := a ∈ S.W ∧ S.ψ a 1 = 0

theorem InY.ψ_eq {S : WSetting G K} {a : G} (ha : S.InY a) : S.ψ a = ![S.ψ a 0, 0] := by
  ext i; fin_cases i
  · rfl
  · exact ha.2

theorem exists_root_conj [CharP K 2] {z : G} (hz : S.InY z) (s : K) :
    ∃ e : K, S.root s * z * (S.root s)⁻¹ = S.ι ![e, 0] * z := by
  by_cases hs : s = 0
  · refine ⟨0, ?_⟩
    have h0 : (![0, 0] : Fin 2 → K) = 0 := by ext i; fin_cases i <;> rfl
    rw [hs, root, upper_zero, map_one, one_mul, inv_one, mul_one, h0, S.ι_zero, one_mul]
  have hgz : S.root s * z * (S.root s)⁻¹ ∈ S.W := S.lev_mem _ z hz.1
  obtain ⟨v, hv⟩ := S.ψ_eq_zero (S.root s * z * (S.root s)⁻¹ * z⁻¹)
    (mul_mem hgz (inv_mem hz.1)) (by
      rw [S.ψ_mul _ hgz _ (inv_mem hz.1), S.ψ_inv hz.1, S.ψ_root hz.1, hz.2, mul_zero, add_zero,
        ← hz.ψ_eq, add_neg_cancel])
  have hgz' : S.root s * z * (S.root s)⁻¹ = S.ι v * z := by
    rw [hv, inv_mul_cancel_right]
  have h2 : S.root s * (S.root s * z * (S.root s)⁻¹) * (S.root s)⁻¹ = z := by
    calc S.root s * (S.root s * z * (S.root s)⁻¹) * (S.root s)⁻¹
        = (S.root s * S.root s) * z * (S.root s * S.root s)⁻¹ := by group
      _ = z := by rw [S.root_mul_self, one_mul, inv_one, mul_one]
  rw [hgz'] at h2
  have h3 : S.root s * (S.ι v * z) * (S.root s)⁻¹ =
      (S.root s * S.ι v * (S.root s)⁻¹) * (S.root s * z * (S.root s)⁻¹) := by group
  rw [h3, hgz', S.root_ι, ← mul_assoc, ← S.ι_add] at h2
  have h4 : S.ι (![v 0 + s * v 1, v 1] + v) = S.ι 0 := by
    rw [S.ι_zero]
    exact mul_eq_right.mp h2
  have h5 := congrFun (S.ι_injective h4) 0
  simp only [Pi.add_apply, Matrix.cons_val_zero, Pi.zero_apply] at h5
  have h6 : s * v 1 = 0 := by
    linear_combination h5 - CharTwo.add_self_eq_zero (v 0)
  have hv1 : v 1 = 0 := (mul_eq_zero.mp h6).resolve_left hs
  have hv' : ![v 0, 0] = v := by
    ext i; fin_cases i
    · rfl
    · exact hv1.symm
  exact ⟨v 0, by rw [hgz', hv']⟩

theorem exists_eq_mul_self [CharP K 2] {a : G} (ha : a ∈ S.W) : ∃ v, S.ι v = a * a :=
  S.ψ_eq_zero _ (mul_mem ha ha) (by rw [S.ψ_mul _ ha _ ha, vec_add_self])

theorem mul_ι_mul_self [CharP K 2] {a : G} (ha : a ∈ S.W) (v : Fin 2 → K) :
    a * S.ι v * (a * S.ι v) = a * a := by
  calc a * S.ι v * (a * S.ι v) = a * (S.ι v * a) * S.ι v := by group
    _ = a * (a * S.ι v) * S.ι v := by rw [S.ι_comm v a ha]
    _ = a * a * (S.ι v * S.ι v) := by group
    _ = a * a := by rw [S.ι_mul_self, mul_one]

theorem ι_mul_mul_self [CharP K 2] {a : G} (ha : a ∈ S.W) (v : Fin 2 → K) :
    S.ι v * a * (S.ι v * a) = a * a := by
  rw [S.ι_comm v a ha, S.mul_ι_mul_self ha]

theorem exists_mul_self_eq [CharP K 2] {z : G} (hz : S.InY z) : ∃ e : K, z * z = S.ι ![e, 0] := by
  obtain ⟨v, hv⟩ := S.exists_eq_mul_self hz.1
  obtain ⟨e, he⟩ := S.exists_root_conj hz 1
  have h1 : S.root 1 * (z * z) * (S.root 1)⁻¹ = z * z := by
    calc S.root 1 * (z * z) * (S.root 1)⁻¹ =
        (S.root 1 * z * (S.root 1)⁻¹) * (S.root 1 * z * (S.root 1)⁻¹) := by group
      _ = z * z := by rw [he, S.ι_mul_mul_self hz.1]
  rw [← hv, S.root_ι, one_mul] at h1
  have h2 := congrFun (S.ι_injective h1) 0
  simp only [Matrix.cons_val_zero] at h2
  have hv1 : v 1 = 0 := left_eq_add.mp h2.symm
  refine ⟨v 0, ?_⟩
  rw [← hv]
  congr 1
  ext i; fin_cases i
  · rfl
  · exact hv1

noncomputable def theta (x : K) : K := S.nu (S.sec ![x, 0] * S.sec ![x, 0]) 0

theorem sec_inY (x : K) : S.InY (S.sec ![x, 0]) :=
  ⟨S.sec_mem _, by rw [S.ψ_sec]; rfl⟩

theorem mul_self_eq_theta [CharP K 2] {z : G} (hz : S.InY z) :
    z * z = S.ι ![S.theta (S.ψ z 0), 0] := by
  obtain ⟨v, hv⟩ := S.exists_eq_mul_ι hz.1 (S.sec_mem ![S.ψ z 0, 0])
    (by rw [S.ψ_sec]; exact hz.ψ_eq)
  obtain ⟨e, he⟩ := S.exists_mul_self_eq (S.sec_inY (S.ψ z 0))
  have h1 : z * z = S.sec ![S.ψ z 0, 0] * S.sec ![S.ψ z 0, 0] := by
    conv_lhs => rw [hv]
    exact S.mul_ι_mul_self (S.sec_mem _) v
  rw [h1, theta, he, S.nu_ι]
  rfl

theorem InY.diag {S : WSetting G K} {z : G} (hz : S.InY z) (l : Kˣ) :
    S.InY (S.diag l * z * (S.diag l)⁻¹) :=
  ⟨S.lev_mem _ z hz.1, by rw [S.ψ_diag hz.1, hz.2, mul_zero]; rfl⟩

theorem theta_mul [CharP K 2] (l : Kˣ) (x : K) : S.theta ((l : K) * x) = l * S.theta x := by
  have hz := S.sec_inY x
  have h1 := S.mul_self_eq_theta (hz.diag l)
  have h2 : S.diag l * S.sec ![x, 0] * (S.diag l)⁻¹ * (S.diag l * S.sec ![x, 0] * (S.diag l)⁻¹) =
      S.diag l * (S.sec ![x, 0] * S.sec ![x, 0]) * (S.diag l)⁻¹ := by group
  rw [h2, S.mul_self_eq_theta hz, S.diag_ι, S.ψ_diag hz.1, S.ψ_sec] at h1
  have h3 := congrFun (S.ι_injective h1) 0
  simpa using h3.symm

theorem theta_zero [CharP K 2] : S.theta (0 : K) = 0 := by
  have hz := S.sec_inY (0 : K)
  have h1 := S.mul_self_eq_theta hz
  obtain ⟨v, hv⟩ := S.ψ_eq_zero _ hz.1 (by rw [S.ψ_sec]; ext i; fin_cases i <;> rfl)
  rw [← hv, S.ι_mul_self, S.ψ_ι, ← S.ι_zero] at h1
  have h2 := congrFun (S.ι_injective h1) 0
  simpa using h2.symm

theorem theta_eq [CharP K 2] (x : K) : S.theta x = x * S.theta 1 := by
  by_cases hx : x = 0
  · rw [hx, theta_zero, zero_mul]
  · have h := S.theta_mul (Units.mk0 x hx) 1
    rwa [Units.val_mk0, mul_one] at h

theorem mul_self_eq [CharP K 2] {z : G} (hz : S.InY z) :
    z * z = S.ι ![S.ψ z 0 * S.theta 1, 0] := by
  rw [S.mul_self_eq_theta hz, S.theta_eq]

noncomputable abbrev hElt (l : Kˣ) : G := S.tor l * S.diag (l ^ 3)

theorem hElt_conj (l : Kˣ) (a : G) : S.hElt l * a * (S.hElt l)⁻¹ =
    S.tor l * (S.diag (l ^ 3) * a * (S.diag (l ^ 3))⁻¹) * (S.tor l)⁻¹ := by
  simp only [hElt]; group

theorem hElt_mem {a : G} (ha : a ∈ S.W) (l : Kˣ) : S.hElt l * a * (S.hElt l)⁻¹ ∈ S.W := by
  rw [hElt_conj]
  exact S.tor_mem _ _ (S.lev_mem _ _ ha)

theorem ψ_hElt {a : G} (ha : a ∈ S.W) (l : Kˣ) :
    S.ψ (S.hElt l * a * (S.hElt l)⁻¹) = ![(l : K) ^ 6 * S.ψ a 0, S.ψ a 1] := by
  rw [hElt_conj, S.tor_ψ _ _ (S.lev_mem _ _ ha), S.ψ_diag ha]
  ext i; fin_cases i
  · simp; ring
  · simp

theorem hElt_ι (l : Kˣ) (v : Fin 2 → K) :
    S.hElt l * S.ι v * (S.hElt l)⁻¹ = S.ι ![(l : K) ^ 6 * v 0, v 1] := by
  rw [hElt_conj, S.diag_ι, S.tor_ι]
  congr 1
  ext i; fin_cases i
  · simp; ring
  · simp

theorem hElt_comm_diag (l l' : Kˣ) : S.hElt l * S.diag l' = S.diag l' * S.hElt l := by
  have h1 : S.diag (l ^ 3) * S.diag l' = S.diag l' * S.diag (l ^ 3) := by
    rw [← map_mul, ← map_mul, dmat_mul_dmat, dmat_mul_dmat, mul_comm]
  simp only [hElt]
  rw [mul_assoc, h1, ← mul_assoc, S.tor_lev, mul_assoc]

theorem InY.mul {S : WSetting G K} {a b : G} (ha : S.InY a) (hb : S.InY b) : S.InY (a * b) :=
  ⟨mul_mem ha.1 hb.1, by rw [S.ψ_mul _ ha.1 _ hb.1, Pi.add_apply, ha.2, hb.2, add_zero]⟩

theorem InY.inv {S : WSetting G K} {a : G} (ha : S.InY a) : S.InY a⁻¹ :=
  ⟨inv_mem ha.1, by rw [S.ψ_inv ha.1, Pi.neg_apply, ha.2, neg_zero]⟩

omit [Field K] in
theorem pow_six_ne_one {K : Type*} [Field K] [CharP K 2] {l : K} (hl : l ^ 3 ≠ 1) :
    l ^ 6 - 1 ≠ 0 := by
  intro h
  apply hl
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (l ^ 3 - 1) ^ 2 = 0 := by linear_combination h - l ^ 3 * h2 + h2
  have h4 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
  linear_combination h4

noncomputable abbrev kap (l : Kˣ) (z : G) : G := S.hElt l * z * (S.hElt l)⁻¹ * z⁻¹

theorem kap_mem {z : G} (hz : z ∈ S.W) (l : Kˣ) : S.kap l z ∈ S.W :=
  mul_mem (S.hElt_mem hz l) (inv_mem hz)

theorem ψ_kap {z : G} (hz : S.InY z) (l : Kˣ) :
    S.ψ (S.kap l z) = ![((l : K) ^ 6 - 1) * S.ψ z 0, 0] := by
  rw [S.ψ_mul _ (S.hElt_mem hz.1 l) _ (inv_mem hz.1), S.ψ_inv hz.1, S.ψ_hElt hz.1]
  ext i; fin_cases i
  · simp; ring
  · simp [hz.2]

def InW₁ (l : Kˣ) (a : G) : Prop := ∃ z, S.InY z ∧ a = S.kap l z

theorem InW₁.inY {S : WSetting G K} {l : Kˣ} {a : G} (ha : S.InW₁ l a) : S.InY a := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨S.kap_mem hz.1 l, by rw [S.ψ_kap hz]; rfl⟩

theorem kap_mul (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {z z' : G} (hz : z ∈ S.W)
    (hz' : z' ∈ S.W) (l : Kˣ) : S.kap l z * S.kap l z' = S.kap l (z * z') := by
  have hA' := S.hElt_mem hz' l
  calc S.kap l z * S.kap l z' = S.hElt l * z * (S.hElt l)⁻¹ *
        (z⁻¹ * (S.hElt l * z' * (S.hElt l)⁻¹ * z'⁻¹)) := by simp only [kap]; group
    _ = S.hElt l * z * (S.hElt l)⁻¹ *
        ((S.hElt l * z' * (S.hElt l)⁻¹ * z'⁻¹) * z⁻¹) := by
      rw [hcomm _ (inv_mem hz) _ (mul_mem hA' (inv_mem hz'))]
    _ = S.kap l (z * z') := by simp only [kap, hElt]; group

theorem kap_inv_mul (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {z z' : G} (hz : z ∈ S.W)
    (hz' : z' ∈ S.W) (l : Kˣ) : (S.kap l z)⁻¹ * S.kap l z' = S.kap l (z⁻¹ * z') := by
  have hA := S.hElt_mem hz l
  have hA' := S.hElt_mem hz' l
  have hm : (S.hElt l * z * (S.hElt l)⁻¹)⁻¹ * (S.hElt l * z' * (S.hElt l)⁻¹) * z'⁻¹ ∈ S.W :=
    mul_mem (mul_mem (inv_mem hA) hA') (inv_mem hz')
  calc (S.kap l z)⁻¹ * S.kap l z' = z * ((S.hElt l * z * (S.hElt l)⁻¹)⁻¹ *
        (S.hElt l * z' * (S.hElt l)⁻¹) * z'⁻¹) := by simp only [kap, hElt]; group
    _ = ((S.hElt l * z * (S.hElt l)⁻¹)⁻¹ * (S.hElt l * z' * (S.hElt l)⁻¹) * z'⁻¹) * z := by
      rw [hcomm _ hz _ hm]
    _ = S.kap l (z⁻¹ * z') := by simp only [kap, hElt]; group

theorem InW₁.mul {S : WSetting G K} (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {l : Kˣ}
    {a b : G} (ha : S.InW₁ l a) (hb : S.InW₁ l b) : S.InW₁ l (a * b) := by
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨z', hz', rfl⟩ := hb
  exact ⟨z * z', hz.mul hz', S.kap_mul hcomm hz.1 hz'.1 l⟩

theorem InW₁.inv_mul {S : WSetting G K} (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a)
    {l : Kˣ} {a b : G} (ha : S.InW₁ l a) (hb : S.InW₁ l b) : S.InW₁ l (a⁻¹ * b) := by
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨z', hz', rfl⟩ := hb
  exact ⟨z⁻¹ * z', hz.inv.mul hz', S.kap_inv_mul hcomm hz.1 hz'.1 l⟩

theorem InW₁.exists_eq_ι [CharP K 2] {S : WSetting G K} {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1)
    {a : G} (ha : S.InW₁ l a) (h0 : S.ψ a = 0) : ∃ e : K, a = S.ι ![e, 0] := by
  obtain ⟨z, hz, rfl⟩ := ha
  have h1 := congrFun h0 0
  rw [S.ψ_kap hz] at h1
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at h1
  have hz0 : S.ψ z 0 = 0 := (mul_eq_zero.mp h1).resolve_left (pow_six_ne_one hl)
  obtain ⟨v, rfl⟩ := S.ψ_eq_zero z hz.1 (by rw [hz.ψ_eq, hz0]; ext i; fin_cases i <;> rfl)
  refine ⟨((l : K) ^ 6 - 1) * v 0, ?_⟩
  rw [kap, S.hElt_ι, ← S.ι_neg, ← S.ι_add]
  congr 1
  ext i; fin_cases i
  · simp; ring
  · simp

theorem exists_inW₁ [CharP K 2] {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1) (x : K) :
    ∃ a, S.InW₁ l a ∧ S.ψ a = ![x, 0] := by
  have hz := S.sec_inY (((l : K) ^ 6 - 1)⁻¹ * x)
  refine ⟨S.kap l _, ⟨_, hz, rfl⟩, ?_⟩
  rw [S.ψ_kap hz, S.ψ_sec]
  simp only [Matrix.cons_val_zero]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_six_ne_one hl), one_mul]

theorem InW₁.diag {S : WSetting G K} {l : Kˣ} {a : G} (ha : S.InW₁ l a) (l' : Kˣ) :
    S.InW₁ l (S.diag l' * a * (S.diag l')⁻¹) := by
  obtain ⟨z, hz, rfl⟩ := ha
  refine ⟨_, hz.diag l', ?_⟩
  have hdh : S.diag l' * S.hElt l * (S.diag l')⁻¹ = S.hElt l := by
    rw [← S.hElt_comm_diag, mul_inv_cancel_right]
  have e : S.diag l' * S.kap l z * (S.diag l')⁻¹ =
      (S.diag l' * S.hElt l * (S.diag l')⁻¹) * (S.diag l' * z * (S.diag l')⁻¹) *
        (S.diag l' * S.hElt l * (S.diag l')⁻¹)⁻¹ * (S.diag l' * z * (S.diag l')⁻¹)⁻¹ := by
    simp only [kap, hElt]; group
  rw [e, hdh]

noncomputable def beta (l : Kˣ) (x : K) : G :=
  Classical.epsilon fun a => S.InW₁ l a ∧ S.ψ a = ![x, 0]

theorem beta_spec [CharP K 2] {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1) (x : K) :
    S.InW₁ l (S.beta l x) ∧ S.ψ (S.beta l x) = ![x, 0] :=
  Classical.epsilon_spec (S.exists_inW₁ hl x)

theorem eq_beta_mul [CharP K 2] (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {l : Kˣ}
    (hl : (l : K) ^ 3 ≠ 1) {a : G} (ha : S.InW₁ l a) {x : K} (hx : S.ψ a = ![x, 0]) :
    ∃ e : K, a = S.beta l x * S.ι ![e, 0] := by
  have hb := S.beta_spec hl x
  obtain ⟨e, he⟩ := InW₁.exists_eq_ι hl (hb.1.inv_mul hcomm ha) (by
    rw [S.ψ_mul _ (inv_mem hb.1.inY.1) _ ha.inY.1, S.ψ_inv hb.1.inY.1, hb.2, hx,
      neg_add_cancel])
  exact ⟨e, by rw [← he, mul_inv_cancel_left]⟩

noncomputable def eFun (l : Kˣ) (s x : K) : K :=
  Classical.epsilon fun e => S.root s * S.beta l x * (S.root s)⁻¹ = S.ι ![e, 0] * S.beta l x

theorem eFun_spec [CharP K 2] {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1) (s x : K) :
    S.root s * S.beta l x * (S.root s)⁻¹ = S.ι ![S.eFun l s x, 0] * S.beta l x :=
  Classical.epsilon_spec (S.exists_root_conj (S.beta_spec hl x).1.inY s)

theorem root_conj_inW₁ [CharP K 2] (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {l : Kˣ}
    (hl : (l : K) ^ 3 ≠ 1) {a : G} (ha : S.InW₁ l a) {x : K} (hx : S.ψ a = ![x, 0]) (s : K) :
    S.root s * a * (S.root s)⁻¹ = S.ι ![S.eFun l s x, 0] * a := by
  obtain ⟨e, rfl⟩ := S.eq_beta_mul hcomm hl ha hx
  have h1 : S.root s * (S.beta l x * S.ι ![e, 0]) * (S.root s)⁻¹ =
      (S.root s * S.beta l x * (S.root s)⁻¹) * (S.root s * S.ι ![e, 0] * (S.root s)⁻¹) := by
    group
  rw [h1, S.eFun_spec hl, S.root_ι]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero,
    add_zero]
  group

theorem eFun_add [CharP K 2] (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {l : Kˣ}
    (hl : (l : K) ^ 3 ≠ 1) (s x x' : K) : S.eFun l s (x + x') = S.eFun l s x + S.eFun l s x' := by
  have hb := S.beta_spec hl x
  have hb' := S.beta_spec hl x'
  have ha := hb.1.mul hcomm hb'.1
  have hx : S.ψ (S.beta l x * S.beta l x') = ![x + x', 0] := by
    rw [S.ψ_mul _ hb.1.inY.1 _ hb'.1.inY.1, hb.2, hb'.2]
    ext i; fin_cases i <;> simp
  have h1 := S.root_conj_inW₁ hcomm hl ha hx s
  have h2 : S.root s * (S.beta l x * S.beta l x') * (S.root s)⁻¹ =
      (S.root s * S.beta l x * (S.root s)⁻¹) * (S.root s * S.beta l x' * (S.root s)⁻¹) := by
    group
  rw [h2, S.eFun_spec hl, S.eFun_spec hl] at h1
  have h3 : S.ι ![S.eFun l s x, 0] * S.beta l x * (S.ι ![S.eFun l s x', 0] * S.beta l x') =
      S.ι (![S.eFun l s x, 0] + ![S.eFun l s x', 0]) * (S.beta l x * S.beta l x') := by
    rw [S.ι_add]
    calc S.ι ![S.eFun l s x, 0] * S.beta l x * (S.ι ![S.eFun l s x', 0] * S.beta l x') =
        S.ι ![S.eFun l s x, 0] * (S.beta l x * S.ι ![S.eFun l s x', 0]) * S.beta l x' := by
          group
      _ = S.ι ![S.eFun l s x, 0] * (S.ι ![S.eFun l s x', 0] * S.beta l x) * S.beta l x' := by
          rw [S.ι_comm _ _ hb.1.inY.1]
      _ = _ := by group
  rw [h3] at h1
  have h4 := congrFun (S.ι_injective (mul_right_cancel h1)) 0
  simpa using h4.symm

theorem eFun_diag [CharP K 2] (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {l : Kˣ}
    (hl : (l : K) ^ 3 ≠ 1) (l' : Kˣ) (s x : K) :
    S.eFun l ((l' : K) ^ 2 * s) ((l' : K) * x) = l' * S.eFun l s x := by
  have hb := S.beta_spec hl x
  have ha := hb.1.diag l'
  have hx : S.ψ (S.diag l' * S.beta l x * (S.diag l')⁻¹) = ![(l' : K) * x, 0] := by
    rw [S.ψ_diag hb.1.inY.1, hb.2]
    ext i; fin_cases i <;> simp
  have h1 := S.root_conj_inW₁ hcomm hl ha hx ((l' : K) ^ 2 * s)
  have h2 : S.root ((l' : K) ^ 2 * s) * (S.diag l' * S.beta l x * (S.diag l')⁻¹) *
      (S.root ((l' : K) ^ 2 * s))⁻¹ =
      S.diag l' * (S.root s * S.beta l x * (S.root s)⁻¹) * (S.diag l')⁻¹ := by
    rw [← S.diag_conj_root]
    group
  rw [h2, S.eFun_spec hl] at h1
  have h3 : S.diag l' * (S.ι ![S.eFun l s x, 0] * S.beta l x) * (S.diag l')⁻¹ =
      (S.diag l' * S.ι ![S.eFun l s x, 0] * (S.diag l')⁻¹) *
        (S.diag l' * S.beta l x * (S.diag l')⁻¹) := by group
  rw [h3, S.diag_ι] at h1
  have h4 := congrFun (S.ι_injective (mul_right_cancel h1)) 0
  simpa using h4.symm

noncomputable abbrev w₂ : G := S.sec ![0, 1]

noncomputable def rFun (l : Kˣ) (s : K) : Fin 2 → K :=
  Classical.epsilon fun r => S.root s * S.w₂ * (S.root s)⁻¹ = S.beta l s * S.ι r * S.w₂

theorem rFun_spec [CharP K 2] {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1) (s : K) :
    S.root s * S.w₂ * (S.root s)⁻¹ = S.beta l s * S.ι (S.rFun l s) * S.w₂ := by
  have hw := S.sec_mem (![0, 1] : Fin 2 → K)
  have hgw : S.root s * S.w₂ * (S.root s)⁻¹ ∈ S.W := S.lev_mem _ _ hw
  have hb := S.beta_spec hl s
  obtain ⟨r, hr⟩ := S.exists_eq_mul_ι (mul_mem hgw (inv_mem hw)) hb.1.inY.1 (by
    rw [S.ψ_mul _ hgw _ (inv_mem hw), S.ψ_inv hw, S.ψ_root hw, hb.2, S.ψ_sec]
    ext i; fin_cases i <;> simp)
  refine Classical.epsilon_spec (p := fun r => S.root s * S.w₂ * (S.root s)⁻¹ =
    S.beta l s * S.ι r * S.w₂) ⟨r, ?_⟩
  rw [← hr, inv_mul_cancel_right]

theorem star [CharP K 2] {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1) (s : K) :
    S.eFun l s s + s * S.rFun l s 1 + s * S.theta 1 = 0 := by
  have hw := S.sec_mem (![0, 1] : Fin 2 → K)
  have hb := S.beta_spec hl s
  have hB := hb.1.inY.1
  set B := S.beta l s
  set r := S.rFun l s
  have h0 : S.root s * (S.root s * S.w₂ * (S.root s)⁻¹) * (S.root s)⁻¹ = S.w₂ := by
    calc S.root s * (S.root s * S.w₂ * (S.root s)⁻¹) * (S.root s)⁻¹ =
        (S.root s * S.root s) * S.w₂ * (S.root s * S.root s)⁻¹ := by group
      _ = S.w₂ := by rw [S.root_mul_self, one_mul, inv_one, mul_one]
  rw [S.rFun_spec hl] at h0
  have h1 : S.root s * (B * S.ι r * S.w₂) * (S.root s)⁻¹ =
      (S.root s * B * (S.root s)⁻¹) * (S.root s * S.ι r * (S.root s)⁻¹) *
        (S.root s * S.w₂ * (S.root s)⁻¹) := by group
  rw [h1, S.eFun_spec hl, S.root_ι, S.rFun_spec hl] at h0
  have h2 : S.ι ![S.eFun l s s, 0] * B * S.ι ![r 0 + s * r 1, r 1] * (B * S.ι r * S.w₂) =
      S.ι (![S.eFun l s s, 0] + ![r 0 + s * r 1, r 1] + r) * (B * B) * S.w₂ := by
    rw [S.ι_add, S.ι_add]
    have c1 := S.ι_comm ![r 0 + s * r 1, r 1] B hB
    have c2 := S.ι_comm r B hB
    calc S.ι ![S.eFun l s s, 0] * B * S.ι ![r 0 + s * r 1, r 1] * (B * S.ι r * S.w₂) =
        S.ι ![S.eFun l s s, 0] * (B * S.ι ![r 0 + s * r 1, r 1]) * B * S.ι r * S.w₂ := by
          group
      _ = S.ι ![S.eFun l s s, 0] * S.ι ![r 0 + s * r 1, r 1] * (B * (B * S.ι r)) * S.w₂ := by
          rw [← c1]; group
      _ = S.ι ![S.eFun l s s, 0] * S.ι ![r 0 + s * r 1, r 1] * (B * (S.ι r * B)) * S.w₂ := by
          rw [c2]
      _ = S.ι ![S.eFun l s s, 0] * S.ι ![r 0 + s * r 1, r 1] * ((B * S.ι r) * B) * S.w₂ := by
          group
      _ = S.ι ![S.eFun l s s, 0] * S.ι ![r 0 + s * r 1, r 1] * ((S.ι r * B) * B) * S.w₂ := by
          rw [c2]
      _ = _ := by group
  rw [h2, S.mul_self_eq hb.1.inY, hb.2, ← S.ι_add] at h0
  have h3 := congrFun (S.ι_injective (mul_eq_right.mp h0 |>.trans S.ι_zero.symm)) 0
  simp only [Pi.add_apply, Matrix.cons_val_zero, Pi.zero_apply] at h3
  linear_combination h3 - CharTwo.add_self_eq_zero (r 0)

theorem root_root_w₂ [CharP K 2] {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1) (s s' : K) :
    S.root s * (S.root s' * S.w₂ * (S.root s')⁻¹) * (S.root s)⁻¹ =
      S.ι (![S.eFun l s s', 0] + ![S.rFun l s' 0 + s * S.rFun l s' 1, S.rFun l s' 1] +
        S.rFun l s) * (S.beta l s' * S.beta l s) * S.w₂ := by
  have hB := (S.beta_spec hl s).1.inY.1
  have hB' := (S.beta_spec hl s').1.inY.1
  set B := S.beta l s
  set B' := S.beta l s'
  set r := S.rFun l s
  set r' := S.rFun l s'
  rw [S.rFun_spec hl s']
  have h1 : S.root s * (B' * S.ι r' * S.w₂) * (S.root s)⁻¹ =
      (S.root s * B' * (S.root s)⁻¹) * (S.root s * S.ι r' * (S.root s)⁻¹) *
        (S.root s * S.w₂ * (S.root s)⁻¹) := by group
  rw [h1, S.eFun_spec hl, S.root_ι, S.rFun_spec hl, S.ι_add, S.ι_add]
  have c1 := S.ι_comm ![r' 0 + s * r' 1, r' 1] B' hB'
  have c2 := S.ι_comm r B hB
  have c3 := S.ι_comm r B' hB'
  calc S.ι ![S.eFun l s s', 0] * B' * S.ι ![r' 0 + s * r' 1, r' 1] * (B * S.ι r * S.w₂) =
      S.ι ![S.eFun l s s', 0] * (B' * S.ι ![r' 0 + s * r' 1, r' 1]) * (B * S.ι r) * S.w₂ := by
        group
    _ = S.ι ![S.eFun l s s', 0] * (S.ι ![r' 0 + s * r' 1, r' 1] * B') * (S.ι r * B) * S.w₂ := by
        rw [c1, c2]
    _ = S.ι ![S.eFun l s s', 0] * S.ι ![r' 0 + s * r' 1, r' 1] * (B' * S.ι r) * B * S.w₂ := by
        group
    _ = S.ι ![S.eFun l s s', 0] * S.ι ![r' 0 + s * r' 1, r' 1] * (S.ι r * B') * B * S.w₂ := by
        rw [c3]
    _ = _ := by group

theorem twostar [CharP K 2] (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {l : Kˣ}
    (hl : (l : K) ^ 3 ≠ 1) (s s' : K) :
    S.eFun l s s' + s * S.rFun l s' 1 = S.eFun l s' s + s' * S.rFun l s 1 := by
  have hB := (S.beta_spec hl s).1.inY.1
  have hB' := (S.beta_spec hl s').1.inY.1
  have h0 : S.root s * (S.root s' * S.w₂ * (S.root s')⁻¹) * (S.root s)⁻¹ =
      S.root s' * (S.root s * S.w₂ * (S.root s)⁻¹) * (S.root s')⁻¹ := by
    calc S.root s * (S.root s' * S.w₂ * (S.root s')⁻¹) * (S.root s)⁻¹ =
        (S.root s * S.root s') * S.w₂ * (S.root s * S.root s')⁻¹ := by group
      _ = (S.root s' * S.root s) * S.w₂ * (S.root s' * S.root s)⁻¹ := by rw [S.root_comm]
      _ = _ := by group
  rw [S.root_root_w₂ hl, S.root_root_w₂ hl, hcomm _ hB _ hB'] at h0
  have h1 := congrFun (S.ι_injective (mul_right_cancel (mul_right_cancel h0))) 0
  simp only [Pi.add_apply, Matrix.cons_val_zero] at h1
  linear_combination h1

theorem theta_one_eq_zero [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) : S.theta 1 = 0 := by
  classical
  obtain ⟨l, hl⟩ := exists_unit_cube_ne_one hK
  have : Fintype K := Fintype.ofFinite K
  set c := S.theta 1 with hc
  set e : K → K := S.eFun l 1 with he
  have he_add : ∀ x x', e (x + x') = e x + e x' := S.eFun_add hcomm hl 1
  have he0 : e 0 = 0 := by
    have h := he_add 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hF : ∀ σ : Kˣ, e ((σ : K) ^ 2) + ((σ⁻¹ : Kˣ) : K) * e σ + c =
      (σ : K) * e ((σ⁻¹ : Kˣ) : K) + (σ : K) ^ 2 * e 1 + (σ : K) ^ 2 * c := by
    intro σ
    set t : K := ((σ⁻¹ : Kˣ) : K)
    have hst : (σ : K) * t = 1 := Units.mul_inv σ
    have h1 := S.star hl 1
    have h2 := S.star hl ((σ : K) ^ 2)
    have h3 := S.twostar hcomm hl 1 ((σ : K) ^ 2)
    have h4 := S.eFun_diag hcomm hl σ 1 (σ : K)
    have h5 := S.eFun_diag hcomm hl σ 1 t
    rw [mul_one, ← sq] at h4
    rw [mul_one, hst] at h5
    rw [h4] at h2
    rw [h5] at h3
    linear_combination h3 + (σ : K) ^ 2 * h1 + t ^ 2 * h2 -
      (t * e σ + (t * σ + 1) * (S.rFun l ((σ : K) ^ 2) 1 + c)) * hst -
      ((σ : K) ^ 2 * e 1 + (σ : K) ^ 2 * c + S.rFun l ((σ : K) ^ 2) 1) * h2K
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset Kˣ)) rfl (fun σ _ => hF σ)
  simp only [Finset.sum_add_distrib] at hsum
  let eHom : K →+ K := { toFun := e, map_zero' := he0, map_add' := he_add }
  have hsq : ∑ σ : Kˣ, (σ : K) ^ 2 = 0 := by
    rw [FiniteField.sum_pow_units]
    split_ifs with hdvd
    · have h1 := Nat.le_of_dvd (by norm_num) hdvd
      have h2 : 8 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
      omega
    · rfl
  have hA : ∑ σ : Kˣ, e ((σ : K) ^ 2) = 0 := by
    have h := map_sum eHom (fun σ : Kˣ => (σ : K) ^ 2) Finset.univ
    change ∑ σ : Kˣ, eHom ((σ : K) ^ 2) = 0
    rw [← h, hsq, map_zero]
  have hB : ∑ σ : Kˣ, ((σ⁻¹ : Kˣ) : K) * e σ = ∑ σ : Kˣ, (σ : K) * e ((σ⁻¹ : Kˣ) : K) :=
    Fintype.sum_equiv (Equiv.inv Kˣ) _ _ (fun σ => by simp)
  have hC : ∑ _σ : Kˣ, c = -c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_units, nsmul_eq_mul,
      Nat.cast_sub (Fintype.card_pos), FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub,
      neg_one_mul]
  have hD : ∑ σ : Kˣ, (σ : K) ^ 2 * e 1 = 0 := by rw [← Finset.sum_mul, hsq, zero_mul]
  have hE : ∑ σ : Kˣ, (σ : K) ^ 2 * c = 0 := by rw [← Finset.sum_mul, hsq, zero_mul]
  rw [hA, hB, hC, hD, hE] at hsum
  linear_combination -hsum

theorem mul_self_eq_one [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    (hcomm : ∀ a ∈ S.W, ∀ b ∈ S.W, a * b = b * a) {a : G} (ha : a ∈ S.W) : a * a = 1 := by
  by_cases h0 : S.ψ a = 0
  · obtain ⟨v, rfl⟩ := S.ψ_eq_zero a ha h0
    exact S.ι_mul_self v
  have he₁ : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨B, hB⟩ := exists_SL_mulVec_eq h0 he₁
  have hz : S.InY (S.lev B * a * (S.lev B)⁻¹) :=
    ⟨S.lev_mem _ _ ha, by rw [S.lev_ψ _ _ ha, hB]; rfl⟩
  have h1 := S.mul_self_eq hz
  rw [S.theta_one_eq_zero hK hcomm, mul_zero] at h1
  have h0' : (![0, 0] : Fin 2 → K) = 0 := by ext i; fin_cases i <;> rfl
  rw [h0', S.ι_zero] at h1
  have h2 : S.lev B * (a * a) * (S.lev B)⁻¹ = 1 := by
    rw [← h1]; group
  calc a * a = (S.lev B)⁻¹ * (S.lev B * (a * a) * (S.lev B)⁻¹) * S.lev B := by group
    _ = 1 := by rw [h2, mul_one, inv_mul_cancel]

theorem card_W [Finite K] : Nat.card S.W = Nat.card K ^ 4 := by
  let f : S.W →* Multiplicative (Fin 2 → K) :=
    { toFun := fun a => Multiplicative.ofAdd (S.ψ a)
      map_one' := by rw [OneMemClass.coe_one, S.ψ_one, ofAdd_zero]
      map_mul' := fun a b => by rw [Subgroup.coe_mul, S.ψ_mul _ a.2 _ b.2, ofAdd_add] }
  have hf : Function.Surjective f := by
    intro ξ
    obtain ⟨a, ha, hψ⟩ := S.ψ_surj (Multiplicative.toAdd ξ)
    exact ⟨⟨a, ha⟩, by simp [f, hψ]⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (S.W ⧸ f.ker) = Nat.card (Fin 2 → K) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have h3 : Nat.card f.ker = Nat.card (Fin 2 → K) := by
    let g : (Fin 2 → K) → f.ker := fun v => ⟨⟨S.ι v, S.ι_mem v⟩, by
      rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd (S.ψ (S.ι v)) = 1
      rw [S.ψ_ι, ofAdd_zero]⟩
    have hg : Function.Bijective g := by
      refine ⟨fun v w h => S.ι_injective (congrArg (fun x : f.ker => ((x : S.W) : G)) h), ?_⟩
      rintro ⟨⟨a, ha⟩, hker⟩
      obtain ⟨v, hv⟩ := S.ψ_eq_zero a ha (by
        have := (MonoidHom.mem_ker).mp hker
        exact this)
      exact ⟨v, by ext; exact hv⟩
    exact (Nat.card_congr (Equiv.ofBijective g hg)).symm
  rw [h1, h2, h3, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  ring

end WSetting

namespace XSetting

variable {G : Type*} [Group G] {K : Type*} [Field K] (S : XSetting G K)

theorem eq_of_comm [Finite K] (hK : 2 ≤ Nat.card K) {W W' : Subgroup G}
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hor : ∀ x ∈ S.X, x ∈ W ∨ x * S.t ∈ W)
    (ht : ∀ x ∈ W, S.t * x * S.t⁻¹ ∈ W)
    (hfix : ∀ x ∈ W, S.t * x * S.t * x⁻¹ = 1 → ∃ v, S.ι v = x)
    (hcard : Nat.card W = Nat.card K ^ 4) (hW'X : W' ≤ S.X)
    (hcomm' : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a) (hcard' : Nat.card W' = Nat.card K ^ 4) :
    W' = W := by
  classical
  have hq : 0 < Nat.card K := by omega
  have hfinW : Finite W := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hfinW' : Finite W' := Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  by_cases hle : W' ≤ W
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard'])
  exfalso
  obtain ⟨a, haW', haW⟩ := Set.not_subset.mp hle
  have hat : a * S.t ∈ W := (hor a (hW'X haW')).resolve_left haW
  have hV : ∀ b ∈ W' ⊓ W, ∃ v, S.ι v = b := by
    intro b hb
    obtain ⟨hbW', hbW⟩ := Subgroup.mem_inf.mp hb
    apply hfix b hbW
    have h1 : b * a = a * b := hcomm' b hbW' a haW'
    have h2 : b * (a * S.t) = (a * S.t) * b := hcomm b hbW _ hat
    have h3 : b * S.t = S.t * b := by
      have e1 : S.t = a⁻¹ * (a * S.t) := by group
      calc b * S.t = b * a⁻¹ * (a * S.t) := by rw [e1]; group
        _ = a⁻¹ * b * (a * S.t) := by
          rw [show b * a⁻¹ = a⁻¹ * b by
            rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h1, mul_inv_cancel_right]]
        _ = a⁻¹ * ((a * S.t) * b) := by rw [mul_assoc, h2]
        _ = S.t * b := by group
    rw [mul_assoc S.t b, h3, ← mul_assoc, S.t_mul_self, one_mul, mul_inv_cancel]
  have hcardV : Nat.card ↥(W' ⊓ W) ≤ Nat.card K ^ 2 := by
    let g : ↥(W' ⊓ W) → (Fin 2 → K) := fun b => Classical.choose (hV b b.2)
    have hg : Function.Injective g := by
      intro b b' h
      apply Subtype.ext
      rw [← Classical.choose_spec (hV b b.2), ← Classical.choose_spec (hV b' b'.2)]
      exact congrArg S.ι h
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at this
  have hinv : ∀ b ∈ W', b ∉ W → a⁻¹ * b ∈ W' ⊓ W := by
    intro b hbW' hbW
    have hbt : b * S.t ∈ W := (hor b (hW'X hbW')).resolve_left hbW
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem haW') hbW', ?_⟩
    have e : a⁻¹ * b = S.t * ((a * S.t)⁻¹ * (b * S.t)) * S.t⁻¹ := by
      rw [S.t_inv]
      calc a⁻¹ * b = a⁻¹ * b * (S.t * S.t) := by rw [S.t_mul_self, mul_one]
        _ = _ := by group
    rw [e]
    exact ht _ (mul_mem (inv_mem hat) hbt)
  let F : W' → ↥(W' ⊓ W) ⊕ ↥(W' ⊓ W) := fun b =>
    if h : (b : G) ∈ W then Sum.inl ⟨b, Subgroup.mem_inf.mpr ⟨b.2, h⟩⟩
    else Sum.inr ⟨_, hinv b b.2 h⟩
  have hF : Function.Injective F := by
    intro b b' h
    by_cases hb : (b : G) ∈ W <;> by_cases hb' : (b' : G) ∈ W <;>
      simp only [F, hb, hb', dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h
    · exact Subtype.ext (congrArg (fun x : ↥(W' ⊓ W) => (x : G)) h)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun x : ↥(W' ⊓ W) => (x : G)) h))
  have : Finite ↥(W' ⊓ W) := Finite.of_injective
    (fun x : ↥(W' ⊓ W) => (⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩ : W'))
    (fun x y h => Subtype.ext (congrArg (fun z : W' => (z : G)) h))
  have h1 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_sum, hcard'] at h1
  have h2 : Nat.card K ^ 4 ≤ 2 * Nat.card K ^ 2 := by omega
  have h3 : 2 * Nat.card K ^ 2 < Nat.card K ^ 4 := by
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    nlinarith
  omega

theorem exists_W [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) :
    ∃ W : Subgroup G, W ≤ S.X ∧ (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∧ (∀ a ∈ W, a * a = 1) ∧
      Nat.card W = Nat.card K ^ 4 ∧ (∀ v, S.ι v ∈ W) ∧ S.t ∉ W ∧
      (∀ x ∈ S.X, x ∈ W ∨ x * S.t ∈ W) ∧ (∀ x ∈ W, S.t * x * S.t⁻¹ ∈ W) ∧
      (∀ x ∈ W, S.t * x * S.t * x⁻¹ = 1 → ∃ v, S.ι v = x) ∧
      (∀ v, ∃ x ∈ W, S.t * x * S.t * x⁻¹ = S.ι v) ∧
      ∀ W' : Subgroup G, W' ≤ S.X → (∀ a ∈ W', ∀ b ∈ W', a * b = b * a) →
        Nat.card W' = Nat.card K ^ 4 → W' = W := by
  obtain ⟨l, hl⟩ := exists_unit_cube_ne_one hK
  let T := S.toWSetting hK hl
  have hcomm : ∀ a ∈ S.Wsub hK l, ∀ b ∈ S.Wsub hK l, a * b = b * a :=
    fun a ha b hb => T.comm ha hb
  have hcard : Nat.card (S.Wsub hK l) = Nat.card K ^ 4 := T.card_W
  have hor : ∀ x ∈ S.X, x ∈ S.Wsub hK l ∨ x * S.t ∈ S.Wsub hK l :=
    fun x hx => S.mem_Wsub_or hK hl hx
  have ht : ∀ x ∈ S.Wsub hK l, S.t * x * S.t⁻¹ ∈ S.Wsub hK l :=
    fun x hx => S.t_conj_mem_Wsub hK hx
  have hfix : ∀ x ∈ S.Wsub hK l, S.t * x * S.t * x⁻¹ = 1 → ∃ v, S.ι v = x :=
    fun x hx h => S.exists_ι_of_mem_Wsub hK hl hx ((S.ψ_eq_zero_iff hx.1).mpr h)
  refine ⟨S.Wsub hK l, S.Wsub_le hK, hcomm, fun a ha => T.mul_self_eq_one hK hcomm ha, hcard,
    S.ι_mem_Wsub hK, S.t_not_mem_Wsub hK hl, hor, ht, hfix, fun v => ?_,
    fun W' hW'X hcomm' hcard' => S.eq_of_comm (by omega) hcomm hor ht hfix hcard hW'X hcomm'
      hcard'⟩
  obtain ⟨x, hx, hψ⟩ := S.exists_mem_Wsub_ψ hK hl v
  exact ⟨x, hx, by rw [← S.ι_ψ hx.1, hψ]⟩

end XSetting

end CFSG.LocalAnalysis.EvenBN.LinearThree.WLocal
