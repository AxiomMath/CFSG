module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.SetLike.Fintype
import Mathlib.Tactic.Group
import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModule

open Subgroup

variable {F : Type*} [Field F] {K : Type*} [Group K] [Fintype K]
  {V : Type*} [AddCommGroup V] [Module F V]

open Classical in
@[expose] noncomputable def sumOver (ρ : K →* Module.End F V) (S : Subgroup K) : Module.End F V :=
  ∑ s ∈ Finset.univ.filter (· ∈ S), ρ s

@[expose] noncomputable def avg (ρ : K →* Module.End F V) (S : Subgroup K) : Module.End F V :=
  ((Nat.card S : ℕ) : F)⁻¹ • sumOver ρ S

open Classical in
theorem mem_filter_iff (S : Subgroup K) (s : K) : s ∈ Finset.univ.filter (· ∈ S) ↔ s ∈ S := by
  simp

open Classical in
theorem card_filter_eq (S : Subgroup K) : (Finset.univ.filter (· ∈ S)).card = Nat.card S := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem mul_sumOver (ρ : K →* Module.End F V) {S : Subgroup K} {s : K} (hs : s ∈ S) :
    ρ s * sumOver ρ S = sumOver ρ S := by
  classical
  unfold sumOver
  rw [Finset.mul_sum]
  simp_rw [← map_mul]
  refine Finset.sum_bij (fun t _ => s * t) ?_ ?_ ?_ ?_
  · intro t ht
    rw [mem_filter_iff] at ht ⊢
    exact S.mul_mem hs ht
  · intro a _ b _ h
    exact mul_left_cancel h
  · intro t ht
    refine ⟨s⁻¹ * t, ?_, by simp⟩
    rw [mem_filter_iff] at ht ⊢
    exact S.mul_mem (S.inv_mem hs) ht
  · intro t _
    rfl

theorem sumOver_mul (ρ : K →* Module.End F V) {S : Subgroup K} {s : K} (hs : s ∈ S) :
    sumOver ρ S * ρ s = sumOver ρ S := by
  classical
  unfold sumOver
  rw [Finset.sum_mul]
  simp_rw [← map_mul]
  refine Finset.sum_bij (fun t _ => t * s) ?_ ?_ ?_ ?_
  · intro t ht
    rw [mem_filter_iff] at ht ⊢
    exact S.mul_mem ht hs
  · intro a _ b _ h
    exact mul_right_cancel h
  · intro t ht
    refine ⟨t * s⁻¹, ?_, by simp⟩
    rw [mem_filter_iff] at ht ⊢
    exact S.mul_mem ht (S.inv_mem hs)
  · intro t _
    rfl

open Classical in
theorem sumOver_mul_right (ρ : K →* Module.End F V) (S : Subgroup K) (Y : Module.End F V) :
    sumOver ρ S * Y = ∑ s ∈ Finset.univ.filter (· ∈ S), ρ s * Y := by
  unfold sumOver
  rw [Finset.sum_mul]

open Classical in
theorem mul_sumOver_right (ρ : K →* Module.End F V) (S : Subgroup K) (Y : Module.End F V) :
    Y * sumOver ρ S = ∑ s ∈ Finset.univ.filter (· ∈ S), Y * ρ s := by
  unfold sumOver
  rw [Finset.mul_sum]

theorem sumOver_mul_self (ρ : K →* Module.End F V) (S : Subgroup K) :
    sumOver ρ S * sumOver ρ S = (Nat.card S) • sumOver ρ S := by
  classical
  rw [sumOver_mul_right]
  have : ∀ s ∈ Finset.univ.filter (· ∈ S), ρ s * sumOver ρ S = sumOver ρ S := fun s hs =>
    mul_sumOver ρ ((mem_filter_iff S s).1 hs)
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_filter_eq]

theorem sumOver_mul_sumOver_of_le (ρ : K →* Module.End F V) {S T : Subgroup K} (hST : S ≤ T) :
    sumOver ρ S * sumOver ρ T = (Nat.card S) • sumOver ρ T := by
  classical
  rw [sumOver_mul_right]
  have : ∀ s ∈ Finset.univ.filter (· ∈ S), ρ s * sumOver ρ T = sumOver ρ T := fun s hs =>
    mul_sumOver ρ (hST ((mem_filter_iff S s).1 hs))
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_filter_eq]

theorem sumOver_mul_sumOver_of_le' (ρ : K →* Module.End F V) {S T : Subgroup K} (hST : S ≤ T) :
    sumOver ρ T * sumOver ρ S = (Nat.card S) • sumOver ρ T := by
  classical
  rw [mul_sumOver_right]
  have : ∀ s ∈ Finset.univ.filter (· ∈ S), sumOver ρ T * ρ s = sumOver ρ T := fun s hs =>
    sumOver_mul ρ (hST ((mem_filter_iff S s).1 hs))
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_filter_eq]

section Avg

variable (ρ : K →* Module.End F V)

theorem avg_def (S : Subgroup K) : avg ρ S = ((Nat.card S : ℕ) : F)⁻¹ • sumOver ρ S := rfl

theorem nsmul_eq_cast_smul (n : ℕ) (X : Module.End F V) : n • X = (n : F) • X :=
  (Nat.cast_smul_eq_nsmul F n X).symm

theorem avg_mul_avg_self (S : Subgroup K) (hS : ((Nat.card S : ℕ) : F) ≠ 0) :
    avg ρ S * avg ρ S = avg ρ S := by
  rw [avg_def, smul_mul_smul_comm, sumOver_mul_self, nsmul_eq_cast_smul, smul_smul]
  congr 1
  field_simp

theorem avg_mul_avg_of_le {S T : Subgroup K} (hST : S ≤ T) (hS : ((Nat.card S : ℕ) : F) ≠ 0) :
    avg ρ S * avg ρ T = avg ρ T := by
  rw [avg_def, avg_def, smul_mul_smul_comm, sumOver_mul_sumOver_of_le ρ hST, nsmul_eq_cast_smul,
    smul_smul]
  congr 1
  field_simp

theorem avg_mul_avg_of_le' {S T : Subgroup K} (hST : S ≤ T) (hS : ((Nat.card S : ℕ) : F) ≠ 0) :
    avg ρ T * avg ρ S = avg ρ T := by
  rw [avg_def, avg_def, smul_mul_smul_comm, sumOver_mul_sumOver_of_le' ρ hST, nsmul_eq_cast_smul,
    smul_smul]
  congr 1
  field_simp

theorem mul_avg_of_mem {S : Subgroup K} {s : K} (hs : s ∈ S) : ρ s * avg ρ S = avg ρ S := by
  rw [avg_def, mul_smul_comm, mul_sumOver ρ hs]

theorem avg_apply_of_fixed {S : Subgroup K} (hS : ((Nat.card S : ℕ) : F) ≠ 0) {v : V}
    (hv : ∀ s ∈ S, ρ s v = v) : avg ρ S v = v := by
  classical
  rw [avg_def, LinearMap.smul_apply]
  have : sumOver ρ S v = ((Nat.card S : ℕ) : F) • v := by
    unfold sumOver
    rw [LinearMap.sum_apply]
    have : ∀ s ∈ Finset.univ.filter (· ∈ S), (ρ s) v = v := fun s hs =>
      hv s ((mem_filter_iff S s).1 hs)
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_filter_eq, ← Nat.cast_smul_eq_nsmul F]
  rw [this, smul_smul, inv_mul_cancel₀ hS, one_smul]

theorem fixed_of_mem_range_avg {S : Subgroup K} {x : V} (hx : x ∈ LinearMap.range (avg ρ S))
    (s : K) (hs : s ∈ S) : ρ s x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, mul_avg_of_mem ρ hs]

theorem sumOver_comm_of_commute {S : Subgroup K} {g : K} (hg : ∀ s ∈ S, g * s = s * g) :
    ρ g * sumOver ρ S = sumOver ρ S * ρ g := by
  classical
  rw [mul_sumOver_right, sumOver_mul_right]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← map_mul, ← map_mul, hg s ((mem_filter_iff S s).1 hs)]

theorem avg_comm_of_commute {S : Subgroup K} {g : K} (hg : ∀ s ∈ S, g * s = s * g) :
    ρ g * avg ρ S = avg ρ S * ρ g := by
  rw [avg_def, mul_smul_comm, smul_mul_assoc, sumOver_comm_of_commute ρ hg]

theorem mul_avg_conj (S : Subgroup K) (g : K) :
    ρ g * avg ρ S = avg ρ (S.map (MulAut.conj g).toMonoidHom) * ρ g := by
  classical
  have hcard : Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [avg_def, avg_def, hcard, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sumOver_right, sumOver_mul_right]
  refine Finset.sum_bij (fun s _ => g * s * g⁻¹) ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_filter_iff] at hs ⊢
    exact ⟨s, hs, rfl⟩
  · intro a _ b _ h
    simpa using h
  · intro t ht
    rw [mem_filter_iff] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨s, (mem_filter_iff S s).2 hs, rfl⟩
  · intro s _
    simp [← map_mul, mul_assoc]

theorem avg_mul_eq_of_forall {S : Subgroup K} (hS : ((Nat.card S : ℕ) : F) ≠ 0)
    {X : Module.End F V} (hX : ∀ u ∈ S, ρ u * X = X) : avg ρ S * X = X := by
  classical
  rw [avg_def, smul_mul_assoc, sumOver_mul_right]
  have : ∀ s ∈ Finset.univ.filter (· ∈ S), ρ s * X = X := fun s hs =>
    hX s ((mem_filter_iff S s).1 hs)
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_filter_eq, nsmul_eq_cast_smul, smul_smul,
    inv_mul_cancel₀ hS, one_smul]

theorem avg_mul_avg_lines {H H' U : Subgroup K} (hU : H ⊔ H' = U)
    (hcomm : ∀ h ∈ H, ∀ h' ∈ H', h * h' = h' * h) (hH : ((Nat.card H : ℕ) : F) ≠ 0)
    (hH' : ((Nat.card H' : ℕ) : F) ≠ 0) (hUc : ((Nat.card U : ℕ) : F) ≠ 0) :
    avg ρ H * avg ρ H' = avg ρ U := by
  set X := avg ρ H * avg ρ H' with hXdef
  let S0 : Subgroup K :=
    { carrier := {u | ρ u * X = X}
      mul_mem' := fun {a b} ha hb => by
        change ρ (a * b) * X = X
        rw [map_mul, mul_assoc]
        change ρ a * X = X at ha
        change ρ b * X = X at hb
        rw [hb, ha]
      one_mem' := by
        change ρ 1 * X = X
        rw [map_one, one_mul]
      inv_mem' := fun {a} ha => by
        change ρ a⁻¹ * X = X
        change ρ a * X = X at ha
        calc ρ a⁻¹ * X = ρ a⁻¹ * (ρ a * X) := by rw [ha]
          _ = X := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] }
  have hHS : H ≤ S0 := fun h hh => by
    change ρ h * (avg ρ H * avg ρ H') = avg ρ H * avg ρ H'
    rw [← mul_assoc, mul_avg_of_mem ρ hh]
  have hH'S : H' ≤ S0 := fun h' hh' => by
    change ρ h' * (avg ρ H * avg ρ H') = avg ρ H * avg ρ H'
    rw [← mul_assoc,
      avg_comm_of_commute ρ (S := H) (g := h') (fun s hs => (hcomm s hs h' hh').symm),
      mul_assoc, mul_avg_of_mem ρ hh']
  have hUS : ∀ u ∈ U, ρ u * X = X := fun u hu => by
    have : u ∈ S0 := (sup_le hHS hH'S : H ⊔ H' ≤ S0) (hU ▸ hu)
    exact this
  have hHU : H ≤ U := hU ▸ le_sup_left
  have hH'U : H' ≤ U := hU ▸ le_sup_right
  have h1 := avg_mul_eq_of_forall ρ hUc hUS
  have h2 : avg ρ U * X = avg ρ U := by
    rw [hXdef, ← mul_assoc, avg_mul_avg_of_le' ρ hHU hH, avg_mul_avg_of_le' ρ hH'U hH']
  rw [← h1, h2]

@[expose] noncomputable def proj (U H : Subgroup K) : Module.End F V := avg ρ H - avg ρ U

theorem proj_def (U H : Subgroup K) : proj ρ U H = avg ρ H - avg ρ U := rfl

end Avg

section Lines

variable {p : ℕ} [hp : Fact p.Prime] {U H H' : Subgroup K}

theorem sup_eq_of_card_prime_ne (hU : Nat.card U = p ^ 2) (hH : H ≤ U) (hH' : H' ≤ U)
    (hHc : Nat.card H = p) (hHc' : Nat.card H' = p) (hne : H ≠ H') : H ⊔ H' = U := by
  have hsupU : H ⊔ H' ≤ U := sup_le hH hH'
  have hdvd : Nat.card (H ⊔ H' : Subgroup K) ∣ p ^ 2 := hU ▸ Subgroup.card_dvd_of_le hsupU
  have hH_dvd : p ∣ Nat.card (H ⊔ H' : Subgroup K) := hHc ▸ Subgroup.card_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime_pow hp.out).1 hdvd with ⟨k, hk, hkc⟩
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkc
    have := Nat.le_of_dvd Nat.one_pos (hkc ▸ hH_dvd)
    exact hp.out.one_lt.ne' (le_antisymm this hp.out.one_lt.le)
  by_cases hk2 : k = 2
  · subst hk2
    exact (Subgroup.eq_of_le_of_card_ge hsupU (by rw [hU, hkc])).symm ▸ rfl
  · have hk1' : k = 1 := by omega
    subst hk1'
    exfalso
    have hHeq : H = H ⊔ H' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hkc, hHc]; simp)
    have hH'eq : H' = H ⊔ H' :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hkc, hHc']; simp)
    exact hne (hHeq.trans hH'eq.symm)

section Proj

variable (hpF : (p : F) ≠ 0)

omit [Fintype K] hp in
include hpF in
theorem card_cast_ne_zero_of_eq {S : Subgroup K} (hS : Nat.card S = p) :
    ((Nat.card S : ℕ) : F) ≠ 0 := by
  rw [hS]
  exact hpF

omit [Fintype K] hp in
include hpF in
theorem card_cast_ne_zero_plane (hU : Nat.card U = p ^ 2) : ((Nat.card U : ℕ) : F) ≠ 0 := by
  rw [hU]
  push_cast
  exact pow_ne_zero 2 hpF

variable (ρ : K →* Module.End F V)

include hpF in
omit hp in
theorem avg_line_mul_avg_plane (hH : H ≤ U) (hHc : Nat.card H = p) :
    avg ρ H * avg ρ U = avg ρ U := avg_mul_avg_of_le ρ hH (card_cast_ne_zero_of_eq hpF hHc)

include hpF in
omit hp in
theorem avg_plane_mul_avg_line (hH : H ≤ U) (hHc : Nat.card H = p) :
    avg ρ U * avg ρ H = avg ρ U := avg_mul_avg_of_le' ρ hH (card_cast_ne_zero_of_eq hpF hHc)

omit hp in
include hpF in
theorem proj_mul_proj_self (hU : Nat.card U = p ^ 2) (hH : H ≤ U) (hHc : Nat.card H = p) :
    proj ρ U H * proj ρ U H = proj ρ U H := by
  have h1 := avg_line_mul_avg_plane hpF ρ hH hHc
  have h2 := avg_plane_mul_avg_line hpF ρ hH hHc
  have h3 := avg_mul_avg_self ρ H (card_cast_ne_zero_of_eq hpF hHc)
  have h4 := avg_mul_avg_self ρ U (card_cast_ne_zero_plane hpF hU)
  simp only [proj_def, sub_mul, mul_sub, h1, h2, h3, h4]
  abel

include hpF in
theorem proj_mul_proj_of_ne (hU : Nat.card U = p ^ 2) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hH : H ≤ U) (hH' : H' ≤ U) (hHc : Nat.card H = p) (hHc' : Nat.card H' = p) (hne : H ≠ H') :
    proj ρ U H * proj ρ U H' = 0 := by
  have hsup := sup_eq_of_card_prime_ne hU hH hH' hHc hHc' hne
  have h0 := avg_mul_avg_lines ρ hsup (fun h hh h' hh' => hcomm h (hH hh) h' (hH' hh'))
    (card_cast_ne_zero_of_eq hpF hHc) (card_cast_ne_zero_of_eq hpF hHc')
    (card_cast_ne_zero_plane hpF hU)
  have h1 := avg_line_mul_avg_plane hpF ρ hH hHc
  have h2 := avg_plane_mul_avg_line hpF ρ hH' hHc'
  have h4 := avg_mul_avg_self ρ U (card_cast_ne_zero_plane hpF hU)
  simp only [proj_def, sub_mul, mul_sub, h0, h1, h2, h4]
  abel

omit hp in
include hpF in
theorem fixed_of_mem_range_proj (hH : H ≤ U) (hHc : Nat.card H = p)
    {x : V} (hx : x ∈ LinearMap.range (proj ρ U H)) (h : K) (hh : h ∈ H) : ρ h x = x := by
  obtain ⟨y, rfl⟩ := hx
  have : proj ρ U H = avg ρ H * (1 - avg ρ U) := by
    rw [proj_def, mul_sub, mul_one, avg_line_mul_avg_plane hpF ρ hH hHc]
  rw [this, ← Module.End.mul_apply, ← mul_assoc, mul_avg_of_mem ρ hh]

omit hp in
include hpF in
theorem proj_apply_of_mem_range (hU : Nat.card U = p ^ 2) (hH : H ≤ U) (hHc : Nat.card H = p)
    {x : V} (hx : x ∈ LinearMap.range (proj ρ U H)) : proj ρ U H x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, proj_mul_proj_self hpF ρ hU hH hHc]

variable {ρ}

theorem proj_comm_of_commute (hH : H ≤ U) {g : K}
    (hg : ∀ u ∈ U, g * u = u * g) : ρ g * proj ρ U H = proj ρ U H * ρ g := by
  rw [proj_def, mul_sub, sub_mul, avg_comm_of_commute ρ (S := H) (g := g)
    (fun s hs => hg s (hH hs)), avg_comm_of_commute ρ hg]

omit hp in
theorem mul_proj_conj {g : K} (hg : g ∈ normalizer (U : Set K)) :
    ρ g * proj ρ U H = proj ρ U (H.map (MulAut.conj g).toMonoidHom) * ρ g := by
  have hUmap : U.map (MulAut.conj g).toMonoidHom = U := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using this
  rw [proj_def, proj_def, mul_sub, sub_mul, mul_avg_conj ρ H g, mul_avg_conj ρ U g, hUmap]

section Independence

variable {H₁ H₂ H₃ : Subgroup K}

include hpF in
theorem disjoint_range_proj (hU : Nat.card U = p ^ 2) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (h₁ : H₁ ≤ U) (h₂ : H₂ ≤ U) (c₁ : Nat.card H₁ = p) (c₂ : Nat.card H₂ = p) (hne : H₁ ≠ H₂) :
    Disjoint (LinearMap.range (proj ρ U H₁)) (LinearMap.range (proj ρ U H₂)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨y, rfl⟩ ⟨z, hz⟩
  have hz' : proj ρ U H₂ z = proj ρ U H₁ y := hz
  have h0 := proj_mul_proj_of_ne hpF ρ hU hcomm h₁ h₂ c₁ c₂ hne
  have hy : proj ρ U H₁ (proj ρ U H₁ y) = proj ρ U H₁ y :=
    proj_apply_of_mem_range hpF ρ hU h₁ c₁ ⟨y, rfl⟩
  have hz2 : proj ρ U H₂ (proj ρ U H₁ y) = proj ρ U H₁ y := by
    rw [← hz']
    exact proj_apply_of_mem_range hpF ρ hU h₂ c₂ ⟨z, rfl⟩
  calc proj ρ U H₁ y = proj ρ U H₁ (proj ρ U H₂ (proj ρ U H₁ y)) := by rw [hz2, hy]
    _ = (proj ρ U H₁ * proj ρ U H₂) (proj ρ U H₁ y) := rfl
    _ = 0 := by rw [h0]; rfl

include hpF in
theorem disjoint_sup_range_proj (hU : Nat.card U = p ^ 2)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (h₁ : H₁ ≤ U) (h₂ : H₂ ≤ U) (h₃ : H₃ ≤ U)
    (c₁ : Nat.card H₁ = p) (c₂ : Nat.card H₂ = p) (c₃ : Nat.card H₃ = p) (n₁₃ : H₁ ≠ H₃)
    (n₂₃ : H₂ ≠ H₃) :
    Disjoint (LinearMap.range (proj ρ U H₁) ⊔ LinearMap.range (proj ρ U H₂))
      (LinearMap.range (proj ρ U H₃)) := by
  rw [Submodule.disjoint_def]
  intro x hx hx3
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  have h3a : proj ρ U H₃ a = 0 := by
    have := proj_apply_of_mem_range hpF ρ hU h₁ c₁ ha
    have h0 := proj_mul_proj_of_ne hpF ρ hU hcomm h₃ h₁ c₃ c₁ n₁₃.symm
    rw [← this, ← Module.End.mul_apply, h0]
    rfl
  have h3b : proj ρ U H₃ b = 0 := by
    have := proj_apply_of_mem_range hpF ρ hU h₂ c₂ hb
    have h0 := proj_mul_proj_of_ne hpF ρ hU hcomm h₃ h₂ c₃ c₂ n₂₃.symm
    rw [← this, ← Module.End.mul_apply, h0]
    rfl
  have := proj_apply_of_mem_range hpF ρ hU h₃ c₃ hx3
  rw [map_add, h3a, h3b, add_zero] at this
  rw [← this]

end Independence

section Surjectivity

@[expose] def fixer (ρ : K →* Module.End F V) (x : V) : Subgroup K where
  carrier := {g | ρ g x = x}
  mul_mem' := fun {a b} ha hb => by
    change ρ (a * b) x = x
    rw [map_mul, Module.End.mul_apply]
    change ρ a x = x at ha
    change ρ b x = x at hb
    rw [hb, ha]
  one_mem' := by
    change ρ 1 x = x
    rw [map_one]
    rfl
  inv_mem' := fun {a} ha => by
    change ρ a⁻¹ x = x
    change ρ a x = x at ha
    calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha]
      _ = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

omit [Fintype K] in
theorem mem_fixer {ρ : K →* Module.End F V} {x : V} {g : K} : g ∈ fixer ρ x ↔ ρ g x = x := Iff.rfl

variable {H₁ H₂ : Subgroup K} [FiniteDimensional F V]

theorem eq_zpowers_of_card_eq_prime' {H : Subgroup K} (hc : Nat.card H = p) {h : K} (hh : h ∈ H)
    (h1 : h ≠ 1) : H = Subgroup.zpowers h := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hh) ?_
  have hdvd : orderOf h ∣ p := hc ▸ Subgroup.orderOf_dvd_natCard H hh
  have : orderOf h = p :=
    (Nat.dvd_prime hp.out).1 hdvd |>.resolve_left (fun h1' => h1 (orderOf_eq_one_iff.mp h1'))
  rw [hc, Nat.card_zpowers, this]

end Surjectivity

section TauBound

variable [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem mem_range_of_commute {f : Module.End F V} {π : Module.End F V} (h : f * π = π * f)
    {x : V} (hx : x ∈ LinearMap.range π) : f x ∈ LinearMap.range π := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨f y, ?_⟩
  rw [← Module.End.mul_apply, ← h, Module.End.mul_apply]

include hpF in
theorem two_le_finrank_range_proj (hp2 : p ≠ 2) (hU : Nat.card U = p ^ 2)
    (hexp : ∀ u ∈ U, u ^ p = 1) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    {τ : K} (hτ : τ ∈ normalizer (U : Set K)) (hτinv : ∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹)
    {H : Subgroup K} (hH : H ≤ U) (hHc : Nat.card H = p)
    (hne : LinearMap.range (proj ρ U H) ≠ ⊥) :
    2 ≤ Module.finrank F (LinearMap.range (proj ρ U H)) := by
  by_contra hlt
  push Not at hlt
  set W := LinearMap.range (proj ρ U H) with hW
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < Module.finrank F W := Module.finrank_pos
  have hrk : Module.finrank F W = 1 := by omega
  obtain ⟨u₀, hu₀U, hu₀H⟩ : ∃ u ∈ U, u ∉ H := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ H := hcon
    have := Subgroup.card_le_of_le hle
    rw [hU, hHc] at this
    have hp1 := hp.out.one_lt
    nlinarith
  have hu₀1 : u₀ ≠ 1 := fun h => hu₀H (h ▸ H.one_mem)
  have hu₀o : orderOf u₀ = p := by
    have : orderOf u₀ ∣ p := orderOf_dvd_of_pow_eq_one (hexp u₀ hu₀U)
    exact (Nat.dvd_prime hp.out).1 this |>.resolve_left
      (fun h1' => hu₀1 (orderOf_eq_one_iff.mp h1'))
  have hL : Nat.card (Subgroup.zpowers u₀) = p := by rw [Nat.card_zpowers, hu₀o]
  have hLU : Subgroup.zpowers u₀ ≤ U := Subgroup.zpowers_le.mpr hu₀U
  have hHL : H ≠ Subgroup.zpowers u₀ := fun h => hu₀H (h ▸ Subgroup.mem_zpowers u₀)
  have hsup := sup_eq_of_card_prime_ne hU hH hLU hHc hL hHL
  have hstabu : ∀ x ∈ W, ρ u₀ x ∈ W := fun x hx =>
    mem_range_of_commute (proj_comm_of_commute (ρ := ρ) hH (g := u₀)
      (fun u hu => hcomm u₀ hu₀U u hu)) hx
  have hHτ : H.map (MulAut.conj τ).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      have : τ * h * τ⁻¹ = h⁻¹ := hτinv h (hH hh)
      show τ * h * τ⁻¹ ∈ H
      rw [this]
      exact H.inv_mem hh
    · rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective]
  have hstabτ : ∀ x ∈ W, ρ τ x ∈ W := by
    intro x hx
    have := mul_proj_conj (ρ := ρ) (U := U) (H := H) hτ
    rw [hHτ] at this
    exact mem_range_of_commute this hx
  obtain ⟨ζ, hζ, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hrk
    ((ρ u₀).restrict hstabu : W →ₗ[F] W)
  obtain ⟨μ, hμ, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hrk
    ((ρ τ).restrict hstabτ : W →ₗ[F] W)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hwu : ρ u₀ w = ζ • w := by
    have := congrArg (fun T : W →ₗ[F] W => (T ⟨w, hwW⟩ : V)) hζ
    simpa using this
  have hwτ : ρ τ w = μ • w := by
    have := congrArg (fun T : W →ₗ[F] W => (T ⟨w, hwW⟩ : V)) hμ
    simpa using this
  have hinvK : ∀ g : K, ρ g⁻¹ (ρ g w) = w := fun g => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hζ0 : ζ ≠ 0 := by
    intro h0
    have := hinvK u₀
    rw [hwu, h0, zero_smul, map_zero] at this
    exact hw0 this.symm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have := hinvK τ
    rw [hwτ, h0, zero_smul, map_zero] at this
    exact hw0 this.symm
  have hwuinv : ρ u₀⁻¹ w = ζ⁻¹ • w := by
    have h1 := hinvK u₀
    rw [hwu, map_smul] at h1
    have h2 : ζ⁻¹ • (ζ • ρ u₀⁻¹ w) = ζ⁻¹ • w := by rw [h1]
    rwa [smul_smul, inv_mul_cancel₀ hζ0, one_smul] at h2
  have hrel : ρ τ (ρ u₀ w) = ρ u₀⁻¹ (ρ τ w) := by
    have h1 : τ * u₀ = u₀⁻¹ * τ := by
      have := hτinv u₀ hu₀U
      calc τ * u₀ = τ * u₀ * τ⁻¹ * τ := by group
        _ = u₀⁻¹ * τ := by rw [this]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h1]
  rw [hwu, hwτ, map_smul, hwτ, map_smul, hwuinv] at hrel
  have hrel2 : (ζ * μ) • w = (μ * ζ⁻¹) • w := by
    rw [mul_smul, mul_smul]
    simpa [smul_comm ζ μ w] using hrel
  have hrel3 : ζ * μ = μ * ζ⁻¹ := by
    have := smul_left_injective F hw0 hrel2
    exact this
  have hζsq : ζ ^ 2 = 1 := by
    have : ζ * μ = ζ⁻¹ * μ := by rw [hrel3, mul_comm μ]
    have h2 := mul_right_cancel₀ hμ0 this
    field_simp at h2
    simpa [sq] using h2
  have hpow : ∀ n : ℕ, ((ρ u₀) ^ n) w = (ζ ^ n) • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hwu, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hζp : ζ ^ p = 1 := by
    have h1 : (ρ u₀) ^ p = 1 := by rw [← map_pow, hexp u₀ hu₀U, map_one]
    have h2 : (ζ ^ p) • w = (1 : F) • w := by
      rw [← hpow p, h1, one_smul]
      rfl
    exact smul_left_injective F hw0 h2
  have hζ1 : ζ = 1 := by
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
    have : ζ ^ p = ζ := by
      rw [hk, pow_succ, pow_mul, hζsq, one_pow, one_mul]
    rw [← this]
    exact hζp
  have hfixu : ρ u₀ w = w := by rw [hwu, hζ1, one_smul]
  have hfixH : ∀ h ∈ H, ρ h w = w := fun h hh =>
    fixed_of_mem_range_proj hpF ρ hH hHc hwW h hh
  have hfixU : ∀ u ∈ U, ρ u w = w := by
    intro u hu
    have hle : U ≤ fixer ρ w := by
      rw [← hsup]
      exact sup_le (fun h hh => mem_fixer.mpr (hfixH h hh))
        (Subgroup.zpowers_le.mpr (mem_fixer.mpr hfixu))
    exact mem_fixer.mp (hle hu)
  have h1 := avg_apply_of_fixed ρ (card_cast_ne_zero_plane hpF hU) hfixU
  have h2 := avg_apply_of_fixed ρ (card_cast_ne_zero_of_eq hpF hHc) hfixH
  have h3 := proj_apply_of_mem_range hpF ρ hU hH hHc hwW
  rw [proj_def, LinearMap.sub_apply, h1, h2, sub_self] at h3
  exact hw0 h3.symm

end TauBound

section LineSum

open Classical in
@[expose] noncomputable def nz (S : Subgroup K) : Finset K := (Finset.univ.filter (· ∈ S)).erase 1

theorem mem_nz {S : Subgroup K} {s : K} : s ∈ nz S ↔ s ≠ 1 ∧ s ∈ S := by
  classical
  unfold nz
  rw [Finset.mem_erase, mem_filter_iff]

theorem card_nz (S : Subgroup K) : (nz S).card = Nat.card S - 1 := by
  classical
  unfold nz
  rw [Finset.card_erase_of_mem ((mem_filter_iff S 1).2 S.one_mem), card_filter_eq]

theorem sumOver_eq_one_add (ρ : K →* Module.End F V) (S : Subgroup K) :
    sumOver ρ S = 1 + ∑ s ∈ nz S, ρ s := by
  classical
  unfold sumOver nz
  rw [← Finset.add_sum_erase _ _ ((mem_filter_iff S 1).2 S.one_mem), map_one]

open Classical in
@[expose] noncomputable def lines (U : Subgroup K) (p : ℕ) : Finset (Subgroup K) :=
  Finset.univ.filter (fun H => H ≤ U ∧ Nat.card H = p)

omit hp in
theorem mem_lines {H : Subgroup K} : H ∈ lines U p ↔ H ≤ U ∧ Nat.card H = p := by
  unfold lines
  simp

theorem zpowers_mem_lines (hexp : ∀ u ∈ U, u ^ p = 1) {u : K} (hu : u ∈ U) (h1 : u ≠ 1) :
    Subgroup.zpowers u ∈ lines U p := by
  rw [mem_lines]
  refine ⟨Subgroup.zpowers_le.mpr hu, ?_⟩
  have hdvd : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one (hexp u hu)
  have : orderOf u = p := (Nat.dvd_prime hp.out).1 hdvd |>.resolve_left
    (fun h1' => h1 (orderOf_eq_one_iff.mp h1'))
  rw [Nat.card_zpowers, this]

theorem sum_lines_nz {M : Type*} [AddCommMonoid M] (hexp : ∀ u ∈ U, u ^ p = 1) (f : K → M) :
    ∑ H ∈ lines U p, ∑ h ∈ nz H, f h = ∑ u ∈ nz U, f u := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := nz U) (t := lines U p)
    (g := fun u => Subgroup.zpowers u) (fun u hu => ?_) f]
  · refine Finset.sum_congr rfl fun H hH => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext h
    rw [Finset.mem_filter, mem_nz, mem_nz]
    obtain ⟨hHU, hHc⟩ := mem_lines.1 hH
    constructor
    · rintro ⟨h1, hh⟩
      exact ⟨⟨h1, hHU hh⟩, (eq_zpowers_of_card_eq_prime' hHc hh h1).symm⟩
    · rintro ⟨⟨h1, -⟩, hz⟩
      exact ⟨h1, hz ▸ Subgroup.mem_zpowers h⟩
  · rw [mem_nz] at hu
    exact zpowers_mem_lines hexp hu.2 hu.1

theorem card_lines (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1) :
    (lines U p).card = p + 1 := by
  have h := sum_lines_nz (U := U) hexp (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have h2 : ∀ H ∈ lines U p, (nz H).card = p - 1 := fun H hH => by
    rw [card_nz, (mem_lines.1 hH).2]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, card_nz, hU, smul_eq_mul] at h
  have hp1 := hp.out.one_lt
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have h3 : (lines U (m + 2)).card * (m + 1) = (m + 3) * (m + 1) := by
    rw [show m + 2 - 1 = m + 1 by omega] at h
    rw [h]
    have : (m + 2) ^ 2 = (m + 3) * (m + 1) + 1 := by ring
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) h3

variable (ρ : K →* Module.End F V)

include hpF in
theorem sum_avg_lines (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1) :
    ∑ H ∈ lines U p, avg ρ H = 1 + (p : F) • avg ρ U := by
  have h1 : ∀ H ∈ lines U p, avg ρ H = (p : F)⁻¹ • (1 + ∑ h ∈ nz H, ρ h) := fun H hH => by
    rw [avg_def, (mem_lines.1 hH).2, sumOver_eq_one_add]
  rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const,
    sum_lines_nz hexp (fun h => ρ h), card_lines hU hexp]
  have h2 : sumOver ρ U = (p : F) ^ 2 • avg ρ U := by
    rw [avg_def, hU, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hpF), one_smul]
  have h3 : ∑ u ∈ nz U, ρ u = (p : F) ^ 2 • avg ρ U - 1 := by
    rw [← h2, sumOver_eq_one_add]
    abel
  rw [h3, nsmul_eq_cast_smul]
  push_cast
  match_scalars
  · field_simp
    ring
  · field_simp

include hpF in
theorem sum_proj_lines (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1) :
    ∑ H ∈ lines U p, proj ρ U H = 1 - avg ρ U := by
  simp only [proj_def, Finset.sum_sub_distrib, sum_avg_lines hpF ρ hU hexp, Finset.sum_const,
    card_lines hU hexp, nsmul_eq_cast_smul]
  push_cast
  match_scalars <;> ring

include hpF in
theorem exists_line_proj_ne_zero (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1)
    (hnt : ∃ u ∈ U, ρ u ≠ 1) : ∃ H ∈ lines U p, proj ρ U H ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := sum_proj_lines hpF ρ hU hexp
  rw [Finset.sum_eq_zero hcon] at h0
  have h1 : avg ρ U = 1 := (sub_eq_zero.mp h0.symm).symm
  obtain ⟨u, hu, hu1⟩ := hnt
  apply hu1
  calc ρ u = ρ u * avg ρ U := by rw [h1, mul_one]
    _ = 1 := by rw [mul_avg_of_mem ρ hu, h1]

end LineSum

section ThreeLines

include hpF in
theorem avg_mul_proj_of_ne (hU : Nat.card U = p ^ 2) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    {H H' : Subgroup K} (hH : H ≤ U) (hH' : H' ≤ U) (hHc : Nat.card H = p)
    (hHc' : Nat.card H' = p) (hne : H' ≠ H) : avg ρ H' * proj ρ U H = 0 := by
  have hsup := sup_eq_of_card_prime_ne hU hH' hH hHc' hHc hne
  have h0 := avg_mul_avg_lines ρ hsup (fun h hh h' hh' => hcomm h (hH' hh) h' (hH hh'))
    (card_cast_ne_zero_of_eq hpF hHc') (card_cast_ne_zero_of_eq hpF hHc)
    (card_cast_ne_zero_plane hpF hU)
  have h1 := avg_line_mul_avg_plane hpF ρ hH' hHc'
  rw [proj_def, mul_sub, h0, h1, sub_self]

omit hp in
theorem proj_conj_ne_zero {σ : K} (hσ : σ ∈ normalizer (U : Set K)) {H : Subgroup K}
    (hne : proj ρ U H ≠ 0) : proj ρ U (H.map (MulAut.conj σ).toMonoidHom) ≠ 0 := by
  intro h0
  have h := mul_proj_conj (ρ := ρ) (U := U) (H := H) hσ
  rw [h0, zero_mul] at h
  apply hne
  have : proj ρ U H = ρ σ⁻¹ * (ρ σ * proj ρ U H) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [this, h, mul_zero]

omit hp in
theorem exists_three_lines {σ : K} (hσ : σ ∈ normalizer (U : Set K))
    (hσ1 : ∀ H : Subgroup K, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * h * σ⁻¹ ∉ H)
    (hσ2 : ∀ H : Subgroup K, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H)
    {H₀ : Subgroup K} (hH₀ : H₀ ≤ U) (hc₀ : Nat.card H₀ = p) (hne : proj ρ U H₀ ≠ 0) :
    ∃ H₁ H₂ : Subgroup K, H₁ ≤ U ∧ H₂ ≤ U ∧ Nat.card H₁ = p ∧ Nat.card H₂ = p ∧
      H₀ ≠ H₁ ∧ H₀ ≠ H₂ ∧ H₁ ≠ H₂ ∧ proj ρ U H₁ ≠ 0 ∧ proj ρ U H₂ ≠ 0 := by
  set c : K →* K := (MulAut.conj σ).toMonoidHom with hc
  have hcU : ∀ H : Subgroup K, H ≤ U → H.map c ≤ U := by
    rintro H hH _ ⟨h, hh, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hσ h).mp (hH hh)
  have hcc : ∀ H : Subgroup K, Nat.card (H.map c) = Nat.card H := fun H =>
    Subgroup.card_map_of_injective (MulAut.conj σ).injective
  have hmem : ∀ (H : Subgroup K) (h : K), h ∈ H → σ * h * σ⁻¹ ∈ H.map c := fun H h hh =>
    ⟨h, hh, rfl⟩
  have h1U := hcU H₀ hH₀
  have h1c : Nat.card (H₀.map c) = p := (hcc H₀).trans hc₀
  refine ⟨H₀.map c, (H₀.map c).map c, h1U, hcU _ h1U, h1c, (hcc _).trans h1c, ?_, ?_, ?_,
    proj_conj_ne_zero hσ hne, proj_conj_ne_zero hσ (proj_conj_ne_zero hσ hne)⟩
  · intro h
    obtain ⟨x, hx, hnot⟩ := hσ1 H₀ hH₀ hc₀
    apply hnot
    rw [h]
    exact hmem H₀ x hx
  · intro h
    obtain ⟨x, hx, hnot⟩ := hσ2 H₀ hH₀ hc₀
    apply hnot
    have := hmem (H₀.map c) _ (hmem H₀ x hx)
    rwa [← h] at this
  · intro h
    obtain ⟨x, hx, hnot⟩ := hσ1 (H₀.map c) h1U h1c
    apply hnot
    rw [h]
    exact hmem _ x hx

end ThreeLines

section Bilinear

variable {W : Type*} [AddCommGroup W] [Module F W]

open Classical in
theorem sumOver_apply (ρ : K →* Module.End F V) (S : Subgroup K) (v : V) :
    sumOver ρ S v = ∑ s ∈ Finset.univ.filter (· ∈ S), ρ s v := by
  unfold sumOver
  rw [LinearMap.sum_apply]

theorem sumOver_eq_card_smul_avg (ρ : K →* Module.End F V) (S : Subgroup K)
    (hS : ((Nat.card S : ℕ) : F) ≠ 0) : sumOver ρ S = ((Nat.card S : ℕ) : F) • avg ρ S := by
  rw [avg_def, smul_smul, mul_inv_cancel₀ hS, one_smul]

include hpF in
theorem bil_eq_zero_of_mem_range_proj (ρ : K →* Module.End F V) (β : V →ₗ[F] V →ₗ[F] W)
    (hinv : ∀ u ∈ U, ∀ v w, β (ρ u v) (ρ u w) = β v w) (hU : Nat.card U = p ^ 2)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {H H' : Subgroup K} (hH : H ≤ U) (hH' : H' ≤ U)
    (hHc : Nat.card H = p) (hHc' : Nat.card H' = p) (hne : H ≠ H') {v w : V}
    (hv : v ∈ LinearMap.range (proj ρ U H)) (hw : w ∈ LinearMap.range (proj ρ U H')) :
    β v w = 0 ∧ β w v = 0 := by
  classical
  have hwfix : ∀ h ∈ H', ρ h w = w := fun h hh =>
    fixed_of_mem_range_proj hpF ρ hH' hHc' hw h hh
  have havg : avg ρ H' v = 0 := by
    obtain ⟨x, rfl⟩ := hv
    have := avg_mul_proj_of_ne hpF (ρ := ρ) hU hcomm hH hH' hHc hHc' hne.symm
    exact congrArg (fun T : Module.End F V => T x) this
  have hsum : ∑ s ∈ Finset.univ.filter (· ∈ H'), ρ s v = 0 := by
    rw [← sumOver_apply, sumOver_eq_card_smul_avg ρ H' (card_cast_ne_zero_of_eq hpF hHc'),
      LinearMap.smul_apply, havg, smul_zero]
  have hcard : (Finset.univ.filter (· ∈ H')).card = p := by
    rw [card_filter_eq, hHc']
  constructor
  · have h1 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β (ρ s v) w = (p : F) • β v w := by
      have : ∀ s ∈ Finset.univ.filter (· ∈ H'), β (ρ s v) w = β v w := fun s hs => by
        have hs' := (mem_filter_iff H' s).1 hs
        rw [← hinv s (hH' hs') v w, hwfix s hs']
      rw [Finset.sum_congr rfl this, Finset.sum_const, hcard]
      exact (Nat.cast_smul_eq_nsmul F p _).symm
    have h2 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β (ρ s v) w = 0 := by
      rw [← LinearMap.sum_apply, ← map_sum, hsum, map_zero, LinearMap.zero_apply]
    rw [h2] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hpF
  · have h1 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β w (ρ s v) = (p : F) • β w v := by
      have : ∀ s ∈ Finset.univ.filter (· ∈ H'), β w (ρ s v) = β w v := fun s hs => by
        have hs' := (mem_filter_iff H' s).1 hs
        rw [← hinv s (hH' hs') w v, hwfix s hs']
      rw [Finset.sum_congr rfl this, Finset.sum_const, hcard]
      exact (Nat.cast_smul_eq_nsmul F p _).symm
    have h2 : ∑ s ∈ Finset.univ.filter (· ∈ H'), β w (ρ s v) = 0 := by
      rw [← map_sum, hsum, map_zero]
    rw [h2] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hpF

include hpF in
theorem exists_isotropic_three (ρ : K →* Module.End F V) (β : V →ₗ[F] V →ₗ[F] W)
    (hinv : ∀ u ∈ U, ∀ v w, β (ρ u v) (ρ u w) = β v w) (halt : ∀ v, β v v = 0)
    (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {σ : K} (hσ : σ ∈ normalizer (U : Set K))
    (hσ1 : ∀ H : Subgroup K, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * h * σ⁻¹ ∉ H)
    (hσ2 : ∀ H : Subgroup K, H ≤ U → Nat.card H = p →
      ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H)
    (hnt : ∃ u ∈ U, ρ u ≠ 1) :
    ∃ S : Submodule F V, Module.finrank F S = 3 ∧ ∀ s ∈ S, ∀ s' ∈ S, β s s' = 0 := by
  obtain ⟨H₀, hH₀, hne₀⟩ := exists_line_proj_ne_zero hpF ρ hU hexp hnt
  obtain ⟨hH₀U, hH₀c⟩ := mem_lines.1 hH₀
  obtain ⟨H₁, H₂, h1U, h2U, h1c, h2c, n01, n02, n12, hne₁, hne₂⟩ :=
    exists_three_lines (ρ := ρ) hσ hσ1 hσ2 hH₀U hH₀c hne₀
  have hW : ∀ {H : Subgroup K}, proj ρ U H ≠ 0 → LinearMap.range (proj ρ U H) ≠ ⊥ :=
    fun h => by rwa [Ne, LinearMap.range_eq_bot]
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hW hne₀)
  obtain ⟨v₁, hv₁, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hW hne₁)
  obtain ⟨v₂, hv₂, hv₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hW hne₂)
  have d01 := disjoint_range_proj hpF (ρ := ρ) hU hcomm hH₀U h1U hH₀c h1c n01
  have d012 := disjoint_sup_range_proj hpF (ρ := ρ) hU hcomm hH₀U h1U h2U hH₀c h1c h2c n02 n12
  have o01 := bil_eq_zero_of_mem_range_proj hpF ρ β hinv hU hcomm hH₀U h1U hH₀c h1c n01 hv₀ hv₁
  have o02 := bil_eq_zero_of_mem_range_proj hpF ρ β hinv hU hcomm hH₀U h2U hH₀c h2c n02 hv₀ hv₂
  have o12 := bil_eq_zero_of_mem_range_proj hpF ρ β hinv hU hcomm h1U h2U h1c h2c n12 hv₁ hv₂
  have hli : LinearIndependent F ![v₀, v₁, v₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have h2 : g 2 • v₂ = 0 := by
      refine (Submodule.disjoint_def.mp d012) _ ?_ ?_
      · have : g 2 • v₂ = -(g 0 • v₀ + g 1 • v₁) := eq_neg_of_add_eq_zero_right hg
        rw [this]
        exact Submodule.neg_mem _ (Submodule.add_mem_sup (Submodule.smul_mem _ _ hv₀)
          (Submodule.smul_mem _ _ hv₁))
      · exact Submodule.smul_mem _ _ hv₂
    have hg2 : g 2 = 0 := (smul_eq_zero.mp h2).resolve_right hv₂0
    rw [hg2, zero_smul, add_zero] at hg
    have h1 : g 1 • v₁ = 0 := by
      refine (Submodule.disjoint_def.mp d01.symm) _ ?_ ?_
      · exact Submodule.smul_mem _ _ hv₁
      · have : g 1 • v₁ = -(g 0 • v₀) := eq_neg_of_add_eq_zero_right hg
        rw [this]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hv₀)
    have hg1 : g 1 = 0 := (smul_eq_zero.mp h1).resolve_right hv₁0
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hv₀0
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  refine ⟨Submodule.span F (Set.range ![v₀, v₁, v₂]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · have key : ∀ i j : Fin 3, β (![v₀, v₁, v₂] i) (![v₀, v₁, v₂] j) = 0 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [halt, o01.1, o01.2, o02.1, o02.2, o12.1, o12.2]
    intro s hs s' hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hs' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact key i j
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, hy, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

end Bilinear

include hpF in
theorem four_le_finrank [FiniteDimensional F V] (ρ : K →* Module.End F V) (hp2 : p ≠ 2)
    (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {τ σ : K} (hτ : τ ∈ normalizer (U : Set K))
    (hτinv : ∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹) (hσ : σ ∈ normalizer (U : Set K))
    (hσ1 : ∀ H : Subgroup K, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * h * σ⁻¹ ∉ H)
    (hσ2 : ∀ H : Subgroup K, H ≤ U → Nat.card H = p →
      ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H)
    (hnt : ∃ u ∈ U, ρ u ≠ 1) : 4 ≤ Module.finrank F V := by
  obtain ⟨H₀, hH₀, hne₀⟩ := exists_line_proj_ne_zero hpF ρ hU hexp hnt
  obtain ⟨hH₀U, hH₀c⟩ := mem_lines.1 hH₀
  obtain ⟨H₁, H₂, h1U, h2U, h1c, h2c, n01, n02, n12, hne₁, hne₂⟩ :=
    exists_three_lines (ρ := ρ) hσ hσ1 hσ2 hH₀U hH₀c hne₀
  have hW : ∀ {H : Subgroup K}, proj ρ U H ≠ 0 → LinearMap.range (proj ρ U H) ≠ ⊥ :=
    fun h => by rwa [Ne, LinearMap.range_eq_bot]
  have b0 := two_le_finrank_range_proj hpF (ρ := ρ) hp2 hU hexp hcomm hτ hτinv hH₀U hH₀c (hW hne₀)
  have b1 := two_le_finrank_range_proj hpF (ρ := ρ) hp2 hU hexp hcomm hτ hτinv h1U h1c (hW hne₁)
  have d01 := disjoint_range_proj hpF (ρ := ρ) hU hcomm hH₀U h1U hH₀c h1c n01
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (proj ρ U H₀))
    (LinearMap.range (proj ρ U H₁))
  rw [disjoint_iff.mp d01, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_le (LinearMap.range (proj ρ U H₀) ⊔ LinearMap.range (proj ρ U H₁))
  omega

end Proj

end Lines

end CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModule
