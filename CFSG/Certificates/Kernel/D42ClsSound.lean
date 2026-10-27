module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.KC.D42Cls

open Finset

variable {G : Type*} [Group G] [DecidableEq G]

def conjs (S : Finset G) (x : G) : Finset G := S.image fun c => c * x * c⁻¹

def stabs (S : Finset G) (x : G) : Finset G := S.filter fun c => c * x * c⁻¹ = x

theorem mem_stabs {S : Finset G} {x c : G} : c ∈ stabs S x ↔ c ∈ S ∧ c * x * c⁻¹ = x :=
  Finset.mem_filter

theorem card_eq_conjs_mul (S : Finset G) (hS : ∀ a ∈ S, ∀ b ∈ S, a⁻¹ * b ∈ S)
    (hS' : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (x : G) :
    S.card = (conjs S x).card * (stabs S x).card := by
  rw [card_eq_sum_card_image (fun c => c * x * c⁻¹) S, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun y hy => ?_
  obtain ⟨c0, hc0, rfl⟩ := mem_image.mp hy
  refine card_bij (fun c _ => c0⁻¹ * c) (fun c hc => ?_) (fun a _ b _ h => mul_left_cancel h)
    (fun b hb => ?_)
  · simp only [mem_filter] at hc
    simp only [stabs, mem_filter]
    refine ⟨hS c0 hc0 c hc.1, ?_⟩
    calc c0⁻¹ * c * x * (c0⁻¹ * c)⁻¹ = c0⁻¹ * (c * x * c⁻¹) * c0 := by group
      _ = x := by rw [hc.2]; group
  · simp only [stabs, mem_filter] at hb
    refine ⟨c0 * b, ?_, by group⟩
    simp only [mem_filter]
    refine ⟨hS' c0 hc0 b hb.1, ?_⟩
    calc c0 * b * x * (c0 * b)⁻¹ = c0 * (b * x * b⁻¹) * c0⁻¹ := by group
      _ = c0 * x * c0⁻¹ := by rw [hb.2]

variable [Fintype G]

theorem mem_of_commute_of_sweep (k : G) (C : Finset G) (hC : ∀ a ∈ C, ∀ b ∈ C, a⁻¹ * b ∈ C)
    (hC' : ∀ a ∈ C, ∀ b ∈ C, a * b ∈ C) (hk : ∀ c ∈ C, c * k = k * c)
    {ι : Type*} (J : Finset ι) (d : ι → G) (s : ι → ℕ) (n : ℕ)
    (hstab : ∀ j ∈ J, (stabs C (d j * k * (d j)⁻¹)).card ≤ s j)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, ∀ c ∈ C, ∀ c' ∈ C,
      c * (d i * k * (d i)⁻¹) * c⁻¹ = c' * (d j * k * (d j)⁻¹) * c'⁻¹ → i = j)
    (hsum : n ≤ ∑ j ∈ J, C.card / s j) (hG : Fintype.card G = n * C.card) (hn : 0 < n)
    (x : G) (hx : x * k = k * x) : x ∈ C := by
  classical
  set r : ι → G := fun j => d j * k * (d j)⁻¹ with hr
  have hsub : J.biUnion (fun j => conjs C (r j)) ⊆ conjs univ k := by
    intro y hy
    obtain ⟨j, -, hj⟩ := mem_biUnion.mp hy
    obtain ⟨c, -, rfl⟩ := mem_image.mp hj
    exact mem_image.mpr ⟨c * d j, mem_univ _, by simp only [hr]; group⟩
  have hdis : (J : Set ι).PairwiseDisjoint fun j => conjs C (r j) := by
    intro i hi j hj hij
    refine disjoint_left.mpr fun y hyi hyj => hij ?_
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hyi
    obtain ⟨c', hc', h⟩ := mem_image.mp hyj
    exact hdisj i hi j hj c hc c' hc' h.symm
  have hcls : ∑ j ∈ J, (conjs C (r j)).card ≤ (conjs univ k).card := by
    rw [← card_biUnion hdis]
    exact card_le_card hsub
  have horb : ∀ j ∈ J, C.card / s j ≤ (conjs C (r j)).card := by
    intro j hj
    apply Nat.div_le_of_le_mul
    rw [card_eq_conjs_mul C hC hC' (r j), mul_comm]
    exact Nat.mul_le_mul_right _ (hstab j hj)
  have hn' : n ≤ (conjs univ k).card := hsum.trans ((sum_le_sum horb).trans hcls)
  have hGk := card_eq_conjs_mul (univ : Finset G) (fun _ _ _ _ => mem_univ _)
    (fun _ _ _ _ => mem_univ _) k
  rw [card_univ, hG] at hGk
  have hle : (stabs univ k).card ≤ C.card := by
    by_contra h
    push Not at h
    have h1 : n * C.card < n * (stabs univ k).card := Nat.mul_lt_mul_of_pos_left h hn
    have h2 : n * (stabs univ k).card ≤ (conjs univ k).card * (stabs univ k).card :=
      Nat.mul_le_mul_right _ hn'
    omega
  have hCs : C ⊆ stabs univ k := by
    intro c hc
    simp only [stabs, mem_filter, mem_univ, true_and]
    rw [hk c hc, mul_inv_cancel_right]
  have heq := eq_of_subset_of_card_le hCs hle
  have hxs : x ∈ stabs univ k := by
    simp only [stabs, mem_filter, mem_univ, true_and]
    rw [hx, mul_inv_cancel_right]
  rw [← heq] at hxs
  exact hxs

theorem exists_of_sweep (k : G) (C : Finset G) (hC : ∀ a ∈ C, ∀ b ∈ C, a⁻¹ * b ∈ C)
    (hC' : ∀ a ∈ C, ∀ b ∈ C, a * b ∈ C) (hk : ∀ c ∈ C, c * k = k * c)
    {ι : Type*} (J : Finset ι) (d : ι → G) (s : ι → ℕ) (n : ℕ)
    (hstab : ∀ j ∈ J, (stabs C (d j * k * (d j)⁻¹)).card ≤ s j)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, ∀ c ∈ C, ∀ c' ∈ C,
      c * (d i * k * (d i)⁻¹) * c⁻¹ = c' * (d j * k * (d j)⁻¹) * c'⁻¹ → i = j)
    (hsum : n ≤ ∑ j ∈ J, C.card / s j) (hG : Fintype.card G = n * C.card) (hn : 0 < n) (g : G) :
    ∃ j ∈ J, ∃ c ∈ C, g * k * g⁻¹ = c * (d j * k * (d j)⁻¹) * c⁻¹ := by
  classical
  have hcent := mem_of_commute_of_sweep k C hC hC' hk J d s n hstab hdisj hsum hG hn
  set r : ι → G := fun j => d j * k * (d j)⁻¹ with hr
  have hsub : J.biUnion (fun j => conjs C (r j)) ⊆ conjs univ k := by
    intro y hy
    obtain ⟨j, -, hj⟩ := mem_biUnion.mp hy
    obtain ⟨c, -, rfl⟩ := mem_image.mp hj
    exact mem_image.mpr ⟨c * d j, mem_univ _, by simp only [hr]; group⟩
  have hdis : (J : Set ι).PairwiseDisjoint fun j => conjs C (r j) := by
    intro i hi j hj hij
    refine disjoint_left.mpr fun y hyi hyj => hij ?_
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hyi
    obtain ⟨c', hc', h⟩ := mem_image.mp hyj
    exact hdisj i hi j hj c hc c' hc' h.symm
  have horb : ∀ j ∈ J, C.card / s j ≤ (conjs C (r j)).card := by
    intro j hj
    apply Nat.div_le_of_le_mul
    rw [card_eq_conjs_mul C hC hC' (r j), mul_comm]
    exact Nat.mul_le_mul_right _ (hstab j hj)
  have hU : n ≤ (J.biUnion fun j => conjs C (r j)).card := by
    rw [card_biUnion hdis]
    exact hsum.trans (sum_le_sum horb)
  have hst : stabs univ k = C := by
    ext c
    simp only [stabs, mem_filter, mem_univ, true_and]
    refine ⟨fun h => hcent c ?_, fun h => by rw [hk c h, mul_inv_cancel_right]⟩
    calc c * k = c * k * c⁻¹ * c := by group
      _ = k * c := by rw [h]
  have hGk := card_eq_conjs_mul (univ : Finset G) (fun _ _ _ _ => mem_univ _)
    (fun _ _ _ _ => mem_univ _) k
  rw [card_univ, hG, hst] at hGk
  have hpos : 0 < C.card := card_pos.mpr ⟨1, by
    obtain ⟨c, hc⟩ : C.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, card_empty, mul_zero] at hG
      exact Fintype.card_ne_zero hG
    have := hC c hc c hc
    rwa [inv_mul_cancel] at this⟩
  have hcls : (conjs univ k).card = n := (Nat.eq_of_mul_eq_mul_right hpos hGk).symm
  have heq := eq_of_subset_of_card_le hsub (hcls ▸ hU)
  have hy : g * k * g⁻¹ ∈ conjs univ k := mem_image.mpr ⟨g, mem_univ _, rfl⟩
  rw [← heq] at hy
  obtain ⟨j, hj, hy⟩ := mem_biUnion.mp hy
  obtain ⟨c, hc, h⟩ := mem_image.mp hy
  exact ⟨j, hj, c, hc, h.symm⟩

theorem overgroup_of_sweep (k : G) (C : Finset G) (hk : ∀ c ∈ C, c * k = k * c)
    (hcent : ∀ x, x * k = k * x → x ∈ C) {ι : Type*} (J : Finset ι) (d : ι → G)
    (hcov : ∀ g : G, ∃ j ∈ J, ∃ c ∈ C, g * k * g⁻¹ = c * (d j * k * (d j)⁻¹) * c⁻¹)
    (hgen : ∀ j ∈ J, d j * k * (d j)⁻¹ = k ∨ d j * k * (d j)⁻¹ = k * k ∨
      ∀ H : Subgroup G, (∀ c ∈ C, c ∈ H) → d j ∈ H → H = ⊤)
    (H : Subgroup G) (hH : ∀ x, x * k = k * x → x ∈ H) :
    (∀ h ∈ H, h * k * h⁻¹ = k ∨ h * k * h⁻¹ = k * k) ∨ H = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨h, hh, h1, h2⟩, htop⟩ := hcon
  obtain ⟨j, hj, c, hc, hjc⟩ := hcov h
  have hCH : ∀ c ∈ C, c ∈ H := fun c hc => hH c (hk c hc)
  rcases hgen j hj with hr | hr | hr
  · apply h1
    rw [hjc, hr, hk c hc, mul_inv_cancel_right]
  · apply h2
    rw [hjc, hr]
    calc c * (k * k) * c⁻¹ = c * k * k * c⁻¹ := by group
      _ = k * c * k * c⁻¹ := by rw [hk c hc]
      _ = k * (c * k) * c⁻¹ := by group
      _ = k * (k * c) * c⁻¹ := by rw [hk c hc]
      _ = k * k := by group
  · apply htop
    refine hr H hCH ?_
    have hz : (d j)⁻¹ * c⁻¹ * h * k = k * ((d j)⁻¹ * c⁻¹ * h) := by
      have e : h * k = c * (d j * k * (d j)⁻¹) * c⁻¹ * h := by rw [← hjc]; group
      calc (d j)⁻¹ * c⁻¹ * h * k = (d j)⁻¹ * c⁻¹ * (h * k) := by group
        _ = (d j)⁻¹ * c⁻¹ * (c * (d j * k * (d j)⁻¹) * c⁻¹ * h) := by rw [e]
        _ = k * ((d j)⁻¹ * c⁻¹ * h) := by group
    have hzH := hH _ hz
    have hcH := hCH c hc
    have : d j = c⁻¹ * h * ((d j)⁻¹ * c⁻¹ * h)⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hcH) hh) (H.inv_mem hzH)

end CFSG.KC.D42Cls

end
