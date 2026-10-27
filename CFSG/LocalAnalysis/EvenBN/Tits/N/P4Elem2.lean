module

public import Mathlib
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Elem

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {Γ : Type*} [Group Γ]

namespace IsF20

variable {U : Subgroup Γ} {x v : Γ}

theorem fpf_zpow (h : IsF20 U x v) (k : ℤ) (hk : k % 5 ≠ 0) (u : Γ) (hu : u ∈ U)
    (hfix : x ^ k * u * (x ^ k)⁻¹ = u) : u = 1 := by
  have hx5 : x ^ (5 : ℤ) = 1 := by exact_mod_cast h.x5
  obtain ⟨m, hm⟩ : ∃ m : ℤ, k * m % 5 = 1 := by
    have : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact ⟨1, by omega⟩
    · exact ⟨3, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨4, by omega⟩
  have hxm : (x ^ k) ^ m = x := by
    rw [← zpow_mul]
    have e : k * m = 1 + 5 * (k * m / 5) := by omega
    rw [e, zpow_add, zpow_mul, hx5, one_zpow, mul_one, zpow_one]
  have hcomm : x ^ k * u = u * x ^ k := by
    calc x ^ k * u = (x ^ k * u * (x ^ k)⁻¹) * x ^ k := by group
      _ = u * x ^ k := by rw [hfix]
  have hmem : x ^ k ∈ centralizer ({u} : Set Γ) := Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have hmem2 : (x ^ k) ^ m ∈ centralizer ({u} : Set Γ) := Subgroup.zpow_mem _ hmem m
  rw [hxm] at hmem2
  have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.1 hmem2)
  apply h.fpf u hu
  calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [hxu]
    _ = u := by group

theorem sq_conj_zpow (h : IsF20 U x v) (k : ℤ) : v ^ 2 * x ^ k * (v ^ 2)⁻¹ = x ^ (-k) := by
  have := conj_zpow (i := k) (a := v ^ 2) (b := x)
  rw [← this, h.sq_conj, inv_zpow']

@[expose] def gInv (x v : Γ) (i : ℤ) : Γ := x ^ i * v ^ 2 * (x ^ i)⁻¹

theorem gInv_norm (h : IsF20 U x v) (i : ℤ) : gInv x v i ∈ normalizer (U : Set Γ) := by
  unfold gInv
  exact mul_mem (mul_mem (zpow_mem h.x_norm i) h.sq_norm) (inv_mem (zpow_mem h.x_norm i))

theorem gInv_mul_self (h : IsF20 U x v) (i : ℤ) : gInv x v i * gInv x v i = 1 := by
  have hww := h.sq_mul_self
  unfold gInv
  calc x ^ i * v ^ 2 * (x ^ i)⁻¹ * (x ^ i * v ^ 2 * (x ^ i)⁻¹)
      = x ^ i * (v ^ 2 * v ^ 2) * (x ^ i)⁻¹ := by group
    _ = 1 := by rw [hww]; group

theorem gInv_conj (h : IsF20 U x v) (i : ℤ) : gInv x v i * x * (gInv x v i)⁻¹ = x⁻¹ := by
  have h1 := h.sq_conj
  unfold gInv
  calc x ^ i * v ^ 2 * (x ^ i)⁻¹ * x * (x ^ i * v ^ 2 * (x ^ i)⁻¹)⁻¹
      = x ^ i * (v ^ 2 * x * (v ^ 2)⁻¹) * (x ^ i)⁻¹ := by group
    _ = x⁻¹ := by rw [h1]; group

theorem card_centralizer_gInv (h : IsF20 U x v) (i : ℤ) :
    Nat.card ↥(U ⊓ centralizer ({gInv x v i} : Set Γ)) = 4 :=
  card_centralizer_inverting h.comm h.sq h.card h.x_norm (h.gInv_norm i) (h.gInv_mul_self i)
    (h.gInv_conj i) h.x5 h.fpf

theorem gInv_mul_gInv (h : IsF20 U x v) (i j : ℤ) : gInv x v i * gInv x v j = x ^ (2 * i - 2 * j) := by
  have h1 := h.sq_conj_zpow (j - i)
  have hww := h.sq_mul_self
  have hwi : (v ^ 2)⁻¹ = v ^ 2 := inv_eq_of_mul_eq_one_right hww
  unfold gInv
  rw [hwi] at h1
  have e : x ^ i * v ^ 2 * (x ^ i)⁻¹ * (x ^ j * v ^ 2 * (x ^ j)⁻¹) =
      x ^ i * (v ^ 2 * x ^ (j - i) * v ^ 2) * (x ^ j)⁻¹ := by group
  rw [e, h1]
  group

theorem eq_one_of_commute_gInv (h : IsF20 U x v) {i j : ℤ} (hi : 0 ≤ i) (hi5 : i < 5) (hj : 0 ≤ j)
    (hj5 : j < 5) (hij : i ≠ j) (u : Γ) (hu : u ∈ U) (hui : gInv x v i * u = u * gInv x v i)
    (huj : gInv x v j * u = u * gInv x v j) : u = 1 := by
  have hk : (2 * i - 2 * j) % 5 ≠ 0 := by omega
  apply h.fpf_zpow (2 * i - 2 * j) hk u hu
  rw [← h.gInv_mul_gInv i j]
  have hc : gInv x v i * gInv x v j * u = u * (gInv x v i * gInv x v j) := by
    calc gInv x v i * gInv x v j * u = gInv x v i * (gInv x v j * u) := by group
      _ = gInv x v i * (u * gInv x v j) := by rw [huj]
      _ = (gInv x v i * u) * gInv x v j := by group
      _ = (u * gInv x v i) * gInv x v j := by rw [hui]
      _ = u * (gInv x v i * gInv x v j) := by group
  calc gInv x v i * gInv x v j * u * (gInv x v i * gInv x v j)⁻¹
      = (u * (gInv x v i * gInv x v j)) * (gInv x v i * gInv x v j)⁻¹ := by rw [hc]
    _ = u := by group

theorem exists_centralizer_gInv (h : IsF20 U x v) (u : Γ) (hu : u ∈ U) :
    ∃ i : Fin 5, gInv x v (i : ℕ) * u = u * gInv x v (i : ℕ) := by
  classical
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  haveI : Fintype U := Fintype.ofFinite U
  let K : Fin 5 → Subgroup U := fun i =>
    (centralizer ({gInv x v ((i : ℕ) : ℤ)} : Set Γ)).subgroupOf U
  have hKcard : ∀ i, Nat.card (K i) = 4 := fun i => by
    show Nat.card ↥((centralizer ({gInv x v ((i : ℕ) : ℤ)} : Set Γ)).subgroupOf U) = 4
    rw [← card_inf_eq_card_subgroupOf, inf_comm]
    exact h.card_centralizer_gInv _
  have hKmem : ∀ i (w : U), w ∈ K i ↔ gInv x v ((i : ℕ) : ℤ) * w = w * gInv x v ((i : ℕ) : ℤ) := by
    intro i w
    show (w : Γ) ∈ centralizer ({gInv x v ((i : ℕ) : ℤ)} : Set Γ) ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hdisj : ∀ i j : Fin 5, i ≠ j → ∀ w : U, w ∈ K i → w ∈ K j → w = 1 := by
    intro i j hij w hwi hwj
    have := h.eq_one_of_commute_gInv (i := ((i : ℕ) : ℤ)) (j := ((j : ℕ) : ℤ)) (by omega) (by omega)
      (by omega) (by omega) (by intro e; apply hij; apply Fin.ext; exact_mod_cast e) w w.2
      ((hKmem i w).1 hwi) ((hKmem j w).1 hwj)
    exact Subtype.ext this
  let T : Fin 5 → Finset U := fun i => Finset.univ.filter (fun w : U => w ∈ K i ∧ w ≠ 1)
  have hTcard : ∀ i, (T i).card = 3 := by
    intro i
    have h1 : (Finset.univ.filter (fun w : U => w ∈ K i)).card = 4 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hKcard i
    have h2 : T i = (Finset.univ.filter (fun w : U => w ∈ K i)).erase 1 := by
      ext w
      simp [T, and_comm]
    rw [h2, Finset.card_erase_of_mem (by simp [Subgroup.one_mem]), h1]
  have hTdisj : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)), i ≠ j →
      Disjoint (T i) (T j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hwi hwj
    exact hwi.2 (hdisj i j hij w hwi.1 hwj.1)
  have hbU : (Finset.univ.biUnion T).card = 15 := by
    rw [Finset.card_biUnion hTdisj]
    simp [hTcard]
  by_contra hnot
  push Not at hnot
  let u' : U := ⟨u, hu⟩
  have hu1 : u' ≠ 1 := by
    intro e
    have := hnot ⟨0, by norm_num⟩
    apply this
    have e' : u = 1 := congrArg Subtype.val e
    rw [e']
    simp
  have hnotin : u' ∉ Finset.univ.biUnion T := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hnot i ((hKmem i u').1 hi.1)
  have h1notin : (1 : U) ∉ Finset.univ.biUnion T := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.2 rfl
  have hne : u' ≠ (1 : U) := hu1
  have hcard17 : (insert u' (insert (1 : U) (Finset.univ.biUnion T))).card = 17 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem h1notin, hbU]
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hnotin⟩
  have hle := Finset.card_le_univ (insert u' (insert (1 : U) (Finset.univ.biUnion T)))
  rw [hcard17, ← Nat.card_eq_fintype_card, h.card] at hle
  omega

theorem exists_square (h : IsF20 U x v) (u : Γ) (hu : u ∈ U) :
    ∃ i : ℕ, ∃ a : Γ, a ∈ U ∧ (a * gInv x v i) * (a * gInv x v i) = u := by
  classical
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  obtain ⟨i, hi⟩ := h.exists_centralizer_gInv u hu
  set g := gInv x v ((i : ℕ) : ℤ) with hg
  have hgn : g ∈ normalizer (U : Set Γ) := h.gInv_norm _
  have hgg : g * g = 1 := h.gInv_mul_self _
  set φ := onePlus U h.comm g hgn with hφ
  have hker : ∀ w : U, w ∈ φ.ker ↔ g * w = w * g := mem_ker_onePlus h.comm h.sq g hgn
  have hrk : φ.range ≤ φ.ker := by
    rintro _ ⟨w, rfl⟩
    rw [hker]
    exact conj_onePlus_of_involution h.comm hgn hgg w w.2
  have hkcard : Nat.card φ.ker = 4 := by
    rw [← card_inf_centralizer_eq h.comm h.sq g hgn]
    exact h.card_centralizer_gInv _
  have hmul : Nat.card φ.ker * Nat.card φ.range = 16 := by
    rw [Subgroup.card_ker_mul_card_range φ, h.card]
  have hrcard : Nat.card φ.range = 4 := by
    rw [hkcard] at hmul
    omega
  have hreq : φ.range = φ.ker := Subgroup.eq_of_le_of_card_ge hrk (by omega)
  have hu' : (⟨u, hu⟩ : U) ∈ φ.ker := (hker _).2 hi
  rw [← hreq] at hu'
  obtain ⟨a, ha⟩ := hu'
  refine ⟨(i : ℕ), a, a.2, ?_⟩
  have hcoe : (a : Γ) * (g * a * g⁻¹) = u := congrArg Subtype.val ha
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  rw [hgi] at hcoe
  calc ((a : Γ) * g) * ((a : Γ) * g) = (a : Γ) * (g * a * g) * (g * g)⁻¹ * (g * g) := by group
    _ = (a : Γ) * (g * a * g) := by rw [hgg]; group
    _ = u := hcoe

theorem zpow_emod_five (h : IsF20 U x v) (i : ℤ) : x ^ i = x ^ (i % 5) := by
  have hx5 : x ^ (5 : ℤ) = 1 := by exact_mod_cast h.x5
  exact zpow_eq_zpow_emod i hx5

theorem exists_vk (h : IsF20 U x v) : ∃ k : ℤ, (k = 2 ∨ k = 3) ∧ ∀ i : ℤ, v * x ^ i * v⁻¹ = x ^ (k * i) := by
  rcases h.vx with hv | hv
  · refine ⟨2, Or.inl rfl, fun i => ?_⟩
    have := conj_zpow (i := i) (a := v) (b := x)
    rw [← this, hv, ← zpow_natCast, ← zpow_mul]
    norm_num
  · refine ⟨3, Or.inr rfl, fun i => ?_⟩
    have := conj_zpow (i := i) (a := v) (b := x)
    rw [← this, hv, ← zpow_natCast, ← zpow_mul]
    norm_num

end IsF20

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
