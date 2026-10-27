module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Attach
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

namespace Cfg

variable {G : Type} [Group G] [Finite G] {n : ℕ} (c : Cfg G n)

structure Embedding where
  ψ : Perm (Fin (n + 2)) →* G
  inj : Function.Injective ψ
  swap_mem : ∀ σ : Perm (Fin (n + 2)), σ.IsSwap → ψ σ ∈ cls c.t
  nbr : ∀ σ : Perm (Fin (n + 2)), σ.IsSwap → ∀ e ∈ cls c.t, e ≠ ψ σ → ψ σ * e = e * ψ σ →
    ∃ τ : Perm (Fin (n + 2)), τ.IsSwap ∧ ψ τ = e
  t_eq : ∃ σ : Perm (Fin (n + 2)), σ.IsSwap ∧ ψ σ = c.t

section Chain

open CFSG.Permutation.SymmetricCoxeter

variable (att : c.Attachment)

private def relabel : Perm (Fin n) := swap att.ρ ⟨n - 1, by have := c.hn; omega⟩

private def pt (i : ℕ) (h : i < n) : Fin n := relabel c att ⟨i, h⟩

variable {c att}

omit [Finite G] in
private theorem pt_injective {i j : ℕ} {hi : i < n} {hj : j < n}
    (h : pt c att i hi = pt c att j hj) : i = j := by
  have := (relabel c att).injective h
  exact congrArg Fin.val this

omit [Finite G] in
private theorem pt_last (h : n - 1 < n) : pt c att (n - 1) h = att.ρ := by
  simp [pt, relabel]

private theorem disjoint_swap_swap_of_ne {α : Type*} [DecidableEq α] {a b d e : α}
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) :
    (swap a b).Disjoint (swap d e) := by
  intro x
  by_cases hx : x = a ∨ x = b
  · right
    apply swap_apply_of_ne_of_ne
    · rcases hx with rfl | rfl <;> assumption
    · rcases hx with rfl | rfl <;> assumption
  · left
    push Not at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

omit [Finite G] in
private theorem braid_of_orderOf_three {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 3) : x * y * x = y * x * y := by
  have h3 : (x * y) ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have h1 : (x * y * x) * (y * x * y) = 1 := by
    calc x * y * x * (y * x * y) = (x * y) ^ 3 := by
          rw [pow_succ, pow_succ, pow_one]; group
      _ = 1 := h3
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hinv : (y * x * y)⁻¹ = y * x * y := by
    simp [mul_inv_rev, hx', hy', mul_assoc]
  exact (eq_inv_of_mul_eq_one_left h1).trans hinv

variable (c att)

private def τ (i : ℕ) (h : i + 1 < n) : Perm (Fin n) :=
  swap (pt c att i (by omega)) (pt c att (i + 1) h)

variable {c att}

omit [Finite G] in
private theorem τ_isSwap (i : ℕ) (h : i + 1 < n) : (τ c att i h).IsSwap :=
  ⟨_, _, fun e => absurd (pt_injective e) (by omega), rfl⟩

omit [Finite G] in
private theorem τ_disjoint {i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n) (hij : i + 2 ≤ j) :
    (τ c att i hi).Disjoint (τ c att j hj) := by
  refine disjoint_swap_swap_of_ne ?_ ?_ ?_ ?_ <;>
    exact fun e => absurd (pt_injective e) (by omega)

omit [Finite G] in
private theorem τ_ne_succ {i : ℕ} (hi : i + 1 < n) (hi2 : i + 1 + 1 < n) :
    τ c att i hi ≠ τ c att (i + 1) hi2 := by
  intro h
  have h1 := congrArg (fun f : Perm (Fin n) => f (pt c att i (by omega))) h
  simp only [τ] at h1
  rw [swap_apply_left, swap_apply_of_ne_of_ne] at h1
  · exact absurd (pt_injective h1) (by omega)
  · exact fun e => absurd (pt_injective e) (by omega)
  · exact fun e => absurd (pt_injective e) (by omega)

omit [Finite G] in
private theorem τ_not_disjoint_succ {i : ℕ} (hi : i + 1 < n) (hi2 : i + 1 + 1 < n) :
    ¬ (τ c att i hi).Disjoint (τ c att (i + 1) hi2) := by
  intro h
  rcases h (pt c att (i + 1) hi) with h1 | h1
  · simp only [τ] at h1
    rw [swap_apply_right] at h1
    exact absurd (pt_injective h1) (by omega)
  · simp only [τ] at h1
    rw [swap_apply_left] at h1
    exact absurd (pt_injective h1) (by omega)

omit [Finite G] in
private theorem τ_fix_ρ {i : ℕ} (hi : i + 1 < n) (h : i + 2 < n) : τ c att i hi att.ρ = att.ρ := by
  rw [← pt_last (c := c) (att := att) (by omega)]
  apply swap_apply_of_ne_of_ne <;>
    exact fun e => absurd (pt_injective e) (by omega)

omit [Finite G] in
private theorem τ_move_ρ {i : ℕ} (hi : i + 1 < n) (h : i + 2 = n) :
    τ c att i hi att.ρ ≠ att.ρ := by
  rw [← pt_last (c := c) (att := att) (by omega)]
  have : pt c att (n - 1) (by omega) = pt c att (i + 1) hi := by congr 1; omega
  rw [this]
  simp only [τ]
  rw [swap_apply_right]
  exact fun e => absurd (pt_injective e) (by omega)

variable (c att)

private theorem chain_exists :
    ∃ x : ℕ → G, IsCoxeterA (n + 1) x ∧ (∀ i, i + 1 < n → x i ∈ c.Dt) ∧
      (∀ (i : ℕ) (h : i + 1 < n), c.φ (x i) = τ c att i h) ∧
      x (n - 1) = att.a ∧ x n = c.t ∧ (∀ i, i ≤ n → x i ∈ cls c.t) := by
  classical
  choose xD hch using fun (i : ℕ) (h : i + 1 < n) =>
    c.exists_Dt_φ_eq (τ_isSwap (c := c) (att := att) i h)
  let x : ℕ → G := fun i =>
    if h : i + 1 < n then xD i h else if i + 1 = n then att.a else if i = n then c.t else 1
  have hx1 : ∀ i (h : i + 1 < n), x i = xD i h := fun i h => by simp [x, h]
  have hxa : x (n - 1) = att.a := by
    have h1 : ¬ (n - 1 + 1 < n) := by have := c.hn; omega
    have h2 : n - 1 + 1 = n := by have := c.hn; omega
    simp [x, h2]
  have hxt : x n = c.t := by
    have h1 : ¬ (n + 1 < n) := by omega
    have h2 : ¬ (n + 1 = n) := by omega
    simp [x, h1]
  have hxD : ∀ i (h : i + 1 < n), x i ∈ c.Dt := fun i h => by rw [hx1 i h]; exact (hch i h).1
  have hxφ : ∀ i (h : i + 1 < n), c.φ (x i) = τ c att i h := fun i h => by
    rw [hx1 i h]; exact (hch i h).2
  have hxcls : ∀ i, i ≤ n → x i ∈ cls c.t := by
    intro i hi
    by_cases h1 : i + 1 < n
    · exact (hxD i h1).1
    · by_cases h2 : i + 1 = n
      · rw [show i = n - 1 by omega, hxa]; exact att.mem
      · rw [show i = n by omega, hxt]; exact self_mem_cls
  refine ⟨x, ⟨?_, ?_, ?_⟩, hxD, hxφ, hxa, hxt, hxcls⟩
  · intro i hi
    exact c.mul_self_of_mem_cls (hxcls i (by omega))
  · intro i hi
    have hxi := c.mul_self_of_mem_cls (hxcls i (by omega))
    have hxi1 := c.mul_self_of_mem_cls (hxcls (i + 1) (by omega))
    apply braid_of_orderOf_three hxi hxi1
    by_cases h1 : i + 1 + 1 < n
    · have hnc : x i * x (i + 1) ≠ x (i + 1) * x i := by
        intro hc
        have := (c.comm_iff_Dt (hxD i (by omega)) (hxD (i + 1) h1)).1 hc
        rw [hxφ i (by omega), hxφ (i + 1) h1] at this
        rcases (isSwap_commute_iff (τ_isSwap (c := c) (att := att) i (by omega))
          (τ_isSwap (c := c) (att := att) (i + 1) h1)).1 this with h | h
        · exact τ_ne_succ (by omega) h1 h
        · exact τ_not_disjoint_succ (by omega) h1 h
      exact c.orderOf_mul_Dt_three (hxD i (by omega)) (hxD (i + 1) h1) hnc
    · by_cases h2 : i + 1 + 1 = n
      · have hxi1a : x (i + 1) = att.a := by rw [show i + 1 = n - 1 by omega]; exact hxa
        rw [hxi1a]
        have hnc : x i * att.a ≠ att.a * x i := by
          intro hc
          have := (att.star (x i) (hxD i (by omega))).1 hc
          rw [hxφ i (by omega)] at this
          exact τ_move_ρ (by omega) (by omega) this
        exact att.ord_x (x i) (hxD i (by omega)) hnc
      · have hin : i = n - 1 := by omega
        rw [show x i = att.a by rw [hin]; exact hxa, show x (i + 1) = c.t by
          rw [show i + 1 = n by omega]; exact hxt]
        exact att.ord_t
  · intro i j hij hj
    have hi : i + 1 < n := by omega
    by_cases hj1 : j + 1 < n
    · refine c.comm_of_disjoint (hxD i hi) (hxD j hj1) ?_
      rw [hxφ i hi, hxφ j hj1]
      exact τ_disjoint hi hj1 hij
    · by_cases hj2 : j + 1 = n
      · rw [show x j = att.a by rw [show j = n - 1 by omega]; exact hxa]
        refine (att.star (x i) (hxD i hi)).2 ?_
        rw [hxφ i hi]
        exact τ_fix_ρ hi (by omega)
      · rw [show j = n by omega, hxt]
        exact (hxD i hi).2.2.symm

end Chain

omit [Finite G] in
private theorem swap_mem_cls {ψ : Perm (Fin (n + 2)) →* G}
    (h0 : ψ (swap ⟨0, by omega⟩ ⟨1, by omega⟩) ∈ cls c.t)
    {σ : Perm (Fin (n + 2))} (hσ : σ.IsSwap) : ψ σ ∈ cls c.t := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨u, hu⟩ := isConj_iff.1 (isConj_swap (w := (⟨0, by omega⟩ : Fin (n + 2)))
    (x := (⟨1, by omega⟩ : Fin (n + 2))) (by simp) hab)
  rw [← hu, map_mul, map_mul, map_inv]
  exact conj_mem_cls h0 (ψ u)

open CFSG.Permutation.SymmetricCoxeter in
theorem nonempty_embedding : Nonempty c.Embedding := by
  obtain ⟨att⟩ := c.nonempty_attachment
  obtain ⟨x, hx, hxD, hxφ, hxa, hxt, hxcls⟩ := chain_exists c att
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Perm (Fin (n + 2)) →* G,
      ∀ i, i < n + 1 → ψ (adjSwap (n + 1) i) = x i := exists_hom_perm (n + 1) x hx
  have hn := c.hn
  have hadj : ∀ i (h : i < n + 1), adjSwap (n + 1) i =
      swap (⟨i, by omega⟩ : Fin (n + 2)) ⟨i + 1, by omega⟩ := fun i h => adjSwap_of_lt h
  have hψx : ∀ i (h : i < n + 1),
      ψ (swap (⟨i, by omega⟩ : Fin (n + 2)) ⟨i + 1, by omega⟩) = x i := fun i h => by
    rw [← hadj i h]; exact hψ i h
  have hsw : ∀ i (h : i < n + 1),
      (swap (⟨i, by omega⟩ : Fin (n + 2)) ⟨i + 1, by omega⟩).IsSwap := fun i h =>
    ⟨_, _, by simp, rfl⟩
  have hx0 : x 0 ∈ cls c.t := hxcls 0 (by omega)
  have hinj : Function.Injective ψ := by
    have hab : (⟨1, by omega⟩ : Fin (n + 2)) ≠ ⟨0, by omega⟩ := by simp
    have hac : (⟨1, by omega⟩ : Fin (n + 2)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have hbc : (⟨0, by omega⟩ : Fin (n + 2)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    refine injective_of_threeCycle (m := n + 2) (by omega) ψ
      (c := swap (⟨1, by omega⟩ : Fin (n + 2)) ⟨0, by omega⟩ * swap ⟨1, by omega⟩ ⟨2, by omega⟩)
      (isThreeCycle_swap_mul_swap_same hab hac hbc) ?_
    rw [map_mul, swap_comm, hψx 0 (by omega), hψx 1 (by omega)]
    intro h1
    have h2 : x 1 = x 0 := by
      rw [← inv_eq_of_mul_eq_one_right h1]
      exact c.inv_of_mem_cls (hxcls 0 (by omega))
    exact τ_ne_succ (c := c) (att := att) (i := 0) (by omega) (by omega) (by
      rw [← hxφ 0 (by omega), ← hxφ 1 (by omega), h2])
  have htsw : ∃ σ : Perm (Fin (n + 2)), σ.IsSwap ∧ ψ σ = c.t :=
    ⟨swap (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩, hsw n (by omega),
      by rw [hψx n (by omega), hxt]⟩
  have hmem : ∀ σ : Perm (Fin (n + 2)), σ.IsSwap → ψ σ ∈ cls c.t := fun σ hσ =>
    swap_mem_cls (c := c) (ψ := ψ) (by rw [hψx 0 (by omega)]; exact hx0) hσ
  have hDt : ∀ y ∈ c.Dt, ∃ σ : Perm (Fin (n + 2)), σ.IsSwap ∧ ψ σ = y := by
    let R : Set (Perm (Fin n)) :=
      {τ | ∃ σ : Perm (Fin (n + 2)), σ.IsSwap ∧ ψ σ ∈ c.Dt ∧ c.φ (ψ σ) = τ}
    have hgen : ∀ (i : ℕ) (h : i + 1 < n),
        (relabel c att)⁻¹⁻¹ * swap (⟨i, Nat.lt_of_succ_lt h⟩ : Fin n) ⟨i + 1, h⟩ *
          (relabel c att)⁻¹ ∈ R := by
      intro i h
      have h1 : (relabel c att)⁻¹⁻¹ * swap (⟨i, Nat.lt_of_succ_lt h⟩ : Fin n) ⟨i + 1, h⟩ *
          (relabel c att)⁻¹ = τ c att i h := by
        rw [inv_inv]; exact (swap_apply_apply (relabel c att) _ _).symm
      rw [h1]
      exact ⟨_, hsw i (by omega), by rw [hψx i (by omega)]; exact hxD i h,
        by rw [hψx i (by omega)]; exact hxφ i h⟩
    have hcl : ∀ τ ∈ R, ∀ τ' ∈ R, τ * τ' * τ ∈ R := by
      intro τ hτ τ' hτ'
      obtain ⟨σ, hσ, hσD, rfl⟩ := hτ
      obtain ⟨σ', hσ', hσ'D, rfl⟩ := hτ'
      refine ⟨σ * σ' * σ⁻¹, isSwap_conj hσ' σ, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv]; exact c.conj_Dt_mem_Dt hσ'D hσD
      · rw [map_mul, map_mul, map_inv, c.φ_conj_Dt hσ'D hσD, isSwap_inv (c.φ_isSwap hσD)]
    intro y hy
    obtain ⟨σ, hσ, hσD, hφ⟩ := swaps_eq_of_conj_closed (relabel c att)⁻¹ R hgen hcl (c.φ y)
      (c.φ_isSwap hy)
    exact ⟨σ, hσ, c.φ_injOn hσD hy hφ⟩
  have hnbr : ∀ σ : Perm (Fin (n + 2)), σ.IsSwap → ∀ e ∈ cls c.t, e ≠ ψ σ → ψ σ * e = e * ψ σ →
      ∃ τ : Perm (Fin (n + 2)), τ.IsSwap ∧ ψ τ = e := by
    intro σ hσ e he hne hcomm
    obtain ⟨a, b, hab, rfl⟩ := hσ
    obtain ⟨σ₀, ⟨a₀, b₀, hab₀, hσ₀⟩, hψσ₀⟩ := htsw
    rw [hσ₀] at hψσ₀
    obtain ⟨u, hu⟩ := isConj_iff.1 (isConj_swap hab₀ hab)
    have hg : ψ (swap a b) = ψ u * c.t * (ψ u)⁻¹ := by
      rw [← hu, map_mul, map_mul, map_inv, hψσ₀]
    have h1 : e ∈ c.Dloc (ψ (swap a b)) := ⟨he, hne, hcomm⟩
    have h2 := (c.Dloc_conj_iff (h := (ψ u)⁻¹)).1 h1
    have h3 : (ψ u)⁻¹ * ψ (swap a b) * ((ψ u)⁻¹)⁻¹ = c.t := by rw [hg]; group
    rw [h3] at h2
    obtain ⟨τ', hτ', hψτ'⟩ := hDt _ h2
    refine ⟨u * τ' * u⁻¹, isSwap_conj hτ' u, ?_⟩
    rw [map_mul, map_mul, hψτ', map_inv]
    group
  exact ⟨⟨ψ, hinj, hmem, hnbr, htsw⟩⟩

end Cfg

end CFSG.EvenSmallLie.OddTranspAlt
