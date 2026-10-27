module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34M12

open Subgroup
open scoped commutatorElement

section Abstract

variable {Y : Type*} [Group Y]

structure BarFacts (W : Subgroup Y) (ζ a : Y) : Prop where
  W_normal : W.Normal
  W_card : Nat.card ↥W = 32
  ζ_mem : ζ ∈ W
  ζ_ne : ζ ≠ 1
  ζ_sq : ζ * ζ = 1
  ζ_central : ∀ y : Y, y * ζ = ζ * y
  comm_mem : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ zpowers ζ
  ext : ∀ u ∈ W, u ∉ zpowers ζ → ∃ w ∈ W, ⁅w, u⁆ = ζ
  a_cube : a * a * a = 1
  a_fix : ∀ w ∈ W, a * w = w * a → w ∈ zpowers ζ
  inv_a : ∀ y : Y, y * y = 1 → y ∉ W → y * a * y⁻¹ * a ∈ W
  two_core : ∀ M : Subgroup Y, M.Normal → (∀ m ∈ M, m * m = 1) → M ≤ W

variable {W : Subgroup Y} {ζ a : Y}

theorem mem_zpowers_inv {c : Y} (hζ : ζ * ζ = 1) (hc : c ∈ zpowers ζ) : c = 1 ∨ c = ζ := by
  obtain ⟨n, hn⟩ := hc
  beta_reduce at hn
  have h2 : ζ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hζ
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [← hn, zpow_mul, h2, one_zpow]
  · right
    rw [← hn, zpow_add, zpow_one, zpow_mul, h2, one_zpow, one_mul]

theorem BarFacts.mem_zpowers_iff (h : BarFacts W ζ a) {c : Y} : c ∈ zpowers ζ ↔ c = 1 ∨ c = ζ := by
  constructor
  · exact mem_zpowers_inv h.ζ_sq
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem BarFacts.ζ_conj (h : BarFacts W ζ a) (y : Y) : y * ζ * y⁻¹ = ζ := by
  rw [h.ζ_central y]; group

theorem BarFacts.a_move (h : BarFacts W ζ a) {e : Y} (heW : e ∈ W) (heZ : e ∉ zpowers ζ) :
    a * e * a⁻¹ ≠ e ∧ a * e * a⁻¹ ≠ ζ * e := by
  have ha3 := h.a_cube
  constructor
  · intro hc
    have : a * e = e * a := by
      calc a * e = (a * e * a⁻¹) * a := by group
        _ = e * a := by rw [hc]
    exact heZ (h.a_fix e heW this)
  · intro hc
    have h1 : a * (a * e * a⁻¹) * a⁻¹ = e := by
      rw [hc]
      calc a * (ζ * e) * a⁻¹ = (a * ζ * a⁻¹) * (a * e * a⁻¹) := by group
        _ = ζ * (ζ * e) := by rw [h.ζ_conj, hc]
        _ = (ζ * ζ) * e := by group
        _ = e := by rw [h.ζ_sq, one_mul]
    have h2 : a * (a * (a * e * a⁻¹) * a⁻¹) * a⁻¹ = e := by
      calc a * (a * (a * e * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * e * (a * a * a)⁻¹ := by group
        _ = e := by rw [ha3]; group
    rw [h1] at h2
    have h3 : ζ * e = e := by rw [← hc, h2]
    have hz : ζ = 1 := by
      calc ζ = ζ * e * e⁻¹ := by group
        _ = e * e⁻¹ := by rw [h3]
        _ = 1 := by group
    exact absurd hz h.ζ_ne

theorem BarFacts.exists_ext_not_comm [Finite Y] (h : BarFacts W ζ a) :
    ∃ u ∈ W, ∃ w ∈ W, ⁅w, u⁆ = ζ := by
  have hz : Nat.card ↥(zpowers ζ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact h.ζ_sq) h.ζ_ne]
  have : ∃ u ∈ W, u ∉ zpowers ζ := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ zpowers ζ := fun u hu => hcon u hu
    have := Subgroup.card_le_of_le hle
    rw [h.W_card, hz] at this
    omega
  obtain ⟨u, hu, huZ⟩ := this
  obtain ⟨w, hw, hwu⟩ := h.ext u hu huZ
  exact ⟨u, hu, w, hw, hwu⟩

theorem BarFacts.dichotomy [Finite Y] (h : BarFacts W ζ a) {M : Subgroup Y} (hMn : M.Normal)
    (hM2 : ∀ m ∈ M, m * m = 1) (hM1 : M ≠ ⊥) :
    ζ ∈ M ∧ (M = zpowers ζ ∨ Nat.card ↥M = 8) := by
  classical
  have hMW : M ≤ W := h.two_core M hMn hM2
  have hz : Nat.card ↥(zpowers ζ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact h.ζ_sq) h.ζ_ne]
  have hζM : ζ ∈ M := by
    by_cases hsub : M ≤ zpowers ζ
    · by_contra hζ
      apply hM1
      rw [eq_bot_iff]
      intro m hm
      rcases h.mem_zpowers_iff.1 (hsub hm) with h1 | h1
      · rw [h1]; exact one_mem _
      · exact absurd (h1 ▸ hm) hζ
    · obtain ⟨m, hm, hmZ⟩ := IsConcreteLE.not_le_iff_exists.1 hsub
      obtain ⟨w, hw, hwm⟩ := h.ext m (hMW hm) hmZ
      have : ⁅w, m⁆ ∈ M := by
        simp only [commutatorElement_def]
        exact M.mul_mem (hMn.conj_mem m hm w) (M.inv_mem hm)
      rwa [hwm] at this
  refine ⟨hζM, ?_⟩
  by_cases hMz : M = zpowers ζ
  · exact Or.inl hMz
  right
  have hzle : zpowers ζ ≤ M := (Subgroup.zpowers_le).2 hζM
  have hN32 : Nat.card ↥M ∣ 32 := by
    rw [← h.W_card]; exact Subgroup.card_dvd_of_le hMW
  have hNge : 2 ≤ Nat.card ↥M := by
    have := Subgroup.card_le_of_le hzle
    omega
  have hN2 : Nat.card ↥M ≠ 2 := by
    intro hN
    apply hMz
    exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hz, hN])).symm
  have hN32' : Nat.card ↥M ≠ 32 := by
    intro hN
    have hMeq : M = W := Subgroup.eq_of_le_of_card_ge hMW (by rw [h.W_card, hN])
    obtain ⟨u, hu, w, hw, hwu⟩ := h.exists_ext_not_comm
    have hu2 : u * u = 1 := hM2 u (hMeq ▸ hu)
    have hw2 : w * w = 1 := hM2 w (hMeq ▸ hw)
    have hwu2 : (w * u) * (w * u) = 1 := hM2 _ (hMeq ▸ W.mul_mem hw hu)
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have : ζ = 1 := by
      rw [← hwu]
      simp only [commutatorElement_def, hwi, hui]
      calc w * u * w * u = (w * u) * (w * u) := by group
        _ = 1 := hwu2
    exact h.ζ_ne this
  have : M.Normal := hMn
  have h3 : a ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact h.a_cube
  let τ : MulAut ↥M := MulAut.conjNormal a
  have hτ : τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  let σ : Equiv.Perm ↥M := MulAut.toPerm ↥M τ
  have hσ : σ ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hτ, map_one]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fintype ↥M := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσ
  have hfix : σ.supportᶜ = {1, ⟨ζ, hζM⟩} := by
    ext m
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_insert,
      Finset.mem_singleton]
    have hσm : ∀ m : ↥M, ((σ m : ↥M) : Y) = a * m * a⁻¹ := fun m => rfl
    constructor
    · intro hm
      have hm' : a * (m : Y) * a⁻¹ = m := by rw [← hσm, hm]
      have hcomm : a * (m : Y) = m * a := by
        calc a * (m : Y) = (a * m * a⁻¹) * a := by group
          _ = m * a := by rw [hm']
      rcases h.mem_zpowers_iff.1 (h.a_fix m (hMW m.2) hcomm) with h1 | h1
      · left; exact Subtype.ext h1
      · right; exact Subtype.ext h1
    · rintro (rfl | rfl)
      · apply Subtype.ext; rw [hσm]; simp
      · apply Subtype.ext; rw [hσm]
        show a * ζ * a⁻¹ = ζ
        exact h.ζ_conj a
  have hcard2 : σ.supportᶜ.card = 2 := by
    rw [hfix, Finset.card_pair]
    intro hc
    have := congrArg Subtype.val hc
    exact h.ζ_ne this.symm
  rw [hcard2, ← Nat.card_eq_fintype_card] at hmod
  have hle : Nat.card ↥M ≤ 32 := Nat.le_of_dvd (by norm_num) hN32
  unfold Nat.ModEq at hmod
  generalize Nat.card ↥M = N at *
  interval_cases N <;> omega

theorem conj_not_mem_zpowers (h : BarFacts W ζ a) {x : Y} (hx : x ∉ zpowers ζ) (g : Y) :
    g * x * g⁻¹ ∉ zpowers ζ := by
  intro hc
  apply hx
  have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rcases h.mem_zpowers_iff.1 hc with h1 | h1
  · rw [hx', h1]; simp
  · rw [hx', h1]
    have : g⁻¹ * ζ * g = ζ := by rw [h.ζ_central g⁻¹]; group
    rw [this]; exact mem_zpowers _

def Sep (ζ x y : Y) : Prop := x ≠ y ∧ x ≠ ζ * y

theorem Sep.symm {x y : Y} (hζ : ζ * ζ = 1) (h : Sep ζ x y) : Sep ζ y x := by
  refine ⟨fun e => h.1 e.symm, fun e => h.2 ?_⟩
  calc x = ζ * (ζ * x) := by rw [← mul_assoc, hζ, one_mul]
    _ = ζ * y := by rw [← e]

theorem Sep.conj (h : BarFacts W ζ a) {x y : Y} (hxy : Sep ζ x y) (g : Y) :
    Sep ζ (g * x * g⁻¹) (g * y * g⁻¹) := by
  refine ⟨fun e => hxy.1 ?_, fun e => hxy.2 ?_⟩
  · have := congrArg (fun t => g⁻¹ * t * g) e
    simpa using this
  · have e' : g * x * g⁻¹ = ζ * (g * y * g⁻¹) := e
    have h' : g * x * g⁻¹ = g * (ζ * y) * g⁻¹ := by
      rw [e']
      calc ζ * (g * y * g⁻¹) = (g * ζ * g⁻¹) * (g * y * g⁻¹) := by rw [h.ζ_conj]
        _ = g * (ζ * y) * g⁻¹ := by group
    have := congrArg (fun t => g⁻¹ * t * g) h'
    simpa using this

theorem BarFacts.transitive [Finite Y] (h : BarFacts W ζ a) {M : Subgroup Y} (hMn : M.Normal)
    (hM2 : ∀ m ∈ M, m * m = 1) (h8 : Nat.card ↥M = 8) (hζM : ζ ∈ M)
    {e e' : Y} (he : e ∈ M) (he' : e' ∈ M) (heZ : e ∉ zpowers ζ) (he'Z : e' ∉ zpowers ζ) :
    ∃ g : Y, g * e * g⁻¹ = e' := by
  classical
  have hMW : M ≤ W := h.two_core M hMn hM2
  have ha3 := h.a_cube
  let u1 : Y := a * e * a⁻¹
  let u2 : Y := a * u1 * a⁻¹
  have hu1M : u1 ∈ M := hMn.conj_mem e he a
  have hu2M : u2 ∈ M := hMn.conj_mem u1 hu1M a
  have hu3 : a * u2 * a⁻¹ = e := by
    calc a * u2 * a⁻¹ = (a * a * a) * e * (a * a * a)⁻¹ := by simp only [u2, u1]; group
      _ = e := by rw [ha3]; group
  have hu1Z : u1 ∉ zpowers ζ := conj_not_mem_zpowers h heZ a
  have hu2Z : u2 ∉ zpowers ζ := conj_not_mem_zpowers h hu1Z a
  have s10 : Sep ζ u1 e := h.a_move (hMW he) heZ
  have s21 : Sep ζ u2 u1 := h.a_move (hMW hu1M) hu1Z
  have s02 : Sep ζ e u2 := by
    have := Sep.conj h s21 a
    rw [hu3] at this
    exact this
  let u : Fin 3 → Y := ![e, u1, u2]
  have hsep : ∀ i k : Fin 3, i ≠ k → Sep ζ (u i) (u k) := by
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact s10.symm h.ζ_sq
    · exact s02
    · exact s10
    · exact absurd rfl hik
    · exact s21.symm h.ζ_sq
    · exact s02.symm h.ζ_sq
    · exact s21
    · exact absurd rfl hik
  have huM : ∀ i, u i ∈ M := by
    intro i; fin_cases i
    · exact he
    · exact hu1M
    · exact hu2M
  have huZ : ∀ i, u i ∉ zpowers ζ := by
    intro i; fin_cases i
    · exact heZ
    · exact hu1Z
    · exact hu2Z
  let f : Fin 3 × Fin 2 → Y := fun ij => ζ ^ ij.2.val * u ij.1
  have hfinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hfe
    have hfe' : ζ ^ j.val * u i = ζ ^ l.val * u k := hfe
    by_cases hik : i = k
    · subst hik
      have hjl : ζ ^ j.val = ζ ^ l.val := mul_right_cancel hfe'
      have : j = l := by
        fin_cases j <;> fin_cases l
        · rfl
        · exfalso; simp at hjl; exact h.ζ_ne hjl.symm
        · exfalso; simp at hjl; exact h.ζ_ne hjl
        · rfl
      rw [this]
    · exfalso
      have hs := hsep i k hik
      fin_cases j <;> fin_cases l
      · simp at hfe'; exact hs.1 hfe'
      · simp at hfe'; exact hs.2 hfe'
      · simp at hfe'; exact hs.2 (by
          calc u i = ζ * (ζ * u i) := by rw [← mul_assoc, h.ζ_sq, one_mul]
            _ = ζ * u k := by rw [hfe'])
      · simp at hfe'
        exact hs.1 (by
          have := hfe'
          calc u i = ζ * (ζ * u i) := by rw [← mul_assoc, h.ζ_sq, one_mul]
            _ = ζ * (ζ * u k) := by rw [this]
            _ = u k := by rw [← mul_assoc, h.ζ_sq, one_mul])
  have : Fintype Y := Fintype.ofFinite Y
  let Mset : Finset Y := Finset.univ.filter (fun x => x ∈ M)
  let Zset : Finset Y := {1, ζ}
  have hMcard : Mset.card = 8 := by
    rw [← h8, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hZcard : Zset.card = 2 := Finset.card_pair (Ne.symm h.ζ_ne)
  have hZsub : Zset ⊆ Mset := by
    intro x hx
    simp only [Zset, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact one_mem _
    · exact hζM
  let F : Finset Y := Finset.univ.image f
  have hFcard : F.card = 6 := by
    rw [Finset.card_image_of_injective _ hfinj]; simp
  have hFsub : F ⊆ Mset \ Zset := by
    intro x hx
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_sdiff, Mset, Zset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    have hζj : ζ ^ j.val ∈ M := M.pow_mem hζM _
    have hζjZ : ζ ^ j.val ∈ zpowers ζ := (zpowers ζ).pow_mem (mem_zpowers ζ) _
    refine ⟨M.mul_mem hζj (huM i), ?_, ?_⟩
    · intro hc
      apply huZ i
      have : u i = (ζ ^ j.val)⁻¹ * (ζ ^ j.val * u i) := by group
      rw [this, show ζ ^ j.val * u i = 1 from hc]
      simp
    · intro hc
      apply huZ i
      have : u i = (ζ ^ j.val)⁻¹ * (ζ ^ j.val * u i) := by group
      rw [this]
      exact (zpowers ζ).mul_mem ((zpowers ζ).inv_mem hζjZ)
        (by show ζ ^ j.val * u i ∈ zpowers ζ; rw [show ζ ^ j.val * u i = ζ from hc]; exact mem_zpowers _)
  have hsdcard : (Mset \ Zset).card = 6 := by
    rw [Finset.card_sdiff_of_subset hZsub, hMcard, hZcard]
  have hFeq : F = Mset \ Zset :=
    Finset.eq_of_subset_of_card_le hFsub (by rw [hFcard, hsdcard])
  have he'mem : e' ∈ F := by
    rw [hFeq]
    simp only [Finset.mem_sdiff, Mset, Zset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨he', ?_, ?_⟩
    · intro hc; apply he'Z; rw [hc]; exact one_mem _
    · intro hc; apply he'Z; rw [hc]; exact mem_zpowers _
  obtain ⟨⟨i, j⟩, -, hij⟩ := Finset.mem_image.1 he'mem
  have hex : ∀ i : Fin 3, ∃ g : Y, u i = g * e * g⁻¹ := by
    intro i; fin_cases i
    · exact ⟨1, by simp [u]⟩
    · exact ⟨a, rfl⟩
    · exact ⟨a * a, by show u2 = _; simp only [u2, u1]; group⟩
  obtain ⟨gi, hgi⟩ := hex i
  fin_cases j
  · refine ⟨gi, ?_⟩
    rw [← hij]
    show gi * e * gi⁻¹ = ζ ^ 0 * u i
    rw [pow_zero, one_mul, hgi]
  · obtain ⟨w, hw, hwu⟩ := h.ext (u i) (hMW (huM i)) (huZ i)
    refine ⟨w * gi, ?_⟩
    rw [← hij]
    show (w * gi) * e * (w * gi)⁻¹ = ζ ^ 1 * u i
    have h1 : w * u i * w⁻¹ = ζ * u i := by
      have : w * u i * w⁻¹ * (u i)⁻¹ = ζ := hwu
      calc w * u i * w⁻¹ = (w * u i * w⁻¹ * (u i)⁻¹) * u i := by group
        _ = ζ * u i := by rw [this]
    calc (w * gi) * e * (w * gi)⁻¹ = w * (gi * e * gi⁻¹) * w⁻¹ := by group
      _ = w * u i * w⁻¹ := by rw [← hgi]
      _ = ζ ^ 1 * u i := by rw [h1, pow_one]

theorem BarFacts.outside [Finite Y] (h : BarFacts W ζ a) {M : Subgroup Y} (hMn : M.Normal)
    (hM2 : ∀ m ∈ M, m * m = 1) (h8 : Nat.card ↥M = 8)
    {y : Y} (hy2 : y * y = 1) (hyW : y ∉ W) : ∃ e ∈ M, ⁅e, y⁆ ∉ zpowers ζ := by
  classical
  by_contra hcon
  push Not at hcon
  have hMW : M ≤ W := h.two_core M hMn hM2
  have hz2 : Nat.card ↥(zpowers ζ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact h.ζ_sq) h.ζ_ne]
  obtain ⟨e, heM, heZ⟩ : ∃ e ∈ M, e ∉ zpowers ζ := by
    by_contra hc
    push Not at hc
    have hle : M ≤ zpowers ζ := fun x hx => hc x hx
    have := Subgroup.card_le_of_le hle
    rw [h8, hz2] at this
    omega
  have hZc : ∀ c ∈ zpowers ζ, ∀ t : Y, c * t = t * c := by
    intro c hc t
    rcases h.mem_zpowers_iff.1 hc with rfl | rfl
    · simp
    · exact (h.ζ_central t).symm
  have hyx : ∀ x ∈ M, ∃ c ∈ zpowers ζ, y * x * y⁻¹ = c * x := fun x hx =>
    ⟨⁅x, y⁆⁻¹, (zpowers ζ).inv_mem (hcon x hx), by simp only [commutatorElement_def]; group⟩
  obtain ⟨w0, hw0def⟩ : ∃ w0, w0 = y * a * y⁻¹ * a := ⟨_, rfl⟩
  have hw0W : w0 ∈ W := hw0def ▸ h.inv_a y hy2 hyW
  have hya : y * a * y⁻¹ = w0 * a⁻¹ := by rw [hw0def]; group
  have hkey : ∀ x ∈ M, ∃ d ∈ zpowers ζ, a * x * a⁻¹ = d * (a⁻¹ * x * a) := by
    intro x hx
    obtain ⟨c, hc, hyc⟩ := hyx x hx
    have hx' : a * x * a⁻¹ ∈ M := hMn.conj_mem x hx a
    obtain ⟨c', hc', hyc'⟩ := hyx _ hx'
    have hxm : a⁻¹ * x * a ∈ M := by simpa using hMn.conj_mem x hx a⁻¹
    have hc3 : ⁅w0, a⁻¹ * x * a⁆ ∈ zpowers ζ := h.comm_mem w0 hw0W _ (hMW hxm)
    have e1 : y * (a * x * a⁻¹) * y⁻¹ = c * (⁅w0, a⁻¹ * x * a⁆ * (a⁻¹ * x * a)) := by
      have h1 : y * (a * x * a⁻¹) * y⁻¹ = (w0 * a⁻¹) * (y * x * y⁻¹) * (w0 * a⁻¹)⁻¹ := by
        rw [← hya]; group
      rw [h1, hyc]
      calc (w0 * a⁻¹) * (c * x) * (w0 * a⁻¹)⁻¹ = (w0 * a⁻¹ * c) * x * (a * w0⁻¹) := by group
        _ = (c * (w0 * a⁻¹)) * x * (a * w0⁻¹) := by rw [hZc c hc (w0 * a⁻¹)]
        _ = c * (w0 * (a⁻¹ * x * a) * w0⁻¹) := by group
        _ = c * (⁅w0, a⁻¹ * x * a⁆ * (a⁻¹ * x * a)) := by
          simp only [commutatorElement_def]; group
    refine ⟨c'⁻¹ * (c * ⁅w0, a⁻¹ * x * a⁆), ?_, ?_⟩
    · exact (zpowers ζ).mul_mem ((zpowers ζ).inv_mem hc') ((zpowers ζ).mul_mem hc hc3)
    · have h2 : c' * (a * x * a⁻¹) = c * (⁅w0, a⁻¹ * x * a⁆ * (a⁻¹ * x * a)) := by
        rw [← hyc', e1]
      calc a * x * a⁻¹ = c'⁻¹ * (c' * (a * x * a⁻¹)) := by group
        _ = c'⁻¹ * (c * (⁅w0, a⁻¹ * x * a⁆ * (a⁻¹ * x * a))) := by rw [h2]
        _ = (c'⁻¹ * (c * ⁅w0, a⁻¹ * x * a⁆)) * (a⁻¹ * x * a) := by group
  have he2M : a⁻¹ * e * a ∈ M := by simpa using hMn.conj_mem e heM a⁻¹
  obtain ⟨d, hd, hde⟩ := hkey _ he2M
  have ha3 := h.a_cube
  have haa : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact ha3)
  have h1 : a * (a⁻¹ * e * a) * a⁻¹ = e := by group
  have h2 : a⁻¹ * (a⁻¹ * e * a) * a = a * e * a⁻¹ := by
    calc a⁻¹ * (a⁻¹ * e * a) * a = (a⁻¹ * a⁻¹) * e * (a * a) := by group
      _ = ((a * a) * (a * a)) * e * (a * a) := by rw [← haa]
      _ = (a * (a * a * a)) * e * (a * a) := by group
      _ = a * e * a⁻¹ := by rw [ha3, mul_one, haa]
  rw [h1, h2] at hde
  obtain ⟨hne1, hne2⟩ := h.a_move (hMW heM) heZ
  rcases h.mem_zpowers_iff.1 hd with hd1 | hd1
  · apply hne1; rw [hd1] at hde; simpa using hde.symm
  · apply hne2
    rw [hd1] at hde
    calc a * e * a⁻¹ = ζ * (ζ * (a * e * a⁻¹)) := by rw [← mul_assoc, h.ζ_sq, one_mul]
      _ = ζ * e := by rw [← hde]

end Abstract

section Involution

variable {X : Type*} [Group X]

theorem exp2_comm {E : Subgroup X} (hE2 : ∀ e ∈ E, e * e = 1) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  have hxy := hE2 _ (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE2 x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE2 y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y * x := by rw [mul_inv_rev, hxi, hyi]

theorem eq_of_card_le_two' {D : Subgroup X} [Finite D] (h : Nat.card ↥D ≤ 2) {a b : X}
    (ha : a ∈ D) (hb : b ∈ D) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![(1 : ↥D), ⟨a, ha⟩, ⟨b, hb⟩] : Fin 3 → ↥D) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [Subtype.ext_iff] at hij; tauto)
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem comm_unique {E : Subgroup X} [Finite E] (hE2 : ∀ e ∈ E, e * e = 1) (hE8 : Nat.card ↥E = 8)
    {t : X} (ht : t * t = 1) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) {e e' : X} (he : e ∈ E) (he' : e' ∈ E)
    (h1 : ⁅e, t⁆ ≠ 1) (h1' : ⁅e', t⁆ ≠ 1) : ⁅e', t⁆ = ⁅e, t⁆ := by
  classical
  have hcomm := exp2_comm hE2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcm : ∀ x ∈ E, ⁅x, t⁆ ∈ E := by
    intro x hx
    simp only [commutatorElement_def]
    have : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
    rw [this]
    exact E.mul_mem hx (htE _ (E.inv_mem hx))
  let δ : ↥E →* ↥E := MonoidHom.mk' (fun x => ⟨⁅(x : X), t⁆, hcm x x.2⟩) (by
    intro x y
    apply Subtype.ext
    show ⁅((x * y : ↥E) : X), t⁆ = ⁅(x : X), t⁆ * ⁅(y : X), t⁆
    obtain ⟨x', hx'd⟩ : ∃ x', x' = t * (x : X)⁻¹ * t⁻¹ := ⟨_, rfl⟩
    obtain ⟨y', hy'd⟩ : ∃ y', y' = t * (y : X)⁻¹ * t⁻¹ := ⟨_, rfl⟩
    have hx' : x' ∈ E := hx'd ▸ htE _ (E.inv_mem x.2)
    have hy' : y' ∈ E := hy'd ▸ htE _ (E.inv_mem y.2)
    have e1 : ⁅((x * y : ↥E) : X), t⁆ = (x : X) * y * (y' * x') := by
      rw [hx'd, hy'd]; simp only [commutatorElement_def, Subgroup.coe_mul]; group
    have e2 : ⁅(x : X), t⁆ * ⁅(y : X), t⁆ = ((x : X) * x') * ((y : X) * y') := by
      rw [hx'd, hy'd]; simp only [commutatorElement_def]; group
    rw [e1, e2]
    have hxy' : y' * x' = x' * y' := hcomm _ hy' _ hx'
    have hyx' : (y : X) * x' = x' * y := hcomm _ y.2 _ hx'
    calc (x : X) * y * (y' * x') = (x : X) * y * (x' * y') := by rw [hxy']
      _ = (x : X) * (y * x') * y' := by group
      _ = (x : X) * (x' * y) * y' := by rw [hyx']
      _ = ((x : X) * x') * ((y : X) * y') := by group)
  have hδ : ∀ x : ↥E, ((δ x : ↥E) : X) = ⁅(x : X), t⁆ := fun x => rfl
  have hrange_le : δ.range ≤ δ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show ⁅((δ x : ↥E) : X), t⁆ = 1
    rw [hδ]
    have hxi : (x : X)⁻¹ = x := inv_eq_of_mul_eq_one_right (hE2 x x.2)
    obtain ⟨z, hzd⟩ : ∃ z, z = t * (x : X) * t⁻¹ := ⟨_, rfl⟩
    have hzE : z ∈ E := hzd ▸ htE _ x.2
    have hr : ⁅(x : X), t⁆ = (x : X) * z := by
      rw [hzd]; simp only [commutatorElement_def, hxi]; group
    have hzz : t * z * t⁻¹ = x := by
      rw [hzd]; calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [ht]; group
    have htr : t * ((x : X) * z) * t⁻¹ = (x : X) * z := by
      calc t * ((x : X) * z) * t⁻¹ = (t * (x : X) * t⁻¹) * (t * z * t⁻¹) := by group
        _ = z * x := by rw [← hzd, hzz]
        _ = x * z := hcomm _ hzE _ x.2 |>.symm ▸ (hcomm _ x.2 _ hzE).symm
    rw [hr]
    calc (x : X) * z * t * ((x : X) * z)⁻¹ * t⁻¹ = ((x : X) * z) * (t * ((x : X) * z)⁻¹ * t⁻¹) := by group
      _ = ((x : X) * z) * (t * ((x : X) * z) * t⁻¹)⁻¹ := by group
      _ = 1 := by rw [htr]; group
  have hcard := Subgroup.card_ker_mul_card_range δ
  have hle := Subgroup.card_le_of_le hrange_le
  have hrle : Nat.card δ.range ≤ 2 := by
    rw [hE8] at hcard
    nlinarith [hcard, hle]
  let a1 : ↥E := ⟨⁅e', t⁆, hcm e' he'⟩
  let a2 : ↥E := ⟨⁅e, t⁆, hcm e he⟩
  have hm1 : a1 ∈ δ.range := ⟨⟨e', he'⟩, Subtype.ext (hδ ⟨e', he'⟩)⟩
  have hm2 : a2 ∈ δ.range := ⟨⟨e, he⟩, Subtype.ext (hδ ⟨e, he⟩)⟩
  have := eq_of_card_le_two' (X := ↥E) (D := δ.range) hrle hm1 hm2
    (fun h => h1' (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem exists_fixed {A : Subgroup X} (hAn : A.Normal) (hA2 : ∀ e ∈ A, e * e = 1) {a₀ : X}
    (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1) {zb : X} (hz2 : zb * zb = 1) :
    ∃ b ∈ A, b * zb = zb * b ∧ b ≠ 1 := by
  by_cases hc : zb * a₀ = a₀ * zb
  · exact ⟨a₀, ha₀, hc.symm, ha₀1⟩
  · have hAc := exp2_comm hA2
    have ha₀i : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right (hA2 a₀ ha₀)
    obtain ⟨c, hcdef⟩ : ∃ c, c = zb * a₀ * zb⁻¹ := ⟨_, rfl⟩
    have hcA : c ∈ A := hcdef ▸ hAn.conj_mem a₀ ha₀ zb
    have hzc : zb * c * zb⁻¹ = a₀ := by
      rw [hcdef]
      calc zb * (zb * a₀ * zb⁻¹) * zb⁻¹ = (zb * zb) * a₀ * (zb * zb)⁻¹ := by group
        _ = a₀ := by rw [hz2]; group
    have hcomm' : a₀ * c = c * a₀ := hAc _ ha₀ _ hcA
    refine ⟨a₀ * c, A.mul_mem ha₀ hcA, ?_, ?_⟩
    · have h1 : zb * (a₀ * c) * zb⁻¹ = a₀ * c := by
        calc zb * (a₀ * c) * zb⁻¹ = (zb * a₀ * zb⁻¹) * (zb * c * zb⁻¹) := by group
          _ = c * a₀ := by rw [← hcdef, hzc]
          _ = a₀ * c := hcomm'.symm
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    · intro h1
      apply hc
      have h2 : c = a₀⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [ha₀i, hcdef] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2

end Involution

section Setup

variable {X Y : Type*} [Group X] [Group Y]

structure Setup (W : Subgroup Y) (ζ a : Y) (Cb : Subgroup X) (pi : X → Y) (zb : X) : Prop where
  bar : BarFacts W ζ a
  mul : ∀ x ∈ Cb, ∀ y ∈ Cb, pi (x * y) = pi x * pi y
  one : pi 1 = 1
  surj : ∀ y : Y, ∃ x ∈ Cb, pi x = y
  ker : ∀ x ∈ Cb, pi x = 1 → x * x = 1 → x = 1
  zb_sq : zb * zb = 1
  Cb_iff : ∀ x : X, x ∈ Cb ↔ x * zb = zb * x
  pi_zb : pi zb = ζ

variable {W : Subgroup Y} {ζ a : Y} {Cb : Subgroup X} {pi : X → Y} {zb : X}

theorem Setup.zb_mem (hS : Setup W ζ a Cb pi zb) : zb ∈ Cb := (hS.Cb_iff zb).2 rfl

theorem Setup.zb_ne (hS : Setup W ζ a Cb pi zb) : zb ≠ 1 := by
  intro h
  apply hS.bar.ζ_ne
  rw [← hS.pi_zb, h, hS.one]

theorem Setup.pi_inv (hS : Setup W ζ a Cb pi zb) {x : X} (hx : x ∈ Cb) : pi x⁻¹ = (pi x)⁻¹ := by
  have := hS.mul x hx x⁻¹ (Cb.inv_mem hx)
  rw [mul_inv_cancel, hS.one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem Setup.pi_comm (hS : Setup W ζ a Cb pi zb) {x y : X} (hx : x ∈ Cb) (hy : y ∈ Cb) :
    pi ⁅x, y⁆ = ⁅pi x, pi y⁆ := by
  have hxi := Cb.inv_mem hx
  have hyi := Cb.inv_mem hy
  simp only [commutatorElement_def]
  rw [hS.mul _ (Cb.mul_mem (Cb.mul_mem hx hy) hxi) _ hyi, hS.mul _ (Cb.mul_mem hx hy) _ hxi,
    hS.mul _ hx _ hy, hS.pi_inv hx, hS.pi_inv hy]

theorem Setup.pi_conj (hS : Setup W ζ a Cb pi zb) {x y : X} (hx : x ∈ Cb) (hy : y ∈ Cb) :
    pi (x * y * x⁻¹) = pi x * pi y * (pi x)⁻¹ := by
  rw [hS.mul _ (Cb.mul_mem hx hy) _ (Cb.inv_mem hx), hS.mul _ hx _ hy, hS.pi_inv hx]

def Setup.img (hS : Setup W ζ a Cb pi zb) (E : Subgroup X) (hE : E ≤ Cb) : Subgroup Y where
  carrier := {y | ∃ e ∈ E, pi e = y}
  mul_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    exact ⟨e * e', E.mul_mem he he', hS.mul e (hE he) e' (hE he')⟩
  one_mem' := ⟨1, E.one_mem, hS.one⟩
  inv_mem' := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e⁻¹, E.inv_mem he, hS.pi_inv (hE he)⟩

theorem Setup.mem_img (hS : Setup W ζ a Cb pi zb) {E : Subgroup X} (hE : E ≤ Cb) {y : Y} :
    y ∈ hS.img E hE ↔ ∃ e ∈ E, pi e = y := Iff.rfl

theorem Setup.img_normal (hS : Setup W ζ a Cb pi zb) {E : Subgroup X} (hE : E ≤ Cb)
    (hEn : ∀ c ∈ Cb, ∀ e ∈ E, c * e * c⁻¹ ∈ E) : (hS.img E hE).Normal := by
  refine ⟨fun m hm g => ?_⟩
  obtain ⟨e, he, rfl⟩ := (hS.mem_img hE).1 hm
  obtain ⟨c, hc, rfl⟩ := hS.surj g
  exact (hS.mem_img hE).2 ⟨c * e * c⁻¹, hEn c hc e he, hS.pi_conj hc (hE he)⟩

theorem Setup.img_exp2 (hS : Setup W ζ a Cb pi zb) {E : Subgroup X} (hE : E ≤ Cb)
    (hE2 : ∀ e ∈ E, e * e = 1) : ∀ m ∈ hS.img E hE, m * m = 1 := by
  intro m hm
  obtain ⟨e, he, rfl⟩ := (hS.mem_img hE).1 hm
  rw [← hS.mul e (hE he) e (hE he), hE2 e he, hS.one]

theorem Setup.eq_of_pi_eq (hS : Setup W ζ a Cb pi zb) {E : Subgroup X} (hE : E ≤ Cb)
    (hE2 : ∀ e ∈ E, e * e = 1) : ∀ e ∈ E, ∀ e' ∈ E, pi e = pi e' → e = e' := by
  intro e he e' he' hee
  have h1 : pi (e⁻¹ * e') = 1 := by
    rw [hS.mul _ (Cb.inv_mem (hE he)) _ (hE he'), hS.pi_inv (hE he), ← hee, inv_mul_cancel]
  have h2 : (e⁻¹ * e') * (e⁻¹ * e') = 1 := hE2 _ (E.mul_mem (E.inv_mem he) he')
  have := hS.ker _ (Cb.mul_mem (Cb.inv_mem (hE he)) (hE he')) h1 h2
  exact (inv_mul_eq_one.1 this)

theorem Setup.card_img (hS : Setup W ζ a Cb pi zb) {E : Subgroup X} (hE : E ≤ Cb)
    (hE2 : ∀ e ∈ E, e * e = 1) : Nat.card ↥(hS.img E hE) = Nat.card ↥E := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun e : ↥E => (⟨pi e, e, e.2, rfl⟩ : ↥(hS.img E hE))) ⟨?_, ?_⟩)
  · intro e e' hee
    exact Subtype.ext (hS.eq_of_pi_eq hE hE2 e e.2 e' e'.2 (congrArg Subtype.val hee))
  · rintro ⟨y, hy⟩
    obtain ⟨e, he, rfl⟩ := (hS.mem_img hE).1 hy
    exact ⟨⟨e, he⟩, rfl⟩

theorem Setup.pi_mem_W (hS : Setup W ζ a Cb pi zb) {E : Subgroup X} (hE : E ≤ Cb)
    (hEn : ∀ c ∈ Cb, ∀ e ∈ E, c * e * c⁻¹ ∈ E) (hE2 : ∀ e ∈ E, e * e = 1) {e : X} (he : e ∈ E) :
    pi e ∈ W :=
  hS.bar.two_core _ (hS.img_normal hE hEn) (hS.img_exp2 hE hE2) ((hS.mem_img hE).2 ⟨e, he, rfl⟩)

theorem Setup.zb_mem_of_fixed [Finite Y] (hS : Setup W ζ a Cb pi zb) {A : Subgroup X} (hAn : A.Normal)
    (hA2 : ∀ e ∈ A, e * e = 1) {b : X} (hbA : b ∈ A) (hbC : b ∈ Cb) (hb1 : b ≠ 1) : zb ∈ A := by
  have hE₁C : A ⊓ Cb ≤ Cb := inf_le_right
  have hE₁n : ∀ c ∈ Cb, ∀ e ∈ A ⊓ Cb, c * e * c⁻¹ ∈ A ⊓ Cb := fun c hc e he =>
    ⟨hAn.conj_mem e he.1 c, Cb.mul_mem (Cb.mul_mem hc he.2) (Cb.inv_mem hc)⟩
  have hE₁2 : ∀ e ∈ A ⊓ Cb, e * e = 1 := fun e he => hA2 e he.1
  have hMn := hS.img_normal hE₁C hE₁n
  have hM2 := hS.img_exp2 hE₁C hE₁2
  have hM1 : hS.img (A ⊓ Cb) hE₁C ≠ ⊥ := by
    intro h
    have : pi b ∈ hS.img (A ⊓ Cb) hE₁C := (hS.mem_img hE₁C).2 ⟨b, ⟨hbA, hbC⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hb1 (hS.ker b hbC this (hA2 b hbA))
  obtain ⟨hζM, -⟩ := hS.bar.dichotomy hMn hM2 hM1
  obtain ⟨e, ⟨heA, heC⟩, hpe⟩ := (hS.mem_img hE₁C).1 hζM
  have hcomm : e * zb = zb * e := (hS.Cb_iff e).1 heC
  have hsq : (e * zb) * (e * zb) = 1 := by
    calc (e * zb) * (e * zb) = e * (zb * e) * zb := by group
      _ = e * (e * zb) * zb := by rw [← hcomm]
      _ = (e * e) * (zb * zb) := by group
      _ = 1 := by rw [hA2 e heA, hS.zb_sq, one_mul]
  have hpi : pi (e * zb) = 1 := by
    rw [hS.mul e heC zb hS.zb_mem, hpe, hS.pi_zb, hS.bar.ζ_sq]
  have h1 := hS.ker _ (Cb.mul_mem heC hS.zb_mem) hpi hsq
  have : e = zb⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hez : e = zb := by rw [this]; exact inv_eq_of_mul_eq_one_right hS.zb_sq
  rw [← hez]
  exact heA

theorem Setup.dich [Finite X] [Finite Y] (hS : Setup W ζ a Cb pi zb) {A : Subgroup X} (hAn : A.Normal)
    (hA2 : ∀ e ∈ A, e * e = 1) (hAC : A ≤ Cb) (hzA : zb ∈ A) :
    A = zpowers zb ∨ Nat.card ↥A = 8 := by
  have hMn := hS.img_normal hAC (fun c _ e he => hAn.conj_mem e he c)
  have hM2 := hS.img_exp2 hAC hA2
  have hM1 : hS.img A hAC ≠ ⊥ := by
    intro h
    have : ζ ∈ hS.img A hAC := (hS.mem_img hAC).2 ⟨zb, hzA, hS.pi_zb⟩
    rw [h, Subgroup.mem_bot] at this
    exact hS.bar.ζ_ne this
  obtain ⟨-, hd⟩ := hS.bar.dichotomy hMn hM2 hM1
  have hcardM := hS.card_img hAC hA2
  rcases hd with hd | hd
  · left
    have h2 : Nat.card ↥A = 2 := by
      rw [← hcardM, hd, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact hS.bar.ζ_sq) hS.bar.ζ_ne]
    have hz2 : Nat.card ↥(zpowers zb) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hS.zb_sq) hS.zb_ne]
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzA) (by rw [hz2, h2])).symm
  · right
    rw [← hcardM]
    exact hd

end Setup

section Trick

variable {X Y : Type*} [Group X] [Group Y] {W : Subgroup Y} {ζ a : Y} {Cb : Subgroup X}
  {pi : X → Y} {zb : X}

theorem zpowers_involution_iff (hz : zb * zb = 1) (x : X) :
    x ∈ zpowers zb ↔ x = 1 ∨ x = zb := by
  constructor
  · exact mem_zpowers_inv hz
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem Setup.trans_E [Finite X] [Finite Y] (hS : Setup W ζ a Cb pi zb)
    (hnc : ∃ g : X, g * zb ≠ zb * g) {E : Subgroup X} (hEn : E.Normal) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEC : E ≤ Cb) (hzE : zb ∈ E) (hE8 : Nat.card ↥E = 8) {e : X} (he : e ∈ E)
    (heZ : e ∉ zpowers zb) : ∃ g : X, g * zb * g⁻¹ = e := by
  classical
  have hY := hS.bar
  have hMn := hS.img_normal hEC (fun c _ e he => hEn.conj_mem e he c)
  have hM2 := hS.img_exp2 hEC hE2
  have hM8 : Nat.card ↥(hS.img E hEC) = 8 := by rw [hS.card_img hEC hE2, hE8]
  have hζM : ζ ∈ hS.img E hEC := (hS.mem_img hEC).2 ⟨zb, hzE, hS.pi_zb⟩
  have hpiE_inj := hS.eq_of_pi_eq hEC hE2
  have hzb_ne := hS.zb_ne
  have hzbZ := zpowers_involution_iff hS.zb_sq
  have hout : ∀ x ∈ E, x ∉ zpowers zb → pi x ∉ zpowers ζ := by
    intro x hx hxZ hpx
    apply hxZ
    rcases hY.mem_zpowers_iff.1 hpx with h1 | h1
    · have : x = 1 := hpiE_inj x hx 1 E.one_mem (h1.trans hS.one.symm)
      rw [this]; exact one_mem _
    · have : x = zb := hpiE_inj x hx zb hzE (h1.trans hS.pi_zb.symm)
      rw [this]; exact mem_zpowers _
  obtain ⟨g₀, hg₀⟩ := hnc
  have he₀E : g₀ * zb * g₀⁻¹ ∈ E := hEn.conj_mem zb hzE g₀
  have he₀Z : g₀ * zb * g₀⁻¹ ∉ zpowers zb := by
    rw [hzbZ]
    push Not
    constructor
    · intro h1
      apply hzb_ne
      have h2 : zb = g₀⁻¹ * (g₀ * zb * g₀⁻¹) * g₀ := by group
      rw [h2, h1]; group
    · intro h1
      apply hg₀
      calc g₀ * zb = (g₀ * zb * g₀⁻¹) * g₀ := by group
        _ = zb * g₀ := by rw [h1]
  obtain ⟨g, hg⟩ := hY.transitive hMn hM2 hM8 hζM
    (e := pi (g₀ * zb * g₀⁻¹)) (e' := pi e) ((hS.mem_img hEC).2 ⟨_, he₀E, rfl⟩)
    ((hS.mem_img hEC).2 ⟨e, he, rfl⟩) (hout _ he₀E he₀Z) (hout _ he heZ)
  obtain ⟨c, hc, hcg⟩ := hS.surj g
  have h1 : pi (c * (g₀ * zb * g₀⁻¹) * c⁻¹) = pi e := by
    rw [hS.pi_conj hc (hEC he₀E), hcg]; exact hg
  have hcE : c * (g₀ * zb * g₀⁻¹) * c⁻¹ ∈ E := hEn.conj_mem _ he₀E c
  have := hpiE_inj _ hcE e he h1
  exact ⟨c * g₀, by rw [← this]; group⟩

theorem Setup.h_trick [Finite X] [Finite Y] (hS : Setup W ζ a Cb pi zb)
    (hnc : ∃ g : X, g * zb ≠ zb * g) {E : Subgroup X} (hEn : E.Normal) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEC : E ≤ Cb) (hzE : zb ∈ E) (hE8 : Nat.card ↥E = 8) {t : X} (ht2 : t * t = 1) (htC : t ∈ Cb)
    (htW : pi t ∉ W) :
    ∃ u ∈ Cb, u * u = 1 ∧ pi u ∈ W ∧ u ∉ E ∧ ∃ g : X, g * t * g⁻¹ = u := by
  classical
  have hY := hS.bar
  have hMn := hS.img_normal hEC (fun c _ e he => hEn.conj_mem e he c)
  have hM2 := hS.img_exp2 hEC hE2
  have hM8 : Nat.card ↥(hS.img E hEC) = 8 := by rw [hS.card_img hEC hE2, hE8]
  have hzb_ne := hS.zb_ne
  have hzbZ := zpowers_involution_iff hS.zb_sq
  have hy2 : pi t * pi t = 1 := by rw [← hS.mul t htC t htC, ht2, hS.one]
  obtain ⟨m, hmM, hm⟩ := hY.outside hMn hM2 hM8 hy2 htW
  obtain ⟨e₁, he₁, rfl⟩ := (hS.mem_img hEC).1 hmM
  have hcE : ⁅e₁, t⁆ ∈ E := by
    simp only [commutatorElement_def]
    have : e₁ * t * e₁⁻¹ * t⁻¹ = e₁ * (t * e₁⁻¹ * t⁻¹) := by group
    rw [this]
    exact E.mul_mem he₁ (hEn.conj_mem _ (E.inv_mem he₁) t)
  have hpic : pi ⁅e₁, t⁆ = ⁅pi e₁, pi t⁆ := hS.pi_comm (hEC he₁) htC
  have hcZ : ⁅e₁, t⁆ ∉ zpowers zb := by
    intro hcz
    apply hm
    rw [← hpic]
    rcases (hzbZ _).1 hcz with h1 | h1
    · rw [h1, hS.one]; exact one_mem _
    · rw [h1, hS.pi_zb]; exact mem_zpowers _
  have hc1 : ⁅e₁, t⁆ ≠ 1 := fun h1 => hcZ (by rw [h1]; exact one_mem _)
  obtain ⟨g, hg⟩ := hS.trans_E hnc hEn hE2 hEC hzE hE8 hcE hcZ
  obtain ⟨h, hhdef⟩ : ∃ h, h = g⁻¹ := ⟨_, rfl⟩
  have hhc : h * ⁅e₁, t⁆ * h⁻¹ = zb := by
    rw [← hg, hhdef]; group
  obtain ⟨u, hudef⟩ : ∃ u, u = h * t * h⁻¹ := ⟨_, rfl⟩
  have hu2 : u * u = 1 := by
    rw [hudef]
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hE_comm := exp2_comm hE2
  have huE : ∀ e ∈ E, u * e * u⁻¹ ∈ E := by
    intro e he
    rw [hudef]
    have h' : h⁻¹ * e * h ∈ E := by simpa using hEn.conj_mem e he h⁻¹
    have : h * t * h⁻¹ * e * (h * t * h⁻¹)⁻¹ = h * (t * (h⁻¹ * e * h) * t⁻¹) * h⁻¹ := by group
    rw [this]
    exact hEn.conj_mem _ (hEn.conj_mem _ h' t) h
  have hcomm_u : ∀ e ∈ E, ⁅e, u⁆ = 1 ∨ ⁅e, u⁆ = zb := by
    intro e he
    have he' : h⁻¹ * e * h ∈ E := by simpa using hEn.conj_mem e he h⁻¹
    have hconj : ⁅e, u⁆ = h * ⁅h⁻¹ * e * h, t⁆ * h⁻¹ := by
      rw [hudef]; simp only [commutatorElement_def]; group
    by_cases h0 : ⁅h⁻¹ * e * h, t⁆ = 1
    · left; rw [hconj, h0]; group
    · right
      have := comm_unique hE2 hE8 ht2 (fun e he => hEn.conj_mem e he t) he₁ he' hc1 h0
      rw [hconj, this]; exact hhc
  have he₂E : h * e₁ * h⁻¹ ∈ E := hEn.conj_mem e₁ he₁ h
  have hzbc : ⁅h * e₁ * h⁻¹, u⁆ = zb := by
    rw [hudef]
    calc ⁅h * e₁ * h⁻¹, h * t * h⁻¹⁆ = h * ⁅e₁, t⁆ * h⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = zb := hhc
  have huC : u ∈ Cb := by
    rw [hS.Cb_iff]
    have he₂i : (h * e₁ * h⁻¹)⁻¹ = h * e₁ * h⁻¹ := inv_eq_of_mul_eq_one_right (hE2 _ he₂E)
    have hfE : u * (h * e₁ * h⁻¹) * u⁻¹ ∈ E := huE _ he₂E
    have huu : u * (u * (h * e₁ * h⁻¹) * u⁻¹) * u⁻¹ = h * e₁ * h⁻¹ := by
      calc u * (u * (h * e₁ * h⁻¹) * u⁻¹) * u⁻¹ = (u * u) * (h * e₁ * h⁻¹) * (u * u)⁻¹ := by group
        _ = h * e₁ * h⁻¹ := by rw [hu2]; group
    have hzb' : zb = (h * e₁ * h⁻¹) * (u * (h * e₁ * h⁻¹) * u⁻¹) := by
      calc zb = ⁅h * e₁ * h⁻¹, u⁆ := hzbc.symm
        _ = (h * e₁ * h⁻¹) * u * (h * e₁ * h⁻¹)⁻¹ * u⁻¹ := rfl
        _ = (h * e₁ * h⁻¹) * (u * (h * e₁ * h⁻¹) * u⁻¹) := by rw [he₂i]; group
    have hconj : u * zb * u⁻¹ = zb := by
      calc u * zb * u⁻¹ = (u * (h * e₁ * h⁻¹) * u⁻¹) * (u * (u * (h * e₁ * h⁻¹) * u⁻¹) * u⁻¹) := by
            rw [hzb']; group
        _ = (u * (h * e₁ * h⁻¹) * u⁻¹) * (h * e₁ * h⁻¹) := by rw [huu]
        _ = (h * e₁ * h⁻¹) * (u * (h * e₁ * h⁻¹) * u⁻¹) := hE_comm _ hfE _ he₂E
        _ = zb := hzb'.symm
    calc u * zb = (u * zb * u⁻¹) * u := by group
      _ = zb * u := by rw [hconj]
  have hpiuW : pi u ∈ W := by
    by_contra hnW
    have hy2' : pi u * pi u = 1 := by rw [← hS.mul u huC u huC, hu2, hS.one]
    obtain ⟨m', hm'M, hm'⟩ := hY.outside hMn hM2 hM8 hy2' hnW
    obtain ⟨e₃, he₃, rfl⟩ := (hS.mem_img hEC).1 hm'M
    apply hm'
    rw [← hS.pi_comm (hEC he₃) huC]
    rcases hcomm_u e₃ he₃ with h1 | h1
    · rw [h1, hS.one]; exact one_mem _
    · rw [h1, hS.pi_zb]; exact mem_zpowers _
  have huNE : u ∉ E := by
    intro huE'
    have h1 : ⁅h * e₁ * h⁻¹, u⁆ = 1 :=
      (commutatorElement_eq_one_iff_mul_comm).2 (hE_comm _ he₂E _ huE')
    rw [hzbc] at h1
    exact hzb_ne h1
  exact ⟨u, huC, hu2, hpiuW, huNE, h, by rw [hudef]⟩

theorem Setup.final_contra [Finite X] [Finite Y] (hS : Setup W ζ a Cb pi zb)
    (hnc : ∃ g : X, g * zb ≠ zb * g) {E : Subgroup X} (hEn : E.Normal) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEC : E ≤ Cb) (hzE : zb ∈ E) (hE8 : Nat.card ↥E = 8) {Sb : Subgroup X} (hES : E ≤ Sb)
    (hSconj : ∀ u ∈ Cb, u * u = 1 → ∃ c ∈ Cb, c * u * c⁻¹ ∈ Sb) {Cls : X → Prop}
    (hCls : ∀ x y : X, Cls x → (∃ g : X, g * x * g⁻¹ = y) → Cls y) (hCzb : Cls zb) {t : X}
    (ht2 : t * t = 1) (htC : t ∈ Cb) (htW : pi t ∉ W) (hCt : Cls t)
    (hcount : {u : X | u ∈ Sb ∧ u * u = 1 ∧ u ≠ 1 ∧ pi u ∈ W ∧ Cls u}.ncard ≤ 7) : False := by
  classical
  have hEn' : ∀ c ∈ Cb, ∀ e ∈ E, c * e * c⁻¹ ∈ E := fun c _ e he => hEn.conj_mem e he c
  have hzbZ := zpowers_involution_iff hS.zb_sq
  obtain ⟨u, huC, hu2, huW, huE, g, hgt⟩ := hS.h_trick hnc hEn hE2 hEC hzE hE8 ht2 htC htW
  obtain ⟨c, hcC, hcu⟩ := hSconj u huC hu2
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set X, Ω = {u : X | u ∈ Sb ∧ u * u = 1 ∧ u ≠ 1 ∧ pi u ∈ W ∧ Cls u} :=
    ⟨_, rfl⟩
  rw [← hΩ] at hcount
  have hE1 : (E : Set X) \ {1} ⊆ Ω := by
    rintro e ⟨heE, he1⟩
    have he1' : e ≠ 1 := he1
    rw [hΩ]
    simp only [Set.mem_ofPred_eq]
    refine ⟨hES heE, hE2 e heE, he1', hS.pi_mem_W hEC hEn' hE2 heE, ?_⟩
    by_cases hez : e = zb
    · rw [hez]; exact hCzb
    · have hnz : e ∉ zpowers zb := by
        rw [hzbZ]; push Not; exact ⟨he1', hez⟩
      obtain ⟨g', hg'⟩ := hS.trans_E hnc hEn hE2 hEC hzE hE8 heE hnz
      exact hCls zb e hCzb ⟨g', hg'⟩
  have hu1 : u ≠ 1 := fun h1 => huE (by rw [h1]; exact E.one_mem)
  have hu'Ω : c * u * c⁻¹ ∈ Ω := by
    rw [hΩ]
    simp only [Set.mem_ofPred_eq]
    refine ⟨hcu, ?_, ?_, ?_, ?_⟩
    · calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    · intro h1
      apply hu1
      have : u = c⁻¹ * (c * u * c⁻¹) * c := by group
      rw [this, h1]; group
    · rw [hS.pi_conj hcC huC]
      exact hS.bar.W_normal.conj_mem _ huW _
    · exact hCls t _ hCt ⟨c * g, by rw [← hgt]; group⟩
  have hu'E : c * u * c⁻¹ ∉ (E : Set X) \ {1} := by
    rintro ⟨hE', -⟩
    apply huE
    have : u = c⁻¹ * (c * u * c⁻¹) * c := by group
    have h2 := hEn.conj_mem _ hE' c⁻¹
    rw [inv_inv] at h2
    rw [this]
    exact h2
  have h7 : ((E : Set X) \ {1}).ncard = 7 := by
    rw [Set.ncard_sdiff_singleton_of_mem (by exact E.one_mem)]
    have : (E : Set X).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hE8
    omega
  have h8 : (insert (c * u * c⁻¹) ((E : Set X) \ {1})).ncard = 8 := by
    rw [Set.ncard_insert_of_notMem hu'E (Set.toFinite _), h7]
  have hsub : insert (c * u * c⁻¹) ((E : Set X) \ {1}) ⊆ Ω := Set.insert_subset hu'Ω hE1
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem mem_center_of_normal_zpowers {zb : X} (hz2 : zb * zb = 1) (hzb1 : zb ≠ 1)
    (hn : (zpowers zb).Normal) : zb ∈ center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g * zb * g⁻¹ ∈ zpowers zb := hn.conj_mem zb (mem_zpowers zb) g
  rcases (zpowers_involution_iff hz2 _).1 hg with h | h
  · exfalso
    apply hzb1
    have h2 : zb = g⁻¹ * (g * zb * g⁻¹) * g := by group
    rw [h2, h]
    group
  · exact mul_inv_eq_iff_eq_mul.1 h

end Trick

end CFSG.GH74.GLS.Stage2.Local.P34M12
