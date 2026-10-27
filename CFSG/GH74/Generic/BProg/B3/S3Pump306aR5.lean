module

public import CFSG.GH74.Generic.Certificates
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

variable {n : ℕ}

@[expose] def cj (σ : Perm (Fin n)) (a : alternatingGroup (Fin n)) : alternatingGroup (Fin n) :=
  ⟨σ * (a : Perm (Fin n)) * σ⁻¹, (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem a a.2 σ⟩

theorem mul_swap' (f : Perm (Fin n)) (x y : Fin n) : f * swap x y = swap (f x) (f y) * f :=
  Equiv.mul_swap_eq_swap_mul f x y

theorem v4_comm (p2 p3 p4 p5 : Fin n) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h25 : p2 ≠ p5)
    (h34 : p3 ≠ p4) (h35 : p3 ≠ p5) (h45 : p4 ≠ p5) :
    (swap p2 p3 * swap p4 p5) * (swap p2 p4 * swap p3 p5) =
      (swap p2 p4 * swap p3 p5) * (swap p2 p3 * swap p4 p5) := by
  obtain ⟨α, hα⟩ : ∃ α : Perm (Fin n), α = swap p2 p3 * swap p4 p5 := ⟨_, rfl⟩
  rw [← hα]
  have e2 : α p2 = p3 := by simp [hα, Perm.mul_apply, swap_apply_of_ne_of_ne h24 h25]
  have e3 : α p3 = p2 := by simp [hα, Perm.mul_apply, swap_apply_of_ne_of_ne h34 h35]
  have e4 : α p4 = p5 := by simp [hα, Perm.mul_apply, swap_apply_of_ne_of_ne h25.symm h35.symm]
  have e5 : α p5 = p4 := by simp [hα, Perm.mul_apply, swap_apply_of_ne_of_ne h24.symm h34.symm]
  have hd : swap p3 p5 * swap p2 p4 = swap p2 p4 * swap p3 p5 := by
    have : Perm.Disjoint (swap p2 p4) (swap p3 p5) :=
      Equiv.Perm.disjoint_swap_swap (by simp [h24, h23, h25, h34.symm, h45, h35])
    exact (this.commute).eq.symm
  calc α * (swap p2 p4 * swap p3 p5) = (α * swap p2 p4) * swap p3 p5 := by rw [mul_assoc]
    _ = (swap p3 p5 * α) * swap p3 p5 := by rw [mul_swap' α p2 p4, e2, e4]
    _ = swap p3 p5 * (α * swap p3 p5) := by rw [mul_assoc]
    _ = swap p3 p5 * (swap p2 p4 * α) := by rw [mul_swap' α p3 p5, e3, e5]
    _ = (swap p3 p5 * swap p2 p4) * α := by rw [mul_assoc]
    _ = (swap p2 p4 * swap p3 p5) * α := by rw [hd]

section Action

variable {Y : Type} [Group Y]

@[expose] def ActsAs (s : Y) (ι : alternatingGroup (Fin n) →* Y) (σ : Perm (Fin n)) : Prop :=
  ∀ a, s * ι a * s⁻¹ = ι (cj σ a)

theorem x4_conj {ι ι' : alternatingGroup (Fin n) →* Y} (hcomm : ∀ a b, ι a * ι' b = ι' b * ι a) {s : Y}
    {σ τ : Perm (Fin n)} (hσ : σ * σ = 1) (hs : ActsAs s ι σ) (l l' : alternatingGroup (Fin n))
    (hl : (l : Perm (Fin n)) = τ * σ) (a : alternatingGroup (Fin n)) :
    (ι l * ι' l' * s) * ι a * (ι l * ι' l' * s)⁻¹ = ι (cj τ a) := by
  have e1 : (ι l * ι' l' * s) * ι a * (ι l * ι' l' * s)⁻¹ =
      ι l * (ι' l' * (s * ι a * s⁻¹) * (ι' l')⁻¹) * (ι l)⁻¹ := by group
  rw [e1, hs a]
  have e2 : ι' l' * ι (cj σ a) * (ι' l')⁻¹ = ι (cj σ a) := by
    rw [← hcomm (cj σ a) l']
    group
  rw [e2, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  show (l : Perm (Fin n)) * (σ * (a : Perm (Fin n)) * σ⁻¹) * (l : Perm (Fin n))⁻¹ =
    τ * (a : Perm (Fin n)) * τ⁻¹
  rw [hl, mul_inv_rev, hσinv]
  calc τ * σ * (σ * (a : Perm (Fin n)) * σ) * (σ * τ⁻¹)
      = τ * (σ * σ) * (a : Perm (Fin n)) * (σ * σ) * τ⁻¹ := by group
    _ = τ * (a : Perm (Fin n)) * τ⁻¹ := by rw [hσ]; group

theorem x4_sq {ι ι' : alternatingGroup (Fin n) →* Y} (hcomm : ∀ a b, ι a * ι' b = ι' b * ι a) {s : Y}
    (hs2 : s * s = 1) {σ σ' τ : Perm (Fin n)} (hσ : σ * σ = 1) (hσ' : σ' * σ' = 1) (hτ : τ * τ = 1)
    (hs : ActsAs s ι σ) (hs' : ActsAs s ι' σ') (l l' : alternatingGroup (Fin n))
    (hl : (l : Perm (Fin n)) = τ * σ) (hl' : (l' : Perm (Fin n)) = τ * σ') :
    (ι l * ι' l' * s) * (ι l * ι' l' * s) = 1 := by
  have e1 : (ι l * ι' l' * s) * (ι l * ι' l' * s) =
      ι l * ι' l' * (s * ι l * s⁻¹) * (s * ι' l' * s⁻¹) * (s * s) := by group
  rw [e1, hs l, hs' l', hs2]
  have e2 : ι' l' * ι (cj σ l) = ι (cj σ l) * ι' l' := (hcomm _ _).symm
  have e3 : ι l * ι' l' * ι (cj σ l) * ι' (cj σ' l') * 1 =
      (ι l * ι (cj σ l)) * (ι' l' * ι' (cj σ' l')) := by
    rw [mul_one, mul_assoc (ι l), e2]
    group
  rw [e3, ← map_mul, ← map_mul]
  have f1 : l * cj σ l = 1 := by
    apply Subtype.ext
    have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
    show (l : Perm (Fin n)) * (σ * (l : Perm (Fin n)) * σ⁻¹) = 1
    rw [hl, hσinv]
    calc τ * σ * (σ * (τ * σ) * σ) = τ * (σ * σ) * τ * (σ * σ) := by group
      _ = 1 := by simp [hσ, hτ]
  have f2 : l' * cj σ' l' = 1 := by
    apply Subtype.ext
    have hσinv : σ'⁻¹ = σ' := inv_eq_of_mul_eq_one_right hσ'
    show (l' : Perm (Fin n)) * (σ' * (l' : Perm (Fin n)) * σ'⁻¹) = 1
    rw [hl', hσinv]
    calc τ * σ' * (σ' * (τ * σ') * σ') = τ * (σ' * σ') * τ * (σ' * σ') := by group
      _ = 1 := by simp [hσ', hτ]
  rw [f1, f2, map_one, map_one, mul_one]

end Action

section Main

variable {Y : Type} [Group Y]

theorem eq_one_of_central (hn : 4 ≤ n) {p : alternatingGroup (Fin n)}
    (hp : ∀ b : alternatingGroup (Fin n), p * b = b * p) : p = 1 := by
  have : (p : Perm (Fin n)) = 1 := by
    refine CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by simpa using hn) fun g hg => ?_
    exact congrArg Subtype.val (hp ⟨g, hg⟩)
  exact Subtype.ext this

theorem eq_one_of_mul_eq_one (hn : 4 ≤ n) {ι₁ ι₂ : alternatingGroup (Fin n) →* Y}
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) {u v : alternatingGroup (Fin n)}
    (h : ι₁ u * ι₂ v = 1) : u = 1 ∧ v = 1 := by
  have h1 : ι₁ u = (ι₂ v)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hu : u = 1 := by
    apply eq_one_of_central hn
    intro b
    apply hι₁
    rw [map_mul, map_mul, h1, ← map_inv]
    exact (hcomm b v⁻¹).symm
  refine ⟨hu, ?_⟩
  rw [hu, map_one, one_mul] at h
  apply hι₂
  rw [h, map_one]

theorem perm_eq_one_of_cj (hn : 4 ≤ n) {τ : Perm (Fin n)} (h : ∀ a, cj τ a = a) : τ = 1 := by
  refine CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
    (by simpa using hn) fun g hg => ?_
  have h1 := congrArg Subtype.val (h ⟨g, hg⟩)
  have h2 : τ * g * τ⁻¹ = g := h1
  calc τ * g = (τ * g * τ⁻¹) * τ := by group
    _ = g * τ := by rw [h2]

theorem sign_eq_one_of_cj (hn : 4 ≤ n) {σ : Perm (Fin n)} (a₀ : alternatingGroup (Fin n))
    (h : ∀ a, cj σ a = a₀ * a * a₀⁻¹) : Perm.sign σ = 1 := by
  have hcent : σ⁻¹ * (a₀ : Perm (Fin n)) = 1 := by
    refine CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by simpa using hn) fun g hg => ?_
    have h1 := congrArg Subtype.val (h ⟨g, hg⟩)
    have h2 : σ * g * σ⁻¹ = (a₀ : Perm (Fin n)) * g * (a₀ : Perm (Fin n))⁻¹ := h1
    calc σ⁻¹ * (a₀ : Perm (Fin n)) * g
        = σ⁻¹ * ((a₀ : Perm (Fin n)) * g * (a₀ : Perm (Fin n))⁻¹) * (a₀ : Perm (Fin n)) := by group
      _ = σ⁻¹ * (σ * g * σ⁻¹) * (a₀ : Perm (Fin n)) := by rw [h2]
      _ = g * (σ⁻¹ * (a₀ : Perm (Fin n))) := by group
  have hσm : σ = (a₀ : Perm (Fin n)) := by
    have := congrArg (fun f => σ * f) hcent
    simpa using this.symm
  rw [hσm]
  exact Perm.mem_alternatingGroup.1 a₀.2

theorem not_s_mem (hn : 4 ≤ n) {ι₁ ι₂ : alternatingGroup (Fin n) →* Y} (hι₁ : Function.Injective ι₁)
    (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) {s : Y} {σ₁ : Perm (Fin n)}
    (hodd : Perm.sign σ₁ = -1) (hs₁ : ActsAs s ι₁ σ₁) (m₁ m₂ : alternatingGroup (Fin n))
    (hs : s = ι₁ m₁ * ι₂ m₂) : False := by
  have key : ∀ a, cj σ₁ a = m₁ * a * m₁⁻¹ := by
    intro a
    apply hι₁
    rw [← hs₁ a, hs]
    have e1 : (ι₁ m₁ * ι₂ m₂) * ι₁ a * (ι₁ m₁ * ι₂ m₂)⁻¹ =
        ι₁ m₁ * (ι₂ m₂ * ι₁ a * (ι₂ m₂)⁻¹) * (ι₁ m₁)⁻¹ := by group
    have e2 : ι₂ m₂ * ι₁ a * (ι₂ m₂)⁻¹ = ι₁ a := by
      rw [← hcomm a m₂]; group
    rw [e1, e2, ← map_inv, ← map_mul, ← map_mul]
  have hs1 := sign_eq_one_of_cj hn m₁ key
  rw [hodd] at hs1
  exact absurd hs1 (by decide)

theorem not_gen4_of_two_alt [Finite Y] (hn : 6 ≤ n) {ι₁ ι₂ : alternatingGroup (Fin n) →* Y}
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) {s : Y} (hs2 : s * s = 1) {σ₁ σ₂ : Perm (Fin n)}
    (hσ₁ : σ₁ * σ₁ = 1) (hσ₂ : σ₂ * σ₂ = 1) (hodd₁ : Perm.sign σ₁ = -1) (hodd₂ : Perm.sign σ₂ = -1)
    (hs₁ : ActsAs s ι₁ σ₁) (hs₂ : ActsAs s ι₂ σ₂) : ¬ CFSG.GH74.Gen4 Y := by
  classical
  intro hgen
  set p : Fin 6 → Fin n := fun i => Fin.castLE hn i with hp
  have hpinj : Function.Injective p := Fin.castLE_injective hn
  have hne : ∀ i j : Fin 6, i ≠ j → p i ≠ p j := fun i j h h' => h (hpinj h')
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h03 := hne 0 3 (by decide)
  have h04 := hne 0 4 (by decide)
  have h05 := hne 0 5 (by decide)
  have h12 := hne 1 2 (by decide)
  have h13 := hne 1 3 (by decide)
  have h14 := hne 1 4 (by decide)
  have h15 := hne 1 5 (by decide)
  have h23 := hne 2 3 (by decide)
  have h24 := hne 2 4 (by decide)
  have h25 := hne 2 5 (by decide)
  have h34 := hne 3 4 (by decide)
  have h35 := hne 3 5 (by decide)
  have h45 := hne 4 5 (by decide)
  obtain ⟨τ, hτdef⟩ : ∃ τ : Perm (Fin n), τ = swap (p 0) (p 1) := ⟨_, rfl⟩
  obtain ⟨a1, ha1def⟩ : ∃ a : Perm (Fin n), a = swap (p 2) (p 3) * swap (p 4) (p 5) := ⟨_, rfl⟩
  obtain ⟨a2, ha2def⟩ : ∃ a : Perm (Fin n), a = swap (p 2) (p 4) * swap (p 3) (p 5) := ⟨_, rfl⟩
  have hτ2 : τ * τ = 1 := by rw [hτdef]; exact swap_mul_self _ _
  have hτodd : Perm.sign τ = -1 := by rw [hτdef]; exact Perm.sign_swap h01
  have hcomm_swap : ∀ {x y z t : Fin n}, [x, y, z, t].Nodup →
      swap x y * swap z t = swap z t * swap x y :=
    fun h => (Equiv.Perm.disjoint_swap_swap h).commute.eq
  have ha1sq : a1 * a1 = 1 := by
    have hc := hcomm_swap (x := p 2) (y := p 3) (z := p 4) (t := p 5)
      (by simp [h23, h24, h25, h34, h35, h45])
    rw [ha1def]
    calc swap (p 2) (p 3) * swap (p 4) (p 5) * (swap (p 2) (p 3) * swap (p 4) (p 5))
        = swap (p 2) (p 3) * (swap (p 4) (p 5) * swap (p 2) (p 3)) * swap (p 4) (p 5) := by group
      _ = swap (p 2) (p 3) * (swap (p 2) (p 3) * swap (p 4) (p 5)) * swap (p 4) (p 5) := by
        rw [← hc]
      _ = 1 := by simp [← mul_assoc, swap_mul_self]
  have ha2sq : a2 * a2 = 1 := by
    have hc := hcomm_swap (x := p 2) (y := p 4) (z := p 3) (t := p 5)
      (by simp [h24, h23, h25, h34.symm, h45, h35])
    rw [ha2def]
    calc swap (p 2) (p 4) * swap (p 3) (p 5) * (swap (p 2) (p 4) * swap (p 3) (p 5))
        = swap (p 2) (p 4) * (swap (p 3) (p 5) * swap (p 2) (p 4)) * swap (p 3) (p 5) := by group
      _ = swap (p 2) (p 4) * (swap (p 2) (p 4) * swap (p 3) (p 5)) * swap (p 3) (p 5) := by
        rw [← hc]
      _ = 1 := by simp [← mul_assoc, swap_mul_self]
  have ha12 : a1 * a2 = a2 * a1 := by
    rw [ha1def, ha2def]; exact v4_comm (p 2) (p 3) (p 4) (p 5) h23 h24 h25 h34 h35 h45
  have hτa1 : τ * a1 = a1 * τ := by
    rw [hτdef, ha1def]
    have c1 := hcomm_swap (x := p 0) (y := p 1) (z := p 2) (t := p 3)
      (by simp [h01, h02, h03, h12, h13, h23])
    have c2 := hcomm_swap (x := p 0) (y := p 1) (z := p 4) (t := p 5)
      (by simp [h01, h04, h05, h14, h15, h45])
    calc swap (p 0) (p 1) * (swap (p 2) (p 3) * swap (p 4) (p 5))
        = (swap (p 0) (p 1) * swap (p 2) (p 3)) * swap (p 4) (p 5) := by rw [mul_assoc]
      _ = swap (p 2) (p 3) * (swap (p 0) (p 1) * swap (p 4) (p 5)) := by rw [c1, mul_assoc]
      _ = swap (p 2) (p 3) * (swap (p 4) (p 5) * swap (p 0) (p 1)) := by rw [c2]
      _ = (swap (p 2) (p 3) * swap (p 4) (p 5)) * swap (p 0) (p 1) := by rw [mul_assoc]
  have hτa2 : τ * a2 = a2 * τ := by
    rw [hτdef, ha2def]
    have c1 := hcomm_swap (x := p 0) (y := p 1) (z := p 2) (t := p 4)
      (by simp [h01, h02, h04, h12, h14, h24])
    have c2 := hcomm_swap (x := p 0) (y := p 1) (z := p 3) (t := p 5)
      (by simp [h01, h03, h05, h13, h15, h35])
    calc swap (p 0) (p 1) * (swap (p 2) (p 4) * swap (p 3) (p 5))
        = (swap (p 0) (p 1) * swap (p 2) (p 4)) * swap (p 3) (p 5) := by rw [mul_assoc]
      _ = swap (p 2) (p 4) * (swap (p 0) (p 1) * swap (p 3) (p 5)) := by rw [c1, mul_assoc]
      _ = swap (p 2) (p 4) * (swap (p 3) (p 5) * swap (p 0) (p 1)) := by rw [c2]
      _ = (swap (p 2) (p 4) * swap (p 3) (p 5)) * swap (p 0) (p 1) := by rw [mul_assoc]
  have ha1even : Perm.sign a1 = 1 := by
    rw [ha1def, Perm.sign_mul, Perm.sign_swap h23, Perm.sign_swap h45]; norm_num
  have ha2even : Perm.sign a2 = 1 := by
    rw [ha2def, Perm.sign_mul, Perm.sign_swap h24, Perm.sign_swap h35]; norm_num
  have e1 : a1 (p 2) = p 3 := by
    rw [ha1def]; simp [Perm.mul_apply, swap_apply_of_ne_of_ne h24 h25]
  have e2 : a2 (p 2) = p 4 := by
    rw [ha2def]; simp [Perm.mul_apply, swap_apply_of_ne_of_ne h23 h25]
  have e1' : a1 (p 4) = p 5 := by
    rw [ha1def]; simp [Perm.mul_apply, swap_apply_of_ne_of_ne h25.symm h35.symm]
  have hind : ∀ e₁ e₂ : ℕ, e₁ ≤ 1 → e₂ ≤ 1 → a1 ^ e₁ * a2 ^ e₂ = 1 → e₁ = 0 ∧ e₂ = 0 := by
    intro e₁ e₂ h₁ h₂ h
    interval_cases e₁ <;> interval_cases e₂
    · exact ⟨rfl, rfl⟩
    · exfalso
      have := congrArg (fun f : Perm (Fin n) => f (p 2)) h
      simp [e2] at this
      exact h24 this.symm
    · exfalso
      have := congrArg (fun f : Perm (Fin n) => f (p 2)) h
      simp [e1] at this
      exact h23 this.symm
    · exfalso
      have := congrArg (fun f : Perm (Fin n) => f (p 2)) h
      simp [Perm.mul_apply, e2, e1'] at this
      exact h25 this.symm
  have hmem : ∀ f : Perm (Fin n), Perm.sign f = 1 → f ∈ alternatingGroup (Fin n) :=
    fun f hf => Perm.mem_alternatingGroup.2 hf
  let A1 : alternatingGroup (Fin n) := ⟨a1, hmem a1 ha1even⟩
  let A2 : alternatingGroup (Fin n) := ⟨a2, hmem a2 ha2even⟩
  have hL1 : Perm.sign (τ * σ₁) = 1 := by rw [Perm.sign_mul, hτodd, hodd₁]; norm_num
  have hL2 : Perm.sign (τ * σ₂) = 1 := by rw [Perm.sign_mul, hτodd, hodd₂]; norm_num
  let L1 : alternatingGroup (Fin n) := ⟨τ * σ₁, hmem _ hL1⟩
  let L2 : alternatingGroup (Fin n) := ⟨τ * σ₂, hmem _ hL2⟩
  have hA1A2 : A1 * A2 = A2 * A1 := Subtype.ext ha12
  have hA1sq : A1 * A1 = 1 := Subtype.ext ha1sq
  have hA2sq : A2 * A2 = 1 := Subtype.ext ha2sq
  have hcjA1 : cj τ A1 = A1 := by
    apply Subtype.ext
    show τ * a1 * τ⁻¹ = a1
    rw [hτa1, mul_assoc, mul_inv_cancel, mul_one]
  have hcjA2 : cj τ A2 = A2 := by
    apply Subtype.ext
    show τ * a2 * τ⁻¹ = a2
    rw [hτa2, mul_assoc, mul_inv_cancel, mul_one]
  have hc1 : ∀ a, (ι₁ L1 * ι₂ L2 * s) * ι₁ a * (ι₁ L1 * ι₂ L2 * s)⁻¹ = ι₁ (cj τ a) :=
    fun a => x4_conj hcomm hσ₁ hs₁ L1 L2 rfl a
  have hc2 : ∀ b, (ι₁ L1 * ι₂ L2 * s) * ι₂ b * (ι₁ L1 * ι₂ L2 * s)⁻¹ = ι₂ (cj τ b) := by
    intro b
    have e : ι₁ L1 * ι₂ L2 * s = ι₂ L2 * ι₁ L1 * s := by rw [hcomm L1 L2]
    rw [e]
    exact x4_conj (fun b a => (hcomm a b).symm) hσ₂ hs₂ L2 L1 rfl b
  have hx4sq : (ι₁ L1 * ι₂ L2 * s) * (ι₁ L1 * ι₂ L2 * s) = 1 :=
    x4_sq hcomm hs2 hσ₁ hσ₂ hτ2 hs₁ hs₂ L1 L2 rfl rfl
  let x : Fin 5 → Y := ![ι₁ A1, ι₁ A2, ι₂ A1, ι₂ A2, ι₁ L1 * ι₂ L2 * s]
  have hcm : ∀ (y : Y) (a : alternatingGroup (Fin n)), y * ι₁ a * y⁻¹ = ι₁ a →
      y * ι₁ a = ι₁ a * y := by
    intro y a h
    calc y * ι₁ a = (y * ι₁ a * y⁻¹) * y := by group
      _ = ι₁ a * y := by rw [h]
  have hcm' : ∀ (y : Y) (a : alternatingGroup (Fin n)), y * ι₂ a * y⁻¹ = ι₂ a →
      y * ι₂ a = ι₂ a * y := by
    intro y a h
    calc y * ι₂ a = (y * ι₂ a * y⁻¹) * y := by group
      _ = ι₂ a * y := by rw [h]
  have c01 : ι₁ A1 * ι₁ A2 = ι₁ A2 * ι₁ A1 := by rw [← map_mul, ← map_mul, hA1A2]
  have c23 : ι₂ A1 * ι₂ A2 = ι₂ A2 * ι₂ A1 := by rw [← map_mul, ← map_mul, hA1A2]
  have c02 := hcomm A1 A1
  have c03 := hcomm A1 A2
  have c12 := hcomm A2 A1
  have c13 := hcomm A2 A2
  have c04 : (ι₁ L1 * ι₂ L2 * s) * ι₁ A1 = ι₁ A1 * (ι₁ L1 * ι₂ L2 * s) :=
    hcm _ _ (by rw [hc1, hcjA1])
  have c14 : (ι₁ L1 * ι₂ L2 * s) * ι₁ A2 = ι₁ A2 * (ι₁ L1 * ι₂ L2 * s) :=
    hcm _ _ (by rw [hc1, hcjA2])
  have c24 : (ι₁ L1 * ι₂ L2 * s) * ι₂ A1 = ι₂ A1 * (ι₁ L1 * ι₂ L2 * s) :=
    hcm' _ _ (by rw [hc2, hcjA1])
  have c34 : (ι₁ L1 * ι₂ L2 * s) * ι₂ A2 = ι₂ A2 * (ι₁ L1 * ι₂ L2 * s) :=
    hcm' _ _ (by rw [hc2, hcjA2])
  have hxx : ∀ i j, x i * x j = x j * x i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [x] <;>
      first
      | rfl
      | exact c01
      | exact c01.symm
      | exact c23
      | exact c23.symm
      | exact c02
      | exact c02.symm
      | exact c03
      | exact c03.symm
      | exact c12
      | exact c12.symm
      | exact c13
      | exact c13.symm
      | exact c04
      | exact c04.symm
      | exact c14
      | exact c14.symm
      | exact c24
      | exact c24.symm
      | exact c34
      | exact c34.symm
  have hxsq : ∀ i, x i ^ 2 ∈ (⊥ : Subgroup Y) := by
    intro i
    rw [Subgroup.mem_bot, pow_two]
    fin_cases i
    · show ι₁ A1 * ι₁ A1 = 1
      rw [← map_mul, hA1sq, map_one]
    · show ι₁ A2 * ι₁ A2 = 1
      rw [← map_mul, hA2sq, map_one]
    · show ι₂ A1 * ι₂ A1 = 1
      rw [← map_mul, hA1sq, map_one]
    · show ι₂ A2 * ι₂ A2 = 1
      rw [← map_mul, hA2sq, map_one]
    · exact hx4sq
  have hker : ∀ a : Fin 5 → Fin 2, a ≠ 0 →
      (List.ofFn fun i => x i ^ (a i : ℕ)).prod ∉ (⊥ : Subgroup Y) := by
    intro a ha hmem1
    rw [Subgroup.mem_bot] at hmem1
    have hprod : (List.ofFn fun i => x i ^ (a i : ℕ)).prod =
        ι₁ A1 ^ (a 0 : ℕ) * (ι₁ A2 ^ (a 1 : ℕ) * (ι₂ A1 ^ (a 2 : ℕ) *
          (ι₂ A2 ^ (a 3 : ℕ) * (ι₁ L1 * ι₂ L2 * s) ^ (a 4 : ℕ)))) := by
      simp [x, List.ofFn_succ]
    rw [hprod] at hmem1
    have hle : ∀ k : Fin 5, (a k : ℕ) ≤ 1 := fun k => Nat.lt_succ_iff.1 (a k).2
    obtain ⟨u, hu⟩ : ∃ u : alternatingGroup (Fin n), u = A1 ^ (a 0 : ℕ) * A2 ^ (a 1 : ℕ) := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : alternatingGroup (Fin n), v = A1 ^ (a 2 : ℕ) * A2 ^ (a 3 : ℕ) := ⟨_, rfl⟩
    have hmem2 : ι₁ u * (ι₂ v * (ι₁ L1 * ι₂ L2 * s) ^ (a 4 : ℕ)) = 1 := by
      rw [← hmem1, hu, hv, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
      simp only [mul_assoc]
    have h4 : (a 4 : ℕ) = 0 ∨ (a 4 : ℕ) = 1 := by
      have := hle 4
      omega
    rcases h4 with h4 | h4
    ·
      rw [h4, pow_zero, mul_one] at hmem2
      obtain ⟨hu1, hv1⟩ := eq_one_of_mul_eq_one (by omega) hι₁ hι₂ hcomm hmem2
      have hu2 : a1 ^ (a 0 : ℕ) * a2 ^ (a 1 : ℕ) = 1 := by
        have := congrArg Subtype.val hu1
        simpa [hu, A1, A2] using this
      have hv2 : a1 ^ (a 2 : ℕ) * a2 ^ (a 3 : ℕ) = 1 := by
        have := congrArg Subtype.val hv1
        simpa [hv, A1, A2] using this
      obtain ⟨b0, b1⟩ := hind _ _ (hle 0) (hle 1) hu2
      obtain ⟨b2, b3⟩ := hind _ _ (hle 2) (hle 3) hv2
      apply ha
      funext i
      fin_cases i
      · exact Fin.ext (by simpa using b0)
      · exact Fin.ext (by simpa using b1)
      · exact Fin.ext (by simpa using b2)
      · exact Fin.ext (by simpa using b3)
      · exact Fin.ext (by simpa using h4)
    ·
      rw [h4, pow_one] at hmem2
      have hs : s = ι₁ (L1⁻¹ * u⁻¹) * ι₂ (L2⁻¹ * v⁻¹) := by
        have h5 : ι₁ u * (ι₂ v * (ι₁ L1 * ι₂ L2 * s)) = 1 := hmem2
        have h6 : s = (ι₂ L2)⁻¹ * ((ι₁ L1)⁻¹ * ((ι₂ v)⁻¹ * (ι₁ u)⁻¹)) := by
          have h7 : (ι₁ u * (ι₂ v * (ι₁ L1 * ι₂ L2))) * s = 1 := by rw [← h5]; group
          have h8 := eq_inv_of_mul_eq_one_right h7
          rw [h8]; group
        rw [h6]
        have hc3 : ∀ (c : alternatingGroup (Fin n)) (d : alternatingGroup (Fin n)),
            (ι₂ c)⁻¹ * (ι₁ d)⁻¹ = (ι₁ d)⁻¹ * (ι₂ c)⁻¹ := by
          intro c d
          rw [← map_inv, ← map_inv]
          exact (hcomm d⁻¹ c⁻¹).symm
        have hc4 : (ι₂ v)⁻¹ * (ι₁ u)⁻¹ = (ι₁ u)⁻¹ * (ι₂ v)⁻¹ := hc3 v u
        calc (ι₂ L2)⁻¹ * ((ι₁ L1)⁻¹ * ((ι₂ v)⁻¹ * (ι₁ u)⁻¹))
            = (ι₂ L2)⁻¹ * ((ι₁ L1)⁻¹ * ((ι₁ u)⁻¹ * (ι₂ v)⁻¹)) := by rw [hc4]
          _ = ((ι₂ L2)⁻¹ * (ι₁ L1)⁻¹) * ((ι₁ u)⁻¹ * (ι₂ v)⁻¹) := by group
          _ = ((ι₁ L1)⁻¹ * (ι₂ L2)⁻¹) * ((ι₁ u)⁻¹ * (ι₂ v)⁻¹) := by rw [hc3 L2 L1]
          _ = (ι₁ L1)⁻¹ * (((ι₂ L2)⁻¹ * (ι₁ u)⁻¹) * (ι₂ v)⁻¹) := by group
          _ = (ι₁ L1)⁻¹ * (((ι₁ u)⁻¹ * (ι₂ L2)⁻¹) * (ι₂ v)⁻¹) := by rw [hc3 L2 u]
          _ = ι₁ (L1⁻¹ * u⁻¹) * ι₂ (L2⁻¹ * v⁻¹) := by
            rw [map_mul, map_mul, map_inv, map_inv, map_inv, map_inv]; group
      exact not_s_mem (by omega) hι₁ hcomm hodd₁ hs₁ _ _ hs
  exact (rankCertified_of_section_involutions (⊥ : Subgroup Y) x
    (fun i => Subgroup.mem_normalizer_iff.2 fun h => by simp [Subgroup.mem_bot]) hxsq
    (fun i j => by
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hxx i j)) hker (s := 4) (by norm_num)).not_gen4
    le_rfl hgen

end Main

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
