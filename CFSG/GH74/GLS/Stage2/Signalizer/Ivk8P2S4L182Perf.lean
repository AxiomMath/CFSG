module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182

open Subgroup
open scoped commutatorElement

theorem eq_one_of_perfect_of_mul {G : Type*} [Group G] {X A : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {f : G → G} (hfA : ∀ x ∈ X, f x ∈ A)
    (hf : ∀ x ∈ X, ∀ y ∈ X, f (x * y) = f x * f y) : ∀ x ∈ X, f x = 1 := by
  have h1 : f 1 = 1 := by
    have h := hf 1 X.one_mem 1 X.one_mem
    rw [mul_one] at h
    simpa using h
  have hinv : ∀ x ∈ X, f x⁻¹ = (f x)⁻¹ := by
    intro x hx
    have h := hf x hx x⁻¹ (X.inv_mem hx)
    rw [mul_inv_cancel, h1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  let K : Subgroup G :=
    { carrier := {x | x ∈ X ∧ f x = 1}
      one_mem' := ⟨X.one_mem, h1⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨X.mul_mem ha.1 hb.1, by rw [hf a ha.1 b hb.1, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by rw [hinv a ha.1, ha.2, inv_one]⟩ }
  have hcomm : ⁅X, X⁆ ≤ K := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    have hab : a * b * a⁻¹ ∈ X := X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)
    refine ⟨X.mul_mem hab (X.inv_mem hb), ?_⟩
    rw [hf _ hab _ (X.inv_mem hb), hf _ (X.mul_mem ha hb) _ (X.inv_mem ha), hf a ha b hb,
      hinv a ha, hinv b hb, hA _ (hfA a ha) _ (hfA b hb)]
    simp
  intro x hx
  exact (hcomm (by rw [hX]; exact hx)).2

theorem centralizes_of_comm_mem {G : Type*} [Group G] {X N : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hN : ∀ y ∈ X, y ∈ N → ∀ x ∈ X, y * x = x * y) {v : G}
    (hv : ∀ x ∈ X, v * x * v⁻¹ ∈ X) (hvN : ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ N) :
    ∀ x ∈ X, v * x * v⁻¹ = x := by
  have hfX : ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ X := fun x hx => X.mul_mem (hv x hx) (X.inv_mem hx)
  have hfc : ∀ x ∈ X, ∀ w ∈ X, (v * x * v⁻¹ * x⁻¹) * w = w * (v * x * v⁻¹ * x⁻¹) :=
    fun x hx w hw => hN _ (hfX x hx) (hvN x hx) w hw
  have key := eq_one_of_perfect_of_mul (A := X ⊓ N) hX
    (fun a ha b hb => hN a ha.1 ha.2 b hb.1) (f := fun x => v * x * v⁻¹ * x⁻¹)
    (fun x hx => ⟨hfX x hx, hvN x hx⟩) (fun x hx y hy => ?_)
  · intro x hx
    exact mul_inv_eq_one.1 (key x hx)
  · have hc : (v * y * v⁻¹ * y⁻¹) * (v * x * v⁻¹) = (v * x * v⁻¹) * (v * y * v⁻¹ * y⁻¹) :=
      hfc y hy _ (hv x hx)
    calc v * (x * y) * v⁻¹ * (x * y)⁻¹
        = (v * x * v⁻¹) * (v * y * v⁻¹ * y⁻¹) * x⁻¹ := by group
      _ = (v * y * v⁻¹ * y⁻¹) * (v * x * v⁻¹) * x⁻¹ := by rw [hc]
      _ = (v * y * v⁻¹ * y⁻¹) * (v * x * v⁻¹ * x⁻¹) := by group
      _ = (v * x * v⁻¹ * x⁻¹) * (v * y * v⁻¹ * y⁻¹) := hfc y hy _ (hfX x hx)

theorem centralizes_of_trivial_on_centralizer {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {P E X : Subgroup G} [Finite P] (hP : IsPGroup p P) (hX : ⁅X, X⁆ = X)
    (hXP : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ ∈ P) (hEP : E ≤ P)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h0 : ∀ y ∈ P, (∀ e ∈ E, e * y = y * e) → ∀ x ∈ X, x * y * x⁻¹ = y) :
    ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ = y := by
  classical
  let K : Subgroup G :=
    { carrier := {y | y ∈ P ∧ ∀ x ∈ X, x * y * x⁻¹ = y}
      one_mem' := ⟨P.one_mem, fun x _ => by group⟩
      mul_mem' := fun {a b} ha hb => ⟨P.mul_mem ha.1 hb.1, fun x hx => by
        calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
          _ = a * b := by rw [ha.2 x hx, hb.2 x hx]⟩
      inv_mem' := fun {a} ha => ⟨P.inv_mem ha.1, fun x hx => by
        calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [ha.2 x hx]⟩ }
  have hKP : ∀ k ∈ K, k ∈ P := fun k hk => hk.1
  have hKfix : ∀ k ∈ K, ∀ x ∈ X, x * k * x⁻¹ = k := fun k hk x hx => hk.2 x hx
  have hEK : ∀ e ∈ E, e ∈ K := fun e he =>
    ⟨hEP he, h0 e (hEP he) (fun e' he' => hEc e' he' e he)⟩
  have hCK : ∀ w ∈ P, (∀ k ∈ K, w * k = k * w) → w ∈ K := fun w hw hwc =>
    ⟨hw, h0 w hw (fun e he => (hwc e (hEK e he)).symm)⟩
  have hN : ∀ y ∈ P, (∀ k ∈ K, y * k * y⁻¹ ∈ K) → y ∈ K := by
    intro y hyP hyN
    let w : G → G := fun x => y⁻¹ * (x * y * x⁻¹)
    have hwP : ∀ x ∈ X, w x ∈ P := fun x hx => P.mul_mem (P.inv_mem hyP) (hXP x hx y hyP)
    have hwc : ∀ x ∈ X, ∀ k ∈ K, w x * k = k * w x := by
      intro x hx k hk
      have h1 : x⁻¹ * k * x = k := by
        have := hKfix k hk x⁻¹ (X.inv_mem hx)
        simpa using this
      have h2 : x * (y * k * y⁻¹) * x⁻¹ = y * k * y⁻¹ := hKfix _ (hyN k hk) x hx
      have h3 : (x * y * x⁻¹) * k = (y * k * y⁻¹) * (x * y * x⁻¹) := by
        apply mul_inv_eq_iff_eq_mul.1
        calc (x * y * x⁻¹) * k * (x * y * x⁻¹)⁻¹ = x * y * (x⁻¹ * k * x) * y⁻¹ * x⁻¹ := by group
          _ = x * y * k * y⁻¹ * x⁻¹ := by rw [h1]
          _ = x * (y * k * y⁻¹) * x⁻¹ := by group
          _ = y * k * y⁻¹ := h2
      show y⁻¹ * (x * y * x⁻¹) * k = k * (y⁻¹ * (x * y * x⁻¹))
      calc y⁻¹ * (x * y * x⁻¹) * k = y⁻¹ * ((y * k * y⁻¹) * (x * y * x⁻¹)) := by
            rw [mul_assoc y⁻¹, h3]
        _ = k * (y⁻¹ * (x * y * x⁻¹)) := by group
    have hwK : ∀ x ∈ X, w x ∈ K := fun x hx => hCK _ (hwP x hx) (hwc x hx)
    have hwm : ∀ x ∈ X, ∀ x' ∈ X, w (x * x') = w x * w x' := by
      intro x hx x' hx'
      have h4 : x * w x' * x⁻¹ = w x' := hKfix _ (hwK x' hx') x hx
      show y⁻¹ * (x * x' * y * (x * x')⁻¹) = (y⁻¹ * (x * y * x⁻¹)) * (y⁻¹ * (x' * y * x'⁻¹))
      calc y⁻¹ * (x * x' * y * (x * x')⁻¹)
          = y⁻¹ * (x * (y * (y⁻¹ * (x' * y * x'⁻¹))) * x⁻¹) := by group
        _ = y⁻¹ * ((x * y * x⁻¹) * (x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹)) := by group
        _ = y⁻¹ * ((x * y * x⁻¹) * (y⁻¹ * (x' * y * x'⁻¹))) := by
          have : x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹ = y⁻¹ * (x' * y * x'⁻¹) := h4
          rw [this]
        _ = (y⁻¹ * (x * y * x⁻¹)) * (y⁻¹ * (x' * y * x'⁻¹)) := by group
    have key := eq_one_of_perfect_of_mul (A := K ⊓ centralizer (K : Set G)) hX
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.1 hb.2 a ha.1).symm.symm ▸ rfl)
      (f := w) (fun x hx => ⟨hwK x hx, Subgroup.mem_centralizer_iff.2 fun k hk =>
        (hwc x hx k hk).symm⟩) hwm
    refine ⟨hyP, fun x hx => ?_⟩
    have := key x hx
    show x * y * x⁻¹ = y
    have h5 : y⁻¹ * (x * y * x⁻¹) = 1 := this
    exact (inv_mul_eq_one.1 h5).symm
  have hnc : NormalizerCondition ↥P :=
    @Group.normalizerCondition_of_isNilpotent ↥P _ (IsPGroup.isNilpotent hP)
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, y, hy, hxy⟩ := hcon
  have hKtop : K.subgroupOf P = ⊤ := by
    by_contra hne
    have hlt : K.subgroupOf P < ⊤ := lt_top_iff_ne_top.2 hne
    have := hnc _ hlt
    obtain ⟨y', hy'N, hy'K⟩ := IsConcreteLE.exists_of_lt this
    apply hy'K
    refine hN y'.1 y'.2 fun k hk => ?_
    have hk' : (⟨k, hKP k hk⟩ : ↥P) ∈ K.subgroupOf P := hk
    have := (Subgroup.mem_normalizer_iff.1 hy'N ⟨k, hKP k hk⟩).1 hk'
    exact this
  have hyK : y ∈ K := by
    have : (⟨y, hy⟩ : ↥P) ∈ K.subgroupOf P := by rw [hKtop]; trivial
    exact this
  exact hxy (hyK.2 x hx)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182
