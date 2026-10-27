module

public import Certificates.Data.Kernel.SporSch.RelTab
public import Aesop.BuiltinRules
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push

public section

namespace CFSG.KS.RelTab

open CFSG.KC.RelTab

variable {G α : Type*} [Monoid G] [Monoid α] {ρ : G →* α} {rd : ℕ → α} {Ok : ℕ → Prop}
  {mm : ℕ → ℕ → ℕ}

theorem prodAcc_sound
    (hmm : ∀ {A B}, Ok A → Ok B → Ok (mm A B) ∧ rd (mm A B) = rd A * rd B)
    {M : ℕ → ℕ} {g : ℕ → G} {fs : List ℕ} (hM : ∀ j ∈ fs, Ok (M j) ∧ rd (M j) = ρ (g j)) :
    ∀ {a : ℕ} {u : G}, Ok a → rd a = ρ u →
      Ok (prodAcc mm M fs a) ∧ rd (prodAcc mm M fs a) = ρ (u * (fs.map g).prod) := by
  induction fs with
  | nil => intro a u ha hu; simpa [prodAcc] using ⟨ha, hu⟩
  | cons j fs ih =>
    intro a u ha hu
    obtain ⟨hj1, hj2⟩ := hM j (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := hmm ha hj1
    have h := ih (fun k hk => hM k (List.mem_cons_of_mem _ hk)) h1
      (u := u * g j) (by rw [h2, hu, hj2, map_mul])
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc]
    exact h

theorem prodL_sound
    (hmm : ∀ {A B}, Ok A → Ok B → Ok (mm A B) ∧ rd (mm A B) = rd A * rd B)
    {M : ℕ → ℕ} {g : ℕ → G} {one : ℕ} {fs : List ℕ} (hfs : fs ≠ [])
    (hM : ∀ j ∈ fs, Ok (M j) ∧ rd (M j) = ρ (g j)) :
    Ok (prodL mm one M fs) ∧ rd (prodL mm one M fs) = ρ (fs.map g).prod := by
  cases fs with
  | nil => exact absurd rfl hfs
  | cons f fs =>
    obtain ⟨hf1, hf2⟩ := hM f (List.mem_cons_self ..)
    have h := prodAcc_sound hmm (fun k hk => hM k (List.mem_cons_of_mem _ hk)) hf1 hf2
    simpa [prodL] using h

theorem relTab_spec {one : ℕ} {Gm X M : ℕ → ℕ} {rows : List (ℕ × ℕ × List ℕ)}
    (h : relTab mm one Gm X M rows = true) :
    ∀ r ∈ rows, relRow mm one Gm X M r.1 r.2.1 r.2.2 = true := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    intro s hs
    have hr : relRow mm one Gm X M r.1 r.2.1 r.2.2 = true ∧ relTab mm one Gm X M rows = true := by
      simp only [relTab] at h
      revert h
      cases relRow mm one Gm X M r.1 r.2.1 r.2.2 <;> simp [relTab]
    rcases List.mem_cons.1 hs with rfl | hs
    · exact hr.1
    · exact ih hr.2 s hs

theorem relRow_sound (hρ : Function.Injective ρ)
    (hmm : ∀ {A B}, Ok A → Ok B → Ok (mm A B) ∧ rd (mm A B) = rd A * rd B)
    {one : ℕ} {Gm X M : ℕ → ℕ} {gG gX g : ℕ → G} {l i : ℕ} {fs : List ℕ} (hfs : fs ≠ [])
    (hGl : Ok (Gm l) ∧ rd (Gm l) = ρ (gG l)) (hXi : Ok (X i) ∧ rd (X i) = ρ (gX i))
    (hM : ∀ j ∈ fs, Ok (M j) ∧ rd (M j) = ρ (g j))
    (h : relRow mm one Gm X M l i fs = true) : gG l * gX i = (fs.map g).prod * gG l := by
  have e : mm (Gm l) (X i) = mm (prodL mm one M fs) (Gm l) := Nat.eq_of_beq_eq_true h
  have hP := prodL_sound (one := one) hmm hfs hM
  have e2 := congrArg rd e
  rw [(hmm hGl.1 hXi.1).2, (hmm hP.1 hGl.1).2, hGl.2, hXi.2, hP.2, ← map_mul, ← map_mul] at e2
  exact hρ e2

end CFSG.KS.RelTab

end
