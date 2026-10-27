module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem g4off {H : Type} [Group H] {Q : Subgroup H} {α α' : H}
    (hα2 : α * α = 1) (hα'2 : α' * α' = 1) (hc : α * α' = α' * α)
    (hαQ : α ∉ Q) (hα'Q : α' ∉ Q) (hαα'Q : α * α' ∉ Q) :
    ∀ i j : Fin 4, i ≠ j → (![1, α, α', α * α'] : Fin 4 → H) j *
      (![1, α, α', α * α'] : Fin 4 → H) i ∉ Q := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all (config := { zeta := false }) [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three] <;> grind

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem exists_E16 {α α' : H} (hα : α ∈ Mc) (hα' : α' ∈ Mc) (hα2 : α * α = 1)
    (hα'2 : α' * α' = 1) (hc : α * α' = α' * α) (hαQ : α ∉ Q) (hα'Q : α' ∉ Q)
    (hαα'Q : α * α' ∉ Q) :
    ∃ F : Subgroup H, F ≤ Mc ∧ V ≤ F ∧ (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧
      (∀ a ∈ F, a * a = 1) ∧ Nat.card F = 16 ∧
      ∀ u ∈ F, u ∉ V → ∃ v ∈ V, u = α * v ∨ u = α' * v ∨ u = (α * α') * v := by
  have hαM : α ∈ Mh := Mc_le_Mh h hMh hMc hα
  have hα'M : α' ∈ Mh := Mc_le_Mh h hMh hMc hα'
  have hαα'M : α * α' ∈ Mh := Mh.mul_mem hαM hα'M
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVQ : V ≤ Q := fun x hx => h.Y_le_Q (hVY hx)
  have hVMc : V ≤ Mc := hVQ.trans (Q_le_Mc h hMh hMc)
  have hV_sq : ∀ v ∈ V, v * v = 1 := fun v hv => h.Y_sq v (hVY hv)
  have hV_comm : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v :=
    fun v hv v' hv' => h.Q_comm v (hVQ hv) v' (hVQ hv')
  have hcent : ∀ {m : H}, m ∈ Mh → ∀ v ∈ V, m * v = v * m := by
    intro m hm v hv
    have h1 := Mh_cent_V h hMh hm hv
    calc m * v = (m * v * m⁻¹) * m := by group
      _ = v * m := by rw [h1]
  have hα_cent : ∀ v ∈ V, α * v = v * α := fun v hv => hcent hαM v hv
  have hα'_cent : ∀ v ∈ V, α' * v = v * α' := fun v hv => hcent hα'M v hv
  have hαα'_cent : ∀ v ∈ V, (α * α') * v = v * (α * α') := fun v hv => hcent hαα'M v hv
  let S : Set H := {u | ∃ v ∈ V, u = v ∨ u = α * v ∨ u = α' * v ∨ u = (α * α') * v}
  have hmul : ∀ {a b : H}, a ∈ S → b ∈ S → a * b ∈ S := by
    rintro a b ⟨v, hv, ha⟩ ⟨v', hv', hb⟩
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb
    · rw [ha, hb]; exact ⟨v * v', V.mul_mem hv hv', Or.inl rfl⟩
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inl ?_)⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inl ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inr ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inl ?_)⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inl ?_⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inr ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inl ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inl ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inr ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inl ?_⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inl ?_)⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inr ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inr (Or.inl ?_))⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inr (Or.inl ?_)⟩; grind
    · rw [ha, hb]; refine ⟨v * v', V.mul_mem hv hv', Or.inl ?_⟩; grind
  have hone : (1 : H) ∈ S := ⟨1, V.one_mem, Or.inl rfl⟩
  have hsq : ∀ {a : H}, a ∈ S → a * a = 1 := by
    rintro a ⟨v, hv, ha⟩
    rcases ha with ha | ha | ha | ha
    · rw [ha]; exact hV_sq v hv
    · rw [ha]; grind
    · rw [ha]; grind
    · rw [ha]; grind
  have hinv : ∀ {a : H}, a ∈ S → a⁻¹ ∈ S := by
    intro a ha
    rw [inv_eq_of_mul_eq_one_right (hsq ha)]
    exact ha
  let F : Subgroup H :=
    { carrier := S
      mul_mem' := by intro x y hx hy; exact hmul hx hy
      one_mem' := hone
      inv_mem' := by intro x hx; exact hinv hx }
  have hFMc : F ≤ Mc := by
    intro u hu
    change u ∈ S at hu
    rcases hu with ⟨v, hv, hu⟩
    rcases hu with hu | hu | hu | hu
    · rw [hu]; exact hVMc hv
    · rw [hu]; exact Mc.mul_mem hα (hVMc hv)
    · rw [hu]; exact Mc.mul_mem hα' (hVMc hv)
    · rw [hu]; exact Mc.mul_mem (Mc.mul_mem hα hα') (hVMc hv)
  have hVF : V ≤ F := by
    intro v hv
    change v ∈ S
    exact ⟨v, hv, Or.inl rfl⟩
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    change a ∈ S at ha
    change b ∈ S at hb
    rcases ha with ⟨v, hv, ha⟩
    rcases hb with ⟨v', hv', hb⟩
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
      rw [ha, hb] <;> grind
  have hFsq : ∀ a ∈ F, a * a = 1 := by
    intro a ha
    change a ∈ S at ha
    exact hsq ha
  let g4 : Fin 4 → H := ![1, α, α', α * α']
  have hg4_mem : ∀ (i : Fin 4) (v : H), v ∈ V → g4 i * v ∈ S := by
    intro i v hv
    fin_cases i
    · exact ⟨v, hv, Or.inl (by simp [g4])⟩
    · exact ⟨v, hv, Or.inr (Or.inl (by simp [g4]))⟩
    · exact ⟨v, hv, Or.inr (Or.inr (Or.inl (by simp [g4])))⟩
    · exact ⟨v, hv, Or.inr (Or.inr (Or.inr (by simp [g4])))⟩
  let f : Fin 4 × V → F := fun x => ⟨g4 x.1 * (x.2 : H), hg4_mem x.1 x.2 x.2.2⟩
  have hg4_sq : ∀ i : Fin 4, g4 i * g4 i = 1 := by
    intro i
    fin_cases i <;> simp [g4] <;> grind
  have hf_inj : Function.Injective f := by
    rintro ⟨i, v⟩ ⟨j, v'⟩ heq
    have heq' : g4 i * (v : H) = g4 j * (v' : H) := by
      simpa [f] using congrArg Subtype.val heq
    have hg : g4 j * g4 i ∈ Q := by
      have h1 : g4 j * g4 i = (v' : H) * (v : H)⁻¹ := by
        have h2 := congrArg (fun x => (g4 j)⁻¹ * x * (v : H)⁻¹) heq'
        have hL : (g4 j)⁻¹ * (g4 i * (v : H)) * (v : H)⁻¹ = (g4 j)⁻¹ * g4 i := by
          group
        have hR : (g4 j)⁻¹ * (g4 j * (v' : H)) * (v : H)⁻¹ = (v' : H) * (v : H)⁻¹ := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [hL, hR] at h2
        simpa [inv_eq_of_mul_eq_one_right (hg4_sq j)] using h2
      rw [h1]
      exact hVQ (V.mul_mem v'.2 (V.inv_mem v.2))
    have hij : i = j := by
      by_contra hne
      exact (g4off hα2 hα'2 hc hαQ hα'Q hαα'Q i j hne) hg
    subst hij
    have hvv : (v : H) = (v' : H) := mul_left_cancel heq'
    exact Prod.ext rfl (Subtype.ext hvv)
  have hf_surj : Function.Surjective f := by
    intro u
    have hu : (u : H) ∈ S := u.2
    rcases hu with ⟨v, hv, hu⟩
    rcases hu with h | h | h | h
    · refine ⟨(0, ⟨v, hv⟩), Subtype.ext ?_⟩
      rw [h]; simp [f, g4]
    · refine ⟨(1, ⟨v, hv⟩), Subtype.ext ?_⟩
      rw [h]; simp [f, g4]
    · refine ⟨(2, ⟨v, hv⟩), Subtype.ext ?_⟩
      rw [h]; simp [f, g4]
    · refine ⟨(3, ⟨v, hv⟩), Subtype.ext ?_⟩
      rw [h]; simp [f, g4]
  have hcard : Nat.card F = 16 := by
    have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
    have h1 : Nat.card (Fin 4 × V) = Nat.card F := Nat.card_congr (Equiv.ofBijective f hbij)
    rw [← h1, Nat.card_prod, Nat.card_fin, h.card_V]
  have hlast : ∀ u ∈ F, u ∉ V →
      ∃ v ∈ V, u = α * v ∨ u = α' * v ∨ u = (α * α') * v := by
    intro u hu huV
    change u ∈ S at hu
    rcases hu with ⟨v, hv, hu⟩
    rcases hu with h | h | h | h
    · exact absurd (by rw [h]; exact hv) huV
    · exact ⟨v, hv, Or.inl h⟩
    · exact ⟨v, hv, Or.inr (Or.inl h)⟩
    · exact ⟨v, hv, Or.inr (Or.inr h)⟩
  exact ⟨F, hFMc, hVF, hFcomm, hFsq, hcard, hlast⟩

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
