module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Timmesfeld.Transvection.QTwoThin

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup Matrix QuadraticMap CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.Fischer.Classification CFSG.Timmesfeld.Transvection.QTwo

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

omit [DecidableEq ι] in
theorem exists_ne_zero_polar_perp {k : ℕ} (hk : k < Fintype.card ι) (w : Fin k → ι → ZMod 2) :
    ∃ y, y ≠ 0 ∧ ∀ i, polar Q y (w i) = 0 := by
  let f : (ι → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    LinearMap.pi fun i => (polarBilin Q).flip (w i)
  have h := LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by simpa using hk)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  refine ⟨y, hy0, fun i => ?_⟩
  have := congrFun (LinearMap.mem_ker.1 hy) i
  simpa [f] using this

omit [Fintype ι] [DecidableEq ι] in
theorem exists_polar_pairings (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {k : ℕ}
    {w : Fin k → ι → ZMod 2} (hw : LinearIndependent (ZMod 2) w) (c : Fin k → ZMod 2) :
    ∃ x, ∀ i, polar Q x (w i) = c i := by
  obtain ⟨x, hx⟩ := exists_pairings_of_nondeg (polarBilin Q)
    (fun x y => by simp only [polarBilin_apply_apply]; exact polar_comm Q x y)
    (fun x hx => hnd x fun y => by simpa using hx y) hw c
  exact ⟨x, fun i => by simpa using hx i⟩

omit [Fintype ι] [DecidableEq ι] in
theorem linearIndependent_pair {a b : ι → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    LinearIndependent (ZMod 2) ![a, b] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  rcases zmod_two_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases zmod_two_eq_zero_or_one (c 1) with h1 | h1 <;>
    rw [h0, h1] at hc <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hc
  · fin_cases i <;> simp [h0, h1]
  · exact absurd hc hb
  · exact absurd hc ha
  · exact absurd (eq_of_add_eq_zero_zmod_two hc) hab

omit [Fintype ι] [DecidableEq ι] in
theorem linearIndependent_triple {u v w : ι → ZMod 2} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hw' : w ≠ u + v) :
    LinearIndependent (ZMod 2) ![u, v, w] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hc
  rcases zmod_two_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases zmod_two_eq_zero_or_one (c 1) with h1 | h1 <;>
    rcases zmod_two_eq_zero_or_one (c 2) with h2 | h2 <;>
    rw [h0, h1, h2] at hc <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hc
  · fin_cases i <;> simp [h0, h1, h2]
  · exact absurd hc hw
  · exact absurd hc hv
  · exact absurd (eq_of_add_eq_zero_zmod_two hc) hvw
  · exact absurd hc hu
  · exact absurd (eq_of_add_eq_zero_zmod_two hc) huw
  · exact absurd (eq_of_add_eq_zero_zmod_two hc) huv
  · refine absurd ?_ hw'
    have := congrArg (· + w) hc
    simp only [add_assoc, add_self_zmod_two, add_zero, zero_add] at this
    exact this.symm

omit [Fintype ι] [DecidableEq ι] in
theorem exists_mem_pair_map_eq_one {u v : ι → ZMod 2} (hv : Q v = 1) (huv : polar Q u v = 0) :
    ∃ a, (a = u ∨ a = u + v) ∧ Q a = 1 := by
  rcases zmod_two_eq_zero_or_one (Q u) with h0 | h1
  · exact ⟨u + v, Or.inr rfl, by rw [map_add_polar, h0, hv, huv]; rfl⟩
  · exact ⟨u, Or.inl rfl, h1⟩

theorem exists_pair_perp (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (h6 : 6 ≤ Fintype.card ι)
    {v : ι → ZMod 2} (hv : Q v = 1) :
    ∃ a b, Q a = 1 ∧ Q b = 1 ∧ polar Q a v = 0 ∧ polar Q b v = 0 ∧ polar Q a b = 0 ∧
      a ≠ b ∧ a ≠ v ∧ b ≠ v := by
  have hv0 := Timmesfeld.Transvection.QTwo.ne_zero_of_eq_one hv
  obtain ⟨x₀, hx₀⟩ := exists_polar_eq_one hnd hv0
  have hvx₀ : polar Q v x₀ = 1 := by rw [polar_comm]; exact hx₀
  obtain ⟨u₁, hu₁0, hu₁⟩ := exists_ne_zero_polar_perp (Q := Q) (k := 2) (by omega) ![v, x₀]
  have hu₁v : polar Q u₁ v = 0 := hu₁ 0
  have hu₁x : polar Q u₁ x₀ = 0 := hu₁ 1
  obtain ⟨a, ha, haQ⟩ := exists_mem_pair_map_eq_one hv hu₁v
  have hav : polar Q a v = 0 := by
    rcases ha with rfl | rfl
    · exact hu₁v
    · rw [polar_add_left, hu₁v, polar_self_zmod_two, add_zero]
  have hane : a ≠ v := by
    rintro rfl
    rcases ha with h | h
    · rw [← h, hvx₀] at hu₁x
      exact one_ne_zero hu₁x
    · apply hu₁0
      have := congrArg (· + a) h
      simpa [add_assoc, add_self_zmod_two] using this.symm
  have ha0 := Timmesfeld.Transvection.QTwo.ne_zero_of_eq_one haQ
  obtain ⟨x₁, hx₁⟩ := exists_polar_pairings hnd (linearIndependent_pair hv0 ha0 hane.symm)
    ![0, 1]
  have hx₁v : polar Q x₁ v = 0 := hx₁ 0
  have hx₁a : polar Q x₁ a = 1 := hx₁ 1
  obtain ⟨u₂, hu₂0, hu₂⟩ := exists_ne_zero_polar_perp (Q := Q) (k := 4) (by omega)
    ![v, a, x₀, x₁]
  have hu₂v : polar Q u₂ v = 0 := hu₂ 0
  have hu₂a : polar Q u₂ a = 0 := hu₂ 1
  have hu₂x₀ : polar Q u₂ x₀ = 0 := hu₂ 2
  have hu₂x₁ : polar Q u₂ x₁ = 0 := hu₂ 3
  have hu₂ne_v : u₂ ≠ v := by
    rintro rfl
    rw [hvx₀] at hu₂x₀
    exact one_ne_zero hu₂x₀
  have hu₂ne_a : u₂ ≠ a := by
    rintro rfl
    rw [polar_comm, hx₁a] at hu₂x₁
    exact one_ne_zero hu₂x₁
  have hu₂ne_av : u₂ ≠ a + v := by
    rintro rfl
    rw [polar_add_left, polar_comm, hx₁a, polar_comm, hx₁v, add_zero] at hu₂x₁
    exact one_ne_zero hu₂x₁
  obtain ⟨b, hb, hbQ⟩ := exists_mem_pair_map_eq_one hv hu₂v
  refine ⟨a, b, haQ, hbQ, hav, ?_, ?_, ?_, hane, ?_⟩
  · rcases hb with rfl | rfl
    · exact hu₂v
    · rw [polar_add_left, hu₂v, polar_self_zmod_two, add_zero]
  · rw [polar_comm]
    rcases hb with rfl | rfl
    · exact hu₂a
    · rw [polar_add_left, hu₂a, polar_comm, hav, add_zero]
  · rintro rfl
    rcases hb with h | h
    · exact hu₂ne_a h.symm
    · apply hu₂ne_av
      have := congrArg (· + v) h
      simpa [add_assoc, add_self_zmod_two] using this.symm
  · rintro rfl
    rcases hb with h | h
    · exact hu₂ne_v h.symm
    · apply hu₂0
      have := congrArg (· + b) h
      simpa [add_assoc, add_self_zmod_two] using this.symm

omit [Fintype ι] [DecidableEq ι] in
theorem exists_cond (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {v a b : ι → ZMod 2}
    (hv : Q v = 1) (ha : Q a = 1) (hb : Q b = 1) (hav : polar Q a v = 0)
    (hbv : polar Q b v = 0) (hne : a ≠ b) (hanv : a ≠ v) (hbnv : b ≠ v) :
    ∃ c, Q c = 1 ∧ polar Q c v = 0 ∧ polar Q c b = 0 ∧ polar Q c a = 1 := by
  have hli : LinearIndependent (ZMod 2) ![v, a, b] := by
    refine linearIndependent_triple (ne_zero_of_eq_one hv) (ne_zero_of_eq_one ha)
      (ne_zero_of_eq_one hb) hanv.symm hbnv.symm hne fun h => ?_
    rw [h, map_add_polar, hv, ha, polar_comm, hav] at hb
    exact absurd hb (by decide)
  obtain ⟨x, hx⟩ := exists_polar_pairings hnd hli ![0, 1, 0]
  have hxv : polar Q x v = 0 := hx 0
  have hxa : polar Q x a = 1 := hx 1
  have hxb : polar Q x b = 0 := hx 2
  obtain ⟨c, hc, hcQ⟩ := exists_mem_pair_map_eq_one hv hxv
  refine ⟨c, hcQ, ?_, ?_, ?_⟩ <;> rcases hc with rfl | rfl
  · exact hxv
  · rw [polar_add_left, hxv, polar_self_zmod_two, add_zero]
  · exact hxb
  · rw [polar_add_left, hxb, polar_comm, hbv, add_zero]
  · exact hxa
  · rw [polar_add_left, hxa, polar_comm, hav, add_zero]

end CFSG.LargeExtraspecial.S12Tri
