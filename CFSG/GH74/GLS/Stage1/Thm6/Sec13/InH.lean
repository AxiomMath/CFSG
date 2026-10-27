module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup3
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure InH (x : G) (V H : Subgroup G) (f : G) : Prop where
  E_le : EV x V ≤ H
  H_le : H ≤ centralizer (V : Set G)
  H2 : IsPGroup 2 ↥H
  f3 : Is3Element f
  f_N : f ∈ normalizer (V : Set G)
  f_H : f ∈ normalizer (H : Set G)
  f_C : f ∉ centralizer (V : Set G)
  C_H : H ⊓ centralizer ({f} : Set G) = zpowers x

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem EV_isPGroup : IsPGroup 2 ↥(EV x V) :=
  IsPGroup.of_card (n := 3) (by rw [h.card_EV]; norm_num)

theorem exists_InH [Finite G] : ∃ (H : Subgroup G) (f : G), InH x V H f := by
  obtain ⟨f, hf3, hfx, hfE, hfV, hfnc, -, hCf⟩ := h.exists_f0
  exact ⟨EV x V, f, ⟨le_refl _, h.E_le_C, h.EV_isPGroup, hf3, hfV, hfE, hfnc, hCf⟩⟩

theorem exists_maximal_InH [Finite G] :
    ∃ (H : Subgroup G) (f : G), InH x V H f ∧ ∀ (H' : Subgroup G) (f' : G), InH x V H' f' →
      Nat.card H' ≤ Nat.card H := by
  classical
  let S : Set ℕ := {n | ∃ (H : Subgroup G) (f : G), InH x V H f ∧ Nat.card H = n}
  obtain ⟨H₁, f₁, hI₁⟩ := h.exists_InH
  have hne : S.Nonempty := ⟨Nat.card H₁, H₁, f₁, hI₁, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro n ⟨H, f, -, rfl⟩
    exact Subgroup.card_le_card_group H
  obtain ⟨H, f, hI, hn⟩ := Nat.sSup_mem hne hbdd
  refine ⟨H, f, hI, fun H' f' hI' => ?_⟩
  rw [hn]
  exact le_csSup hbdd ⟨H', f', hI', rfl⟩

end Out12

namespace InH

variable {x : G} {T V H : Subgroup G} {f : G}

theorem x_mem (hI : InH x V H f) : x ∈ H := hI.E_le x_mem_EV

theorem C_H_x [Finite G] (h : Out12 G x T V) (hI : InH x V H f) :
    H ⊓ centralizer ({x} : Set G) = EV x V := by
  apply le_antisymm
  · have hP : IsPGroup 2 ↥(H ⊓ centralizer ({x} : Set G)) := hI.H2.to_le inf_le_left
    apply h.cent_E_le hP
    intro g hg
    rw [mem_centralizer_iff]
    intro e he
    have hvg : ∀ v ∈ V, v * g = g * v := fun v hv => mem_centralizer_iff.1 (hI.H_le hg.1) v hv
    have hxg : x * g = g * x := mem_centralizer_iff.1 hg.2 x rfl
    obtain ⟨v, hv, he' | he'⟩ := (h.mem_EV).1 he <;> rw [he']
    · exact hvg v hv
    · calc v * x * g = v * (x * g) := by group
        _ = v * (g * x) := by rw [hxg]
        _ = (v * g) * x := by group
        _ = (g * v) * x := by rw [hvg v hv]
        _ = g * (v * x) := by group
  · exact le_inf hI.E_le (fun e he => by
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h.EV_comm x_mem_EV he)

theorem f_comm_x (hI : InH x V H f) : f * x = x * f := by
  have hx : x ∈ H ⊓ centralizer ({f} : Set G) := by rw [hI.C_H]; exact mem_zpowers x
  exact mem_centralizer_iff.1 hx.2 f rfl

theorem exists_noncomm [Finite G] (h : Out12 G x T V) (hI : InH x V H f) :
    ∃ g ∈ H, f * g ≠ g * f := by
  by_contra hcon
  push Not at hcon
  have hle : H ≤ zpowers x := by
    intro g hg
    rw [← hI.C_H]
    refine ⟨hg, ?_⟩
    show g ∈ centralizer ({f} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hcon g hg
  have h1 : Nat.card H ≤ Nat.card (zpowers x) := Subgroup.card_le_of_le hle
  have h2 : Nat.card (zpowers x) ≤ 2 := by
    rw [Nat.card_zpowers]
    apply Nat.le_of_dvd (by norm_num)
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two]; exact h.x_sq
  have h8 : 8 ≤ Nat.card H := by
    have := Subgroup.card_le_of_le hI.E_le
    rw [h.card_EV] at this
    exact this
  omega

end InH

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
