module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AQ
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {Y : Type*} [Group Y] [Finite Y]

private abbrev Z4c : Type := Fin 3 → Multiplicative (ZMod 4)

private abbrev z4cubeOfBool (b : Fin 3 → Bool) : Z4c :=
  fun i => Multiplicative.ofAdd (if b i then (1 : ZMod 4) else 0)

private lemma z4c_pow_four (x : Z4c) : x ^ 4 = 1 := by
  funext i
  change (x i) ^ 4 = 1
  have h := pow_card_eq_one (G := Multiplicative (ZMod 4)) (x := x i)
  rw [Fintype.card_multiplicative, ZMod.card] at h
  exact h

private lemma z4_bool_sq_injective {b c : Bool}
    (h : (Multiplicative.ofAdd (if b then (1 : ZMod 4) else 0)) ^ 2 =
      (Multiplicative.ofAdd (if c then (1 : ZMod 4) else 0)) ^ 2) : b = c := by
  revert h
  cases b <;> cases c <;> decide

theorem y6f4a_card_ge_eight {M N : Subgroup Y}
    (hM : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))) (hN : ∀ m ∈ M, m ^ 2 ∈ N) :
    8 ≤ Nat.card N := by
  obtain ⟨e⟩ := hM
  let F : (Fin 3 → Bool) → ↥N := fun b =>
    ⟨(((e.symm (z4cubeOfBool b) : ↥M) : Y)) ^ 2, hN _ (SetLike.coe_mem _)⟩
  have hF : Function.Injective F := by
    intro b b' hbb'
    have hMY : (((e.symm (z4cubeOfBool b) : ↥M) : Y)) ^ 2 =
        (((e.symm (z4cubeOfBool b') : ↥M) : Y)) ^ 2 :=
      congrArg (fun x : ↥N => (x : Y)) hbb'
    have hM2 : (e.symm (z4cubeOfBool b)) ^ 2 = (e.symm (z4cubeOfBool b')) ^ 2 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_pow] using hMY
    have hv2 : (z4cubeOfBool b) ^ 2 = (z4cubeOfBool b') ^ 2 := by
      have := congrArg e hM2
      simpa using this
    funext i
    have hcoord : (Multiplicative.ofAdd (if b i then (1 : ZMod 4) else 0)) ^ 2 =
        (Multiplicative.ofAdd (if b' i then (1 : ZMod 4) else 0)) ^ 2 := by
      have := congrFun hv2 i
      simpa only [z4cubeOfBool, Pi.pow_apply] using this
    exact z4_bool_sq_injective hcoord
  have hcard : Nat.card (Fin 3 → Bool) = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have := Nat.card_le_card_of_injective F hF
  rw [hcard] at this
  exact this

theorem y6f4a_not_normal {J M : Subgroup Y}
    (hS : ∀ S : Sylow 2 ↥(centralizer (J : Set Y)), Nat.card S = 2)
    (hM : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4))))
    (h4 : ∀ α : MulAut ↥J, α ^ 4 = 1 → α ^ 2 = 1) : ¬ J.Normal := by
  intro hJ
  haveI : J.Normal := hJ
  obtain ⟨e⟩ := hM
  let ρ : ↥M →* MulAut ↥J := (MulAut.conjNormal : Y →* MulAut ↥J).comp M.subtype
  have hρ_apply : ∀ m : ↥M, ρ m = MulAut.conjNormal ((m : Y)) := fun _ => rfl
  have hm4 : ∀ m : ↥M, m ^ 4 = 1 := by
    intro m
    apply e.injective
    rw [map_pow, map_one]
    exact z4c_pow_four (e m)
  have hsq_cent : ∀ m : ↥M, ((m : Y) ^ 2) ∈ Subgroup.centralizer (J : Set Y) := by
    intro m
    have hρ4 : ρ m ^ 4 = 1 := by rw [← map_pow, hm4 m, map_one]
    have hρ2 : ρ m ^ 2 = 1 := h4 (ρ m) hρ4
    have hρsq : ρ (m ^ 2) = 1 := by rw [map_pow, hρ2]
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hconj : ((m : Y) ^ 2) * j * ((m : Y) ^ 2)⁻¹ = j := by
      have h1 : ((ρ (m ^ 2) ⟨j, hj⟩ : ↥J) : Y) = j := by
        have := congrArg (fun φ : MulAut ↥J => ((φ ⟨j, hj⟩ : ↥J) : Y)) hρsq
        simpa using this
      rw [hρ_apply (m ^ 2), MulAut.conjNormal_apply] at h1
      simpa only [Subgroup.coe_pow] using h1
    have hgj : (m : Y) ^ 2 * j = j * (m : Y) ^ 2 := by
      have := congrArg (fun x => x * (m : Y) ^ 2) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
    exact hgj.symm
  let N : Subgroup Y := Subgroup.closure {x : Y | ∃ m ∈ M, x = m ^ 2}
  have hNleM : N ≤ M := by
    rw [Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    exact M.pow_mem hm 2
  let D : Subgroup Y := Subgroup.centralizer (J : Set Y)
  have hNleC : N ≤ D := by
    rw [Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    simpa [D] using hsq_cent ⟨m, hm⟩
  have hM4 : ∀ m : ↥M, ((m : Y)) ^ 4 = 1 := by
    intro m
    have := hm4 m
    simpa using congrArg (fun z : ↥M => (z : Y)) this
  have hNisP : IsPGroup 2 ↥N := by
    intro x
    refine ⟨2, ?_⟩
    have hx4 : x ^ 4 = 1 := by
      apply Subtype.ext
      have := hM4 ⟨(x : Y), hNleM x.2⟩
      simpa using this
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]
    exact hx4
  have hcardN : 8 ≤ Nat.card ↥N :=
    y6f4a_card_ge_eight ⟨e⟩ (fun m hm => Subgroup.subset_closure ⟨m, hm, rfl⟩)
  let N' : Subgroup ↥D := N.subgroupOf D
  have hcardN' : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleC).toEquiv
  have hN'isP : IsPGroup 2 ↥N' :=
    hNisP.of_equiv (Subgroup.subgroupOfEquivOfLe hNleC).symm
  obtain ⟨S, hSle⟩ := hN'isP.exists_le_sylow
  have hle2 : Nat.card ↥N ≤ 2 := by
    have h1 : Nat.card ↥N ≤ Nat.card ↥S := by
      rw [← hcardN']
      exact Subgroup.card_le_of_le hSle
    have hS2 : Nat.card ↥S = 2 := hS S
    omega
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
