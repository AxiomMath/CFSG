module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakDefs
public import CFSG.CGT.PushingUpLit.SolKR2.Pair

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n (conjSubgroup_mul)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

section Core

variable
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
  {h : R2 M B} {g m α x : G} (D : R2StarData h g m α x)
include hCen hU D

theorem weakEnd_core {X F₀ : Subgroup G}
    (hX : X = conjSubgroup g (omegaTwoSub B) ⊔ conjSubgroup α (conjSubgroup g (omegaTwoSub B)))
    (hF₀ : ∃ y : G, F₀ = conjSubgroup y (omegaOneSub B))
    (hFX : F₀ ≤ Subgroup.centralizer (X : Set G))
    (hA : ∀ a ∈ conjSubgroup m (omegaOneSub B), ∃ z ∈ X, ∃ f ∈ F₀, a = z * f) : False := by
  obtain ⟨y, rfl⟩ := hF₀
  set D₁ := conjSubgroup g (omegaTwoSub B) with hD₁
  set C₁ := conjSubgroup x D₁ with hC₁
  set F₁ := conjSubgroup y (omegaTwoSub B) with hF₁
  have K := D.data31.core
  have hαmem := D.data31.mem
  have hα1 := D.data31.ne_one
  have hXC : X = D₁ ⊔ C₁ := hX.trans (D.data31.sup_eq hCen hU hαmem hα1)
  have hC₁X : C₁ ≤ X := by rw [hXC]; exact le_sup_right
  have hD₁X : D₁ ≤ X := by rw [hXC]; exact le_sup_left
  have hFX' : ∀ f ∈ conjSubgroup y (omegaOneSub B), ∀ z ∈ X, f * z = z * f := fun f hf z hz =>
    (Subgroup.mem_centralizer_iff.mp (hFX hf) z hz).symm
  have hF₀F₁ : conjSubgroup y (omegaOneSub B) ≤ F₁ := Pair.conj_B0_le_U h y
  have hF₁c := Pair.comm_conj_U h y
  have hC₁F : ∀ a ∈ C₁, ∀ b ∈ F₁, a * b = b * a := by
    have := D.comm_of_cent y (x * g) (by
      rw [conjSubgroup_mul]
      intro f hf
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (hFX' f hf c (hC₁X hc)).symm)
    rw [conjSubgroup_mul] at this
    exact this
  have hD₁F : ∀ a ∈ D₁, ∀ b ∈ F₁, a * b = b * a := by
    refine D.comm_of_cent y g ?_
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hFX' f hf c (hD₁X hc)).symm
  have hXF : ∀ z ∈ X, ∀ b ∈ F₁, z * b = b * z := by
    have : X ≤ Subgroup.centralizer (F₁ : Set G) := by
      rw [hXC]
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hD₁F a ha b hb).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hC₁F a ha b hb).symm
    intro z hz b hb
    exact (Subgroup.mem_centralizer_iff.mp (this hz) b hb).symm
  have hA₀F : ∀ a ∈ conjSubgroup m (omegaOneSub B), ∀ b ∈ F₁, b * a = a * b := by
    intro a ha b hb
    obtain ⟨z, hz, f, hf, rfl⟩ := hA a ha
    calc b * (z * f) = (b * z) * f := by group
      _ = (z * b) * f := by rw [← hXF z hz b hb]
      _ = z * (b * f) := by group
      _ = z * (f * b) := by rw [hF₁c b hb f (hF₀F₁ hf)]
      _ = z * f * b := by group
  have hD₀F : ∀ a ∈ conjSubgroup g (omegaOneSub B), ∀ b ∈ F₁, b * a = a * b := by
    intro a ha b hb
    exact (hXF a (hD₁X (Pair.conj_B0_le_U h g ha)) b hb).symm
  have hcomm := D.gamma_comm y m g
    (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hA₀F a ha b hb)
    (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hD₀F a ha b hb)
  have hΩ : omegaOneSub (conjSubgroup (m * g⁻¹) D₁) = conjSubgroup m (omegaOneSub B) := by
    rw [hD₁, ← conjSubgroup_mul, inv_mul_cancel_right]
    exact Pair.omegaOne_conj_U h m
  have hΩ' : omegaOneSub D₁ = conjSubgroup g (omegaOneSub B) := Pair.omegaOne_conj_U h g
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one, hΩ'] at hβ
  rw [hΩ] at hαmem
  exact K.not_comm (by rwa [hΩ]) hα1 (by rwa [hΩ']) hβ1 (hcomm α hαmem β hβ)

end Core

end CFSG.CGT.PushingUpLit.SolKR2
