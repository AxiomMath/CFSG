module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Model

variable {G : Type*} [Group G] {P R : Subgroup G}

@[expose] def IsAutModel (e : R ≃* MulAut P) : Prop :=
  ∀ (x : R) (p : P), ((e x p : P) : G) = (x : G) * p * (x : G)⁻¹

variable {hPR : P ≤ R} {e : R ≃* MulAut P}

theorem IsAutModel.apply_incl (hPR : P ≤ R) (he : IsAutModel e) (a : P) :
    e ⟨(a : G), hPR a.2⟩ = MulAut.conj a := by
  ext p
  exact (he _ p).trans (by simp [MulAut.conj_apply])

theorem IsAutModel.isInnerAut_iff (hPR : P ≤ R) (he : IsAutModel e) (x : R) :
    IsInnerAut (e x) ↔ (x : G) ∈ P := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 : e x = e ⟨(y : G), hPR y.2⟩ := hy.trans (he.apply_incl hPR y).symm
    have h2 : x = ⟨(y : G), hPR y.2⟩ := e.injective h1
    rw [h2]
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, he.apply_incl hPR ⟨x, hx⟩⟩

theorem OuterBetaFor.of_model [Finite P] (hPR : P ≤ R) (he : IsAutModel e)
    (hcard : Nat.card R = 2 * Nat.card P) {β : P} {x₀ : G} (hx₀R : x₀ ∈ R) (hx₀P : x₀ ∉ P)
    (hx₀β : x₀ * β = β * x₀)
    (hno : ∀ d : P, (d : G) * β = β * d → (d : G) * x₀ * ((d : G) * x₀) ≠ 1) :
    OuterBetaFor P β := by
  have hidx : (P.subgroupOf R).index = 2 := by
    have h1 := (P.subgroupOf R).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card P := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  refine ⟨⟨e ⟨x₀, hx₀R⟩, fun hin => hx₀P ((he.isInnerAut_iff hPR _).1 hin), ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [he]
    show x₀ * (β : G) * x₀⁻¹ = β
    rw [hx₀β]
    group
  · intro r hr1 hrβ
    set x : R := e.symm r with hx
    have hxr : e x = r := by rw [hx]; exact e.apply_symm_apply r
    by_cases hxP : (x : G) ∈ P
    · exact ((he.isInnerAut_iff hPR x).2 hxP).imp fun y hy => by rw [← hxr, hy]
    · exfalso
      have hxx : x * x = 1 := by
        apply e.injective
        rw [map_mul, hxr, hr1, map_one]
      have hxβ : (x : G) * β * (x : G)⁻¹ = β := by
        have := congrArg (fun q : P => (q : G)) (hrβ)
        rw [← hxr] at this
        exact (he x β).symm.trans this
      let x₀R : R := ⟨x₀, hx₀R⟩
      have hxx₀ : (x * x₀R⁻¹ : R) ∈ P.subgroupOf R := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        constructor
        · intro h
          exact absurd (mem_subgroupOf.1 h) hxP
        · intro h
          exact absurd (mem_subgroupOf.1 h) (by
            intro h'
            apply hx₀P
            have : (x₀R⁻¹)⁻¹ ∈ P.subgroupOf R := inv_mem h
            simpa using mem_subgroupOf.1 this)
      have hdP : (x : G) * x₀⁻¹ ∈ P := by simpa using mem_subgroupOf.1 hxx₀
      set d : P := ⟨(x : G) * x₀⁻¹, hdP⟩ with hd
      have hdβ : (d : G) * β = β * d := by
        show (x : G) * x₀⁻¹ * β = β * ((x : G) * x₀⁻¹)
        have h1 : x₀⁻¹ * (β : G) = β * x₀⁻¹ := by
          calc x₀⁻¹ * (β : G) = x₀⁻¹ * ((β : G) * x₀) * x₀⁻¹ := by group
            _ = x₀⁻¹ * (x₀ * (β : G)) * x₀⁻¹ := by rw [hx₀β]
            _ = (β : G) * x₀⁻¹ := by group
        calc (x : G) * x₀⁻¹ * β = (x : G) * (x₀⁻¹ * β) := by group
          _ = (x : G) * (β * x₀⁻¹) := by rw [h1]
          _ = ((x : G) * β) * x₀⁻¹ := by group
          _ = (β * (x : G)) * x₀⁻¹ := by
              rw [show (x : G) * β = β * x by
                have := hxβ
                rw [mul_inv_eq_iff_eq_mul] at this
                exact this]
          _ = β * ((x : G) * x₀⁻¹) := by group
      apply hno d hdβ
      have hxd : (d : G) * x₀ = x := by
        show (x : G) * x₀⁻¹ * x₀ = x
        group
      rw [hxd]
      exact congrArg Subtype.val hxx

theorem OuterInvData.of_model (hPR : P ≤ R) (he : IsAutModel e)
    {u : G} (huR : u ∈ R) (huP : u ∉ P) (hu2 : u * u = 1) (reps : List P)
    (hcls : ∀ a : P, a * a = 1 → a ≠ 1 → ∃ g : P, ∃ a₀ ∈ reps, a = g * a₀ * g⁻¹)
    (hsq : ∀ a₀ ∈ reps, ∃ y ∈ R, y * y = (a₀ : G)) : OuterInvData P := by
  refine OuterInvData.of_reps reps hcls ?_ ?_
  · intro a₀ h0
    obtain ⟨y, hyR, hy⟩ := hsq a₀ h0
    refine ⟨e ⟨y, hyR⟩, ?_⟩
    rw [← map_mul]
    have : (⟨y, hyR⟩ * ⟨y, hyR⟩ : R) = ⟨(a₀ : G), hPR a₀.2⟩ := Subtype.ext hy
    rw [this]
    exact he.apply_incl hPR a₀
  · refine ⟨e ⟨u, huR⟩, ?_, fun hin => huP ((he.isInnerAut_iff hPR _).1 hin)⟩
    rw [← map_mul]
    have : (⟨u, huR⟩ * ⟨u, huR⟩ : R) = 1 := Subtype.ext hu2
    rw [this, map_one]

end Model

end CFSG.EvenSporadicStandard.Fin76b
