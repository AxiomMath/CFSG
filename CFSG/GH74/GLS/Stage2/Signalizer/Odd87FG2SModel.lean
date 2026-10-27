module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SCross
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Three

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open scoped MatrixGroups
open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem noPNorm_of_inner {Y : Type} [Group Y] (hZ : center Y = ⊥)
    (hNo : ∀ g : Y, g * g = 1 → g ≠ 1 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup Y,
      IsPGroup p ↥X → X ≠ ⊥ → centralizer ({g} : Set Y) ≤ normalizer (X : Set Y) → False)
    {α : MulAut Y} (hin : α ∈ (MulAut.conj : Y →* MulAut Y).range) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    NoPNorm α := by
  obtain ⟨g, rfl⟩ := hin
  have hgg : g * g = 1 := by
    have hmem : g * g ∈ center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun σ : MulAut Y => σ y) hα2
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = (g * g) * y := by group
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hg1 : g ≠ 1 := fun h1 => hα1 (by rw [h1, map_one])
  have hfix : fixSub (MulAut.conj g) = centralizer ({g} : Set Y) := by
    ext s
    rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulAut.conj_apply]
    constructor
    · intro h1
      calc s * g = (g * s * g⁻¹) * g := by rw [h1]
        _ = g * s := by group
    · intro h1
      calc g * s * g⁻¹ = (s * g) * g⁻¹ := by rw [← h1]
        _ = s := by group
  intro p _ hp2 X hX hX1 hN
  rw [hfix] at hN
  exact hNo g hgg hg1 p hp2 X hX hX1 hN

theorem g2_small_arith {q p d : ℕ} (hq : q = 5 ∨ q = 7 ∨ q = 9) (hp : p.Prime) (hpq : ¬ p ∣ q)
    (h2 : 2 ≤ d) (hdiv : p ^ d * (q * (q ^ 2 - 1) * (q * (q ^ 2 - 1))) ∣ CFSG.Open.ordG2 q) : False := by
  have hsq : ¬ p ^ 2 ∣ q ^ 4 * (q ^ 4 + q ^ 2 + 1) := by
    intro h
    have hcop : Nat.Coprime (p ^ 2) (q ^ 4) :=
      Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
    have h1 : p ^ 2 ∣ q ^ 4 + q ^ 2 + 1 := hcop.dvd_of_dvd_mul_left h
    rcases hq with rfl | rfl | rfl
    · have : Squarefree (651 : ℕ) := by decide +kernel
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (this p (by simpa [sq] using h1)))
    · have : Squarefree (2451 : ℕ) := by decide +kernel
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (this p (by simpa [sq] using h1)))
    · have : Squarefree (6643 : ℕ) := by decide +kernel
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (this p (by simpa [sq] using h1)))
  have hord : CFSG.Open.ordG2 q = (q * (q ^ 2 - 1) * (q * (q ^ 2 - 1))) * (q ^ 4 * (q ^ 4 + q ^ 2 + 1)) := by
    rcases hq with rfl | rfl | rfl <;> norm_num [CFSG.Open.ordG2]
  rw [hord, mul_comm (p ^ d)] at hdiv
  have hpos : 0 < q * (q ^ 2 - 1) * (q * (q ^ 2 - 1)) := by
    rcases hq with rfl | rfl | rfl <;> norm_num
  have h3 : p ^ d ∣ q ^ 4 * (q ^ 4 + q ^ 2 + 1) := (Nat.mul_dvd_mul_iff_left hpos).mp hdiv
  exact hsq ((pow_dvd_pow p h2).trans h3)


section Certs


theorem g2_noPNorm_cross {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ r ^ f) (hm : LieModel Y .G2 0 r f) {u : Y} (hu : u * u = 1) (hu1 : u ≠ 1)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpr : p ≠ r) {X : Subgroup Y} (hX : IsPGroup p ↥X)
    (hX1 : X ≠ ⊥) (hN : centralizer ({u} : Set Y) ≤ normalizer (X : Set Y)) : False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hadm : StatedLieAdmissible .G2 0 r f := ⟨hr, hf, rfl, by omega⟩
  obtain ⟨ψ⟩ := equiv_modelUniv_g2 hr hr2 hf (by omega) hm
  have hO : InvOddCore Y := invOddCore_of_equiv ψ fun v hv2 hv1 N hN hNn hNodd =>
    Asc77.thm5IH_g2_oddCoreTrivial hr2 hadm v hv2 hv1 N hN hNn hNodd
  have hodd := hO u hu hu1
  have hShape : ∀ e : Y, e * e = 1 → e ≠ 1 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂)
      (_ : Finite F₁) (_ : Finite F₂) (S : Shape ↥(centralizer ({e} : Set Y)) F₁ F₂),
        Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ ringChar F₁ ≠ p ∧ ringChar F₂ ≠ p := by
    intro e he he1
    obtain ⟨F, hF, hFin, S, hcard, hSz⟩ :=
      CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hr hr2 hm e (orderOf_eq_two_of_inv he he1)
    have hodd' : Odd (Nat.card F) := by rw [hcard]; exact (hr.odd_of_ne_two hr2).pow
    have hch : ringChar F = r := ringChar_eq_of_card hr hcard
    exact ⟨F, F, hF, hF, hFin, hFin, S, hodd', hodd', by rw [hch]; exact hpr.symm, by rw [hch]; exact hpr.symm⟩
  obtain ⟨F, hF, hFin, S, hcard, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hr hr2 hm u (orderOf_eq_two_of_inv hu hu1)
  have hodd' : Odd (Nat.card F) := by rw [hcard]; exact (hr.odd_of_ne_two hr2).pow
  have hch : ringChar F = r := ringChar_eq_of_card hr hcard
  obtain ⟨d, hd4, hdw, hdiv⟩ := cross_char_core hu hp2 hodd hShape S hSz hodd' (by rw [hcard]; exact h5)
    (by rw [hch]; exact hpr.symm) hX hX1 hN
  rw [hcard] at hdw
  have hp : p.Prime := Fact.out
  by_cases hq : 11 ≤ r ^ f
  · omega
  ·
    have hq' : r ^ f = 5 ∨ r ^ f = 7 ∨ r ^ f = 9 := by
      have hodd'' : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
      obtain ⟨k, hk⟩ := hodd''
      omega
    have hd2 : 2 ≤ d := by omega
    obtain ⟨F', hF', hFin', hcard', ⟨e⟩⟩ := exists_equiv_of_lieModel hm
    have hcardY : Nat.card Y = CFSG.Open.ordG2 (r ^ f) := by
      rw [Nat.card_congr e.toEquiv]
      have := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := F')
      rw [hcard'] at this
      exact this
    have hcardD : Nat.card ↥(centralizer ({u} : Set Y)) =
        (r ^ f) * ((r ^ f) ^ 2 - 1) * ((r ^ f) * ((r ^ f) ^ 2 - 1)) := by
      have := shape_card S hodd' hodd'
      rwa [hcard] at this
    rw [hcardY, hcardD] at hdiv
    exact g2_small_arith hq' hp (by
      intro hpd
      have : p ∣ r := hp.dvd_of_dvd_pow hpd
      exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp this)) hd2 hdiv


theorem td4_noPNorm_cross {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 r f) {u : Y} (hu : u * u = 1) (hu1 : u ≠ 1)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpr : p ≠ r) {X : Subgroup Y} (hX : IsPGroup p ↥X)
    (hX1 : X ≠ ⊥) (hN : centralizer ({u} : Set Y) ≤ normalizer (X : Set Y)) : False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hadm : StatedLieAdmissible .trialityD4 0 r f := ⟨hr, hf, rfl⟩
  obtain ⟨ψ⟩ := equiv_modelUniv_d4 hr hr2 hf hm
  have hO : InvOddCore Y := invOddCore_of_equiv ψ fun v hv2 hv1 N hN hNn hNodd =>
    Asc77.thm5IH_td4_oddCoreTrivial hr2 hadm v hv2 hv1 N hN hNn hNodd
  have hodd := hO u hu hu1
  have h3 : 3 ≤ r ^ f := by
    calc 3 ≤ r := by have := hr.two_le; omega
      _ ≤ r ^ f := Nat.le_self_pow (by omega) r
  have hShape : ∀ e : Y, e * e = 1 → e ≠ 1 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂)
      (_ : Finite F₁) (_ : Finite F₂) (S : Shape ↥(centralizer ({e} : Set Y)) F₁ F₂),
        Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ ringChar F₁ ≠ p ∧ ringChar F₂ ≠ p := by
    intro e he he1
    obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, hSz⟩ :=
      CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 hr hr2 hm e (orderOf_eq_two_of_inv he he1)
    have hodd₁ : Odd (Nat.card F₁) := by rw [hc₁]; exact ((hr.odd_of_ne_two hr2).pow).pow
    have hodd₂ : Odd (Nat.card F₂) := by rw [hc₂]; exact (hr.odd_of_ne_two hr2).pow
    have hch₁ : ringChar F₁ = r := ringChar_eq_of_card (f := f * 3) hr (by rw [hc₁, ← pow_mul])
    have hch₂ : ringChar F₂ = r := ringChar_eq_of_card hr hc₂
    exact ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hodd₁, hodd₂, by rw [hch₁]; exact hpr.symm,
      by rw [hch₂]; exact hpr.symm⟩
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 hr hr2 hm u (orderOf_eq_two_of_inv hu hu1)
  have hodd₁ : Odd (Nat.card F₁) := by rw [hc₁]; exact ((hr.odd_of_ne_two hr2).pow).pow
  have hch₁ : ringChar F₁ = r := ringChar_eq_of_card (f := f * 3) hr (by rw [hc₁, ← pow_mul])
  have h27 : 27 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (r ^ f) ^ 3 := Nat.pow_le_pow_left h3 3
  obtain ⟨d, hd4, hdw, -⟩ := cross_char_core hu hp2 hodd hShape S hSz hodd₁ (by omega)
    (by rw [hch₁]; exact hpr.symm) hX hX1 hN
  omega

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
