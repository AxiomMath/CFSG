module

public import CFSG.LieType.SpecialLinear.TypeLabel.Basic
public import CFSG.LieType.SpecialLinear.TypeLabel.Period
public import CFSG.LieType.SpecialLinear.CentralCharacter

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {k : Type} [Field k]

theorem rankOne_hh_eq_hdiag (s : Fin m) (u : Fˣ) :
    (rankOne m F 2).hh s u = hdiag m F s u := rfl

theorem exists_eps_of_isCoverType [Algebra F k] (hF : Nat.card F = 2 ^ f)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    ∃ ε : Fin f → Finset (Fin (m + 1)), (∀ r, (0 : Fin (m + 1)) ∉ ε r) ∧
      (∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g) ∧
      ∀ s : Fin m, s ∈ J ↔ ∀ r, s.succ ∉ ε r := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ f := by rwa [Nat.card_eq_fintype_card] at hF
  let D := curtisDatum m F 2
  let H : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) := ⨆ s, torus m F s
  have hDH : D.H = H := rfl
  have hmulH : ∀ a ∈ H, ∀ b ∈ H, χ (a * b) = χ a * χ b := by
    intro a ha b hb
    have ha' : a ∈ D.H.comap (MonoidHom.id _) := by
      rw [Subgroup.comap_id]
      rwa [hDH]
    have hb' : b ∈ D.H.comap (MonoidHom.id _) := by
      rw [Subgroup.comap_id]
      rwa [hDH]
    exact ht.chi_mul_of_mem ha' hb'
  have hone : χ 1 = 1 := ht.chi_one
  let e : Fin m → ℕ := fun s => IsCoverType.exponent m F 2 ht s
  have he_lt : ∀ s, e s < Nat.card F - 1 := fun s =>
    IsCoverType.exponent_lt m F 2 ht s
  have he_val : ∀ (s : Fin m) (u : Fˣ),
      χ (hdiag m F s u) = (algebraMap F k (u : F)) ^ e s := fun s u =>
    IsCoverType.chi_hdiag_eq_pow m F 2 ht s u
  let a : Fin m → ℕ := fun s =>
    if s ∈ J then 0 else if e s = 0 then Nat.card F - 1 else e s
  let d : Fin (m + 1) → ℕ := Fin.cases 0 a
  have hd_lt : ∀ j, d j < 2 ^ f := by
    intro j
    induction j using Fin.cases with
    | zero => positivity
    | succ s =>
      change a s < 2 ^ f
      by_cases hsJ : s ∈ J
      · simp [a, hsJ]
      · by_cases he0 : e s = 0
        · simp [a, hsJ, he0]
          rw [hFcard]
          have : 0 < 2 ^ f := by positivity
          omega
        · simp [a, hsJ, he0]
          have hlt := he_lt s
          rw [hF] at hlt
          omega
  obtain ⟨ε, hε⟩ := exists_bDigit_eq d hd_lt
  have hεa : ∀ s : Fin m, bDigit ε s.succ = a s := fun s => by
    simpa [d] using hε s.succ
  have hzero : ∀ r, (0 : Fin (m + 1)) ∉ ε r := by
    refine (bDigit_eq_zero_iff ε 0).mp ?_
    simpa [d] using hε 0
  have hχeq : ∀ g ∈ H, χ g = slChiEps m (algebraMap F k) ε g := by
    refine eq_on_H_of_eq_hdiag m (χ := χ) (χ' := slChiEps m (algebraMap F k) ε)
      hmulH (fun a ha b hb => slChiEps_mul m (algebraMap F k) ε ha hb) hone
      (slChiEps_one m (algebraMap F k) ε) ?_
    intro s u
    rw [he_val s u, slChiEps_hdiag, hεa s]
    by_cases hsJ : s ∈ J
    · have hchi : χ (hdiag m F s u) = 1 := by
        have := ((ht.2.2.2 s).mp hsJ).1 u
        rwa [rankOne_hh_eq_hdiag] at this
      have hphi : (algebraMap F k (u : F)) ^ e s = 1 := by
        rw [← he_val s u]
        exact hchi
      rw [hphi, show a s = 0 by simp [a, hsJ], pow_zero]
    · by_cases he0 : e s = 0
      · have hphi : (algebraMap F k (u : F)) ^ e s = 1 := by rw [he0, pow_zero]
        have hq1 : (algebraMap F k (u : F)) ^ (Nat.card F - 1) = 1 := by
          rw [← map_pow]
          have h : (u : F) ^ (Nat.card F - 1) = 1 := by
            have hpow := FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero
            simpa [Nat.card_eq_fintype_card] using hpow
          rw [h, map_one]
        rw [hphi, show a s = Nat.card F - 1 by simp [a, hsJ, he0], hq1]
      · rw [show a s = e s by simp [a, hsJ, he0]]
  refine ⟨ε, hzero, ?_, ?_⟩
  · intro g hg
    exact hχeq g (by rwa [hDH] at hg)
  · intro s
    rw [← bDigit_eq_zero_iff ε s.succ, hεa s]
    constructor
    · intro hsJ
      simp [a, hsJ]
    · intro ha0
      by_contra hsJ
      by_cases he0 : e s = 0
      · have hq : a s = Nat.card F - 1 := by simp [a, hsJ, he0]
        rw [hq] at ha0
        have hgt : 0 < Nat.card F - 1 := by
          have hcard : 1 < Nat.card F := Finite.one_lt_card
          omega
        omega
      · have he : a s = e s := by simp [a, hsJ, he0]
        rw [he] at ha0
        exact he0 ha0

end

end CFSG.LieType.SpecialLinear
