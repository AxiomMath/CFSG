module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup

theorem ff_gen {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hcomm : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hsq : ∀ a : H, a * a ∈ Z)
    (hcard : Nat.card H = 16 * Nat.card Z)
    (σ : H ≃* H) (hσ2 : ∀ a, σ (σ a) = a) (hσZ : ∀ z ∈ Z, σ z ∈ Z)
    (p₁ p₂ : H) (h₁ : p₁ * σ p₁ ∉ Z) (h₂ : p₂ * σ p₂ ∉ Z)
    (h₁₂ : p₁ * σ p₁ * (p₂ * σ p₂) ∉ Z) :
    ∀ s : H, s * σ s ∈ Z → ∃ p : H, s⁻¹ * (p * σ p) ∈ Z := by
  classical
  let _ : CommGroup (H ⧸ Z) :=
    { (inferInstance : Group (H ⧸ Z)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with
        | H a =>
          induction y using QuotientGroup.induction_on with
          | H b =>
            refine QuotientGroup.eq.2 ?_
            simpa [mul_assoc] using hcomm b⁻¹ a⁻¹ }
  have hE16 : Nat.card (H ⧸ Z) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hpos : 0 < Nat.card Z := Nat.card_pos
    rw [hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have hEsq : ∀ e : H ⧸ Z, e * e = 1 := by
    intro e
    induction e using QuotientGroup.induction_on with
    | H a => exact (QuotientGroup.eq_one_iff (a * a)).2 (hsq a)
  have hEinv : ∀ e : H ⧸ Z, e⁻¹ = e := fun e => inv_eq_of_mul_eq_one_right (hEsq e)
  let σb : H ⧸ Z →* H ⧸ Z := QuotientGroup.map Z Z σ.toMonoidHom (fun z hz => hσZ z hz)
  have hσb : ∀ a : H, σb (a : H ⧸ Z) = ((σ a : H) : H ⧸ Z) := fun a => rfl
  have hσb2 : ∀ e : H ⧸ Z, σb (σb e) = e := by
    intro e
    induction e using QuotientGroup.induction_on with
    | H a => rw [hσb, hσb, hσ2]
  let ν : H ⧸ Z →* H ⧸ Z :=
    MonoidHom.mk' (fun e => e * (σb e)⁻¹) (by
      intro x y
      simp only [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  have hνe : ∀ e : H ⧸ Z, ν e = e * σb e := fun e => by
    show e * (σb e)⁻¹ = e * σb e
    rw [hEinv]
  have hν : ∀ p : H, ν (p : H ⧸ Z) = ((p * σ p : H) : H ⧸ Z) := fun p => by
    rw [hνe, hσb, QuotientGroup.mk_mul]
  have hνν : ∀ e : H ⧸ Z, ν (ν e) = 1 := by
    intro e
    rw [hνe, hνe, map_mul, hσb2]
    calc e * σb e * (σb e * e) = (e * e) * (σb e * σb e) := by ac_rfl
      _ = 1 := by rw [hEsq, hEsq, one_mul]
  have hle : ν.range ≤ ν.ker := by
    rintro _ ⟨e, rfl⟩
    exact hνν e
  have hker_range : Nat.card ν.ker * Nat.card ν.range = 16 :=
    (Subgroup.card_ker_mul_card_range ν).trans hE16
  have key4 : ∀ a b : H ⧸ Z, a ∈ ν.range → b ∈ ν.range → a ≠ 1 → b ≠ 1 → a * b ≠ 1 →
      4 ≤ Nat.card ν.range := by
    intro a b ha hb ha1 hb1 hab1
    have hab : a ≠ b := fun h => hab1 (by rw [h, hEsq])
    have hab' : a ≠ a * b := fun h => hb1 (by simpa using h)
    have hba' : b ≠ a * b := fun h => ha1 (by simpa using h)
    have h1a : (1 : H ⧸ Z) ≠ a := ha1.symm
    have h1b : (1 : H ⧸ Z) ≠ b := hb1.symm
    have h1ab : (1 : H ⧸ Z) ≠ a * b := hab1.symm
    have hS : ({1, a, b, a * b} : Finset (H ⧸ Z)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [h1a, h1b, h1ab]),
        Finset.card_insert_of_notMem (by simp [hab, hab']), Finset.card_pair hba']
    have hsub : (({1, a, b, a * b} : Finset (H ⧸ Z)) : Set (H ⧸ Z)) ⊆
        (ν.range : Set (H ⧸ Z)) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ν.range.one_mem
      · exact ha
      · exact hb
      · exact ν.range.mul_mem ha hb
    have := Set.ncard_le_ncard hsub
    rwa [Set.ncard_coe_finset, hS] at this
  have h4 : 4 ≤ Nat.card ν.range :=
    key4 ((p₁ * σ p₁ : H) : H ⧸ Z) ((p₂ * σ p₂ : H) : H ⧸ Z)
      ⟨(p₁ : H ⧸ Z), hν p₁⟩ ⟨(p₂ : H ⧸ Z), hν p₂⟩
      (fun h => h₁ ((QuotientGroup.eq_one_iff _).1 h))
      (fun h => h₂ ((QuotientGroup.eq_one_iff _).1 h))
      (fun h => h₁₂ ((QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_mul]; exact h)))
  have hker4 : Nat.card ν.ker ≤ 4 := by
    by_contra hlt
    have hlt' : 5 ≤ Nat.card ν.ker := not_le.1 hlt
    have : 5 * 4 ≤ Nat.card ν.ker * Nat.card ν.range := Nat.mul_le_mul hlt' h4
    omega
  have heq : ν.range = ν.ker := Subgroup.eq_of_le_of_card_ge hle (hker4.trans h4)
  intro s hs
  have hker : (s : H ⧸ Z) ∈ ν.ker := by
    rw [MonoidHom.mem_ker, hν]
    exact (QuotientGroup.eq_one_iff _).2 hs
  rw [← heq] at hker
  obtain ⟨e, he⟩ := hker
  induction e using QuotientGroup.induction_on with
  | H p =>
    refine ⟨p, ?_⟩
    rw [hν] at he
    exact QuotientGroup.eq.1 he.symm

end CFSG.OddStandard.ChengHeld.Sec1
