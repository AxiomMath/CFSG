module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLRed
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.U

@[expose] def ClU.USplitInput : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), p ≠ 2 → ∀ {n : ℕ} (hn : 3 ≤ n),
    Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))) →
    ∀ (A : uU h n) {l : K}, l ≠ 0 → h.norm l = 1 →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1 →
      (∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c) →
    ∀ R : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K))), Odd (Nat.card R) →
      (∀ y ∈ R, y * uConjAut h (by omega) A = uConjAut h (by omega) A * y) →
      (∀ s, uConjAut h (by omega) A s = s → Odd (orderOf s) → ∀ y ∈ R,
        MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

@[expose] def ClU.UPairedInput : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), p ≠ 2 → ∀ {n : ℕ} (hn : 3 ≤ n),
    Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))) →
    ∀ (A : uU h n) {l : K}, l ≠ 0 → h.norm l = -1 →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1 →
    ∀ R : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K))), Odd (Nat.card R) →
      (∀ y ∈ R, y * uConjAut h (by omega) A = uConjAut h (by omega) A * y) →
      (∀ s, uConjAut h (by omega) A s = s → Odd (orderOf s) → ∀ y ∈ R,
        MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

@[expose] def ClU.UGraphInput : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), p ≠ 2 → ∀ {n : ℕ} (hn : 3 ≤ n),
    Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))) →
    ∀ (A : uU h n) {c : K},
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h) = c • 1 →
    ∀ R : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K))), Odd (Nat.card R) →
      (∀ y ∈ R, y * (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) =
        (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) * y) →
      (∀ s, (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h) :
          MulAut (StatedProj (StatedSU n (p ^ f) K))) s = s →
        Odd (orderOf s) → ∀ y ∈ R, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

theorem ClU.commute_psu (hsplit : ClU.USplitInput) (hpair : ClU.UPairedInput)
    (hgraph : ClU.UGraphInput) {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hq' : ¬(n = 3 ∧ p ^ f = 2))
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    (i : MulAut (StatedProj (StatedSU n (p ^ f) K))) (hi : orderOf i = 2)
    {R : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * i = i * y)
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  obtain ⟨A, φ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq' i
  have hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1 := by
    rw [← hi, pow_orderOf_eq_one]
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  rcases uFieldAut_eq_or_of_sq h hn hq' hsq with rfl | hφ
  ·
    rw [map_one, mul_one] at hsq hi hRi hRc
    rw [← map_pow] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
    have hAA : Am * Am = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
        at e
      rw [← pow_two, e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
    have hN : h.norm (c : K) = 1 := by
      have e : ((Am * Am).map h.bar)ᵀ * (Am * Am) = 1 := by
        rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
          Matrix.one_mul, hU]
      rw [hAA] at e
      have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
      simp [Matrix.mul_apply, Matrix.one_apply] at e1
      rw [UnitaryFieldData.norm, mul_comm]
      simpa [Matrix.smul_apply, Matrix.one_apply] using e1
    obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hN
    have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
    have hNl : h.norm l * h.norm l = 1 := by
      rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
      ring
    rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
    · have hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c := by
        intro c e
        have h1 : uConjAut h (by omega) A = 1 := (uConjAut_eq_one_iff h hn A).2 ⟨c, e⟩
        rw [h1, orderOf_one] at hi
        exact absurd hi (by decide)
      exact hsplit h hp2 hn hinj A hl0 hN1 hAA' hns R hRodd hRi hRc
    · exact hpair h hp2 hn hinj A hl0 hN1 hAA' R hRodd hRi hRc
  ·
    have hφe : φ = barEq h := RingEquiv.ext hφ
    subst hφe
    rw [graph_sq] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
    have hAc : Am * Am.map (barEq h) = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut]
        at e
      change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h) = _
      rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    exact hgraph h hp2 hn hinj A hAc R hRodd hRi hRc

theorem oddLieCoreFamilyInput_psu_of (hsplit : ClU.USplitInput) (hpair : ClU.UPairedInput)
    (hgraph : ClU.UGraphInput) : OddLieCoreFamilyInput .PSU := by
  intro S _ _ _ hna n p f hp hp2 hadm hm hL2 i hi R hRodd hRi hRc
  have hcl : StatedClassicalModel S .PSU n p f := by
    rcases hm with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals obtain ⟨-, -, hn, -⟩ := hadm; omega
  obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hKc, ⟨θ⟩⟩ := hcl
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e1, e2⟩ => hq (by rw [e1, e2])
  have hZ := center_eq_bot_of_mulEquiv θ (center_eq_bot_of_simple hna)
  have hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [← hZ, mem_center_iff]
    intro g
    have hg : x * g * x⁻¹ = g := by
      have := congrArg (fun φ : MulAut _ => φ g) (MonoidHom.mem_ker.1 hx)
      simpa [MulAut.conj_apply] using this
    calc g * x = x * g * x⁻¹ * x := by rw [hg]
      _ = x * g := by group
  refine commute_of_congr θ (fun R' hR'odd hR'i hR'c =>
    ClU.commute_psu hsplit hpair hgraph h hp2 hn hq' hinj _ ?_ hR'odd hR'i hR'c) hRodd hRi hRc
  rw [MulEquiv.orderOf_eq]
  exact hi

end CFSG.ComponentClassification.Foote5.OddLieCore
