module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisProj
public import CFSG.RankThree.PartOne.KC.LinearPlaneCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane

variable {n : ℕ} {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact (1 < p)]
variable {ψ : AddChar (ZMod p) F}

section Split

variable {x : Module.End F (Fin n → F)} {e : F}

theorem commute_eigProj (a : Module.End F (Fin n → F)) (j : ZMod p) {y : Module.End F (Fin n → F)}
    (hay : Commute a y) : Commute (eigProj ψ a j) y := by
  unfold eigProj
  refine Commute.smul_left (Commute.sum_left _ _ _ fun k _ => ?_) _
  exact Commute.smul_left (hay.pow_left _) _

theorem aeval_X_sub_C_apply (μ : F) (v : Fin n → F) :
    aeval x (X - C μ) v = x v - μ • v := by
  simp [map_sub]

theorem apply_of_mem_range_eigProj (he : e ≠ 0) (ha : (e⁻¹ • x) ^ p = 1) (j : ZMod p)
    {w : Fin n → F} (hw : w ∈ LinearMap.range (eigProj ψ (e⁻¹ • x) j))
    (hpF : (p : F) ≠ 0) : x w = (e * ψ j) • w := by
  have := (mem_range_eigProj_iff (ψ := ψ) ha hpF j w).1 hw
  simp only [LinearMap.smul_apply] at this
  have h2 : x w = e • (e⁻¹ • x w) := by rw [smul_smul, mul_inv_cancel₀ he, one_smul]
  rw [h2, this, smul_smul]

theorem exists_ne_zero_of_dim (j : ZMod p) {a : Module.End F (Fin n → F)}
    (hdim : 2 ≤ finrank F (LinearMap.range (eigProj ψ a j))) :
    ∃ v ∈ LinearMap.range (eigProj ψ a j), v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : LinearMap.range (eigProj ψ a j) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot F).2 (hcon v hv)
  rw [this] at hdim
  simp at hdim

theorem mem_primaryFactors_split {a : Module.End F (Fin n → F)} (hax : e⁻¹ • x = a) (hpF : (p : F) ≠ 0) (he : e ≠ 0) (ha : a ^ p = 1)
    (hdim : ∀ j, 2 ≤ finrank F (LinearMap.range (eigProj ψ a j))) (j : ZMod p) :
    (X - C (e * ψ j) : F[X]) ∈ primaryFactors x := by
  subst hax
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_dim j (hdim j)
  refine mem_primaryFactors_of_ne_zero (irreducible_X_sub_C _) (monic_X_sub_C _) hv0 ?_
  rw [mem_primaryComponent, aeval_X_sub_C_apply, apply_of_mem_range_eigProj he ha j hv hpF,
    sub_self]

theorem primaryProjection_split {a : Module.End F (Fin n → F)} (hax : e⁻¹ • x = a) [FiniteDimensional F (Fin n → F)] (hpF : (p : F) ≠ 0)
    (he : e ≠ 0) (hψ : ψ.IsPrimitive) (ha : a ^ p = 1)
    (hsq : Squarefree (minpoly F x))
    (hdim : ∀ j, 2 ≤ finrank F (LinearMap.range (eigProj ψ a j))) (j : ZMod p) :
    primaryProjection x (X - C (e * ψ j)) = eigProj ψ a j := by
  subst hax
  have hmem := mem_primaryFactors_split rfl hpF he ha hdim j
  set P := primaryProjection x (X - C (e * ψ j)) with hP
  set E := eigProj ψ (e⁻¹ • x) j with hE
  have hEx : Commute E x := by
    refine commute_eigProj _ j ?_
    exact ((Commute.refl x).smul_left _)
  have hEP : Commute E P := commute_aeval hEx _
  refine LinearMap.ext fun v => ?_
  have h1 : E (P v) = P v := by
    have hPv := primaryProjection_mem hsq hmem v
    rw [mem_primaryComponent, aeval_X_sub_C_apply, sub_eq_zero] at hPv
    refine eigProj_apply_eigen hpF ?_
    simp only [LinearMap.smul_apply]
    rw [hPv, smul_smul, inv_mul_cancel_left₀ he]
  have h2 : P (E v) = E v := by
    refine primaryProjection_of_mem hsq hmem ?_
    rw [mem_primaryComponent, aeval_X_sub_C_apply, apply_of_mem_range_eigProj he ha j
      (LinearMap.mem_range_self _ v) hpF, sub_self]
  calc P v = E (P v) := h1.symm
    _ = P (E v) := by
      have := congrArg (fun g : Module.End F (Fin n → F) => g v) hEP.eq
      simpa [Module.End.mul_apply] using this
    _ = E v := h2

theorem eq_X_sub_C_of_mem_primaryFactors_split {a : Module.End F (Fin n → F)} (hax : e⁻¹ • x = a) [FiniteDimensional F (Fin n → F)]
    (hpF : (p : F) ≠ 0) (he : e ≠ 0) (hψ : ψ.IsPrimitive) (ha : a ^ p = 1)
    (hsq : Squarefree (minpoly F x))
    (hdim : ∀ j, 2 ≤ finrank F (LinearMap.range (eigProj ψ a j)))
    {h : F[X]} (hh : h ∈ primaryFactors x) : ∃ j : ZMod p, h = X - C (e * ψ j) := by
  subst hax
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq hh)
  have hsum := LinearMap.congr_fun (sum_eigProj hψ (a := e⁻¹ • x) ha hpF) v
  rw [LinearMap.sum_apply] at hsum
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun j => eigProj ψ (e⁻¹ • x) j v) (by
      intro h0
      have hv' : v = ∑ j, eigProj ψ (e⁻¹ • x) j v := by rw [hsum]; rfl
      exact hv0 (hv'.trans h0))
  refine ⟨j, ?_⟩
  have hEx : Commute (eigProj ψ (e⁻¹ • x) j) x :=
    commute_eigProj _ j ((Commute.refl x).smul_left _)
  have hwh : eigProj ψ (e⁻¹ • x) j v ∈ primaryComponent x h :=
    apply_mem_primaryComponent hEx hv
  have hwμ : eigProj ψ (e⁻¹ • x) j v ∈ primaryComponent x (X - C (e * ψ j)) := by
    rw [mem_primaryComponent, aeval_X_sub_C_apply,
      apply_of_mem_range_eigProj he ha j (LinearMap.mem_range_self _ v) hpF, sub_self]
  by_contra hne
  exact hj (eq_zero_of_mem_primaryComponent_ne hh (mem_primaryFactors_split rfl hpF he ha hdim j)
    hne hwh hwμ)

theorem primaryComponent_split_eq {a : Module.End F (Fin n → F)} (hax : e⁻¹ • x = a) (hpF : (p : F) ≠ 0) (he : e ≠ 0) (ha : a ^ p = 1)
    (j : ZMod p) :
    primaryComponent x (X - C (e * ψ j)) = LinearMap.range (eigProj ψ a j) := by
  subst hax
  ext v
  rw [mem_primaryComponent, aeval_X_sub_C_apply, sub_eq_zero, mem_range_eigProj_iff ha hpF]
  simp only [LinearMap.smul_apply]
  constructor
  · intro hv
    rw [hv, smul_smul, inv_mul_cancel_left₀ he]
  · intro hv
    have h2 : x v = e • (e⁻¹ • x v) := by rw [smul_smul, mul_inv_cancel₀ he, one_smul]
    rw [h2, hv, smul_smul]

theorem goodBlock_split {a : Module.End F (Fin n → F)} (hax : e⁻¹ • x = a) [Finite F] [FiniteDimensional F (Fin n → F)] (hpF : (p : F) ≠ 0)
    (he : e ≠ 0) (hψ : ψ.IsPrimitive) (ha : a ^ p = 1)
    (hsq : Squarefree (minpoly F x))
    (hdim : ∀ j, 2 ≤ finrank F (LinearMap.range (eigProj ψ a j)))
    (hF4 : 3 < Nat.card F) (h : primaryFactors x) : GoodBlock h := by
  subst hax
  obtain ⟨j, hj⟩ := eq_X_sub_C_of_mem_primaryFactors_split rfl hpF he hψ ha hsq hdim h.2
  have hfr := finrank_primaryComponent x (h : F[X])
  have hcomp : primaryComponent x (h : F[X]) = LinearMap.range (eigProj ψ (e⁻¹ • x) j) := by
    rw [hj]
    exact primaryComponent_split_eq rfl hpF he ha j
  have hdeg : (h : F[X]).natDegree = 1 := by rw [hj, natDegree_X_sub_C]
  rw [hdeg, one_mul] at hfr
  have h2' : 2 ≤ finrank F (primaryComponent x (h : F[X])) := by
    rw [hcomp]
    exact hdim j
  have h2 : 2 ≤ mult x h := by
    unfold mult primaryMultiplicity
    omega
  refine Or.inr ⟨h2, ?_⟩
  have hcard : Nat.card (Efac x h) = Nat.card F ^ (h : F[X]).natDegree :=
    natCard_adjoinRoot (h : F[X])
  rw [hcard, hdeg, pow_one]
  exact hF4

end Split

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
