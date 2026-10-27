module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X8
public import CFSG.ClassicalInvolution.Asc77.AscCX4L4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


theorem reflWit_psl4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hsq : ¬ IsSquare (-1 : GaloisField p f))
    {Y : Type} [Group Y] [Finite Y] (ψ : SL(4, GaloisField p f) →* Y)
    (hker : ψ.ker ≤ Subgroup.center SL(4, GaloisField p f)) (hsurj : Function.Surjective ψ)
    {R R' : Subgroup SL(4, GaloisField p f)}
    (hR : R ∈ longRootSet (K := GaloisField p f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := GaloisField p f) (show 2 ≤ 4 by norm_num))
    {Φ : Set (Subgroup Y)} {z' a₀ b₀ : Y} (htw : TwinSect0 Φ (R.map ψ) (R'.map ψ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ R.map ψ, β y = y) (hβA' : ∀ y ∈ R'.map ψ, β y = y) (hβ2 : β * β = 1)
    (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj z') :
    ∃ (hA : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup β))
      (hB : R.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
      (hB' : R'.map ψ ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
      IsOm5 p f (centTG _ _ β hA hA') ∧ IsOm5 p f (centTG _ _ (β * MulAut.conj z') hB hB') ∧
        DiagWit p (centTG _ _ β hA hA') (centTG _ _ (β * MulAut.conj z') hB hB') := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => htw.ne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hψi⟩ := CX4.L4.twin_data h2 ψ hker hi htw.hzA
  obtain ⟨hi'R, hi'2, hi'1, hψi'⟩ := CX4.L4.twin_data h2 ψ hker hi' htw.hzA'
  have hc : i' * i⁻¹ ∈ Subgroup.center SL(4, GaloisField p f) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ := twin_std h2 ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hk := CX4.L4.ker_eq_scalars h2 hsq ψ hker hi hi' hRR htw.hzA htw.hzA'
  set θ := ψ.comp (MulAut.conj g).toMonoidHom with hθdef
  have hθ : Function.Surjective θ := fun y => by
    obtain ⟨s, rfl⟩ := hsurj y
    refine ⟨g⁻¹ * s * g, ?_⟩
    simp only [hθdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    congr 1
    group
  have hθker : θ.ker = scalars 4 (GaloisField p f) := by
    ext x
    rw [MonoidHom.mem_ker]
    show ψ (g * x * g⁻¹) = 1 ↔ x ∈ scalars 4 (GaloisField p f)
    rw [← MonoidHom.mem_ker, hk]
    constructor
    · intro h
      have hcen := Subgroup.mem_center_iff.mp ((scalars_eq_center 4 (GaloisField p f)).le h)
      have e : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = (g * x * g⁻¹) * g⁻¹ * g := by rw [hcen g⁻¹]
          _ = g * x * g⁻¹ := by group
      rw [e]
      exact h
    · intro h
      have hcen := Subgroup.mem_center_iff.mp ((scalars_eq_center 4 (GaloisField p f)).le h)
      have e : g * x * g⁻¹ = x := by rw [hcen g]; group
      rw [e]
      exact h
  have hAθ : R.map ψ = (blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ := by
    rw [hRg, Subgroup.map_map]
  have hA'θ : R'.map ψ = (blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ := by
    rw [hR'g, Subgroup.map_map]
  have hzθ : z' = θ (rootInv (GaloisField p f) (show 2 ≤ 4 by norm_num)) := by
    rw [← hψi, hig]
    rfl
  rw [hAθ] at htw hβA ⊢
  rw [hA'θ] at htw hβA' ⊢
  subst hzθ
  exact reflWit_std hp2 hq hsq θ hθ hθker htw hconj β hβA hβA' hβ2 hβ1 hβz

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
