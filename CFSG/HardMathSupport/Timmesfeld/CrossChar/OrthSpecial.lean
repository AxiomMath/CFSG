module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SLOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2

section Unitary

open Matrix CFSG.LieType.Universal.Unitary

theorem exists_orderOf_SUid_of_conj_inv {E : Type*} [Field E] (σ : E ≃+* E) {p n : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) {ζ : E} (hζ : IsPrimitiveRoot ζ p) (hσ : σ ζ = ζ⁻¹) :
    ∃ s : SUid σ n, orderOf s = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  let v : Fin n → E := fun i => if i = ⟨0, by omega⟩ then ζ else
    if i = ⟨1, by omega⟩ then ζ⁻¹ else 1
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne]
    · simp [v, hζ0]
    · intro c _ hc
      simp [v, hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  let s : SpecialLinearGroup (Fin n) E := ⟨Matrix.diagonal v, hdet⟩
  have hσv : ∀ i, σ (v i) * v i = 1 := fun i => by
    by_cases h0 : i = ⟨0, by omega⟩
    · simp [v, h0, hσ, hζ0]
    · by_cases h1 : i = ⟨1, by omega⟩
      · simp [v, h1, hne.symm, hσ, hζ0]
      · simp [v, h0, h1]
  have hmem : s.toGL ∈ SUid σ n := by
    refine ⟨by simp, ?_⟩
    have : conjTr σ (Matrix.diagonal v) = Matrix.diagonal (fun i => σ (v i)) := by
      simp [conjTr, Matrix.diagonal_map, map_zero]
    change conjTr σ (Matrix.diagonal v) * Matrix.diagonal v = 1
    rw [this, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext hσv)
  refine ⟨⟨s.toGL, hmem⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  show orderOf s.toGL = p
  rw [orderOf_injective (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) E →* _)
    (fun a b hab => by simp at hab; exact hab) s]
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    change (Matrix.diagonal v) ^ p = 1
    rw [Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq]
      by_cases h0 : i = ⟨0, by omega⟩
      · simp [v, h0, hζ.pow_eq_one]
      · by_cases h1 : i = ⟨1, by omega⟩
        · simp [v, h1, hne.symm, inv_pow, hζ.pow_eq_one]
        · simp [v, h0, h1]
    · simp [hij]
  · intro h1
    have := congrArg (fun s : SpecialLinearGroup (Fin n) E =>
      (s : Matrix (Fin n) (Fin n) E) ⟨0, by omega⟩ ⟨0, by omega⟩) h1
    simp only [s, v] at this
    simp at this
    exact hζ.ne_one hp.one_lt this

end Unitary

section Special

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem dvd_card_orthSpecialBlock_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    p ∣ Nat.card ↥(specialBlock Q x h) := by
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root hp hh hne1
  have h1 : p ∣ Nat.card (AdjoinRoot h) - 1 := by
    rw [← Nat.card_units, ← hord]
    exact orderOf_dvd_natCard _
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  rw [← Nat.card_congr ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm).toEquiv]
  exact dvd_card_SL_of_dvd_card_sub_one hp hm h1

theorem dvd_card_orthSpecialBlock_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp3 : 3 < p) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    p ∣ Nat.card ↥(specialBlock Q x h) := by
  classical
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range =
      CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH,
      CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
    e₀ he₀
  have hn : 2 ≤ finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := hm
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root hp hh hne1
  have hζ : IsPrimitiveRoot (AdjoinRoot.root h) p := by
    have h1 : IsPrimitiveRoot (Units.mk0 (AdjoinRoot.root h) hlam0) p :=
      hord ▸ IsPrimitiveRoot.orderOf _
    simpa using IsPrimitiveRoot.coe_units_iff.mpr h1
  have hσ : hU.barEquiv (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
    show hU.bar _ = _
    rw [hbar, hroot]
  obtain ⟨s, hs⟩ := exists_orderOf_SUid_of_conj_inv hU.barEquiv hp hn hζ hσ
  rw [Nat.card_congr (e₁.trans e₂).toEquiv, ← hs]
  exact orderOf_dvd_natCard s

end Special

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem dvd_card_orthSpecialBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    p ∣ Nat.card ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact dvd_card_orthSpecialBlock_selfDual hx hp hp3 hh hne1 hself hm
  · exact dvd_card_orthSpecialBlock_paired hx hp hh hne1 hself hm

end CFSG.HardMathSupport.Timmesfeld.CrossChar
