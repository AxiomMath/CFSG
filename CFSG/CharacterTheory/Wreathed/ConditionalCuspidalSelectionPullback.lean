module

public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionDegrees
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesRows

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

section Definition

variable {E H K : Type} [Group E] [Fintype E] [Group H]

structure CuspidalSelectionPullbackData (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (fE : E →* H) {m : ℕ} (ℓ : Fin m → H → ℂ) (Φ : H → ℂ) (PH BH TN : Set (H → ℂ))
    (Δ : Set (K → ℂ)) (res : (H → ℂ) → K → ℂ) (q κp κm : ℕ) : Prop where
  block_pullback : (fun l => (basis.representation l).character) ''
      ↑(coefficientBlock basis (localizedComplexIntegerRing ideal) principal) =
    (fun χ y => χ (fE y)) '' BH
  cuspidal_pullback : (fun l => (basis.representation l).character) ''
      ↑(cuspidalLabels basis ideal principal fE ℓ Φ PH) = (fun χ y => χ (fE y)) '' TN
  cuspidal_odd : ∀ l ∈ cuspidalLabels basis ideal principal fE ℓ Φ PH, ∀ y : E,
    Odd (orderOf y) → (basis.representation l).character y = Φ (fE y) - 1
  cuspidal_bij : ∀ θ ∈ Δ, ∃! l, l ∈ cuspidalLabels basis ideal principal fE ℓ Φ PH ∧
    ∃ χ ∈ TN, (basis.representation l).character = (fun y => χ (fE y)) ∧ res χ = θ
  degrees : (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).val.map
      (fun l => (basis.representation l).character 1) =
    Multiset.replicate m 1 + Multiset.replicate m (q : ℂ) +
      Multiset.replicate (m * (κp - 1) / 2) ((q : ℂ) + 1) +
        Multiset.replicate (m * (κm - 1) / 2) ((q : ℂ) - 1)
  cuspidal_card : (cuspidalLabels basis ideal principal fE ℓ Φ PH).card = m * (κm - 1) / 2
  block_card : (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).card =
    m * (m + 4) / 2

end Definition

section Transfer

variable {E H K : Type} [Group E] [Fintype E] [Group H] [Fintype H]

theorem cuspidalSelectionPullbackData_of_correspondence
    (basisH : FiniteIrreducibleCharacterBasis H) (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principalH : basisH.index)
    (principal : basis.index) (fE : E →* H) (hfE : Function.Surjective fE) {m : ℕ}
    {ℓ : Fin m → H → ℂ} {Φ : H → ℂ} {PH BH TN : Set (H → ℂ)} {Δ : Set (K → ℂ)}
    {res : (H → ℂ) → K → ℂ} {q κp κm : ℕ} {ε : ℤ}
    (hcorr : PrincipalFamilyCorrespondence fE basisH basis ideal principalH principal
      (MonoidHom.id H) fE ℓ Φ PH ε)
    (hH : CuspidalSelectionPullbackData basisH ideal principalH (MonoidHom.id H) ℓ Φ PH BH TN Δ
      res q κp κm) :
    CuspidalSelectionPullbackData basis ideal principal fE ℓ Φ PH BH TN Δ res q κp κm := by
  obtain ⟨τ, hτchar, -, -, -, hτC⟩ := hcorr
  have hCHB : cuspidalLabels basisH ideal principalH (MonoidHom.id H) ℓ Φ PH ⊆
      coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH := Finset.sdiff_subset
  have hCEB : cuspidalLabels basis ideal principal fE ℓ Φ PH ⊆
      coefficientBlock basis (localizedComplexIntegerRing ideal) principal := Finset.sdiff_subset
  have hid : ∀ X : Set (H → ℂ), (fun (χ : H → ℂ) (y : H) => χ (MonoidHom.id H y)) '' X = X := by
    intro X
    ext χ
    simp
  have hτc : ∀ x, (basis.representation (τ x).1).character =
      fun y => (basisH.representation x.1).character (fE y) := hτchar
  have hBimg : (fun l => (basis.representation l).character) ''
      ↑(coefficientBlock basis (localizedComplexIntegerRing ideal) principal) =
      (fun χ y => χ (fE y)) '' ((fun l => (basisH.representation l).character) ''
        ↑(coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)) := by
    ext χ'
    constructor
    · rintro ⟨l', hl', rfl⟩
      obtain ⟨x, hx⟩ := τ.surjective ⟨l', hl'⟩
      refine ⟨(basisH.representation x.1).character, ⟨x.1, x.2, rfl⟩, ?_⟩
      have h := hτc x
      rw [hx] at h
      exact h.symm
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨(τ ⟨l, hl⟩).1, (τ ⟨l, hl⟩).2, hτc ⟨l, hl⟩⟩
  have hCimg : (fun l => (basis.representation l).character) ''
      ↑(cuspidalLabels basis ideal principal fE ℓ Φ PH) =
      (fun χ y => χ (fE y)) '' ((fun l => (basisH.representation l).character) ''
        ↑(cuspidalLabels basisH ideal principalH (MonoidHom.id H) ℓ Φ PH)) := by
    ext χ'
    constructor
    · rintro ⟨l', hl', rfl⟩
      obtain ⟨x, hx⟩ := τ.surjective ⟨l', hCEB hl'⟩
      have hxC := (hτC x).mpr (by rw [hx]; exact hl')
      refine ⟨(basisH.representation x.1).character, ⟨x.1, hxC, rfl⟩, ?_⟩
      have h := hτc x
      rw [hx] at h
      exact h.symm
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨(τ ⟨l, hCHB hl⟩).1, (hτC ⟨l, hCHB hl⟩).mp hl, hτc ⟨l, hCHB hl⟩⟩
  have hBH := hH.block_pullback
  have hTN := hH.cuspidal_pullback
  rw [hid] at hBH hTN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBimg, hBH]
  · rw [hCimg, hTN]
  ·
    intro l' hl' y hy
    obtain ⟨x, hx⟩ := τ.surjective ⟨l', hCEB hl'⟩
    have hxC := (hτC x).mpr (by rw [hx]; exact hl')
    have h := congrFun (hτc x) y
    rw [hx] at h
    rw [h]
    exact hH.cuspidal_odd x.1 hxC (fE y) (hy.of_dvd_nat (orderOf_map_dvd fE y))
  ·
    intro θ hθ
    obtain ⟨l, ⟨hlC, χ, hχ, hlχ, hres⟩, huniq⟩ := hH.cuspidal_bij θ hθ
    refine ⟨(τ ⟨l, hCHB hlC⟩).1, ⟨(hτC _).mp hlC, χ, hχ, ?_, hres⟩, ?_⟩
    · rw [hτc, hlχ]
      rfl
    · rintro l'' ⟨hl''C, χ'', hχ'', hl''χ, hres''⟩
      obtain ⟨x, hx⟩ := τ.surjective ⟨l'', hCEB hl''C⟩
      have hxC := (hτC x).mpr (by rw [hx]; exact hl''C)
      have hchar : (basisH.representation x.1).character = χ'' := by
        funext z
        obtain ⟨y, rfl⟩ := hfE z
        have h := congrFun (hτc x) y
        rw [hx] at h
        rw [← h, hl''χ]
      have hxl : x.1 = l := huniq x.1 ⟨hxC, χ'', hχ'', by rw [hchar]; rfl, hres''⟩
      have hxl' : x = ⟨l, hCHB hlC⟩ := Subtype.ext hxl
      rw [← hxl', hx]
  ·
    rw [← hH.degrees]
    apply map_val_eq_of_equiv τ
    intro x
    rw [hτc]
    exact congrArg _ (map_one fE)
  · rw [← hH.cuspidal_card]
    exact (card_eq_of_equiv_mem τ hCHB hCEB hτC).symm
  · rw [← hH.block_card]
    exact (Finset.card_eq_of_equiv τ).symm

end Transfer

end CFSG.Wreathed
