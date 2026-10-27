module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Descent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem

@[expose] def thetaF4' : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

theorem thetaF4_eq : thetaF4 = thetaF4' := by
  set X : Fin (Tag.rank .F4) → ℤ := thetaF4 - thetaF4' with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    rw [hX, iform_sub_left, iform_thetaF4_single]
    revert j
    unfold thetaF4'
    decide +kernel
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [iform_eq_sum_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.1 hX0

@[expose] def IsPartnerF4 (δ : Fin (Tag.rank .F4) → ℤ) : Prop :=
  IsRoot .F4 δ ∧ iform δ δ = 4 ∧ iform thetaF4 δ = -2

@[expose] def partnersF4 : Finset (Fin (Tag.rank .F4) → ℤ) :=
  {![-1, -2, -4, -2], ![-1, 0, 0, 0], ![-1, -1, -2, -2], ![-1, -2, -2, -2], ![-1, -1, 0, 0],
    ![-1, -1, -2, 0], ![-1, -2, -2, 0], ![-1, -3, -4, -2]}

theorem partnersF4_char : ∀ δ ∈ rootFinset .F4, iform δ δ = 4 → iform thetaF4' δ = -2 →
    δ ∈ partnersF4 := by
  unfold thetaF4'
  decide +kernel

theorem partnersF4_isPartner : ∀ δ ∈ partnersF4, δ ∈ rootFinset .F4 ∧ iform δ δ = 4 ∧
    iform thetaF4' δ = -2 := by
  unfold thetaF4'
  decide +kernel

theorem isPartnerF4_iff {δ : Fin (Tag.rank .F4) → ℤ} : IsPartnerF4 δ ↔ δ ∈ partnersF4 := by
  rw [IsPartnerF4, thetaF4_eq]
  exact ⟨fun h => partnersF4_char δ (mem_rootFinset.2 h.1) h.2.1 h.2.2, fun h =>
    let h' := partnersF4_isPartner δ h
    ⟨mem_rootFinset.1 h'.1, h'.2.1, h'.2.2⟩⟩

@[expose] def deltaF4 : Fin (Tag.rank .F4) → ℤ := ![-1, 0, 0, 0]

theorem isPartnerF4_deltaF4 : IsPartnerF4 deltaF4 := isPartnerF4_iff.2 (by decide +kernel)

@[expose] def idxF4 (n : ℕ) (h : n < 4 := by decide) : Fin (Tag.rank .F4) := ⟨n, h⟩

@[expose] def wordActF4 (l : List (Fin (Tag.rank .F4))) (v : Fin (Tag.rank .F4) → ℤ) :
    Fin (Tag.rank .F4) → ℤ :=
  l.foldr (fun j w => reflect .F4 j w) v

@[expose] def partnerWordsF4 : List ((Fin (Tag.rank .F4) → ℤ) × List (Fin (Tag.rank .F4))) :=
  [(![-1, 0, 0, 0], []), (![-1, -1, 0, 0], [idxF4 1]),
    (![-1, -1, -2, 0], [idxF4 2, idxF4 1]),
    (![-1, -2, -2, 0], [idxF4 1, idxF4 2, idxF4 1]),
    (![-1, -1, -2, -2], [idxF4 3, idxF4 2, idxF4 1]),
    (![-1, -2, -2, -2], [idxF4 3, idxF4 1, idxF4 2, idxF4 1]),
    (![-1, -2, -4, -2], [idxF4 2, idxF4 3, idxF4 1, idxF4 2, idxF4 1]),
    (![-1, -3, -4, -2], [idxF4 1, idxF4 2, idxF4 3, idxF4 1, idxF4 2, idxF4 1])]

theorem partnerWordsF4_spec : ∀ x ∈ partnerWordsF4, wordActF4 x.2 deltaF4 = x.1 ∧
    ∀ j ∈ x.2, j ∈ JF4 := by
  unfold partnerWordsF4 wordActF4 JF4 idxF4 deltaF4
  decide +kernel

theorem partnerWordsF4_cover : ∀ δ ∈ partnersF4, ∃ x ∈ partnerWordsF4, x.1 = δ := by
  unfold partnerWordsF4 partnersF4
  decide +kernel

theorem exists_word_partnerF4 {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsPartnerF4 δ) :
    ∃ l : List (Fin (Tag.rank .F4)), (∀ j ∈ l, j ∈ JF4) ∧ wordActF4 l deltaF4 = δ := by
  obtain ⟨x, hx, rfl⟩ := partnerWordsF4_cover δ (isPartnerF4_iff.1 hδ)
  obtain ⟨h1, h2⟩ := partnerWordsF4_spec x hx
  exact ⟨x.2, h2, h1⟩

variable {F : Type} [Field F]

theorem corootDiagF4_reflect (j : Fin (Tag.rank .F4)) {δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (hl : iform δ δ = 4) (c : Fˣ) :
    corootDiagF4 (reflect .F4 j δ) c =
      fun l => corootDiagF4 δ c l * corootDiagF4 δ c j ^ (-Tag.cartan .F4 j l) := by
  funext l
  have hev := even_iform_single_of_long_F4 δ (mem_rootFinset.2 hδ) hl
  obtain ⟨a, ha⟩ := hev j
  obtain ⟨b, hb⟩ := hev l
  have h1 : iform (reflect .F4 j δ) (Pi.single l 1) = 2 * (b - a * Tag.cartan .F4 j l) := by
    rw [iform_reflect_single, ha, hb]
    ring
  have e1 : iform (reflect .F4 j δ) (Pi.single l 1) / 2 = b - a * Tag.cartan .F4 j l := by
    rw [h1]
    omega
  have e2 : iform δ (Pi.single l 1) / 2 = b := by rw [hb]; omega
  have e3 : iform δ (Pi.single j 1) / 2 = a := by rw [ha]; omega
  have h1' : iform (reflect .F4 j δ) (Pi.single l 1) / 2 =
      iform δ (Pi.single l 1) / 2 + iform δ (Pi.single j 1) / 2 * (-Tag.cartan .F4 j l) := by
    rw [e1, e2, e3]
    ring
  simp only [corootDiagF4, h1', zpow_add, ← zpow_mul]

end CFSG.ClassicalInvolution.ModelFacts.Levi
