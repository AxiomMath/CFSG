module

public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.AdditiveArraySupportBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem subsingleton_setOf_cfInner_ne_zero [Fintype G] {ι : Type*} {η : ι → G → ℂ}
    (hη : ∀ i, η i ∈ signedIrr G) (hortho : ∀ i j, i ≠ j → cfInner (η i) (η j) = 0)
    {b : G → ℂ} (hb : b ∈ signedIrr G) :
    {i : ι | cfInner b (η i) ≠ 0}.Subsingleton := by
  intro i hi j hj
  simp only [Set.mem_ofPred_eq] at hi hj
  by_contra hij
  have key : ∀ k : ι, cfInner b (η k) ≠ 0 → η k = b ∨ η k = -b := by
    intro k hk
    rcases eq_or_eq_neg_of_cfInner_ne_zero hb (hη k) hk with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  have h0 := hortho i j hij
  rcases key i hi with h1 | h1 <;> rcases key j hj with h2 | h2 <;>
    rw [h1, h2] at h0 <;>
    simp [cfInner_neg_left, cfInner_neg_right, cfInner_self_of_mem_signedIrr hb] at h0

theorem ncard_setOf_cfInner_ne_zero_le_one [Fintype G] {ι : Type*} [Finite ι] {η : ι → G → ℂ}
    (hη : ∀ i, η i ∈ signedIrr G) (hortho : ∀ i j, i ≠ j → cfInner (η i) (η j) = 0)
    {b : G → ℂ} (hb : b ∈ signedIrr G) : {i : ι | cfInner b (η i) ≠ 0}.ncard ≤ 1 :=
  (Set.ncard_le_one (Set.toFinite _)).2 fun _ ha _ hb' =>
    subsingleton_setOf_cfInner_ne_zero hη hortho hb ha hb'

variable {W W1 W2 : Subgroup G} {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIIsometry

theorem eq_apply_of_eqOn_cyclicTIDiff [Fintype G] [Fintype ↥W]
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) {ρ : G → ℂ} (hρ : ρ ∈ signedIrr G)
    (hval : ∀ v : ↥W, (v : G) ∈ cyclicTIDiff W W1 W2 → ρ (v : G) = (χ : ↥W → ℂ) v) :
    ρ = (σ χ : G → ℂ) := by
  classical
  have hfin1 : Finite ↥W1 := hW.finite_left
  have hfin2 : Finite ↥W2 := hW.finite_right
  obtain ⟨lam, hlam, mu, hmu, hχe⟩ := hW.exists_prodChar_eq_of_mem_Irr hχ
  set p₀ : Irr ↥W1 × Irr ↥W2 := (⟨lam, hlam⟩, ⟨mu, hmu⟩) with hp₀
  have hbasis : hW.basisProdIrr p₀ = χ :=
    Subtype.ext ((IsCyclicTIPair.coe_basisProdIrr_apply hW p₀).trans hχe)
  set η : Irr ↥W1 × Irr ↥W2 → G → ℂ := fun p => hW.prodCharEta σ p.1 p.2 with hη
  have hψη : (σ χ : G → ℂ) = η p₀ := by
    have hp : η p₀ = (σ (hW.basisProdIrr p₀) : G → ℂ) :=
      IsCyclicTIPair.prodCharEta_eq_coe_apply hW p₀.1 p₀.2
    rw [hp, hbasis]
  rw [hψη]
  have hηsigned : ∀ p, η p ∈ signedIrr G := fun p =>
    mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
      (mem_virtualChars_iff.1 (hW.prodCharEta_mem_virtualChars hσ p.1 p.2))
      (by rw [hη, hW.cfInner_prodCharEta hσ, if_pos ⟨rfl, rfl⟩])
  have hηinner : ∀ p q, cfInner (η p) (η q) = if p = q then 1 else 0 := by
    intro p q
    rw [hη, hW.cfInner_prodCharEta hσ]
    exact if_congr (by rw [Prod.ext_iff]) rfl rfl
  have hηortho : ∀ p q, p ≠ q → cfInner (η p) (η q) = 0 := fun p q h => by
    rw [hηinner, if_neg h]
  have hψsigned := hηsigned p₀
  set f : G → ℂ := ρ - η p₀ with hf
  have hfcf : f ∈ classFun G :=
    (classFun G).sub_mem (signedIrr_subset_classFun hρ)
      (by rw [hη]; exact hW.prodCharEta_mem_classFun p₀.1 p₀.2)
  have hf0 : ∀ x ∈ cyclicTIDiff W W1 W2, f x = 0 := by
    intro x hx
    have hxW : x ∈ W := cyclicTIDiff_subset hx
    have h1 : ρ x = (χ : ↥W → ℂ) ⟨x, hxW⟩ := hval ⟨x, hxW⟩ hx
    have h2 : η p₀ x = (χ : ↥W → ℂ) ⟨x, hxW⟩ := by
      rw [← hψη, hσ.apply_eq_of_mem_cyclicTIDiff' hW χ hx]
    simp only [hf, Pi.sub_apply, h1, h2, sub_self]
  set a : Irr ↥W1 → Irr ↥W2 → ℂ := fun i j => cfInner f (η (i, j)) with ha
  have hexch : ∀ i j, a i j + a (principalIrr ↥W1) (principalIrr ↥W2)
      = a i (principalIrr ↥W2) + a (principalIrr ↥W1) j := fun i j =>
    hW.cfInner_prodCharEta_exchange hσ hfcf hf0 i j
  have hrect : ∀ i k : Irr ↥W1, ∀ j l : Irr ↥W2, a i j + a k l = a i l + a k j := by
    intro i k j l
    linear_combination hexch i j + hexch k l - hexch i l - hexch k j
  have hsupp : {p : Irr ↥W1 × Irr ↥W2 | a p.1 p.2 ≠ 0}
      ⊆ {p | cfInner ρ (η p) ≠ 0} ∪ {p | cfInner (η p₀) (η p) ≠ 0} := by
    intro p hp
    simp only [Set.mem_ofPred_eq, ha, hf, cfInner_sub_left] at hp
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hnot
    exact hp (by rw [hnot.1, hnot.2, sub_zero])
  have hle1 : {p : Irr ↥W1 × Irr ↥W2 | cfInner ρ (η p) ≠ 0}.ncard ≤ 1 :=
    ncard_setOf_cfInner_ne_zero_le_one hηsigned hηortho hρ
  have hle2 : {p : Irr ↥W1 × Irr ↥W2 | cfInner (η p₀) (η p) ≠ 0}.ncard ≤ 1 :=
    ncard_setOf_cfInner_ne_zero_le_one hηsigned hηortho hψsigned
  have hle : {p : Irr ↥W1 × Irr ↥W2 | a p.1 p.2 ≠ 0}.ncard ≤ 2 :=
    le_trans (Set.ncard_le_ncard hsupp (Set.toFinite _))
      (le_trans (Set.ncard_union_le _ _) (by omega))
  have hmin : 3 ≤ min (Nat.card (Irr ↥W1)) (Nat.card (Irr ↥W2)) := by
    rw [hW.card_Irr_left, hW.card_Irr_right]
    exact le_min hW.three_le_natCard_left hW.three_le_natCard_right
  have hazero : ∀ i j, a i j = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨i, j, hij⟩ := hne
    have := min_le_ncard_support_of_add_swap a hrect ⟨i, j, hij⟩
    omega
  have h1 : cfInner ρ (η p₀) = 1 := by
    have h0 := hazero p₀.1 p₀.2
    simp only [ha, hf, cfInner_sub_left] at h0
    rw [hηinner, if_pos rfl] at h0
    linear_combination h0
  exact eq_of_cfInner_eq_one hρ hψsigned h1

theorem eq_apply_of_eqOn_cyclicTIDiff' [Fintype G] [Fintype ↥W]
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (χ : Irr ↥W) {ρ : G → ℂ} (hρ : ρ ∈ signedIrr G)
    (hval : ∀ v : ↥W, (v : G) ∈ cyclicTIDiff W W1 W2 → ρ (v : G) = (χ : ↥W → ℂ) v) :
    ρ = (σ (Irr.toClassFun χ) : G → ℂ) :=
  eq_apply_of_eqOn_cyclicTIDiff hW hσ (by rw [Irr.coe_toClassFun]; exact χ.2) hρ
    (by simpa only [Irr.coe_toClassFun] using hval)

end IsCyclicTIIsometry

end CFSG.FeitThompson
