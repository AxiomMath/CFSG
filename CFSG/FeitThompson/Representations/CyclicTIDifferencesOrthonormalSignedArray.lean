module

public import CFSG.FeitThompson.Representations.SubtractPivotsOrthonormalSignedBasis
public import CFSG.FeitThompson.Representations.InducedRectangleDifferencesNormThree
public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.GramArrayDistinctRowColumnPivots

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix

noncomputable section Coords

variable {X : Type*} [Group X]

def charOfIntCoords [Fintype (Irr X)] (n : Irr X → ℤ) : X → ℂ :=
  ∑ χ : Irr X, (n χ : ℂ) • ((χ : Irr X) : X → ℂ)

theorem charOfIntCoords_eq [Fintype (Irr X)] (n : Irr X → ℤ) :
    charOfIntCoords n = ∑ χ : Irr X, (n χ : ℂ) • ((χ : Irr X) : X → ℂ) := (rfl)

theorem charOfIntCoords_mem_span_Irr [Fintype (Irr X)] (n : Irr X → ℤ) :
    charOfIntCoords n ∈ Submodule.span ℤ (Irr X) :=
  mem_span_Irr_iff_exists_intCast_sum.2 ⟨n, charOfIntCoords_eq n⟩

theorem charOfIntCoords_mem_virtualChars [Fintype (Irr X)] (n : Irr X → ℤ) :
    charOfIntCoords n ∈ virtualChars X :=
  mem_virtualChars_of_mem_span_Irr (charOfIntCoords_mem_span_Irr n)

theorem exists_charOfIntCoords_of_mem_span_Irr [Fintype (Irr X)] {f : X → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr X)) : ∃ n : Irr X → ℤ, f = charOfIntCoords n :=
  mem_span_Irr_iff_exists_intCast_sum.1 hf

theorem charOfIntCoords_add [Fintype (Irr X)] (a b : Irr X → ℤ) :
    charOfIntCoords (a + b) = charOfIntCoords a + charOfIntCoords b := by
  simp only [charOfIntCoords_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun χ _ => by simp [add_smul]

theorem charOfIntCoords_neg [Fintype (Irr X)] (a : Irr X → ℤ) :
    charOfIntCoords (-a) = -charOfIntCoords a := by
  simp only [charOfIntCoords_eq, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun χ _ => by simp

theorem charOfIntCoords_single_principalIrr [Fintype (Irr X)] [DecidableEq (Irr X)] :
    charOfIntCoords (Pi.single (principalIrr X) (1 : ℤ)) = (1 : X → ℂ) := by
  rw [charOfIntCoords_eq, Finset.sum_eq_single_of_mem (principalIrr X) (Finset.mem_univ _)
    (fun χ _ hχ => by rw [Pi.single_eq_of_ne hχ]; simp), Pi.single_eq_same, coe_principalIrr]
  simp

variable [Fintype X]

theorem cfInner_charOfIntCoords_coe [Fintype (Irr X)] (n : Irr X → ℤ) (χ : Irr X) :
    cfInner (charOfIntCoords n) ((χ : Irr X) : X → ℂ) = (n χ : ℂ) :=
  cfInner_intCast_sum_Irr_coe n χ

theorem cfInner_charOfIntCoords [Fintype (Irr X)] (a b : Irr X → ℤ) :
    cfInner (charOfIntCoords a) (charOfIntCoords b) = ((a ⬝ᵥ b : ℤ) : ℂ) := by
  rw [charOfIntCoords_eq, charOfIntCoords_eq, cfInner_intCast_sum_Irr_intCast_sum_Irr]
  rfl

end Coords

theorem charOfIntCoords_mem_signedIrr {X : Type*} [Group X] [Finite X] [Fintype (Irr X)]
    {a : Irr X → ℤ} (ha : a ⬝ᵥ a = 1) : charOfIntCoords a ∈ signedIrr X :=
  have : Fintype X := Fintype.ofFinite X
  mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one (charOfIntCoords_mem_span_Irr a)
    (by rw [cfInner_charOfIntCoords, ha]; norm_num)

section Vectors

variable {ι μ ν : Type*} [DecidableEq ι]

theorem IsSignedCoordVec.neg {v : ι → ℤ} (hv : IsSignedCoordVec v) :
    IsSignedCoordVec (-v) := by
  obtain ⟨q, hsupp, hval⟩ := hv.exists_support_eq
  refine isSignedCoordVec_of_support_eq (i := q) (by simpa using hsupp) ?_
  rcases hval with h | h <;> simp [h]

theorem IsSignedCoordVec.apply_eq_zero_or_of_dotProduct_eq_zero [Fintype ι] {v w : ι → ℤ}
    (hv : IsSignedCoordVec v) (hvw : v ⬝ᵥ w = 0) (p : ι) : v p = 0 ∨ w p = 0 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨q, hq, -⟩ := hv.exists_support_eq
  have hpq : p = q := by simpa [hq] using Function.mem_support.2 hcon.1
  subst hpq
  rw [eq_single_of_support_eq hq, single_dotProduct] at hvw
  rcases mul_eq_zero.1 hvw with h | h
  · exact hcon.1 h
  · exact hcon.2 h

theorem eq_zero_of_isSignedCoordVec_add_add [Fintype ι] {u v w : ι → ℤ} {p : ι}
    (hu : IsSignedCoordVec u) (hv : IsSignedCoordVec v)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0)
    (hsum : (u + v + w) p = 0) : u p = 0 ∧ v p = 0 ∧ w p = 0 := by
  simp only [Pi.add_apply] at hsum
  have hup : u p ≠ 0 → v p = 0 ∧ w p = 0 := fun h =>
    ⟨(hu.apply_eq_zero_or_of_dotProduct_eq_zero huv p).resolve_left h,
      (hu.apply_eq_zero_or_of_dotProduct_eq_zero huw p).resolve_left h⟩
  have hvp : v p ≠ 0 → w p = 0 := fun h =>
    (hv.apply_eq_zero_or_of_dotProduct_eq_zero hvw p).resolve_left h
  rcases eq_or_ne (u p) 0 with hu0 | hu0
  · rcases eq_or_ne (v p) 0 with hv0 | hv0
    · exact ⟨hu0, hv0, by omega⟩
    · exact absurd (hvp hv0) (by omega)
  · exact absurd (hup hu0).1 (by have := (hup hu0).2; omega)

def optionPivotVec (p : ι) (r : μ → ι → ℤ) (c : ν → ι → ℤ)
    (t : μ → ν → ι → ℤ) : Option μ → Option ν → ι → ℤ
  | none, none => Pi.single p 1
  | some i, none => -r i
  | none, some j => -c j
  | some i, some j => t i j

variable {p : ι} {r : μ → ι → ℤ} {c : ν → ι → ℤ} {t : μ → ν → ι → ℤ}

@[simp] theorem optionPivotVec_none_none :
    optionPivotVec p r c t none none = Pi.single p 1 := (rfl)

@[simp] theorem optionPivotVec_some_none (i : μ) :
    optionPivotVec p r c t (some i) none = -r i := (rfl)

@[simp] theorem optionPivotVec_none_some (j : ν) :
    optionPivotVec p r c t none (some j) = -c j := (rfl)

@[simp] theorem optionPivotVec_some_some (i : μ) (j : ν) :
    optionPivotVec p r c t (some i) (some j) = t i j := (rfl)

theorem isSignedCoordVec_optionPivotVec
    (hrs : ∀ i, IsSignedCoordVec (r i)) (hcs : ∀ j, IsSignedCoordVec (c j))
    (hts : ∀ i j, IsSignedCoordVec (t i j)) (o₁ : Option μ) (o₂ : Option ν) :
    IsSignedCoordVec (optionPivotVec p r c t o₁ o₂) := by
  cases o₁ <;> cases o₂ <;> simp only [optionPivotVec_none_none, optionPivotVec_some_none,
    optionPivotVec_none_some, optionPivotVec_some_some]
  · exact isSignedCoordVec_single_one p
  · exact (hcs _).neg
  · exact (hrs _).neg
  · exact hts _ _

theorem dotProduct_optionPivotVec [Fintype ι] [DecidableEq μ] [DecidableEq ν]
    (hrr : ∀ i k, r i ⬝ᵥ r k = if i = k then 1 else 0)
    (hcc : ∀ j l, c j ⬝ᵥ c l = if j = l then 1 else 0)
    (htt : ∀ i j k l, t i j ⬝ᵥ t k l = if i = k ∧ j = l then 1 else 0)
    (hrc : ∀ i j, r i ⬝ᵥ c j = 0) (hrt : ∀ i k l, r i ⬝ᵥ t k l = 0)
    (hct : ∀ j k l, c j ⬝ᵥ t k l = 0)
    (hrp : ∀ i, r i p = 0) (hcp : ∀ j, c j p = 0) (htp : ∀ i j, t i j p = 0)
    (o₁ o₁' : Option μ) (o₂ o₂' : Option ν) :
    optionPivotVec p r c t o₁ o₂ ⬝ᵥ optionPivotVec p r c t o₁' o₂' =
      if o₁ = o₁' ∧ o₂ = o₂' then 1 else 0 := by
  cases o₁ <;> cases o₂ <;> cases o₁' <;> cases o₂' <;>
    simp only [optionPivotVec_none_none, optionPivotVec_some_none, optionPivotVec_none_some,
      optionPivotVec_some_some, dotProduct_neg, neg_dotProduct, neg_neg, single_dotProduct,
      dotProduct_single] <;>
    simp_all [dotProduct_comm (r _) (c _), dotProduct_comm (t _ _) (r _),
      dotProduct_comm (t _ _) (c _)]

end Vectors

section Transport

variable {ι κ μ ν : Type*}

theorem dotProduct_comp_equiv [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v w : κ → ℤ) :
    (v ∘ e) ⬝ᵥ (w ∘ e) = v ⬝ᵥ w := by
  simp only [dotProduct, Function.comp_apply]
  exact Equiv.sum_comp e fun k => v k * w k

theorem IsSignedCoordVec.comp_equiv [DecidableEq ι] [DecidableEq κ] {v : κ → ℤ}
    (hv : IsSignedCoordVec v) (e : ι ≃ κ) : IsSignedCoordVec (v ∘ e) := by
  obtain ⟨a, hsupp, hval⟩ := hv.exists_support_eq
  refine isSignedCoordVec_of_support_eq (i := e.symm a) ?_ (by simpa using hval)
  ext x
  simp only [Function.mem_support, Function.comp_apply, Set.mem_singleton_iff]
  rw [← Function.mem_support, hsupp]
  simp [Equiv.eq_symm_apply]

theorem IsGramArray.comp_equiv {μ' ν' : Type*} [DecidableEq μ] [DecidableEq ν] [DecidableEq μ']
    [DecidableEq ν'] [Fintype ι] [Fintype κ] {b : μ → ν → κ → ℤ} (hb : IsGramArray b)
    (eμ : μ' ≃ μ) (eν : ν' ≃ ν) (eι : ι ≃ κ) :
    IsGramArray fun i j => b (eμ i) (eν j) ∘ eι := by
  refine isGramArray_of_dotProduct (fun i j => ?_) (fun i {j l} hjl => ?_)
    (fun {i k} hik j => ?_) (fun {i k j l} hik hjl => ?_)
  · exact (dotProduct_comp_equiv eι _ _).trans (hb.dotProduct_self _ _)
  · exact (dotProduct_comp_equiv eι _ _).trans (hb.dotProduct_row _ (by simpa using hjl))
  · exact (dotProduct_comp_equiv eι _ _).trans (hb.dotProduct_col (by simpa using hik) _)
  · exact (dotProduct_comp_equiv eι _ _).trans
      (hb.dotProduct_eq_zero (by simpa using hik) (by simpa using hjl))

theorem exists_orthonormal_signed_decomposition_of_isGramArray'
    [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] [Fintype ι] [DecidableEq ι]
    (hm : 2 ≤ Fintype.card μ) (hn : 2 ≤ Fintype.card ν)
    (hme : Even (Fintype.card μ)) (hne : Even (Fintype.card ν))
    (hmn : Fintype.card μ ≠ Fintype.card ν)
    {b : μ → ν → ι → ℤ} (hb : IsGramArray b) :
    ∃ (r : μ → ι → ℤ) (c : ν → ι → ℤ) (t : μ → ν → ι → ℤ),
      (∀ i, IsSignedCoordVec (r i)) ∧ (∀ j, IsSignedCoordVec (c j)) ∧
      (∀ i j, IsSignedCoordVec (t i j)) ∧
      (∀ i k, r i ⬝ᵥ r k = if i = k then 1 else 0) ∧
      (∀ j l, c j ⬝ᵥ c l = if j = l then 1 else 0) ∧
      (∀ i j k l, t i j ⬝ᵥ t k l = if i = k ∧ j = l then 1 else 0) ∧
      (∀ i j, r i ⬝ᵥ c j = 0) ∧
      (∀ i k l, r i ⬝ᵥ t k l = 0) ∧
      (∀ j k l, c j ⬝ᵥ t k l = 0) ∧
      (∀ i j, b i j = r i + c j + t i j) := by
  set eμ := Fintype.equivFin μ
  set eν := Fintype.equivFin ν
  set eι := Fintype.equivFin ι
  obtain ⟨r', c', t', hrs, hcs, hts, hrr, hcc, htt, hrc, hrt, hct, hsum⟩ :=
    exists_orthonormal_signed_decomposition_of_isGramArray hm hn hme hne hmn
      (hb.comp_equiv eμ.symm eν.symm eι.symm)
  refine ⟨fun i => r' (eμ i) ∘ eι, fun j => c' (eν j) ∘ eι, fun i j => t' (eμ i) (eν j) ∘ eι,
    fun i => (hrs _).comp_equiv eι, fun j => (hcs _).comp_equiv eι,
    fun i j => (hts _ _).comp_equiv eι, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k; rw [dotProduct_comp_equiv, hrr]; simp
  · intro j l; rw [dotProduct_comp_equiv, hcc]; simp
  · intro i j k l; rw [dotProduct_comp_equiv, htt]; simp
  · intro i j; rw [dotProduct_comp_equiv, hrc]
  · intro i k l; rw [dotProduct_comp_equiv, hrt]
  · intro j k l; rw [dotProduct_comp_equiv, hct]
  · intro i j
    funext x
    simpa using congrFun (hsum (eμ i) (eν j)) (eι x)

end Transport

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

open scoped Classical in
theorem IsCyclicTIPair.exists_prodCharEta [Fintype G] (h : IsCyclicTIPair W W1 W2) :
    ∃ η : Irr ↥W1 → Irr ↥W2 → G → ℂ,
      η (principalIrr ↥W1) (principalIrr ↥W2) = 1 ∧
      (∀ i j, η i j ∈ virtualChars G) ∧
      (∀ i j k l, cfInner (η i j) (η k l) = if i = k ∧ j = l then 1 else 0) ∧
      (∀ i j, η i j ∈ signedIrr G) ∧
      (∀ i ≠ principalIrr ↥W1, ∀ j ≠ principalIrr ↥W2,
        indClassFun W (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) =
          1 - η i (principalIrr ↥W2) - η (principalIrr ↥W1) j + η i j) := by
  classical
  have : Fintype (Irr G) := Fintype.ofFinite _
  have := h.finite_left
  have := h.finite_right
  have hf1 : Finite (Irr ↥W1) := finite_coe_Irr
  have hf2 : Finite (Irr ↥W2) := finite_coe_Irr
  have inst1 : Fintype {i : Irr ↥W1 // i ≠ principalIrr ↥W1} := Fintype.ofFinite _
  have inst2 : Fintype {j : Irr ↥W2 // j ≠ principalIrr ↥W2} := Fintype.ofFinite _
  have hcμ : Fintype.card {i : Irr ↥W1 // i ≠ principalIrr ↥W1} = Nat.card ↥W1 - 1 := by
    rw [← Nat.card_eq_fintype_card, natCard_ne_eq, h.card_Irr_left]
  have hcν : Fintype.card {j : Irr ↥W2 // j ≠ principalIrr ↥W2} = Nat.card ↥W2 - 1 := by
    rw [← Nat.card_eq_fintype_card, natCard_ne_eq, h.card_Irr_right]
  have hβex : ∀ (i : {i : Irr ↥W1 // i ≠ principalIrr ↥W1})
      (j : {j : Irr ↥W2 // j ≠ principalIrr ↥W2}), ∃ n : Irr G → ℤ,
      h.prodCharBeta ((i.1 : Irr ↥W1) : ↥W1 → ℂ) ((j.1 : Irr ↥W2) : ↥W2 → ℂ) =
        charOfIntCoords n := fun i j =>
    exists_charOfIntCoords_of_mem_span_Irr
      (mem_span_Irr_of_mem_virtualChars (h.prodCharBeta_mem_virtualChars i.1.2 j.1.2))
  choose b hb using hβex
  have hdot : ∀ i k j l, b i j ⬝ᵥ b k l =
      (if i = k then 1 else 0) + (if j = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
    intro i k j l
    have h1 : cfInner (charOfIntCoords (b i j)) (charOfIntCoords (b k l))
        = ((b i j ⬝ᵥ b k l : ℤ) : ℂ) := cfInner_charOfIntCoords _ _
    rw [← hb, ← hb, h.cfInner_prodCharBeta i.2 k.2 j.2 l.2] at h1
    simp only [Subtype.val_inj] at h1
    exact_mod_cast h1.symm
  have hbG : IsGramArray b :=
    isGramArray_of_dotProduct (fun i j => by simpa using hdot i i j j)
      (fun i {j l} hjl => by simpa [hjl] using hdot i i j l)
      (fun {i k} hik j => by simpa [hik] using hdot i k j j)
      (fun {i k j l} hik hjl => by simpa [hik, hjl] using hdot i k j l)
  have hbp : ∀ i j, b i j (principalIrr G) = 0 := by
    intro i j
    have h1 := h.cfInner_prodCharBeta_one i.2 j.2
    rw [hb i j] at h1
    rw [show cfInner (charOfIntCoords (b i j)) (1 : G → ℂ) = (b i j (principalIrr G) : ℂ) by
      rw [← coe_principalIrr G]; exact cfInner_charOfIntCoords_coe _ _] at h1
    exact_mod_cast h1
  obtain ⟨r, c, t, hrs, hcs, hts, hrr, hcc, htt, hrc, hrt, hct, hsum⟩ :=
    exists_orthonormal_signed_decomposition_of_isGramArray'
      (by rw [hcμ]; exact h.two_le_natCard_sub_one_left)
      (by rw [hcν]; exact h.two_le_natCard_sub_one_right)
      (by rw [hcμ]; exact h.even_natCard_sub_one_left)
      (by rw [hcν]; exact h.even_natCard_sub_one_right)
      (by rw [hcμ, hcν]; exact h.natCard_sub_one_ne) hbG
  have hzero : ∀ i j, r i (principalIrr G) = 0 ∧ c j (principalIrr G) = 0 ∧
      t i j (principalIrr G) = 0 := fun i j =>
    eq_zero_of_isSignedCoordVec_add_add (hrs i) (hcs j) (hrc i j) (hrt i i j) (hct j i j)
      (by rw [← hsum i j]; exact hbp i j)
  have hne1 : Nonempty {i : Irr ↥W1 // i ≠ principalIrr ↥W1} := by
    have := h.nontrivial_Irr_left
    obtain ⟨i, hi⟩ := exists_ne (principalIrr ↥W1); exact ⟨i, hi⟩
  have hne2 : Nonempty {j : Irr ↥W2 // j ≠ principalIrr ↥W2} := by
    have := h.nontrivial_Irr_right
    obtain ⟨j, hj⟩ := exists_ne (principalIrr ↥W2); exact ⟨j, hj⟩
  have hrp : ∀ i, r i (principalIrr G) = 0 := fun i => (hzero i hne2.some).1
  have hcp : ∀ j, c j (principalIrr G) = 0 := fun j => (hzero hne1.some j).2.1
  have htp : ∀ i j, t i j (principalIrr G) = 0 := fun i j => (hzero i j).2.2
  obtain ⟨v, hvdef⟩ : ∃ v : Irr ↥W1 → Irr ↥W2 → Irr G → ℤ, ∀ i j,
      v i j = optionPivotVec (principalIrr G) r c t
        ((Equiv.optionSubtypeNe (principalIrr ↥W1)).symm i)
        ((Equiv.optionSubtypeNe (principalIrr ↥W2)).symm j) := ⟨_, fun i j => rfl⟩
  have hv00 : v (principalIrr ↥W1) (principalIrr ↥W2) = Pi.single (principalIrr G) 1 := by
    rw [hvdef, show (Equiv.optionSubtypeNe (principalIrr ↥W1)).symm (principalIrr ↥W1) = none by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_none],
      show (Equiv.optionSubtypeNe (principalIrr ↥W2)).symm (principalIrr ↥W2) = none by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_none]]
    exact optionPivotVec_none_none
  have hvij : ∀ (i : Irr ↥W1) (hi : i ≠ principalIrr ↥W1) (j : Irr ↥W2)
      (hj : j ≠ principalIrr ↥W2), v i j = t ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i hi j hj
    rw [hvdef, show (Equiv.optionSubtypeNe (principalIrr ↥W1)).symm i = some ⟨i, hi⟩ by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_some],
      show (Equiv.optionSubtypeNe (principalIrr ↥W2)).symm j = some ⟨j, hj⟩ by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_some]]
    exact optionPivotVec_some_some _ _
  have hvi0 : ∀ (i : Irr ↥W1) (hi : i ≠ principalIrr ↥W1),
      v i (principalIrr ↥W2) = -r ⟨i, hi⟩ := by
    intro i hi
    rw [hvdef, show (Equiv.optionSubtypeNe (principalIrr ↥W1)).symm i = some ⟨i, hi⟩ by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_some],
      show (Equiv.optionSubtypeNe (principalIrr ↥W2)).symm (principalIrr ↥W2) = none by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_none]]
    exact optionPivotVec_some_none _
  have hv0j : ∀ (j : Irr ↥W2) (hj : j ≠ principalIrr ↥W2),
      v (principalIrr ↥W1) j = -c ⟨j, hj⟩ := by
    intro j hj
    rw [hvdef, show (Equiv.optionSubtypeNe (principalIrr ↥W1)).symm (principalIrr ↥W1) = none by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_none],
      show (Equiv.optionSubtypeNe (principalIrr ↥W2)).symm j = some ⟨j, hj⟩ by
      rw [Equiv.symm_apply_eq, Equiv.optionSubtypeNe_some]]
    exact optionPivotVec_none_some _
  have hdotv : ∀ i j k l, v i j ⬝ᵥ v k l = if i = k ∧ j = l then 1 else 0 := by
    intro i j k l
    rw [hvdef, hvdef, dotProduct_optionPivotVec hrr hcc htt hrc hrt hct hrp hcp htp]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨η, hη⟩ : ∃ η : Irr ↥W1 → Irr ↥W2 → G → ℂ, ∀ i j, η i j = charOfIntCoords (v i j) :=
    ⟨_, fun i j => rfl⟩
  refine ⟨η, ?_, fun i j => by rw [hη]; exact charOfIntCoords_mem_virtualChars _, ?_, ?_, ?_⟩
  · rw [hη, hv00, charOfIntCoords_single_principalIrr]
  · intro i j k l
    rw [hη, hη, cfInner_charOfIntCoords, hdotv]
    split_ifs <;> norm_num
  · intro i j
    rw [hη]
    exact charOfIntCoords_mem_signedIrr (by rw [hdotv]; simp)
  · intro i hi j hj
    have hbeta : h.prodCharBeta (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) =
        charOfIntCoords (b ⟨i, hi⟩ ⟨j, hj⟩) := hb ⟨i, hi⟩ ⟨j, hj⟩
    have hsplit : charOfIntCoords (b ⟨i, hi⟩ ⟨j, hj⟩) =
        -η i (principalIrr ↥W2) - η (principalIrr ↥W1) j + η i j := by
      rw [hsum ⟨i, hi⟩ ⟨j, hj⟩, charOfIntCoords_add, charOfIntCoords_add, hη, hη, hη,
        hvij i hi j hj, hvi0 i hi, hv0j j hj, charOfIntCoords_neg, charOfIntCoords_neg]
      ring
    have hkey := h.prodCharBeta_eq (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)
    rw [hbeta, hsplit] at hkey
    rw [eq_comm, ← sub_eq_iff_eq_add'] at hkey
    linear_combination hkey

open scoped Classical in
theorem IsCyclicTIPair.exists_prodCharEta' [Fintype G] (h : IsCyclicTIPair W W1 W2) :
    ∃ η : Irr ↥W1 → Irr ↥W2 → G → ℂ,
      η (principalIrr ↥W1) (principalIrr ↥W2) = 1 ∧
      (∀ i j, η i j ∈ virtualChars G) ∧
      (∀ i j k l, cfInner (η i j) (η k l) = if i = k ∧ j = l then 1 else 0) ∧
      (∀ i j, η i j ∈ Irr G ∨ -η i j ∈ Irr G) ∧
      (∀ i ≠ principalIrr ↥W1, ∀ j ≠ principalIrr ↥W2,
        indClassFun W (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) =
          1 - η i (principalIrr ↥W2) - η (principalIrr ↥W1) j + η i j) := by
  classical
  obtain ⟨η, h00, hZ, horth, hsigned, hind⟩ := h.exists_prodCharEta
  exact ⟨η, h00, hZ, horth, fun i j => mem_signedIrr.1 (hsigned i j), hind⟩

end CFSG.FeitThompson
