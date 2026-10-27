module

public import CFSG.Monster.B.TwoA.Sp8.Orth8Plus
public import CFSG.Monster.B.TwoA.Amalgam.Kernels
public import CFSG.Monster.B.CTIB.Rep4371SpinBasis
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFixInputs

public noncomputable section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Rep4371


theorem testBit_zero_xor_191 (d : ℕ) : (d ^^^ 191).testBit 0 = !d.testBit 0 := by
  rw [Nat.testBit_xor, show (191 : ℕ).testBit 0 = true by decide, Bool.xor_true]

theorem redW_d_xor (d : ℕ) :
    (if (d ^^^ 191).testBit 0 then d ^^^ 191 ^^^ 191 else d ^^^ 191) =
      if d.testBit 0 then d ^^^ 191 else d := by
  rw [testBit_zero_xor_191]
  cases d.testBit 0
  · simp
  · simp

theorem xor_xor_xor_cancel (a b r : ℕ) : (a ^^^ r) ^^^ (b ^^^ r) = a ^^^ b :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> cases r.testBit i <;> rfl

theorem xor_eq_zero_iff' {a b : ℕ} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    have h1 := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at h1
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro rfl
    exact Nat.xor_self a

theorem xor_redW_d (d : ℕ) :
    d ^^^ (if d.testBit 0 then d ^^^ 191 else d) = 0 ∨
      d ^^^ (if d.testBit 0 then d ^^^ 191 else d) = 191 := by
  split_ifs
  · right
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · left
    exact Nat.xor_self d

theorem redW_d_eq_iff (d d' : ℕ) :
    ((if d.testBit 0 then d ^^^ 191 else d) = if d'.testBit 0 then d' ^^^ 191 else d') ↔
      d ^^^ d' = 0 ∨ d ^^^ d' = 191 := by
  constructor
  · intro h
    have e : d ^^^ d' = (d ^^^ (if d.testBit 0 then d ^^^ 191 else d)) ^^^
        (d' ^^^ (if d'.testBit 0 then d' ^^^ 191 else d')) := by
      rw [h, xor_xor_xor_cancel]
    rcases xor_redW_d d with h1 | h1 <;> rcases xor_redW_d d' with h2 | h2 <;>
      rw [e, h1, h2] <;> simp
  · rintro (h | h)
    · rw [xor_eq_zero_iff'.1 h]
    · have e : d' = d ^^^ 191 := by rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e, redW_d_xor]

theorem boxed_iff (y : Model.Pauli) : boxed y = true ↔ y.2.1 < 2 ^ 12 ∧ y.2.2 < 2 ^ 12 := by
  simp [boxed]

theorem boxed_mul {y y' : Model.Pauli} (hy : boxed y = true) (hy' : boxed y' = true) :
    boxed (Model.Pauli.mul y y') = true := by
  rw [boxed_iff] at *
  exact ⟨Nat.xor_lt_two_pow hy.1 hy'.1, Nat.xor_lt_two_pow hy.2 hy'.2⟩

open Classical in
@[expose] def pcC (y : Model.Pauli) : Cgen :=
  if h : pauliQ y ∈ Subgroup.centralizer {rStar} then ⟨rhoEquiv (pauliQ y), rhoEquiv_mem_Cgen h⟩
  else 1

@[expose] def pcD (y : Model.Pauli) : Dfull := iotaD (kappa (pcC y))

theorem pcC_of_mem {y : Model.Pauli} (h : pauliQ y ∈ Subgroup.centralizer {rStar}) :
    pcC y = ⟨rhoEquiv (pauliQ y), rhoEquiv_mem_Cgen h⟩ :=
  dite_eq_left h

theorem pcD_mem_Ehat (y : Model.Pauli) : pcD y ∈ Ehat := by
  by_cases h : pauliQ y ∈ Subgroup.centralizer {rStar}
  · rw [pcD, pcC_of_mem h]
    exact ⟨_, kappa_rho_mem_Ebar h, rfl⟩
  · rw [pcD, pcC, dite_eq_right h, map_one, map_one]
    exact Ehat.one_mem

theorem pauliQ_mul_mem {y y' : Model.Pauli} (hy : pauliQ y ∈ Subgroup.centralizer {rStar})
    (hy' : pauliQ y' ∈ Subgroup.centralizer {rStar}) :
    pauliQ (Model.Pauli.mul y y') ∈ Subgroup.centralizer {rStar} := by
  rw [pauliQ_mul]
  exact Subgroup.mul_mem _ hy hy'

theorem pcD_mul {y y' : Model.Pauli} (hy : pauliQ y ∈ Subgroup.centralizer {rStar})
    (hy' : pauliQ y' ∈ Subgroup.centralizer {rStar}) :
    pcD (Model.Pauli.mul y y') = pcD y' * pcD y := by
  have h : pcC (Model.Pauli.mul y y') = pcC y' * pcC y := by
    rw [pcC_of_mem (pauliQ_mul_mem hy hy'), pcC_of_mem hy, pcC_of_mem hy']
    apply Subtype.ext
    show rhoEquiv (pauliQ (Model.Pauli.mul y y')) = rhoEquiv (pauliQ y') * rhoEquiv (pauliQ y)
    rw [pauliQ_mul, rhoEquiv_mul]
  rw [pcD, h, map_mul, map_mul]
  rfl

theorem pauliQ_h1ConjN_mem (k : Fin 44) {y : Model.Pauli}
    (hy : pauliQ y ∈ Subgroup.centralizer {rStar}) :
    pauliQ (h1ConjN k y) ∈ Subgroup.centralizer {rStar} := by
  rw [← conjQ_h1Lift, Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (conjQ (h1Lift k)) (Subgroup.mem_centralizer_singleton_iff.1 hy)
  rw [map_mul, map_mul, conjQ_h1Lift_rStar] at h
  exact h

theorem h1LiftC_conj_pcC (k : Fin 44) {y : Model.Pauli}
    (hy : pauliQ y ∈ Subgroup.centralizer {rStar}) :
    h1LiftC k * pcC y * (h1LiftC k)⁻¹ = pcC (h1ConjN k y) := by
  rw [pcC_of_mem hy, pcC_of_mem (pauliQ_h1ConjN_mem k hy)]
  apply Subtype.ext
  show thetaEquiv (h1Lift k) * rhoEquiv (pauliQ y) * (thetaEquiv (h1Lift k))⁻¹ =
    rhoEquiv (pauliQ (h1ConjN k y))
  rw [Short.thetaEquiv_conj_rhoEquiv]
  exact congrArg rhoEquiv (conjQ_h1Lift k y)

theorem h1LiftD_conj_pcD (k : Fin 44) {y : Model.Pauli}
    (hy : pauliQ y ∈ Subgroup.centralizer {rStar}) :
    h1LiftD k * pcD y * (h1LiftD k)⁻¹ = pcD (h1ConjN k y) := by
  rw [h1LiftD, pcD, pcD, conj_iotaD_kappa, h1LiftC_conj_pcC k hy]

theorem PhiD_eq_pcD (v : Fin 8 → ZMod 2) : PhiD v = pcD (foldP v) := by
  rw [PhiD, pcD, pcC_of_mem (PhiQ_mem v)]
  rfl

theorem pauliQ_cPauli : pauliQ cPauli = rMinus 0 2 :=
  pauliQ_cocode (w := 5) (by decide) (by decide)

theorem pauliQ_cPauli_mem : pauliQ cPauli ∈ Subgroup.centralizer {rStar} := by
  rw [pauliQ_cPauli]
  exact DQ_mem_centralizer _

theorem cQ_eq_pcD : cQ = pcD cPauli := by
  rw [pcD, pcC_of_mem pauliQ_cPauli_mem]
  show iotaD (kappa ⟨rhoEquiv (rMinus 0 2), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩) =
    iotaD (kappa ⟨rhoEquiv (pauliQ cPauli), rhoEquiv_mem_Cgen pauliQ_cPauli_mem⟩)
  exact congrArg iotaD (kappa_congr pauliQ_cPauli.symm _ _)

open Classical in
@[expose] def psiD (g : Dfull) : Wv v0 := if h : g ∈ Ehat then psiW ⟨g, h⟩ else 0

theorem psiD_of_mem {g : Dfull} (h : g ∈ Ehat) : psiD g = psiW ⟨g, h⟩ := dite_eq_left h

theorem psiD_mul {g g' : Dfull} (hg : g ∈ Ehat) (hg' : g' ∈ Ehat) :
    psiD (g * g') = psiD g + psiD g' := by
  rw [psiD_of_mem (Ehat.mul_mem hg hg'), psiD_of_mem hg, psiD_of_mem hg', ← psiW_mul]
  rfl

theorem psiD_inv {g : Dfull} (hg : g ∈ Ehat) : psiD g⁻¹ = psiD g := by
  rw [psiD_of_mem (Ehat.inv_mem hg), psiD_of_mem hg]
  have h := psiW_inv ⟨g, hg⟩
  rw [ZModModule.neg_eq_self] at h
  exact h

theorem psiD_eq_zero_iff {g : Dfull} (hg : g ∈ Ehat) : psiD g = 0 ↔ g = 1 ∨ g = xhat := by
  rw [psiD_of_mem hg, psiW_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem psiD_xhat : psiD xhat = 0 := (psiD_eq_zero_iff xhat_mem_Ehat).2 (Or.inr rfl)

theorem eq_of_psiD_eq {g g' : Dfull} (hg : g ∈ Ehat) (hg' : g' ∈ Ehat)
    (h : psiD g = psiD g') : g = g' ∨ g = xhat * g' := by
  have h0 : psiD (g * g'⁻¹) = 0 := by
    rw [psiD_mul hg (Ehat.inv_mem hg'), psiD_inv hg', h, ZModModule.add_self]
  rcases (psiD_eq_zero_iff (Ehat.mul_mem hg (Ehat.inv_mem hg'))).1 h0 with e | e
  · exact Or.inl (mul_inv_eq_one.1 e)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.1 e)

theorem coordOf_pauliQ' (y : Model.Pauli) : coordOf (pauliQ y) = (toC y.2.1, toD y.2.2) :=
  Griess.coordOf_spinEquiv _

theorem psiD_pcD_eq_zero_iff {u : Model.Pauli} (hu : pauliQ u ∈ Subgroup.centralizer {rStar}) :
    psiD (pcD u) = 0 ↔ coordOf (pauliQ u) = 0 ∨ coordOf (pauliQ u) = coordOf rStar := by
  rw [psiD_of_mem (pcD_mem_Ehat u)]
  refine CTIB.psiW_eq_zero_iff_coordOf hu ?_
  show iotaD (kappa ⟨rhoEquiv (pauliQ u), rhoEquiv_mem_Cgen hu⟩) = pcD u
  rw [pcD, pcC_of_mem hu]

theorem psiD_pcD_mul {y y' : Model.Pauli} (hy : pauliQ y ∈ Subgroup.centralizer {rStar})
    (hy' : pauliQ y' ∈ Subgroup.centralizer {rStar}) :
    psiD (pcD (Model.Pauli.mul y y')) = psiD (pcD y) + psiD (pcD y') := by
  rw [pcD_mul hy hy', psiD_mul (pcD_mem_Ehat _) (pcD_mem_Ehat _), add_comm]

theorem toC_eq_zero_iff {x : ℕ} (hx : x < 2 ^ 12) : toC x = 0 ↔ x = 0 :=
  ⟨fun h => TwoA.Census.toC_injective hx (by norm_num) (h.trans toC_zero.symm),
    fun h => h ▸ toC_zero⟩

theorem toD_eq_toD_iff {x y : ℕ} (hx : x < 2 ^ 12) (hy : y < 2 ^ 12) : toD x = toD y ↔ x = y :=
  ⟨TwoA.Census.toD_injective hx hy, fun h => h ▸ rfl⟩

theorem psiD_pcD_eq_iff {y y' : Model.Pauli} (hy : pauliQ y ∈ Subgroup.centralizer {rStar})
    (hy' : pauliQ y' ∈ Subgroup.centralizer {rStar}) (hb : boxed y = true)
    (hb' : boxed y' = true) : psiD (pcD y) = psiD (pcD y') ↔ redW y = redW y' := by
  have h0 : psiD (pcD y) = psiD (pcD y') ↔ psiD (pcD (Model.Pauli.mul y y')) = 0 := by
    rw [psiD_pcD_mul hy hy', add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self]
  rw [h0, psiD_pcD_eq_zero_iff (pauliQ_mul_mem hy hy'), coordOf_pauliQ', B.rStar_eq,
    coordOf_pauliQ']
  obtain ⟨s, a, d⟩ := y
  obtain ⟨s', a', d'⟩ := y'
  rw [boxed_iff] at hb hb'
  simp only at hb hb'
  have ha := Nat.xor_lt_two_pow hb.1 hb'.1
  have hd := Nat.xor_lt_two_pow hb.2 hb'.2
  have hR : redW (s, a, d) = redW (s', a', d') ↔ a = a' ∧ (d ^^^ d' = 0 ∨ d ^^^ d' = 191) := by
    show (a, if d.testBit 0 then d ^^^ 191 else d) = (a', if d'.testBit 0 then d' ^^^ 191 else d') ↔ _
    rw [Prod.mk.injEq, redW_d_eq_iff]
  rw [hR]
  show (toC (a ^^^ a'), toD (d ^^^ d')) = 0 ∨ (toC (a ^^^ a'), toD (d ^^^ d')) = (toC 0, toD 191) ↔
    _
  constructor
  · rintro (h | h)
    · rw [Prod.mk_eq_zero] at h
      exact ⟨xor_eq_zero_iff'.1 ((toC_eq_zero_iff ha).1 h.1),
        Or.inl ((toD_eq_toD_iff hd (by norm_num)).1 (h.2.trans toD_zero.symm))⟩
    · rw [Prod.mk.injEq, toC_zero] at h
      exact ⟨xor_eq_zero_iff'.1 ((toC_eq_zero_iff ha).1 h.1),
        Or.inr ((toD_eq_toD_iff hd (by norm_num)).1 h.2)⟩
  · rintro ⟨h1, h2 | h2⟩
    · left
      rw [h1, Nat.xor_self, h2, toC_zero, toD_zero]
      rfl
    · right
      rw [h1, Nat.xor_self, h2]

@[expose] def lftD (k : ℕ) : Dfull := if h : k < 44 then h1LiftD ⟨k, h⟩ else 1

@[expose] def wordD (w : List ℕ) : Dfull := (w.map lftD).prod

theorem lftD_of_lt {k : ℕ} (h : k < 44) : lftD k = h1LiftD ⟨k, h⟩ := dite_eq_left h

theorem lftD_mem_H1 (k : ℕ) : lftD k ∈ H1 := by
  unfold lftD
  split_ifs
  · exact h1LiftD_mem_H1 _
  · exact H1.one_mem

theorem wordD_nil : wordD [] = 1 := rfl

theorem wordD_cons (k : ℕ) (w : List ℕ) : wordD (k :: w) = lftD k * wordD w := by
  rw [wordD, List.map_cons, List.prod_cons]
  rfl

theorem wordD_append (w w' : List ℕ) : wordD (w ++ w') = wordD w * wordD w' := by
  rw [wordD, List.map_append, List.prod_append]
  rfl

theorem wordD_mem_H1 (w : List ℕ) : wordD w ∈ H1 :=
  list_prod_mem fun _ hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact lftD_mem_H1 k

theorem wordD_mem_Xgrp (w : List ℕ) : wordD w ∈ Xgrp := H1_le_Xgrp (wordD_mem_H1 w)

theorem wordD_mem_Jhat (w : List ℕ) : wordD w ∈ Jhat := H1_le_Jhat (wordD_mem_H1 w)

theorem wordD_mem_Shat (w : List ℕ) : wordD w ∈ Shat := Xgrp_le_Shat (wordD_mem_Xgrp w)

theorem wordD_mem_NA8 (w : List ℕ) : wordD w ∈ NA8 := Xgrp_le_normalizer (wordD_mem_Xgrp w)

theorem lftD_mem_Jhat (k : ℕ) : lftD k ∈ Jhat := H1_le_Jhat (lftD_mem_H1 k)

theorem wordD_conj_pcD : ∀ (w : List ℕ), (∀ k ∈ w, k < 44) → ∀ {y : Model.Pauli},
    pauliQ y ∈ Subgroup.centralizer {rStar} →
    pauliQ (wordConj w y) ∈ Subgroup.centralizer {rStar} ∧
      wordD w * pcD y * (wordD w)⁻¹ = pcD (wordConj w y)
  | [], _, y, hy => ⟨hy, by rw [wordD_nil, one_mul, inv_one, mul_one]; rfl⟩
  | k :: w, hw, y, hy => by
    obtain ⟨h1, h2⟩ := wordD_conj_pcD w (fun k' h => hw k' (List.mem_cons_of_mem _ h)) hy
    have hk : k < 44 := hw k (List.mem_cons_self ..)
    have e : wordConj (k :: w) y = h1ConjN (⟨k, hk⟩ : Fin 44) (wordConj w y) := rfl
    rw [e]
    refine ⟨pauliQ_h1ConjN_mem ⟨k, hk⟩ h1, ?_⟩
    rw [wordD_cons, lftD_of_lt hk, ← h1LiftD_conj_pcD ⟨k, hk⟩ h1, ← h2]
    group

theorem lftD_pauli {k : ℕ} (hk : k < 23) : lftD k = pcD (pauliGen k) := by
  rw [lftD_of_lt (by omega), h1LiftD, h1LiftC_pauli (k := ⟨k, by omega⟩) hk, pcD,
    pcC_of_mem (pauliQ_pauliGen_mem k hk)]

theorem pauliQ_zero : pauliQ (false, 0, 0) = 1 := Census.pauliQ_sqPauli_one

theorem psiD_pcD_zero : psiD (pcD (false, 0, 0)) = 0 := by
  have h : pauliQ (false, 0, 0) ∈ Subgroup.centralizer {rStar} := by
    rw [pauliQ_zero]
    exact Subgroup.one_mem _
  refine (psiD_pcD_eq_zero_iff h).2 (Or.inl ?_)
  rw [coordOf_pauliQ']
  show (toC 0, toD 0) = 0
  rw [toC_zero, toD_zero]
  rfl

theorem pauliVec_spec : ∀ w : List ℕ, (∀ k ∈ w, k < 23) →
    pauliQ (pauliVec w) ∈ Subgroup.centralizer {rStar} ∧ wordD w ∈ Ehat ∧
      psiD (wordD w) = psiD (pcD (pauliVec w))
  | [], _ => by
    refine ⟨?_, ?_, ?_⟩
    · show pauliQ (false, 0, 0) ∈ _
      rw [pauliQ_zero]
      exact Subgroup.one_mem _
    · exact Ehat.one_mem
    · rw [wordD_nil, show pauliVec [] = (false, 0, 0) from rfl, psiD_pcD_zero,
        psiD_of_mem Ehat.one_mem]
      exact psiW_one
  | k :: w, hw => by
    obtain ⟨h1, h2, h3⟩ := pauliVec_spec w fun k' h => hw k' (List.mem_cons_of_mem _ h)
    have hk : k < 23 := hw k (List.mem_cons_self ..)
    have hg := pauliQ_pauliGen_mem k hk
    have e : pauliVec (k :: w) = Model.Pauli.mul (pauliGen k) (pauliVec w) := rfl
    have hl : lftD k ∈ Ehat := by
      rw [lftD_pauli hk]
      exact pcD_mem_Ehat _
    rw [e, wordD_cons]
    refine ⟨pauliQ_mul_mem hg h1, Ehat.mul_mem hl h2, ?_⟩
    rw [psiD_mul hl h2, h3, psiD_pcD_mul hg h1, lftD_pauli hk]

theorem mem_subWord {gs : List (List ℕ)} {m k : ℕ} (h : k ∈ subWord gs m) : ∃ w ∈ gs, k ∈ w := by
  obtain ⟨i, hi, hk⟩ := List.mem_flatMap.1 h
  have hi' := List.mem_range.1 (List.mem_filter.1 hi).1
  refine ⟨gs.getD i [], ?_, hk⟩
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

theorem wordD_flatMap (l : List ℕ) (f : ℕ → List ℕ) :
    wordD (l.flatMap f) = (l.map fun i => wordD (f i)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, wordD_append, ih, List.map_cons, List.prod_cons]

theorem wordD_subWord_mem {H : Subgroup Dfull} {gs : List (List ℕ)}
    (h : ∀ w ∈ gs, wordD w ∈ H) (m : ℕ) : wordD (subWord gs m) ∈ H := by
  rw [subWord, wordD_flatMap]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 (List.mem_filter.1 hi).1
  rw [List.getD_eq_getElem _ _ hi']
  exact h _ (List.getElem_mem hi')

theorem conjHom_wordD : ∀ (w : List ℕ), (∀ k ∈ w, k < 44) → ∀ x : ℕ,
    conjHom ⟨wordD w, wordD_mem_NA8 w⟩ (bvec 8 x) = bvec 8 (actWord w x)
  | [], _, x => by
    have e : (⟨wordD [], wordD_mem_NA8 []⟩ : NA8) = 1 := rfl
    rw [e, map_one]
    rfl
  | k :: w, hw, x => by
    have hk : k < 44 := hw k (List.mem_cons_self ..)
    have e : (⟨wordD (k :: w), wordD_mem_NA8 _⟩ : NA8) =
        ⟨xGen ⟨k, by omega⟩, xGen_mem_NA8 _⟩ * ⟨wordD w, wordD_mem_NA8 w⟩ := by
      apply Subtype.ext
      show wordD (k :: w) = xGen ⟨k, by omega⟩ * wordD w
      rw [wordD_cons, lftD_of_lt hk, h1LiftD_eq_xGen]
    rw [e, map_mul, LinearEquiv.mul_apply,
      conjHom_wordD w (fun k' h => hw k' (List.mem_cons_of_mem _ h)) x]
    exact xGenL_bvec ⟨k, by omega⟩ (actWord w x)

theorem wordD_mem_Lgrp {w : List ℕ} (hw : ∀ k ∈ w, k < 44) (h : ∀ x < 256, actWord w x = x) :
    wordD w ∈ Lgrp := by
  rw [Lgrp, Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨u, hu⟩ := aEquiv.surjective ⟨a, ha⟩
  obtain ⟨x, hx, hxu⟩ := exists_bvec8 (Multiplicative.toAdd u)
  have e := aEquiv_conjHom ⟨wordD w, wordD_mem_NA8 w⟩ (bvec 8 x)
  rw [conjHom_wordD w hw x, h x hx] at e
  have ha' : (aEquiv (Multiplicative.ofAdd (bvec 8 x)) : Dfull) = a := by
    rw [hxu, ofAdd_toAdd, hu]
  rw [ha'] at e
  have e' : a = wordD w * a * (wordD w)⁻¹ := e
  calc a * wordD w = wordD w * a * (wordD w)⁻¹ * wordD w := by rw [← e']
    _ = wordD w * a := by group

theorem wordD_mem_P4p {w : List ℕ} (hw : ∀ k ∈ w, k < 44)
    (h : ∀ x < 256, actWord w x < 256 ∧ qN (actWord w x ^^^ 64) = qN (x ^^^ 64)) :
    wordD w ∈ P4p := by
  refine (mem_P4p_iff ⟨wordD w, wordD_mem_Xgrp w⟩).2 ?_
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨x, hx, rfl⟩ := exists_bvec8 v
  have e : rhoX ⟨wordD w, wordD_mem_Xgrp w⟩ (bvec 8 x) = bvec 8 (actWord w x) :=
    conjHom_wordD w hw x
  have h64 : (64 : ℕ) < 2 ^ 8 := by norm_num
  obtain ⟨h1, h2⟩ := h x hx
  rw [e, qPlus_apply, qPlus_apply, show Sp8.vPlus = bvec 8 64 from rfl, ← bvec_xor, ← bvec_xor,
    qPoly_bvec _ (Nat.xor_lt_two_pow (show actWord w x < 2 ^ 8 from h1) h64),
    qPoly_bvec _ (Nat.xor_lt_two_pow (show x < 2 ^ 8 from hx) h64), h2]

open Classical in
@[expose] def projK (g : Dfull) : Kstab v0 := if h : g ∈ Jhat then jhatToKv0 ⟨g, h⟩ else 1

theorem projK_of_mem {g : Dfull} (h : g ∈ Jhat) : projK g = jhatToKv0 ⟨g, h⟩ := dite_eq_left h

theorem projK_mul {g g' : Dfull} (hg : g ∈ Jhat) (hg' : g' ∈ Jhat) :
    projK (g * g') = projK g * projK g' := by
  rw [projK_of_mem (Jhat.mul_mem hg hg'), projK_of_mem hg, projK_of_mem hg', ← map_mul]
  rfl

theorem projK_one : projK 1 = 1 := by
  rw [projK_of_mem Jhat.one_mem]
  exact map_one jhatToKv0

theorem projK_inv {g : Dfull} (hg : g ∈ Jhat) : projK g⁻¹ = (projK g)⁻¹ := by
  rw [projK_of_mem (Jhat.inv_mem hg), projK_of_mem hg, ← map_inv]
  rfl

theorem projK_eq_one_iff {g : Dfull} (hg : g ∈ Jhat) : projK g = 1 ↔ g ∈ Ehat := by
  rw [projK_of_mem hg, ← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf]

theorem projK_lftD_pauli {k : ℕ} (hk : k < 23) : projK (lftD k) = 1 := by
  rw [projK_eq_one_iff (lftD_mem_Jhat k), lftD_of_lt (by omega)]
  exact h1LiftD_mem_Ehat (k := ⟨k, by omega⟩) hk

theorem projK_lftD {k : ℕ} (h1 : 23 ≤ k) (h2 : k < 44) :
    projK (lftD k) = (Co2Inv.cGen ⟨k - 23, by omega⟩)⁻¹ := by
  have e : projK (lftD k) = jhatToKv0 ⟨h1LiftD ⟨k, h2⟩, h1LiftD_mem_Jhat _⟩ := by
    rw [projK_of_mem (lftD_mem_Jhat k)]
    congr 2
    exact lftD_of_lt h2
  rw [e]
  exact jhatToKv0_h1LiftD (k := ⟨k, h2⟩) h1

theorem rK_inv : Co2Inv.rK⁻¹ = Co2Inv.rK := inv_eq_of_mul_eq_one_right Co2Inv.rK_mul_self

theorem projK_lftD_32 : projK (lftD 32) = Co2Inv.rK := by
  rw [projK_lftD (by norm_num) (by norm_num), Co2Inv.cGen_of_ge (by norm_num), ← rK_inv]
  rfl

theorem wAct_lftD {k : ℕ} (hk : k < 44) :
    wAct v0 (projK (lftD k))⁻¹ = Co2Inv.rowsEnd (liftRows k) := by
  by_cases h : 23 ≤ k
  · rw [projK_lftD h hk, inv_inv, Co2Inv.wAct_cGen, liftRows, ite_eq_left ⟨h, hk⟩]
  · rw [projK_lftD_pauli (by omega), inv_one, wAct_one, liftRows, ite_eq_right (by omega),
      Co2Inv.rowsEnd_idRows]

theorem wAct_wordD : ∀ (w : List ℕ), (∀ k ∈ w, k < 44) →
    wAct v0 (projK (wordD w))⁻¹ = Co2Inv.rowsEnd (wordRows w)
  | [], _ => by
    rw [wordD_nil, projK_one, inv_one, wAct_one]
    exact Co2Inv.rowsEnd_idRows.symm
  | k :: w, hw => by
    have hk : k < 44 := hw k (List.mem_cons_self ..)
    rw [wordD_cons, projK_mul (lftD_mem_Jhat k) (wordD_mem_Jhat w), mul_inv_rev, wAct_mul,
      wAct_lftD hk, wAct_wordD w (fun k' h => hw k' (List.mem_cons_of_mem _ h)),
      Co2Inv.rowsEnd_mul]
    rfl

theorem rowKey_eq (w : List ℕ) : rowKey w = (List.range 22).map fun t => (wordRows w)[t]! := rfl

theorem wordRows_lt {w : List ℕ} (h : keyOK (rowKey w) = true) {t : ℕ} (ht : t < 22) :
    (wordRows w)[t]! < 2 ^ 22 := by
  have h1 := List.all_eq_true.1 h
  rw [rowKey_eq] at h1
  exact of_decide_eq_true (h1 _ (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩))

theorem rowKey_eq_of_projK_eq {w w' : List ℕ} (hw : ∀ k ∈ w, k < 44) (hw' : ∀ k ∈ w', k < 44)
    (h : projK (wordD w) = projK (wordD w')) (hk : keyOK (rowKey w) = true)
    (hk' : keyOK (rowKey w') = true) : rowKey w = rowKey w' := by
  have e : Co2Inv.rowsEnd (wordRows w) = Co2Inv.rowsEnd (wordRows w') := by
    rw [← wAct_wordD w hw, ← wAct_wordD w' hw', h]
  rw [rowKey_eq, rowKey_eq]
  refine List.map_congr_left fun t ht => ?_
  have ht' := List.mem_range.1 ht
  have e1 := congrArg (fun f => f (qbW ⟨t, ht'⟩)) e
  simp only [Co2Inv.rowsEnd_qbW] at e1
  exact decW_injective (wordRows_lt hk ht') (wordRows_lt hk' ht') e1

theorem projK_eq_one_of_rowKey {w : List ℕ} (hw : ∀ k ∈ w, k < 44) (h : rowKey w = rowKey []) :
    projK (wordD w) = 1 := by
  rw [rowKey_eq, rowKey_eq] at h
  have e : Co2Inv.rowsEnd (wordRows w) = Co2Inv.rowsEnd Co2Inv.idRows :=
    Co2Inv.rowsEnd_congr fun t ht => List.map_inj_left.1 h t (List.mem_range.2 ht)
  rw [← wAct_wordD w hw, Co2Inv.rowsEnd_idRows, ← wAct_one] at e
  exact inv_eq_one.1 (Co2Inv.eq_of_wAct_eq e)

theorem A8_le_Jhat : A8 ≤ Jhat := (A8_le_T9.trans T9_le_Lgrp).trans Amalgam.Lgrp_le_Jhat

theorem projK_A8 {a : Dfull} (ha : a ∈ A8) : projK a = 1 ∨ projK a = Co2Inv.rK := by
  rw [← range_PsiHom] at ha
  obtain ⟨v, rfl⟩ := ha
  rw [PsiHom_apply, Psi]
  have h1 : PhiD v.toAdd ∈ Jhat := A8_le_Jhat (B7_le_A8 (PhiD_mem_B7 _))
  rw [projK_mul h1 (Jhat.pow_mem ghat8_mem_Jhat _),
    (projK_eq_one_iff h1).2 (B7_le_Ehat (PhiD_mem_B7 _)), one_mul]
  rcases Sp8.zmod2_cases (v.toAdd 7) with h | h
  · rw [h, ZMod.val_zero, pow_zero, projK_one]
    exact Or.inl rfl
  · rw [h, show (1 : ZMod 2).val = 1 from rfl, pow_one, projK_of_mem ghat8_mem_Jhat,
      jhatToKv0_ghat8]
    exact Or.inr rfl

theorem projK_T9 {t : Dfull} (ht : t ∈ T9) : projK t = 1 ∨ projK t = Co2Inv.rK := by
  rcases (mem_T9_iff t).1 ht with h | h
  · exact projK_A8 h
  · have e : t = cQ * (cQ * t) := by rw [← mul_assoc, cQ_mul_self, one_mul]
    have hc : cQ ∈ Jhat := Ehat_le_Jhat cQ_mem_Ehat
    rw [e, projK_mul hc (A8_le_Jhat h), (projK_eq_one_iff hc).2 cQ_mem_Ehat, one_mul]
    exact projK_A8 h

theorem exists_of_mem_T9_Ehat {t : Dfull} (ht : t ∈ T9) (he : t ∈ Ehat) :
    ∃ m < 256, t = pcD (foldP (bvec 8 m)) ∨
      t = pcD (Model.Pauli.mul (foldP (bvec 8 m)) cPauli) := by
  have hA : ∀ a ∈ A8, a ∈ Ehat → ∃ v, a = PhiD v := by
    intro a ha hae
    rw [← range_PsiHom] at ha
    obtain ⟨v, rfl⟩ := ha
    refine ⟨v.toAdd, ?_⟩
    rcases Sp8.zmod2_cases (v.toAdd 7) with h | h
    · rw [PsiHom_apply, Psi, h, ZMod.val_zero, pow_zero, mul_one]
    · exact absurd hae (Psi_not_mem_Ehat h)
  rcases (mem_T9_iff t).1 ht with h | h
  · obtain ⟨v, rfl⟩ := hA t h he
    obtain ⟨m, hm, rfl⟩ := exists_bvec8 v
    exact ⟨m, hm, Or.inl (PhiD_eq_pcD _)⟩
  · obtain ⟨v, hv⟩ := hA _ h (Ehat.mul_mem cQ_mem_Ehat he)
    obtain ⟨m, hm, rfl⟩ := exists_bvec8 v
    refine ⟨m, hm, Or.inr ?_⟩
    have e : t = cQ * (cQ * t) := by rw [← mul_assoc, cQ_mul_self, one_mul]
    rw [e, hv, PhiD_eq_pcD, cQ_eq_pcD, pcD_mul (PhiQ_mem _) pauliQ_cPauli_mem]

theorem pcD_foldP_mem_T9 (v : Fin 8 → ZMod 2) : pcD (foldP v) ∈ T9 := by
  rw [← PhiD_eq_pcD]
  exact A8_le_T9 (B7_le_A8 (PhiD_mem_B7 v))

theorem pcD_foldP_cPauli_mem_T9 (v : Fin 8 → ZMod 2) :
    pcD (Model.Pauli.mul (foldP v) cPauli) ∈ T9 := by
  rw [pcD_mul (PhiQ_mem _) pauliQ_cPauli_mem, ← cQ_eq_pcD, ← PhiD_eq_pcD]
  exact T9.mul_mem cQ_mem_T9 (A8_le_T9 (B7_le_A8 (PhiD_mem_B7 v)))

theorem boxed_foldP (v : Fin 8 → ZMod 2) : boxed (foldP v) = true :=
  (boxed_iff _).2 (foldP_checks.2.2.2.2.1 v)

theorem boxed_foldP_cPauli (v : Fin 8 → ZMod 2) :
    boxed (Model.Pauli.mul (foldP v) cPauli) = true :=
  boxed_mul (boxed_foldP v) (by decide)

theorem mem_u7Elts {m : ℕ} {u : Model.Pauli} :
    u ∈ u7Elts m ↔ u = foldP (bvec 8 m) ∨ u = Model.Pauli.mul (foldP (bvec 8 m)) cPauli := by
  simp [u7Elts]

theorem u7Elts_mem {m : ℕ} {u : Model.Pauli} (hu : u ∈ u7Elts m) :
    pauliQ u ∈ Subgroup.centralizer {rStar} ∧ boxed u = true ∧ pcD u ∈ T9 := by
  rcases mem_u7Elts.1 hu with rfl | rfl
  · exact ⟨PhiQ_mem _, boxed_foldP _, pcD_foldP_mem_T9 _⟩
  · exact ⟨pauliQ_mul_mem (PhiQ_mem _) pauliQ_cPauli_mem, boxed_foldP_cPauli _,
      pcD_foldP_cPauli_mem_T9 _⟩

theorem mem_u7Idx {n : ℕ} : n ∈ u7Idx ↔ ∃ m < 256, ∃ u ∈ u7Elts m, decodeW (redW u) = n := by
  simp only [u7Idx, List.mem_dedup, List.mem_flatMap, List.mem_range, List.mem_map]

theorem exists_u7Elts_of_mem {t : Dfull} (ht : t ∈ T9) (he : t ∈ Ehat) :
    ∃ m < 256, ∃ u ∈ u7Elts m, t = pcD u := by
  obtain ⟨m, hm, h | h⟩ := exists_of_mem_T9_Ehat ht he
  · exact ⟨m, hm, _, mem_u7Elts.2 (Or.inl rfl), h⟩
  · exact ⟨m, hm, _, mem_u7Elts.2 (Or.inr rfl), h⟩

@[expose] def projL : Lgrp →* Kstab v0 := jhatToKv0.comp (Subgroup.inclusion Amalgam.Lgrp_le_Jhat)

theorem projL_apply (g : Lgrp) : projL g = projK g := (projK_of_mem (Amalgam.Lgrp_le_Jhat g.2)).symm

theorem mem_ker_projL (g : Lgrp) : g ∈ projL.ker ↔ (g : Dfull) ∈ Ehat := by
  rw [MonoidHom.mem_ker, projL_apply, projK_eq_one_iff (Amalgam.Lgrp_le_Jhat g.2)]

theorem coGens_lt : ∀ w ∈ coGens, ∀ k ∈ w, k < 44 := by decide

theorem pauliWords_lt : ∀ w ∈ pauliWords, ∀ k ∈ w, k < 23 := by decide

theorem subWord_coGens_lt (m : ℕ) : ∀ k ∈ subWord coGens m, k < 44 := fun _ hk => by
  obtain ⟨w, hw, hkw⟩ := mem_subWord hk
  exact coGens_lt w hw _ hkw

theorem subWord_pauliWords_lt (m : ℕ) : ∀ k ∈ subWord pauliWords m, k < 23 := fun _ hk => by
  obtain ⟨w, hw, hkw⟩ := mem_subWord hk
  exact pauliWords_lt w hw _ hkw

theorem rowsCheck_spec (h : rowsCheck = true) :
    ∀ w ∈ coGens ++ pauliWords, ∀ x < 256, actWord w x = x := by
  intro w hw x hx
  have h1 := List.all_eq_true.1 h w hw
  exact beq_iff_eq.1 (List.all_eq_true.1 h1 x (List.mem_range.2 hx))

theorem wordD_coGens_mem_Lgrp (h : rowsCheck = true) (m : ℕ) :
    wordD (subWord coGens m) ∈ Lgrp :=
  wordD_subWord_mem (fun w hw => wordD_mem_Lgrp (coGens_lt w hw)
    (rowsCheck_spec h w (List.mem_append_left _ hw))) m

theorem wordD_pauliWords_mem_Lgrp (h : rowsCheck = true) (m : ℕ) :
    wordD (subWord pauliWords m) ∈ Lgrp :=
  wordD_subWord_mem (fun w hw => wordD_mem_Lgrp (fun k hk => by
    have := pauliWords_lt w hw k hk
    omega) (rowsCheck_spec h w (List.mem_append_right _ hw))) m

theorem qCheck_spec (h : qCheck = true) :
    ((List.range 512).map fun m => rowKey (subWord coGens m)).Nodup ∧
      ∀ m < 512, keyOK (rowKey (subWord coGens m)) = true := by
  simp only [qCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun m hm => h.2 _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)⟩

theorem pauliCheck_spec (h : pauliCheck = true) :
    ∀ m < 32768, decodeW (redW (pauliProd m)) = m ∧ boxed (pauliProd m) = true := by
  simp only [pauliCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h

theorem getD_pauliWords_lt (i : ℕ) : ∀ k ∈ pauliWords.getD i [], k < 23 := by
  intro k hk
  by_cases hi : i < pauliWords.length
  · rw [List.getD_eq_getElem _ _ hi] at hk
    exact pauliWords_lt _ (List.getElem_mem hi) k hk
  · rw [List.getD_eq_default _ _ (not_lt.1 hi)] at hk
    simp at hk

theorem pauliProd_spec (m : ℕ) :
    pauliQ (pauliProd m) ∈ Subgroup.centralizer {rStar} ∧
      wordD (subWord pauliWords m) ∈ Ehat ∧
      psiD (wordD (subWord pauliWords m)) = psiD (pcD (pauliProd m)) :=
  pauliVec_spec _ (subWord_pauliWords_lt m)

theorem finite_of_natCard_mul {α β : Type*} {n : ℕ} (h : Nat.card α * Nat.card β = n)
    (hn : n ≠ 0) : Finite α ∧ Finite β :=
  ⟨Nat.finite_of_card_ne_zero fun h0 => hn (by rw [← h, h0, zero_mul]),
    Nat.finite_of_card_ne_zero fun h0 => hn (by rw [← h, h0, mul_zero])⟩

theorem natCard_projL : Nat.card projL.ker * Nat.card projL.range = 2 ^ 25 := by
  rw [Co2Inv.natCard_ker_mul_range, natCard_Lgrp]

@[expose] def rangeElt (h : rowsCheck = true) (m : Fin 512) : projL.range :=
  ⟨projL ⟨wordD (subWord coGens m), wordD_coGens_mem_Lgrp h m⟩, ⟨_, rfl⟩⟩

theorem rangeElt_injective (h : rowsCheck = true) (hq : qCheck = true) :
    Function.Injective (rangeElt h) := by
  intro m m' e
  have e1 : projK (wordD (subWord coGens m)) = projK (wordD (subWord coGens m')) := by
    rw [← projL_apply ⟨_, wordD_coGens_mem_Lgrp h m⟩, ← projL_apply ⟨_, wordD_coGens_mem_Lgrp h m'⟩]
    exact congrArg Subtype.val e
  obtain ⟨hnd, hok⟩ := qCheck_spec hq
  have e2 := rowKey_eq_of_projK_eq (subWord_coGens_lt m) (subWord_coGens_lt m') e1 (hok m m.2)
    (hok m' m'.2)
  exact Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 m.2) (List.mem_range.2 m'.2) e2)

@[expose] def kerElt (h : rowsCheck = true) (p : Fin 32768 × Fin 2) : projL.ker :=
  ⟨⟨wordD (subWord pauliWords p.1) * xhat ^ (p.2 : ℕ),
    Lgrp.mul_mem (wordD_pauliWords_mem_Lgrp h p.1) (Lgrp.pow_mem (A8_le_Lgrp xhat_mem_A8) _)⟩,
    (mem_ker_projL _).2 (Ehat.mul_mem (pauliProd_spec p.1).2.1 (Ehat.pow_mem xhat_mem_Ehat _))⟩

theorem psiD_xhat_pow (n : ℕ) : psiD (xhat ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero, psiD_of_mem Ehat.one_mem]; exact psiW_one
  | succ n ih =>
    rw [pow_succ, psiD_mul (Ehat.pow_mem xhat_mem_Ehat _) xhat_mem_Ehat, ih, psiD_xhat, add_zero]

theorem psiD_kerElt (h : rowsCheck = true) (p : Fin 32768 × Fin 2) :
    psiD ((kerElt h p : Lgrp) : Dfull) = psiD (pcD (pauliProd p.1)) := by
  show psiD (wordD (subWord pauliWords p.1) * xhat ^ (p.2 : ℕ)) = _
  rw [psiD_mul (pauliProd_spec p.1).2.1 (Ehat.pow_mem xhat_mem_Ehat _), psiD_xhat_pow, add_zero,
    (pauliProd_spec p.1).2.2]

theorem eq_of_xhat_pow_eq {a b : Fin 2} (h : xhat ^ (a : ℕ) = xhat ^ (b : ℕ)) : a = b := by
  have hx : xhat ≠ 1 := TwoA.xhat_ne_one
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only at h
  interval_cases a <;> interval_cases b
  · rfl
  · rw [pow_zero, pow_one] at h
    exact absurd h.symm hx
  · rw [pow_zero, pow_one] at h
    exact absurd h hx
  · rfl

theorem kerElt_injective (h : rowsCheck = true) (hp : pauliCheck = true) :
    Function.Injective (kerElt h) := by
  intro p p' e
  have e0 : ((kerElt h p : Lgrp) : Dfull) = ((kerElt h p' : Lgrp) : Dfull) := by rw [e]
  have e1 := congrArg psiD e0
  rw [psiD_kerElt, psiD_kerElt] at e1
  have hc := pauliCheck_spec hp
  have e2 := (psiD_pcD_eq_iff (pauliProd_spec p.1).1 (pauliProd_spec p'.1).1 (hc p.1 p.1.2).2
    (hc p'.1 p'.1.2).2).1 e1
  have hm : p.1 = p'.1 := Fin.ext (by rw [← (hc p.1 p.1.2).1, e2, (hc p'.1 p'.1.2).1])
  change wordD (subWord pauliWords p.1) * xhat ^ (p.2 : ℕ) =
    wordD (subWord pauliWords p'.1) * xhat ^ (p'.2 : ℕ) at e0
  rw [hm] at e0
  exact Prod.ext hm (eq_of_xhat_pow_eq (mul_left_cancel e0))

theorem card_le_ker (h : rowsCheck = true) (hp : pauliCheck = true) [Finite projL.ker] :
    65536 ≤ Nat.card projL.ker := by
  have h1 := Nat.card_le_card_of_injective _ (kerElt_injective h hp)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 32768),
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Fintype.card_fin] at h1
  exact h1

theorem card_le_range (h : rowsCheck = true) (hq : qCheck = true) [Finite projL.range] :
    512 ≤ Nat.card projL.range := by
  have h1 := Nat.card_le_card_of_injective _ (rangeElt_injective h hq)
  rw [Nat.card_eq_fintype_card (α := Fin 512), Fintype.card_fin] at h1
  exact h1

theorem natCard_projL_eq (h : rowsCheck = true) (hq : qCheck = true) (hp : pauliCheck = true) :
    Finite projL.ker ∧ Finite projL.range ∧ Nat.card projL.ker = 65536 ∧
      Nat.card projL.range = 512 := by
  obtain ⟨hk, hr⟩ := finite_of_natCard_mul natCard_projL (by norm_num)
  have h1 := card_le_ker h hp
  have h2 := card_le_range h hq
  have h3 : Nat.card projL.ker * Nat.card projL.range = 33554432 := by
    rw [natCard_projL]
    norm_num
  have hb : Nat.card projL.range = 512 := by
    by_contra hne
    have h4 := Nat.mul_le_mul h1 (show 513 ≤ Nat.card projL.range by omega)
    rw [h3] at h4
    omega
  refine ⟨hk, hr, ?_, hb⟩
  rw [hb] at h3
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 512) (h3.trans (by norm_num))

theorem exists_projK_eq (h : rowsCheck = true) (hq : qCheck = true) (hp : pauliCheck = true)
    {y : Dfull} (hy : y ∈ Lgrp) : ∃ m < 512, projK y = projK (wordD (subWord coGens m)) := by
  obtain ⟨-, hr, -, h2⟩ := natCard_projL_eq h hq hp
  have hc : Nat.card projL.range ≤ Nat.card (Fin 512) := by
    rw [Nat.card_eq_fintype_card (α := Fin 512), Fintype.card_fin, h2]
  obtain ⟨m, hm⟩ := ((rangeElt_injective h hq).bijective_of_nat_card_le hc).2
    ⟨projL ⟨y, hy⟩, ⟨_, rfl⟩⟩
  refine ⟨m, m.2, ?_⟩
  have e : projL ⟨wordD (subWord coGens m), wordD_coGens_mem_Lgrp h m⟩ = projL ⟨y, hy⟩ :=
    congrArg Subtype.val hm
  rw [← projL_apply ⟨y, hy⟩, ← projL_apply ⟨_, wordD_coGens_mem_Lgrp h m⟩]
  exact e.symm

theorem exists_psiD_eq (h : rowsCheck = true) (hq : qCheck = true) (hp : pauliCheck = true)
    {e : Dfull} (heL : e ∈ Lgrp) (heE : e ∈ Ehat) :
    ∃ m < 32768, psiD e = psiD (pcD (pauliProd m)) := by
  obtain ⟨hk, -, h1, -⟩ := natCard_projL_eq h hq hp
  have hc : Nat.card projL.ker ≤ Nat.card (Fin 32768 × Fin 2) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 32768),
      Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Fintype.card_fin, h1]
  obtain ⟨p, hp'⟩ := ((kerElt_injective h hp).bijective_of_nat_card_le hc).2
    ⟨⟨e, heL⟩, (mem_ker_projL _).2 heE⟩
  refine ⟨p.1, p.1.2, ?_⟩
  have e1 : ((kerElt h p : Lgrp) : Dfull) = e :=
    congrArg (fun x : projL.ker => ((x : Lgrp) : Dfull)) hp'
  rw [← e1, psiD_kerElt]

@[expose] def bW (i : ℕ) : Wv v0 := psiD (pcD (pauliBasis i))

@[expose] def vecW (n : ℕ) : Wv v0 := ∑ i ∈ Finset.range 15, if n.testBit i then bW i else 0

theorem vecW_xor (a b : ℕ) : vecW (a ^^^ b) = vecW a + vecW b := by
  rw [vecW, vecW, vecW, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp [ZModModule.add_self]

theorem vecW_zero : vecW 0 = 0 := by simp [vecW]

theorem psiD_list_prod : ∀ l : List Dfull, (∀ x ∈ l, x ∈ Ehat) → psiD l.prod = (l.map psiD).sum
  | [], _ => by
    rw [List.prod_nil, List.map_nil, List.sum_nil, psiD_of_mem Ehat.one_mem]
    exact psiW_one
  | x :: l, h => by
    have hl : ∀ y ∈ l, y ∈ Ehat := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      psiD_mul (h x (List.mem_cons_self ..)) (list_prod_mem hl), psiD_list_prod l hl]

theorem sum_filter_range {M : Type*} [AddCommMonoid M] (p : ℕ → Bool) (g : ℕ → M) :
    ∀ n, (((List.range n).filter p).map g).sum = ∑ i ∈ Finset.range n, if p i then g i else 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range p g n, Finset.sum_range_succ]
    cases h : p n <;> simp [h]

theorem psiD_wordD_getD (i : ℕ) : psiD (wordD (pauliWords.getD i [])) = bW i := by
  rw [bW, pauliBasis]
  exact (pauliVec_spec _ (getD_pauliWords_lt i)).2.2

theorem psiD_wordD_subWord (m : ℕ) : psiD (wordD (subWord pauliWords m)) = vecW m := by
  have hmem : ∀ x ∈ ((List.range pauliWords.length).filter fun i => m.testBit i).map
      fun i => wordD (pauliWords.getD i []), x ∈ Ehat := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact (pauliVec_spec _ (getD_pauliWords_lt i)).2.1
  rw [subWord, wordD_flatMap, psiD_list_prod _ hmem, List.map_map]
  have e : (psiD ∘ fun i => wordD (pauliWords.getD i [])) = bW := funext psiD_wordD_getD
  rw [e, show pauliWords.length = 15 from rfl, sum_filter_range]
  rfl

theorem psiD_pauliProd (m : ℕ) : psiD (pcD (pauliProd m)) = vecW m := by
  rw [← (pauliProd_spec m).2.2, psiD_wordD_subWord]

theorem vecW_injective (hp : pauliCheck = true) {n n' : ℕ} (hn : n < 32768) (hn' : n' < 32768)
    (h : vecW n = vecW n') : n = n' := by
  rw [← psiD_pauliProd, ← psiD_pauliProd] at h
  have hc := pauliCheck_spec hp
  have e := (psiD_pcD_eq_iff (pauliProd_spec n).1 (pauliProd_spec n').1 (hc n hn).2
    (hc n' hn').2).1 h
  rw [← (hc n hn).1, e, (hc n' hn').1]

@[expose] def sD : Dfull := wordD sWord

theorem sWord_lt : ∀ k ∈ sWord, k < 44 := by decide

theorem conj_mem_Ehat' {g e : Dfull} (hg : g ∈ Jhat) (he : e ∈ Ehat) : g * e * g⁻¹ ∈ Ehat := by
  have h := conj_mem_Ehat (Jhat.inv_mem hg) he
  rwa [inv_inv] at h

theorem psiD_conj {g e : Dfull} (hg : g ∈ Jhat) (he : e ∈ Ehat) :
    psiD (g * e * g⁻¹) = wAct v0 (projK g)⁻¹ (psiD e) := by
  have h := psiW_conj (Jhat.inv_mem hg) he
  rw [← projK_inv hg, projK_of_mem (Jhat.inv_mem hg), psiD_of_mem he, ← h,
    psiD_of_mem (conj_mem_Ehat' hg he)]
  congr 1
  apply Subtype.ext
  show g * e * g⁻¹ = g⁻¹⁻¹ * e * g⁻¹
  rw [inv_inv]

theorem psiD_comm {e g : Dfull} (he : e ∈ Ehat) (hg : g ∈ Jhat) :
    psiD (e * g * e⁻¹ * g⁻¹) = psiD e + wAct v0 (projK g)⁻¹ (psiD e) := by
  rw [show e * g * e⁻¹ * g⁻¹ = e * (g * e⁻¹ * g⁻¹) by group,
    psiD_mul he (conj_mem_Ehat' hg (Ehat.inv_mem he)), psiD_conj hg (Ehat.inv_mem he),
    psiD_inv he]

theorem commCheck_spec (hc : commCheck = true) : ∀ i < 15, boxed (commS (pauliBasis i)) = true ∧
    commRows[i]! < 32768 ∧ redW (pauliProd commRows[i]!) = redW (commS (pauliBasis i)) := by
  simp only [commCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hc
  exact fun i hi => ⟨(hc i hi).1.1, (hc i hi).1.2, (hc i hi).2⟩

theorem bW_add_wAct (hp : pauliCheck = true) (hc : commCheck = true) {i : ℕ} (hi : i < 15) :
    bW i + wAct v0 (projK sD)⁻¹ (bW i) = vecW commRows[i]! := by
  have hP : pauliQ (pauliBasis i) ∈ Subgroup.centralizer {rStar} :=
    (pauliVec_spec _ (getD_pauliWords_lt i)).1
  obtain ⟨hC, hconj⟩ := wordD_conj_pcD sWord sWord_lt hP
  obtain ⟨hb, hlt, hred⟩ := commCheck_spec hc i hi
  have hcomm : psiD (pcD (commS (pauliBasis i))) =
      psiD (pcD (wordConj sWord (pauliBasis i))) + psiD (pcD (pauliBasis i)) :=
    psiD_pcD_mul hC hP
  rw [bW, sD, ← psiD_conj (wordD_mem_Jhat sWord) (pcD_mem_Ehat _), hconj, ← psiD_pauliProd,
    add_comm, ← hcomm]
  exact (psiD_pcD_eq_iff (pauliQ_mul_mem hC hP) (pauliProd_spec _).1 hb
    (pauliCheck_spec hp _ hlt).2).2 hred.symm

theorem vecW_add_wAct (hp : pauliCheck = true) (hc : commCheck = true) (m : ℕ) :
    vecW m + wAct v0 (projK sD)⁻¹ (vecW m) = vecW (Native.actD 15 commRows m) := by
  have h := xorHom_actGo vecW vecW_xor commRows m 15 0
  rw [show Native.actD 15 commRows m = VisCert.Native.actGo commRows m 15 0 from rfl, h,
    vecW_zero, zero_add, vecW, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  split_ifs
  · exact bW_add_wAct hp hc (Finset.mem_range.1 hi)
  · rw [map_zero, add_zero]

theorem u7Check_spec (hu : u7Check = true) : ∀ m < 256, ∀ u ∈ u7Elts m,
    decodeW (redW u) < 32768 ∧ redW (pauliProd (decodeW (redW u))) = redW u := by
  simp only [u7Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hu
  exact hu

theorem psiD_u7Elt (hp : pauliCheck = true) (hu : u7Check = true) {m : ℕ} (hm : m < 256)
    {u : Model.Pauli} (hu' : u ∈ u7Elts m) : psiD (pcD u) = vecW (decodeW (redW u)) := by
  obtain ⟨hlt, hred⟩ := u7Check_spec hu m hm u hu'
  obtain ⟨hC, hb, -⟩ := u7Elts_mem hu'
  rw [← psiD_pauliProd]
  exact (psiD_pcD_eq_iff hC (pauliProd_spec _).1 hb (pauliCheck_spec hp _ hlt).2).2 hred.symm

theorem betaCheck_spec (hβ : betaCheck = true) : ∀ m < 32768,
    Native.actD 15 commRows m < 32768 ∧ (Native.actD 15 commRows m ∈ u7Idx → m ∈ u7Idx) := by
  intro m hm
  have h := List.all_eq_true.1 hβ m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, fun hx => ?_⟩
  rcases h.2 with h' | h'
  · exact absurd (List.contains_iff_mem.2 hx) (by rw [h']; decide)
  · exact List.contains_iff_mem.1 h'

end CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
