module

import CFSG.Permutation.AlternatingAutomorphism.Conjugation
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixGenerators
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.QuasithinUnique.K1.Alt

open CFSG.Open Equiv

private abbrev AltGrp (n : ℕ) := alternatingGroup (Fin n)

private abbrev SW (n : ℕ) := List (Fin n × Fin n)

private def sp {n : ℕ} (l : SW n) : Perm (Fin n) := (l.map fun p => swap p.1 p.2).prod

private def appSw {n : ℕ} (l : SW n) (i : Fin n) : Fin n :=
  l.foldr (fun p j => if j = p.1 then p.2 else if j = p.2 then p.1 else j) i

private def eqT {n : ℕ} (l m : SW n) : Prop := ∀ i : Fin n, appSw l i = appSw m i

private instance {n : ℕ} (l m : SW n) : Decidable (eqT l m) := by unfold eqT; infer_instance

section Layer
variable {n : ℕ}

@[simp] private theorem sp_nil : sp ([] : SW n) = 1 := by simp [sp]

private theorem sp_cons (p : Fin n × Fin n) (l : SW n) : sp (p :: l) = swap p.1 p.2 * sp l := by
  simp [sp]

private theorem sp_append (l m : SW n) : sp (l ++ m) = sp l * sp m := by
  simp [sp, List.prod_append]

private theorem appSw_cons (p : Fin n × Fin n) (l : SW n) (i : Fin n) :
    appSw (p :: l) i = swap p.1 p.2 (appSw l i) := by
  rw [Equiv.swap_apply_def]
  rfl

private theorem sp_apply (l : SW n) (i : Fin n) : sp l i = appSw l i := by
  induction l with
  | nil => simp [appSw]
  | cons p l ih =>
    rw [sp_cons, Perm.mul_apply, ih, appSw_cons]

private theorem sp_singleton (p : Fin n × Fin n) : sp [p] = swap p.1 p.2 := by simp [sp_cons]

private theorem sp_reverse (l : SW n) : sp l.reverse = (sp l)⁻¹ := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.reverse_cons, sp_append, ih, sp_singleton, sp_cons, mul_inv_rev, Equiv.swap_inv]

private theorem sp_eq_of_eqT {l m : SW n} (h : eqT l m) : sp l = sp m := by
  ext i
  rw [sp_apply, sp_apply]
  exact congrArg Fin.val (h i)

private theorem sign_sp (l : SW n) (h : ∀ p ∈ l, p.1 ≠ p.2) : (sp l).sign = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [sp_cons, Perm.sign_mul, Perm.sign_swap (h p (by simp)),
      ih (fun q hq => h q (by simp [hq])), List.length_cons, pow_succ, mul_comm]

end Layer

section WordSub

variable {n : ℕ}

private def EvenSW (l : SW n) : Prop := (∀ p ∈ l, p.1 ≠ p.2) ∧ Even l.length

private instance (l : SW n) : Decidable (EvenSW l) := by unfold EvenSW; infer_instance

private theorem sp_mem_alt {l : SW n} (h : EvenSW l) : sp l ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, sign_sp l h.1]
  exact h.2.neg_one_pow

private def liftSW (l : SW n) (h : EvenSW l) : AltGrp n := ⟨sp l, sp_mem_alt h⟩

@[simp] private theorem coe_liftSW (l : SW n) (h : EvenSW l) : ((liftSW l h : AltGrp n) : Perm (Fin n)) = sp l :=
  rfl

private structure WordCert (E : List (SW n)) : Prop where
  even : ∀ l ∈ E, EvenSW l
  nil : [] ∈ E
  mul : ∀ l ∈ E, ∀ m ∈ E, ∃ c ∈ E, eqT (l ++ m) c
  inv : ∀ l ∈ E, ∃ c ∈ E, eqT l.reverse c

private def wordSub (E : List (SW n)) (h : WordCert E) : Subgroup (AltGrp n) where
  carrier := {x | ∃ l ∈ E, (x : Perm (Fin n)) = sp l}
  mul_mem' := by
    rintro x y ⟨l, hl, hxl⟩ ⟨m, hm, hym⟩
    obtain ⟨c, hc, hlm⟩ := h.mul l hl m hm
    exact ⟨c, hc, by rw [Subgroup.coe_mul, hxl, hym, ← sp_append, sp_eq_of_eqT hlm]⟩
  one_mem' := ⟨[], h.nil, by simp⟩
  inv_mem' := by
    rintro x ⟨l, hl, hxl⟩
    obtain ⟨c, hc, hlc⟩ := h.inv l hl
    exact ⟨c, hc, by rw [Subgroup.coe_inv, hxl, ← sp_reverse, sp_eq_of_eqT hlc]⟩

private theorem liftSW_mem_wordSub {E : List (SW n)} {h : WordCert E} {l : SW n} (hl : l ∈ E) :
    liftSW l (h.even l hl) ∈ wordSub E h := ⟨l, hl, rfl⟩

private theorem isPGroup_wordSub {E : List (SW n)} {h : WordCert E}
    (hpow : ∀ l ∈ E, eqT (l ++ l ++ l ++ l) []) : IsPGroup 2 (wordSub E h) := by
  rintro ⟨x, l, hl, hxl⟩
  refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
  have h4 : (x : Perm (Fin n)) ^ 4 = 1 := by
    rw [hxl]
    have : sp l ^ 4 = sp (l ++ l ++ l ++ l) := by
      simp [sp_append, pow_succ, mul_assoc]
    rw [this, sp_eq_of_eqT (hpow l hl)]
    simp
  simpa using h4

end WordSub

@[expose] def QLevelFalse (n : ℕ) (R : Subgroup (alternatingGroup (Fin n))) : Prop :=
  ∀ (P V : Subgroup (alternatingGroup (Fin n))) (β : MulAut (alternatingGroup (Fin n))),
    R ≤ P → β ≠ 1 → (∀ p ∈ P, β p = p) → V ≤ P → IsElemAbelian 2 V →
    (∀ v ∈ V, ∀ x : alternatingGroup (Fin n), x⁻¹ * v * x ∈ P → x⁻¹ * v * x ∈ V) →
    (∀ x : alternatingGroup (Fin n), (β x)⁻¹ * x ∈ P → (β x)⁻¹ * x ∈ V) → False

private def AltH1 (n : ℕ) (R : Subgroup (AltGrp n)) : Prop :=
  ∀ β : MulAut (AltGrp n), β ≠ 1 → (∀ p ∈ R, β p = p) →
    ∃ y x x' : AltGrp n, (β y)⁻¹ * y ∈ R ∧
      ((β y)⁻¹ * y * ((β y)⁻¹ * y) ≠ 1 ∨
        (x⁻¹ * ((β y)⁻¹ * y) * x ∈ R ∧ x'⁻¹ * ((β y)⁻¹ * y) * x' ∈ R ∧
          (x⁻¹ * ((β y)⁻¹ * y) * x) * (x'⁻¹ * ((β y)⁻¹ * y) * x') ≠
            (x'⁻¹ * ((β y)⁻¹ * y) * x') * (x⁻¹ * ((β y)⁻¹ * y) * x)))

private theorem qlevelFalse_of_altH1 {n : ℕ} {R : Subgroup (AltGrp n)} (h : AltH1 n R) :
    QLevelFalse n R := by
  intro P V β hRP hβ1 hβP hVP hVe hVcl hTC
  obtain ⟨y, x, x', hqR, hfin⟩ := h β hβ1 (fun p hp => hβP p (hRP hp))
  have hqV : (β y)⁻¹ * y ∈ V := hTC y (hRP hqR)
  rcases hfin with h2 | ⟨hxR, hx'R, hnc⟩
  · exact h2 (by simpa [pow_two] using hVe.2 _ hqV)
  · have ha := hVcl _ hqV x (hRP hxR)
    have hb := hVcl _ hqV x' (hRP hx'R)
    exact hnc (congrArg Subtype.val (hVe.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩))

section Conj

variable {n : ℕ}

private theorem eqT_of_sp_eq {l m : SW n} (h : sp l = sp m) : eqT l m := fun i => by
  rw [← sp_apply, ← sp_apply, h]

private def qw (σ y : SW n) : SW n := σ ++ y.reverse ++ σ.reverse ++ y

private theorem sp_qw (σ y : SW n) : sp (qw σ y) = sp σ * (sp y)⁻¹ * (sp σ)⁻¹ * sp y := by
  simp [qw, sp_append, sp_reverse, mul_assoc]

private def PairOk (E : List (SW n)) (ql x x' : SW n) : Prop :=
  EvenSW x ∧ EvenSW x' ∧
    (∃ c ∈ E, eqT (x.reverse ++ ql ++ x) c) ∧
    (∃ c ∈ E, eqT (x'.reverse ++ ql ++ x') c) ∧
    ¬ eqT ((x.reverse ++ ql ++ x) ++ (x'.reverse ++ ql ++ x'))
      ((x'.reverse ++ ql ++ x') ++ (x.reverse ++ ql ++ x))

private instance (E : List (SW n)) (ql x x' : SW n) : Decidable (PairOk E ql x x') := by
  unfold PairOk; infer_instance

private def WitOk (E : List (SW n)) (σ y x x' : SW n) : Prop :=
  EvenSW y ∧ (∃ c ∈ E, eqT (qw σ y) c) ∧
    (¬ eqT (qw σ y ++ qw σ y) [] ∨ PairOk E (qw σ y) x x')

private instance (E : List (SW n)) (σ y x x' : SW n) : Decidable (WitOk E σ y x x') := by
  unfold WitOk; infer_instance

private theorem coe_conj_liftSW {x ql : SW n} (hx : EvenSW x) {q : AltGrp n}
    (hq : (q : Perm (Fin n)) = sp ql) :
    (((liftSW x hx)⁻¹ * q * liftSW x hx : AltGrp n) : Perm (Fin n)) = sp (x.reverse ++ ql ++ x) := by
  simp [hq, sp_append, sp_reverse, mul_assoc]

private theorem altH1_conclusion {E : List (SW n)} {hE : WordCert E} {β : MulAut (AltGrp n)}
    {y : AltGrp n} {ql x x' : SW n}
    (hq : (((β y)⁻¹ * y : AltGrp n) : Perm (Fin n)) = sp ql) (hql : ∃ c ∈ E, eqT ql c)
    (hfin : ¬ eqT (ql ++ ql) [] ∨ PairOk E ql x x') :
    ∃ y x x' : AltGrp n, (β y)⁻¹ * y ∈ wordSub E hE ∧
      ((β y)⁻¹ * y * ((β y)⁻¹ * y) ≠ 1 ∨
        (x⁻¹ * ((β y)⁻¹ * y) * x ∈ wordSub E hE ∧ x'⁻¹ * ((β y)⁻¹ * y) * x' ∈ wordSub E hE ∧
          (x⁻¹ * ((β y)⁻¹ * y) * x) * (x'⁻¹ * ((β y)⁻¹ * y) * x') ≠
            (x'⁻¹ * ((β y)⁻¹ * y) * x') * (x⁻¹ * ((β y)⁻¹ * y) * x))) := by
  obtain ⟨c, hcE, hqc⟩ := hql
  have hmem : (β y)⁻¹ * y ∈ wordSub E hE := ⟨c, hcE, by rw [hq, sp_eq_of_eqT hqc]⟩
  rcases hfin with hnot | ⟨hx, hx', ⟨c1, hc1, e1⟩, ⟨c2, hc2, e2⟩, hnc⟩
  · refine ⟨y, 1, 1, hmem, Or.inl ?_⟩
    intro hone
    apply hnot
    apply eqT_of_sp_eq
    have h5 := congrArg (fun z : AltGrp n => (z : Perm (Fin n))) hone
    simp only [Subgroup.coe_mul, hq, OneMemClass.coe_one] at h5
    rw [sp_append, sp_nil]
    exact h5
  · refine ⟨y, liftSW x hx, liftSW x' hx', hmem, Or.inr ⟨?_, ?_, ?_⟩⟩
    · exact ⟨c1, hc1, by rw [coe_conj_liftSW hx hq, sp_eq_of_eqT e1]⟩
    · exact ⟨c2, hc2, by rw [coe_conj_liftSW hx' hq, sp_eq_of_eqT e2]⟩
    · intro heq
      apply hnc
      apply eqT_of_sp_eq
      have hA := coe_conj_liftSW hx hq
      have hB := coe_conj_liftSW hx' hq
      set A : AltGrp n := (liftSW x hx)⁻¹ * ((β y)⁻¹ * y) * liftSW x hx with hAdef
      set B : AltGrp n := (liftSW x' hx')⁻¹ * ((β y)⁻¹ * y) * liftSW x' hx' with hBdef
      have h5 := congrArg (fun z : AltGrp n => (z : Perm (Fin n))) heq
      simp only [Subgroup.coe_mul] at h5
      rw [hA, hB] at h5
      simpa [sp_append, mul_assoc] using h5

private theorem altH1_of_conj (hn : n = 5 ∨ 7 ≤ n) {E : List (SW n)} (hE : WordCert E)
    (C : List (SW n)) (W : List (SW n × SW n × SW n × SW n))
    (hcls : ∀ σ : Perm (Fin n), (∀ g ∈ E, σ * sp g = sp g * σ) → ∃ σ' ∈ C, σ = sp σ')
    (hwit : ∀ σ' ∈ C, ¬ eqT σ' [] → ∃ t ∈ W, t.1 = σ' ∧ WitOk E σ' t.2.1 t.2.2.1 t.2.2.2) :
    AltH1 n (wordSub E hE) := by
  intro β hβ1 hβR
  obtain ⟨σ, hσ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le hn β
  have hcomm : ∀ g ∈ E, σ * sp g = sp g * σ := by
    intro g hg
    have h1 := hβR (liftSW g (hE.even g hg)) (liftSW_mem_wordSub hg)
    have h2 := hσ (liftSW g (hE.even g hg))
    rw [h1] at h2
    simp only [coe_liftSW] at h2
    calc σ * sp g = (σ * sp g * σ⁻¹) * σ := by group
      _ = sp g * σ := by rw [← h2]
  obtain ⟨σ', hσ'C, rfl⟩ := hcls σ hcomm
  have hσ1 : ¬ eqT σ' [] := by
    intro h
    apply hβ1
    refine MulEquiv.ext fun g => ?_
    show β g = g
    apply Subtype.ext
    have h0 : sp σ' = 1 := by rw [sp_eq_of_eqT h]; simp
    have h3 := hσ g
    rw [h0] at h3
    simpa using h3
  obtain ⟨t, htW, hts, hok⟩ := hwit σ' hσ'C hσ1
  obtain ⟨hy, hqc, hfin⟩ := hok
  have hq : (((β (liftSW t.2.1 hy))⁻¹ * liftSW t.2.1 hy : AltGrp n) : Perm (Fin n)) =
      sp (qw σ' t.2.1) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, coe_liftSW, sp_qw]
    group
  exact altH1_conclusion hq hqc hfin

end Conj

section Seven

private def a7 : SW 7 := [(0, 1), (1, 2), (2, 3), (4, 5)]
private def b7 : SW 7 := [(0, 2), (4, 5)]
private def E7 : List (SW 7) :=
  [[],
   a7,
   b7,
   a7 ++ a7,
   a7 ++ b7,
   b7 ++ a7,
   a7 ++ a7 ++ a7,
   b7 ++ a7 ++ a7]
private def tbl7 : Fin 7 → SW 7 :=
  ![b7 ++ a7 ++ a7,
    a7,
    a7 ++ a7,
    a7 ++ b7,
    a7 ++ b7,
    b7 ++ a7 ++ a7,
    a7 ++ b7]
private def rep7 : Fin 7 → Fin 7 := ![0, 0, 0, 0, 4, 4, 6]
private def C7 : List (SW 7) :=
  [[],
   [(4, 5)],
   [(0, 2), (1, 3)],
   [(0, 2), (1, 3), (4, 5)]]
private def W7 : List (SW 7 × SW 7 × SW 7 × SW 7) :=
  [([(4, 5)], [(1, 4), (4, 2), (3, 5), (5, 6)], [], [(0, 1), (1, 3), (3, 5), (5, 6), (6, 2), (2, 4)]),
   ([(0, 2), (1, 3)], [(2, 3), (5, 6)], [], [(1, 4), (4, 3), (3, 5), (5, 2)]),
   ([(0, 2), (1, 3), (4, 5)], [(2, 3), (4, 5)], [], [(1, 4), (4, 3), (3, 5), (5, 2)])]

set_option maxRecDepth 100000 in
private theorem E7_cert : WordCert E7 where
  even := by decide +kernel
  nil := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel

set_option maxRecDepth 100000 in
private theorem E7_pow : ∀ l ∈ E7, eqT (l ++ l ++ l ++ l) [] := by decide +kernel

set_option maxRecDepth 100000 in
private theorem tbl7_spec : ∀ j, tbl7 j ∈ E7 ∧ appSw (tbl7 j) (rep7 j) = j := by decide +kernel

private def F7 (a b c : Fin 7) (j : Fin 7) : Fin 7 :=
  appSw (tbl7 j) (if rep7 j = 0 then a else if rep7 j = 4 then b else c)

set_option maxRecDepth 100000 in
private theorem cls7_aux : ∀ a b c : Fin 7,
    (∀ g ∈ E7, ∀ j, F7 a b c (appSw g j) = appSw g (F7 a b c j)) →
    (∀ i j, F7 a b c i = F7 a b c j → i = j) →
    ∃ σ' ∈ C7, ∀ j, F7 a b c j = appSw σ' j := by decide +kernel

private theorem cls7 : ∀ σ : Perm (Fin 7), (∀ g ∈ E7, σ * sp g = sp g * σ) → ∃ σ' ∈ C7, σ = sp σ' := by
  intro σ hσ
  have key : ∀ j, σ j = appSw (tbl7 j) (σ (rep7 j)) := by
    intro j
    obtain ⟨hm, hr⟩ := tbl7_spec j
    have h := congrArg (fun f : Perm (Fin 7) => f (rep7 j)) (hσ _ hm)
    simp only [Perm.mul_apply, sp_apply, hr] at h
    exact h
  have hF : ∀ j, σ j = F7 (σ 0) (σ 4) (σ 6) j := by
    intro j
    rw [key j]
    have h3 : rep7 j = 0 ∨ rep7 j = 4 ∨ rep7 j = 6 := by revert j; decide
    unfold F7
    rcases h3 with h | h | h <;> simp [h]
  have hcomm : ∀ g ∈ E7, ∀ j, F7 (σ 0) (σ 4) (σ 6) (appSw g j) =
      appSw g (F7 (σ 0) (σ 4) (σ 6) j) := by
    intro g hg j
    rw [← hF, ← hF]
    have h := congrArg (fun f : Perm (Fin 7) => f j) (hσ g hg)
    simpa [sp_apply] using h
  have hinj : ∀ i j, F7 (σ 0) (σ 4) (σ 6) i = F7 (σ 0) (σ 4) (σ 6) j → i = j := by
    intro i j hij
    rw [← hF, ← hF] at hij
    exact σ.injective hij
  obtain ⟨σ', hC, h⟩ := cls7_aux (σ 0) (σ 4) (σ 6) hcomm hinj
  exact ⟨σ', hC, Equiv.ext fun j => (hF j).trans ((h j).trans (sp_apply σ' j).symm)⟩

set_option maxRecDepth 100000 in
private theorem wit7 : ∀ σ' ∈ C7, ¬ eqT σ' [] → ∃ t ∈ W7, t.1 = σ' ∧
    WitOk E7 σ' t.2.1 t.2.2.1 t.2.2.2 := by decide +kernel

private theorem altH1_seven : AltH1 7 (wordSub E7 E7_cert) :=
  altH1_of_conj (Or.inr (by norm_num)) E7_cert C7 W7 cls7 wit7

end Seven

section Eight

private def a8 : SW 8 := [(0, 1), (1, 2), (2, 3), (4, 5), (5, 6), (6, 7)]
private def b8 : SW 8 := [(0, 7), (1, 6), (2, 5), (3, 4)]
private def E8 : List (SW 8) :=
  [[],
   a8,
   b8,
   a8 ++ a8,
   a8 ++ b8,
   b8 ++ a8,
   a8 ++ a8 ++ a8,
   b8 ++ a8 ++ a8]
private def tbl8 : Fin 8 → SW 8 :=
  ![[],
    a8,
    a8 ++ a8,
    a8 ++ a8 ++ a8,
    a8 ++ b8,
    b8 ++ a8 ++ a8,
    b8 ++ a8,
    b8]
private def rep8 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 0]
private def C8 : List (SW 8) :=
  [[],
   [(0, 1), (1, 2), (2, 3), (4, 7), (7, 6), (6, 5)],
   [(0, 2), (1, 3), (4, 6), (5, 7)],
   [(0, 3), (3, 2), (2, 1), (4, 5), (5, 6), (6, 7)],
   [(0, 4), (1, 5), (2, 6), (3, 7)],
   [(0, 5), (1, 6), (2, 7), (3, 4)],
   [(0, 6), (1, 7), (2, 4), (3, 5)],
   [(0, 7), (1, 4), (2, 5), (3, 6)]]
private def W8 : List (SW 8 × SW 8 × SW 8 × SW 8) :=
  [([(0, 1), (1, 2), (2, 3), (4, 7), (7, 6), (6, 5)], [(1, 3), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [(2, 4), (3, 7)]),
   ([(0, 2), (1, 3), (4, 6), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [], [(3, 4), (4, 5), (5, 6), (6, 7)]),
   ([(0, 3), (3, 2), (2, 1), (4, 5), (5, 6), (6, 7)], [(1, 3), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [(2, 4), (3, 7)]),
   ([(0, 4), (1, 5), (2, 6), (3, 7)], [(4, 6), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [(2, 4), (3, 7)]),
   ([(0, 5), (1, 6), (2, 7), (3, 4)], [(4, 6), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [(2, 4), (3, 7)]),
   ([(0, 6), (1, 7), (2, 4), (3, 5)], [(4, 6), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [(2, 4), (3, 7)]),
   ([(0, 7), (1, 4), (2, 5), (3, 6)], [(4, 6), (5, 7)], [(2, 4), (4, 3), (3, 5), (6, 7)], [(2, 4), (3, 7)])]

set_option maxRecDepth 100000 in
private theorem E8_cert : WordCert E8 where
  even := by decide +kernel
  nil := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel

set_option maxRecDepth 100000 in
private theorem E8_pow : ∀ l ∈ E8, eqT (l ++ l ++ l ++ l) [] := by decide +kernel

set_option maxRecDepth 100000 in
private theorem tbl8_spec : ∀ j, tbl8 j ∈ E8 ∧ appSw (tbl8 j) (rep8 j) = j := by decide +kernel

set_option maxRecDepth 100000 in
private theorem cls8_aux : ∀ i : Fin 8, ∃ σ' ∈ C8, ∀ j, appSw (tbl8 j) i = appSw σ' j := by decide +kernel

private theorem rep8_zero : ∀ j, rep8 j = 0 := by decide

private theorem cls8 : ∀ σ : Perm (Fin 8), (∀ g ∈ E8, σ * sp g = sp g * σ) → ∃ σ' ∈ C8, σ = sp σ' := by
  intro σ hσ
  have key : ∀ j, σ j = appSw (tbl8 j) (σ 0) := by
    intro j
    obtain ⟨hm, hr⟩ := tbl8_spec j
    have h := congrArg (fun f : Perm (Fin 8) => f (rep8 j)) (hσ _ hm)
    simp only [Perm.mul_apply, sp_apply, hr] at h
    rw [rep8_zero j] at h
    exact h
  obtain ⟨σ', hC, h⟩ := cls8_aux (σ 0)
  exact ⟨σ', hC, Equiv.ext fun j => (key j).trans ((h j).trans (sp_apply σ' j).symm)⟩

set_option maxRecDepth 100000 in
private theorem wit8 : ∀ σ' ∈ C8, ¬ eqT σ' [] → ∃ t ∈ W8, t.1 = σ' ∧
    WitOk E8 σ' t.2.1 t.2.2.1 t.2.2.2 := by decide +kernel

private theorem altH1_eight : AltH1 8 (wordSub E8 E8_cert) :=
  altH1_of_conj (Or.inr (by norm_num)) E8_cert C8 W8 cls8 wit8

end Eight

section Six

open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

private def a6 : SW 6 := [(0, 1), (1, 2), (2, 3), (4, 5)]
private def b6 : SW 6 := [(0, 2), (4, 5)]
private def E6 : List (SW 6) :=
  [[],
   a6,
   b6,
   a6 ++ a6,
   a6 ++ b6,
   b6 ++ a6,
   a6 ++ a6 ++ a6,
   b6 ++ a6 ++ a6]
private def zl6 : SW 6 := [(0, 2), (1, 3)]
private def L16 : List (SW 6) :=
  [[],
   [(4, 5)],
   [(1, 3)],
   [(1, 3), (4, 5)],
   [(0, 1), (2, 3)],
   [(0, 1), (2, 3), (4, 5)],
   [(0, 1), (1, 2), (2, 3)],
   [(0, 1), (1, 2), (2, 3), (4, 5)],
   [(0, 2)],
   [(0, 2), (4, 5)],
   [(0, 2), (1, 3)],
   [(0, 2), (1, 3), (4, 5)],
   [(0, 3), (3, 2), (2, 1)],
   [(0, 3), (3, 2), (2, 1), (4, 5)],
   [(0, 3), (1, 2)],
   [(0, 3), (1, 2), (4, 5)]]
private def H2tab6 : List (SW 6 × SW 6 × SW 6) :=
  [(b6, [], [(1, 2), (2, 4), (4, 3), (3, 5)]),
   (a6 ++ a6, [(2, 3), (4, 5)], [(1, 4), (3, 5)]),
   (a6 ++ b6, [], [(1, 4), (4, 2), (2, 3), (3, 5)]),
   (b6 ++ a6, [], [(1, 4), (4, 3), (3, 5), (5, 2)]),
   (b6 ++ a6 ++ a6, [], [(0, 1), (1, 3), (3, 5), (2, 4)])]
private def u0 : SW 6 := [(0, 1), (1, 2)]
private def ug : SW 6 := [(1, 2), (2, 3), (3, 4), (4, 5)]
private def u1 : SW 6 := [(2, 3), (4, 5)]
private def u2 : SW 6 := [(0, 1), (1, 4), (2, 3), (3, 5)]
private def u3 : SW 6 := [(1, 2), (4, 5)]
private def u4 : SW 6 := [(0, 5), (2, 4)]

set_option maxRecDepth 100000 in
private theorem E6_cert : WordCert E6 where
  even := by decide +kernel
  nil := by decide +kernel
  mul := by decide +kernel
  inv := by decide +kernel

set_option maxRecDepth 100000 in
private theorem E6_pow : ∀ l ∈ E6, eqT (l ++ l ++ l ++ l) [] := by decide +kernel

set_option maxRecDepth 100000 in
private theorem zl6_mem : ∃ c ∈ E6, eqT zl6 c := by decide +kernel

private theorem zl6_even : EvenSW zl6 := by decide

private def z6 : AltGrp 6 := liftSW zl6 zl6_even

private def Fz (a b e f : Fin 6) (j : Fin 6) : Fin 6 :=
  if j = 0 then a else if j = 1 then b else if j = 2 then appSw zl6 a
  else if j = 3 then appSw zl6 b else if j = 4 then e else f

set_option maxRecDepth 100000 in
private theorem cls6_aux : ∀ a b e f : Fin 6,
    (∀ j, Fz a b e f (appSw zl6 j) = appSw zl6 (Fz a b e f j)) →
    (∀ i j, Fz a b e f i = Fz a b e f j → i = j) →
    ∃ l ∈ L16, ∀ j, Fz a b e f j = appSw l j := by decide +kernel

set_option maxRecDepth 100000 in
private theorem L16_spec : ∀ l ∈ L16, (∀ p ∈ l, p.1 ≠ p.2) ∧ (Even l.length → ∃ c ∈ E6, eqT l c) := by
  decide +kernel

private theorem cent6 : ∀ c : Perm (Fin 6), c.sign = 1 → c * sp zl6 = sp zl6 * c →
    ∃ l ∈ E6, c = sp l := by
  intro c hs hc
  have hz : ∀ j, c (appSw zl6 j) = appSw zl6 (c j) := by
    intro j
    have h := congrArg (fun f : Perm (Fin 6) => f j) hc
    simpa [sp_apply] using h
  have hF : ∀ j, c j = Fz (c 0) (c 1) (c 4) (c 5) j := by
    intro j
    have h0 : appSw zl6 0 = 2 := by decide
    have h1 : appSw zl6 1 = 3 := by decide
    fin_cases j
    · simp [Fz]
    · simp [Fz]
    · have := hz 0
      rw [h0] at this
      simp [Fz, this]
    · have := hz 1
      rw [h1] at this
      simp [Fz, this]
    · simp [Fz]
    · simp [Fz]
  have hcomm : ∀ j, Fz (c 0) (c 1) (c 4) (c 5) (appSw zl6 j) =
      appSw zl6 (Fz (c 0) (c 1) (c 4) (c 5) j) := by
    intro j
    rw [← hF, ← hF]
    exact hz j
  have hinj : ∀ i j, Fz (c 0) (c 1) (c 4) (c 5) i = Fz (c 0) (c 1) (c 4) (c 5) j → i = j := by
    intro i j hij
    rw [← hF, ← hF] at hij
    exact c.injective hij
  obtain ⟨l, hl, h⟩ := cls6_aux (c 0) (c 1) (c 4) (c 5) hcomm hinj
  have hcl : c = sp l := Equiv.ext fun j => (hF j).trans ((h j).trans (sp_apply l j).symm)
  obtain ⟨hd, hev⟩ := L16_spec l hl
  have hsign : (-1 : ℤˣ) ^ l.length = 1 := by
    rw [← sign_sp l hd, ← hcl]; exact hs
  have heven : Even l.length := (neg_one_pow_eq_one_iff_even (by decide)).mp hsign
  obtain ⟨c', hc', hlc⟩ := hev heven
  exact ⟨c', hc', by rw [hcl, sp_eq_of_eqT hlc]⟩

private theorem z6_mem : z6 ∈ wordSub E6 E6_cert := by
  obtain ⟨cz, hczE, hcz⟩ := zl6_mem
  exact ⟨cz, hczE, by simp [z6, sp_eq_of_eqT hcz]⟩

private theorem Y_mem (u : SW 6) (hu : EvenSW u) (h : ∃ c ∈ E6, eqT (u ++ zl6 ++ u.reverse) c) :
    liftSW u hu * z6 * (liftSW u hu)⁻¹ ∈ wordSub E6 E6_cert := by
  obtain ⟨c, hc, hcu⟩ := h
  refine ⟨c, hc, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_liftSW, z6]
  rw [← sp_reverse, ← sp_append, ← sp_append, sp_eq_of_eqT hcu]

set_option maxRecDepth 100000 in
private theorem u_ok : (EvenSW u1 ∧ ∃ c ∈ E6, eqT (u1 ++ zl6 ++ u1.reverse) c) ∧
    (EvenSW u2 ∧ ∃ c ∈ E6, eqT (u2 ++ zl6 ++ u2.reverse) c) ∧
    (EvenSW u3 ∧ ∃ c ∈ E6, eqT (u3 ++ zl6 ++ u3.reverse) c) ∧
    (EvenSW u4 ∧ ∃ c ∈ E6, eqT (u4 ++ zl6 ++ u4.reverse) c) ∧
    (EvenSW u0 ∧ ∃ c ∈ E6, eqT (u0 ++ zl6 ++ u0.reverse) c) ∧
    eqT ug (u1 ++ u2 ++ u3 ++ u4) := by decide +kernel

private theorem exists_y6 (β : MulAut (AltGrp 6)) (hβ1 : β ≠ 1)
    (hβR : ∀ p ∈ wordSub E6 E6_cert, β p = p) :
    ∃ y : AltGrp 6, (β y)⁻¹ * y ∈ wordSub E6 E6_cert ∧ (β y)⁻¹ * y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hβz : β z6 = z6 := hβR z6 z6_mem
  have hY : ∀ y : AltGrp 6, y * z6 * y⁻¹ ∈ wordSub E6 E6_cert → β y = y := by
    intro y hy
    have h1 : β (y * z6 * y⁻¹) = y * z6 * y⁻¹ := hβR _ hy
    rw [map_mul, map_mul, map_inv, hβz] at h1
    have hc : (β y)⁻¹ * y * z6 = z6 * ((β y)⁻¹ * y) := by
      calc (β y)⁻¹ * y * z6 = (β y)⁻¹ * (y * z6 * y⁻¹) * y := by group
        _ = (β y)⁻¹ * (β y * z6 * (β y)⁻¹) * y := by rw [h1]
        _ = z6 * ((β y)⁻¹ * y) := by group
    have hmem : (β y)⁻¹ * y ∈ wordSub E6 E6_cert := by
      refine cent6 (((β y)⁻¹ * y : AltGrp 6) : Perm (Fin 6))
        (Perm.mem_alternatingGroup.mp ((β y)⁻¹ * y).2) ?_
      have h2 := congrArg (fun w : AltGrp 6 => (w : Perm (Fin 6))) hc
      simpa [Subgroup.coe_mul, z6] using h2
    exact inv_mul_eq_one.mp (hcon y hmem)
  obtain ⟨⟨hu1, hu1'⟩, ⟨hu2, hu2'⟩, ⟨hu3, hu3'⟩, ⟨hu4, hu4'⟩, ⟨hu0, hu0'⟩, hug⟩ := u_ok
  let K : Subgroup (AltGrp 6) :=
    { carrier := {g | β g = g}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        rw [map_inv, ha] }
  have hx : x = liftSW u0 hu0 := by
    apply Subtype.ext
    simp [x, xPermutation, u0, sp_cons]
  have hy : y = liftSW u1 hu1 * liftSW u2 hu2 * liftSW u3 hu3 * liftSW u4 hu4 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_liftSW]
    rw [← sp_append, ← sp_append, ← sp_append, ← sp_eq_of_eqT hug]
    simp [y, yPermutation, ug, sp_cons, mul_assoc]
  have hKx : x ∈ K := by
    rw [hx]; exact hY _ (Y_mem u0 hu0 hu0')
  have hKy : y ∈ K := by
    rw [hy]
    have e1 : β (liftSW u1 hu1) = liftSW u1 hu1 := hY _ (Y_mem u1 hu1 hu1')
    have e2 : β (liftSW u2 hu2) = liftSW u2 hu2 := hY _ (Y_mem u2 hu2 hu2')
    have e3 : β (liftSW u3 hu3) = liftSW u3 hu3 := hY _ (Y_mem u3 hu3 hu3')
    have e4 : β (liftSW u4 hu4) = liftSW u4 hu4 := hY _ (Y_mem u4 hu4 hu4')
    show β _ = _
    rw [map_mul, map_mul, map_mul, e1, e2, e3, e4]
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← generating_pair]
    refine (Subgroup.closure_le K).mpr ?_
    rintro g (rfl | rfl)
    · exact hKx
    · exact hKy
  apply hβ1
  refine MulEquiv.ext fun g => ?_
  have hg : g ∈ K := hKtop ▸ Subgroup.mem_top g
  exact hg

set_option maxRecDepth 100000 in
private theorem h2_6 : ∀ l ∈ E6, ¬ eqT l [] →
    ¬ eqT (l ++ l) [] ∨ ∃ t ∈ H2tab6, t.1 = l ∧ PairOk E6 l t.2.1 t.2.2 := by
  decide +kernel

private theorem altH1_six : AltH1 6 (wordSub E6 E6_cert) := by
  intro β hβ1 hβR
  obtain ⟨y, hyR, hy1⟩ := exists_y6 β hβ1 hβR
  obtain ⟨l, hl, hql⟩ := hyR
  have hl1 : ¬ eqT l [] := by
    intro h
    apply hy1
    apply Subtype.ext
    rw [hql, sp_eq_of_eqT h]
    simp
  rcases h2_6 l hl hl1 with h | ⟨t, ht, hts, hpair⟩
  · exact altH1_conclusion (x := []) (x' := []) hql ⟨l, hl, fun _ => rfl⟩ (Or.inl h)
  · exact altH1_conclusion hql ⟨l, hl, fun _ => rfl⟩ (Or.inr hpair)

end Six

def R6 : Subgroup (alternatingGroup (Fin 6)) := wordSub E6 E6_cert

def R7 : Subgroup (alternatingGroup (Fin 7)) := wordSub E7 E7_cert

def R8 : Subgroup (alternatingGroup (Fin 8)) := wordSub E8 E8_cert

theorem R6_isPGroup : IsPGroup 2 R6 := isPGroup_wordSub E6_pow

theorem R7_isPGroup : IsPGroup 2 R7 := isPGroup_wordSub E7_pow

theorem R8_isPGroup : IsPGroup 2 R8 := isPGroup_wordSub E8_pow

theorem qlevelFalse_six : QLevelFalse 6 R6 := qlevelFalse_of_altH1 altH1_six

theorem qlevelFalse_seven : QLevelFalse 7 R7 := qlevelFalse_of_altH1 altH1_seven

theorem qlevelFalse_eight : QLevelFalse 8 R8 := qlevelFalse_of_altH1 altH1_eight

end CFSG.QuasithinUnique.K1.Alt
