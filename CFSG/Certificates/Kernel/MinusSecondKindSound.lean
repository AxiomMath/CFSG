module

public import Certificates.Data.Kernel.MinusSecondKind
public import CFSG.Certificates.Kernel.MinusQuandleSound
public import CFSG.OddTranspositions.PartThree.EightSix.OFourMinusCheck

public section

namespace CFSG.KC.MinusSecondKind

open CFSG.OddTranspositions.PartThree CFSG.KD.MinusQuandle CFSG.KD.MinusSecondKind
open CFSG.KC.MinusQuandle CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[simp] theorem bOr_eq (x y : Bool) : bOr x y = (x || y) := by cases x <;> rfl

@[simp] theorem bAnd_eq (x y : Bool) : bAnd x y = (x && y) := by cases x <;> rfl

@[simp] theorem bNot_eq (x : Bool) : bNot x = !x := by cases x <;> rfl

theorem ln_eq (R : ℕ → ℕ) (a x : ℕ) : ln (R a) x = tq R a x := rfl

variable {R : ℕ → ℕ}

theorem inv_spec (h : invOK R = true) {a x : ℕ} (ha : a < 65) (hx : x < 65) :
    ln (R a) (ln (R a) x) = x := by
  have h1 := allF_spec h ha
  simp only [force_eq] at h1
  exact Nat.eq_of_beq_eq_true (allF_spec h1 hx)

theorem quandle_spec (h : quandleOK R = true) {a b x : ℕ} (ha : a < 65) (hb : b < 65)
    (hx : x < 65) : ln (R a) (ln (R b) (ln (R a) x)) = ln (R (ln (R a) b)) x := by
  have h1 := allF_spec h ha
  simp only [force_eq] at h1
  have h2 := allF_spec h1 hb
  simp only [quandleRow, force_eq] at h2
  exact Nat.eq_of_beq_eq_true (allF_spec h2 hx)

theorem base_spec (h : baseOK R = true) {a b : ℕ} (ha : a < 65) (hb : b < 65)
    (hk : keyOf (R a) = keyOf (R b)) : a = b := by
  have h1 := allF_spec h ha
  simp only [force_eq] at h1
  have h2 := allF_spec h1 hb
  simp only [bOr_eq, bNot_eq, Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact Nat.eq_of_beq_eq_true h2
  · rw [hk, Nat.beq_refl] at h2
    exact Bool.noConfusion h2

theorem sk_spec (h : skOK R = true) {i k j : ℕ} (hi : i < 65) (hk : k < 65) (hj : j < 65)
    (hik : i ≠ k) (hc : ln (R i) k = k) (hij : ln (R i) j ≠ j) (hkj : ln (R k) j ≠ j)
    (h4 : ln (R (ln (R i) (ln (R k) j))) j = j) (h2 : ln (R i) (ln (R k) j) ≠ j) :
    ln (R i) j = ln (R j) i ∧ ln (R k) j = ln (R j) k := by
  have h1 := allF_spec h hi
  simp only [force_eq] at h1
  have h3 := allF_spec h1 hk
  simp only [force_eq, bOr_eq, bNot_eq, Bool.or_eq_true, Bool.not_eq_true'] at h3
  rcases h3 with h3 | h3 | h3
  · exact absurd (Nat.eq_of_beq_eq_true h3) hik
  · rw [hc, Nat.beq_refl] at h3
    exact Bool.noConfusion h3
  have h5 := allF_spec h3 hj
  simp only [skT, force_eq, bOr_eq, bAnd_eq, bNot_eq, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Nat.beq_eq] at h5
  rcases h5 with h5 | h5 | h5 | h5 | h5
  · exact absurd h5 hij
  · exact absurd h5 hkj
  · rw [h4, Nat.beq_refl] at h5
    exact Bool.noConfusion h5
  · exact absurd h5 h2
  · exact h5

section Perm

theorem ln_lt (hR : rowsOK R = true) {a x : ℕ} (ha : a < 65) (hx : x < 65) : ln (R a) x < 65 :=
  (tq_spec hR ha hx).2

@[expose] def fF (hR : rowsOK R = true) (a b : Fin 65) : Fin 65 := ⟨ln (R a) b, ln_lt hR a.2 b.2⟩

@[expose] def sig (hR : rowsOK R = true) (hI : invOK R = true) (a : Fin 65) : Equiv.Perm (Fin 65) :=
  Function.Involutive.toPerm (fF hR a) fun x => Fin.ext (inv_spec hI a.2 x.2)

theorem sig_val (hR : rowsOK R = true) (hI : invOK R = true) (a x : Fin 65) :
    (sig hR hI a x : ℕ) = ln (R a) x := rfl

theorem rep_sig (hR : rowsOK R = true) (hI : invOK R = true) (a : Fin 65) :
    Rep 65 minusTable[(a : ℕ)]! (sig hR hI a) := fun x => by
  rw [sig_val]
  exact (tq_spec hR a.2 x.2).1

theorem sig_mul_self (hR : rowsOK R = true) (hI : invOK R = true) (a : Fin 65) :
    sig hR hI a * sig hR hI a = 1 := by
  ext x
  rw [Equiv.Perm.mul_apply, sig_val, sig_val, inv_spec hI a.2 x.2]
  rfl

theorem sig_conj (hR : rowsOK R = true) (hI : invOK R = true) (hQ : quandleOK R = true)
    (a b : Fin 65) : sig hR hI a * sig hR hI b * sig hR hI a = sig hR hI (fF hR a b) := by
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sig_val, sig_val, sig_val, sig_val]
  exact quandle_spec hQ a.2 b.2 x.2

theorem sig_inj (hR : rowsOK R = true) (hI : invOK R = true) (hB : baseOK R = true)
    {a b : Fin 65} (h : sig hR hI a = sig hR hI b) : a = b := by
  have e : ∀ x : Fin 65, ln (R a) x = ln (R b) x := fun x => by
    rw [← sig_val hR hI, ← sig_val hR hI, h]
  have e0 := e ⟨0, by decide⟩
  have e1 := e ⟨1, by decide⟩
  have e29 := e ⟨29, by decide⟩
  refine Fin.ext (base_spec hB a.2 b.2 ?_)
  unfold keyOf
  rw [e0, e1, e29]

end Perm

section Group

variable {G : Type*} [Group G]

theorem sq_triple {x y z w : G} (hxy : x * y = y * x) (hw : x * (y * z * y) * x = w) :
    x * y * z * (x * y * z) = w * z := by
  rw [← hw]
  calc x * y * z * (x * y * z) = x * y * z * (x * y) * z := by simp only [mul_assoc]
    _ = x * y * z * (y * x) * z := by rw [hxy]
    _ = x * (y * z * y) * x * z := by simp only [mul_assoc]

theorem sq_pair {x z w : G} (hw : x * z * x = w) : x * z * (x * z) = w * z := by
  rw [← hw]
  simp only [mul_assoc]

theorem cube_pair {x z u v : G} (hu : x * z * x = u) (hv : z * x * z = v) :
    x * z * (x * z) * (x * z) = u * v := by
  rw [← hu, ← hv]
  simp only [mul_assoc]

theorem comm_of {x y : G} (hx : x * x = 1) (h : x * y * x = y) : x * y = y * x := by
  calc x * y = x * y * x * x := by rw [mul_assoc (x * y), hx, mul_one]
    _ = y * x := by rw [h]

theorem eq_of_mul_eq_one {u v : G} (hv : v * v = 1) (h : u * v = 1) : u = v := by
  calc u = u * v * v := by rw [mul_assoc, hv, mul_one]
    _ = v := by rw [h, one_mul]

end Group

theorem secondKind_of (hR : rowsOK R = true) (hI : invOK R = true) (hQ : quandleOK R = true)
    (hB : baseOK R = true) (hS : skOK R = true) : minusSecondKindCheck () = true := by
  unfold minusSecondKindCheck
  dsimp only
  rw [allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro j hj
  obtain ⟨a, rfl⟩ : ∃ a : Fin 65, (a : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨c, rfl⟩ : ∃ c : Fin 65, (c : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : Fin 65, (b : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
  have ent : ∀ p q : Fin 65, (minusTable[(p : ℕ)]!)[(q : ℕ)]! = ln (R p) q := fun p q =>
    (tq_spec hR p.2 q.2).1
  have repP := rep_compA (rep_compA (rep_sig hR hI a) (rep_sig hR hI c)) (rep_sig hR hI b)
  have rep2 := rep_compA repP repP
  have rep4 := rep_compA rep2 rep2
  have repA := rep_compA (rep_sig hR hI a) (rep_sig hR hI b)
  have repA3 := rep_compA (rep_compA repA repA) repA
  have repB := rep_compA (rep_sig hR hI c) (rep_sig hR hI b)
  have repB3 := rep_compA (rep_compA repB repB) repB
  rw [ent, ent, ent]
  by_cases hac : (a : ℕ) = c
  · simp [hac]
  rw [if_neg (by simpa using hac)]
  by_cases hcom : ln (R a) c = c
  swap
  · rw [if_neg (by simpa using hcom)]
  rw [if_pos (by simpa using hcom)]
  by_cases hab : ln (R a) b = b
  · simp [hab]
  rw [if_neg (by simpa using hab)]
  by_cases hcb : ln (R c) b = b
  · simp [hcb]
  rw [if_neg (by simpa using hcb)]
  split_ifs with hcond
  swap
  · rfl
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
  obtain ⟨h4arr, h2arr⟩ := hcond
  unfold minusTripleFourth at h4arr
  unfold minusTripleSq at h4arr h2arr
  unfold minusTripleArr at h4arr h2arr
  unfold minusPairCube minusPairArr
  dsimp only at h4arr h2arr ⊢
  have e4 := (eqA_iff rep4 rep_idA).1 h4arr
  have e2 : ¬ (sig hR hI a * sig hR hI c * sig hR hI b *
      (sig hR hI a * sig hR hI c * sig hR hI b) = 1) := fun h => by
    rw [(eqA_iff rep2 rep_idA).2 h] at h2arr
    exact Bool.noConfusion h2arr
  have inv : ∀ p, sig hR hI p * sig hR hI p = 1 := sig_mul_self hR hI
  have conj : ∀ p q, sig hR hI p * sig hR hI q * sig hR hI p = sig hR hI (fF hR p q) :=
    sig_conj hR hI hQ
  have hac' : sig hR hI a * sig hR hI c = sig hR hI c * sig hR hI a := by
    refine comm_of (inv a) ?_
    rw [conj]
    congr 1
    exact Fin.ext hcom
  have hP2 : sig hR hI a * sig hR hI c * sig hR hI b * (sig hR hI a * sig hR hI c * sig hR hI b) =
      sig hR hI (fF hR a (fF hR c b)) * sig hR hI b :=
    sq_triple hac' (by rw [conj c b, conj a])
  rw [hP2] at e4 e2
  rw [sq_pair (conj _ b)] at e4
  have h4 := congrArg Fin.val (sig_inj hR hI hB (eq_of_mul_eq_one (inv b) e4))
  have h2 : ln (R a) (ln (R c) b) ≠ b := fun h => e2 (by
    rw [Fin.ext (a := fF hR a (fF hR c b)) (b := b) h]
    exact inv b)
  obtain ⟨hx, hy⟩ := sk_spec hS a.2 c.2 b.2 hac hcom hab hcb h4 h2
  rw [Bool.and_eq_true]
  constructor
  · refine (eqA_iff repA3 rep_idA).2 ?_
    rw [cube_pair (conj a b) (conj b a), Fin.ext (a := fF hR a b) (b := fF hR b a) hx]
    exact inv _
  · refine (eqA_iff repB3 rep_idA).2 ?_
    rw [cube_pair (conj c b) (conj b c), Fin.ext (a := fF hR c b) (b := fF hR b c) hy]
    exact inv _

end CFSG.KC.MinusSecondKind
