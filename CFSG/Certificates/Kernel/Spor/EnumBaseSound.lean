module

public import Certificates.Data.Kernel.Spor.EnumBase
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.EnumBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.BaseEq

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

theorem blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

theorem beq_eq (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem allL_spec {ps : List Nat} {f : Nat → Bool} (h : allL ps f = true) :
    ∀ p ∈ ps, f p = true := by
  induction ps with
  | nil => intro p hp; simp at hp
  | cons q ps ih =>
    intro p hp
    change bAnd(f q, allL ps f) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hp with e | e
    · rw [e]
      exact h.1
    · exact ih h.2 p e

theorem left2K_spec {w m : Nat} {ps : List Nat} {a b c : Nat} (h : left2K w m ps a b c = true) :
    ∀ p ∈ ps, pg w m a (pg w m b p) = pg w m c p := fun p hp =>
  Nat.eq_of_beq_eq_true (allL_spec h p hp)

theorem conj3K_spec {w m : Nat} {ps : List Nat} {a b ai c : Nat}
    (h : conj3K w m ps a b ai c = true) :
    ∀ p ∈ ps, pg w m a (pg w m b (pg w m ai p)) = pg w m c p := fun p hp =>
  Nat.eq_of_beq_eq_true (allL_spec h p hp)

theorem sqFixK_iff {w m : Nat} {ps : List Nat} {b : Nat} :
    sqFixK w m ps b = true ↔ ∀ p ∈ ps, pg w m b (pg w m b p) = p := by
  constructor
  · exact fun h p hp => Nat.eq_of_beq_eq_true (allL_spec h p hp)
  · intro h
    unfold sqFixK
    induction ps with
    | nil => rfl
    | cons q ps ih =>
      change bAnd(Nat.beq (pg w m b (pg w m b q)) q, allL ps _) = true
      rw [bAnd_eq, Bool.and_eq_true, beq_eq, decide_eq_true_eq]
      exact ⟨h q List.mem_cons_self, ih fun p hp => h p (List.mem_cons_of_mem q hp)⟩

theorem cntN_eq (n : Nat) (f : Nat → Bool) : cntN n f = (List.range n).countP f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change strictN (cntN n f) (fun a => Nat.add a (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (nat_lit 1) (f n))) = _
    rw [strictN_eq, ih, List.range_succ, List.countP_append]
    by_cases hf : f n = true
    · simp [hf]
    · simp [Bool.eq_false_iff.2 hf]

theorem sliceK_spec {N L S : Nat} {f : Nat → Bool} (hL : 0 < L) (hN : N ≤ L * S)
    (h : ∀ s < S, sliceK N L f s = true) : ∀ i < N, f i = true := by
  intro i hi
  have hs : i / L < S := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; omega)
  have h1 := allN_spec (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [blt_eq]; exact decide_eq_true hi)] at h1
  exact h1

theorem recK_spec {n w m ng : Nat} {G T PL : Nat → Nat} {k : Nat}
    (h : recK n w m ng G T PL k = true) :
    (k = 0 → T 0 = pidn n w) ∧
      (k ≠ 0 → parOf PL k < k ∧ labOf PL k < ng ∧
        T k = pcomp n w m (G (labOf PL k)) (T (parOf PL k))) := by
  unfold recK at h
  rw [strictB_eq, bIf_eq] at h
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk
    have e : Nat.beq 0 0 = true := rfl
    rw [e, if_pos rfl] at h
    exact Nat.eq_of_beq_eq_true h
  · have e : Nat.beq k 0 = false := by rw [beq_eq]; simpa using hk
    rw [e, if_neg Bool.false_ne_true] at h
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
    exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem leftK_spec {w m : Nat} {ps : List Nat} {ng N : Nat} {G T POS : Nat → Nat} {k : Nat}
    (h : leftK w m ps ng N G T POS k = true) :
    ∀ g < ng, r32 POS (k * ng + g) < N ∧
      ∀ p ∈ ps, pg w m (G g) (pg w m (T k) p) = pg w m (T (r32 POS (k * ng + g))) p := by
  intro g hg
  unfold leftK at h
  rw [strictB_eq] at h
  have h1 := allN_spec h g hg
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at h1
  exact ⟨h1.1, left2K_spec h1.2⟩

theorem classPtK_spec {w m : Nat} {ps : List Nat} {ng N : Nat}
    {G GI T FL FP FG FQ MK PIX : Nat → Nat} {c o cnt j : Nat}
    (h : classPtK w m ps ng N G GI T FL FP FG FQ MK PIX c o cnt j = true) :
    FL (o + j) < N ∧ MK (FL (o + j)) = c ∧ PIX (FL (o + j)) = j ∧
    (j ≠ 0 → FP (o + j) < j ∧ FG (o + j) < ng ∧
      (∀ p ∈ ps, pg w m (G (FG (o + j))) (pg w m (T (FL (o + FP (o + j))))
        (pg w m (GI (FG (o + j))) p)) = pg w m (T (FL (o + j))) p) ∧
      (j + 1 < cnt → lexLtK (FP (o + j)) (FG (o + j)) (FP (o + (j + 1))) (FG (o + (j + 1))) =
        true)) ∧
    (∀ g < ng, FQ ((o + j) * ng + g) < cnt ∧
      (∀ p ∈ ps, pg w m (G g) (pg w m (T (FL (o + j))) (pg w m (GI g) p)) =
        pg w m (T (FL (o + FQ ((o + j) * ng + g)))) p) ∧
      (FQ ((o + j) * ng + g) = 0 ∨ lexLtK j g (FP (o + FQ ((o + j) * ng + g)))
        (FG (o + FQ ((o + j) * ng + g))) = false)) := by
  unfold classPtK at h
  simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, fun hj => ?_,
    fun g hg => ?_⟩
  · have e : Nat.beq j 0 = false := by rw [beq_eq]; simpa using hj
    rw [bIf_eq, e, if_neg Bool.false_ne_true] at h4
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h4
    obtain ⟨a1, a2, a3, a4⟩ := h4
    refine ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, conj3K_spec a3, fun hc => ?_⟩
    rw [bIf_eq, if_pos (Nat.blt_eq.mpr hc)] at a4
    exact a4
  · have hq := allN_spec h5 g hg
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at hq
    obtain ⟨a1, a2, a3⟩ := hq
    refine ⟨Nat.blt_eq.mp a1, conj3K_spec a2, ?_⟩
    by_cases e : FQ ((o + j) * ng + g) = 0
    · exact Or.inl e
    · have e' : Nat.beq (FQ ((o + j) * ng + g)) 0 = false := by rw [beq_eq]; simpa using e
      rw [bIf_eq, e', if_neg Bool.false_ne_true, bIf_eq] at a3
      right
      cases hl : lexLtK j g (FP (o + FQ ((o + j) * ng + g))) (FG (o + FQ ((o + j) * ng + g)))
      · rfl
      · rw [hl, if_pos rfl] at a3
        exact absurd a3 Bool.false_ne_true

theorem classK_spec {w m : Nat} {ps : List Nat} {ng N : Nat}
    {G GI T FL FP FG FQ CO MK PIX : Nat → Nat} {c : Nat}
    (h : classK w m ps ng N G GI T FL FP FG FQ CO MK PIX c = true) :
    CO c ≤ CO (c + 1) ∧ 0 < CO (c + 1) - CO c ∧ CO (c + 1) - CO c ≤ N ∧
      FP (CO c) = 0 ∧ FG (CO c) = 0 ∧ sqFixK w m ps (T (FL (CO c))) = true ∧
      ∀ j < CO (c + 1) - CO c,
        classPtK w m ps ng N G GI T FL FP FG FQ MK PIX c (CO c) (CO (c + 1) - CO c) j = true := by
  unfold classK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_eq, ble_eq, beq_eq,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, allN_spec h7⟩

theorem coverK_spec {w m : Nat} {ps : List Nat} {nc : Nat} {T FL CO MK PIX : Nat → Nat} {k : Nat}
    (h : coverK w m ps nc T FL CO MK PIX k = true) (hs : sqFixK w m ps (T k) = true) :
    MK k < nc ∧ PIX k < CO (MK k + 1) - CO (MK k) ∧ FL (CO (MK k) + PIX k) = k := by
  unfold coverK at h
  rw [bIf_eq, if_pos hs] at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_eq, beq_eq, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem posRK_spec {POS : Nat → Nat} {ng g : Nat} :
    ∀ (L : List Nat) (i : Nat), posRK POS ng g L i = true →
      ∀ j < L.length, L[j]! = r32 POS ((i + j) * ng + g)
  | [], _, _, j, hj => absurd hj (by simp)
  | x :: xs, i, h, j, hj => by
    change bAnd(Nat.beq x (r32 POS (Nat.add (Nat.mul i ng) g)), posRK POS ng g xs (Nat.succ i)) =
      true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using Nat.eq_of_beq_eq_true h.1
    | succ j =>
      have := posRK_spec xs (i + 1) h.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem iNat_eq (z : Int) : iNat z = z.toNat := by cases z <;> rfl

theorem fstN_eq (r : List Int) : fstN r = (r.getD 0 0).toNat := by
  cases r with
  | nil => rfl
  | cons z zs => exact iNat_eq z

theorem sndN_eq (r : List Int) : sndN r = (r.getD 1 0).toNat := by
  cases r with
  | nil => rfl
  | cons z zs => exact fstN_eq zs

theorem parRK_spec {PL : Nat → Nat} :
    ∀ (L : List (List Int)) (i : Nat), parRK PL L i = true →
      ∀ j < L.length, ((L[j]!).getD 0 0).toNat = parOf PL (i + j) ∧
        ((L[j]!).getD 1 0).toNat = labOf PL (i + j)
  | [], _, _, j, hj => absurd hj (by simp)
  | r :: rs, i, h, j, hj => by
    change bAnd(Nat.beq (fstN r) (parOf PL i), bAnd(Nat.beq (sndN r) (labOf PL i),
      parRK PL rs (Nat.succ i))) = true at h
    simp only [bAnd_eq, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getElem!_cons_zero, Nat.add_zero]
      rw [← fstN_eq, ← sndN_eq]
      exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩
    | succ j =>
      have := parRK_spec rs (i + 1) h.2.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

end CFSG.KS.EnumBase

end
