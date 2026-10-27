module

public import Certificates.Data.Kernel.LyModel.Cp3
public import CFSG.Certificates.Kernel.LyBenes.Sound
import CFSG.Certificates.Kernel.KDense.SortSound

public section

namespace CFSG.KC.LyModel

open CFSG.KC CFSG.KC.Loop CFSG.KC.LyDce CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.LyBenes

theorem cp3_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem cp3_orB {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem allFrom_sound {lo : Nat} {f : Nat → Bool} :
    ∀ {n : Nat}, allFrom lo n f = true → ∀ i < n, f (lo + i) = true
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    have h' : andB (f (Nat.add lo n)) (allFrom lo n f) = true := h
    obtain ⟨h1, h2⟩ := cp3_andB h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allFrom_sound h2 i hi
    · exact h1

theorem memN_sound {p : Nat} : ∀ {R : List Nat}, memN p R = true → p ∈ R
  | [], h => absurd h Bool.false_ne_true
  | a :: R, h => by
    have h' : orB (Nat.beq a p) (memN p R) = true := h
    rcases cp3_orB h' with h1 | h1
    · rw [Nat.eq_of_beq_eq_true h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memN_sound h1)

theorem invAt_sound {Tc Td root C : Nat} {ys : List Nat} {l : Nat}
    (h : invAt Tc Td root C ys l = true) (hl : l < nL) :
    l = root ∨ C.testBit l = true ∨ mvC Tc Td ys l ≠ l := by
  have h' : orB (notB (Nat.blt l nL)) (orB (Nat.beq l root)
      (orB (Nat.beq (Nat.land (Nat.shiftRight C l) 1) 1)
        (notB (Nat.beq (mvC Tc Td ys l) l)))) = true := h
  rcases cp3_orB h' with h1 | h1
  · have hb : Nat.blt l nL = true := by simpa [Nat.blt_eq] using hl
    rw [hb] at h1
    exact absurd h1 Bool.false_ne_true
  rcases cp3_orB h1 with h2 | h2
  · exact Or.inl (Nat.eq_of_beq_eq_true h2)
  rcases cp3_orB h2 with h3 | h3
  · refine Or.inr (Or.inl ?_)
    have e := Nat.eq_of_beq_eq_true h3
    have e2 : C.shiftRight l % 2 = 1 := by
      rw [← Nat.and_one_is_mod]
      exact e
    rw [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, ← Nat.shiftRight_eq]
    simp only [beq_iff_eq]
    exact e2
  · refine Or.inr (Or.inr ?_)
    intro e
    have : Nat.beq (mvC Tc Td ys l) l = true := by rw [e]; exact Nat.beq_refl l
    rw [this] at h3
    exact absurd h3 Bool.false_ne_true

theorem orbOK_sound {Tc Td : Nat} {us : List (List Nat)} {Q : Nat → Prop}
    (hQ : ∀ j < 4, ∀ p, Q p → Q (mvC Tc Td (us.getD j []) p)) :
    ∀ {es : List (Nat × Nat × Nat)} {R : List Nat}, (∀ p ∈ R, Q p) →
      orbOK Tc Td us es R = true → ∀ e ∈ es, Q e.1
  | [], _, _, _, e, he => absurd he List.not_mem_nil
  | e' :: es, R, hR, h, e, he => by
    have h' : andB (andB (memN e'.2.1 R) (andB (Nat.blt e'.2.2 4)
        (Nat.beq (mvC Tc Td (us.getD e'.2.2 []) e'.2.1) e'.1)))
        (orbOK Tc Td us es (e'.1 :: R)) = true := h
    obtain ⟨h1, h2⟩ := cp3_andB h'
    obtain ⟨h3, h4⟩ := cp3_andB h1
    obtain ⟨h5, h6⟩ := cp3_andB h4
    have hq : Q e'.1 := by
      rw [← Nat.eq_of_beq_eq_true h6]
      exact hQ _ (by simpa [Nat.blt_eq] using h5) _ (hR _ (memN_sound h3))
    rcases List.mem_cons.1 he with rfl | he
    · exact hq
    · refine orbOK_sound hQ ?_ h2 e he
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hq
      · exact hR p hp

theorem rec_or_bit (P : Nat → Nat) (r : Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) 0 (fun u acc => strictN acc fun a => Nat.lor a (P u))
      n).testBit r = true ↔ ∃ u < n, (P u).testBit r = true
  | 0 => by simp
  | n + 1 => by
    change (strictN (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => strictN acc fun a => Nat.lor a (P u)) n) fun a => Nat.lor a (P n)).testBit r =
        true ↔ _
    rw [Benes.strictN_eq, nlor, Nat.testBit_or, Bool.or_eq_true, rec_or_bit P r n]
    constructor
    · rintro (⟨u, hu, h⟩ | h)
      · exact ⟨u, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨u, hu, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact Or.inl ⟨u, hu, h⟩
      · exact Or.inr h

theorem fixM_sound {N M : Nat} (hv : StagesValid 17 N) (h : fixM N M = true) :
    ∀ r < 66825, M.testBit r = true ↔ benesPerm 17 N r = r := by
  intro r hr
  have hr' : r < 2 ^ 17 := by omega
  have hA := acts_netApply_one hv
  have e := (Nat.eq_of_beq_eq_true h).symm
  have hm : (movedM N).testBit r = true ↔ ∃ u < 17,
      (Nat.xor (netApply 17 (Nat.shiftLeft 1 17) 1 N (idPlane (Nat.shiftLeft 1 17) u))
        (idPlane (Nat.shiftLeft 1 17) u)).testBit r = true :=
    rec_or_bit (fun u => Nat.xor (netApply 17 (Nat.shiftLeft 1 17) 1 N
      (idPlane (Nat.shiftLeft 1 17) u)) (idPlane (Nat.shiftLeft 1 17) u)) r 17
  have hbit : ∀ u < 17,
      (Nat.xor (netApply 17 (Nat.shiftLeft 1 17) 1 N (idPlane (Nat.shiftLeft 1 17) u))
        (idPlane (Nat.shiftLeft 1 17) u)).testBit r =
        ((benesPerm 17 N r).testBit u ^^ r.testBit u) := by
    intro u hu
    rw [nxor, Nat.testBit_xor, testBit_acts_idPlane hA hu hr', YModel.Sem.shl1,
      idPlane_testBit hu, decide_eq_true hr', Bool.true_and]
  rw [e, nland, nxor, Nat.testBit_and, Nat.testBit_xor, KDense.SortAux.testBit_ones,
    KDense.SortAux.testBit_ones, decide_eq_true (by omega : r < 131072), decide_eq_true hr,
    Bool.and_true, Bool.xor_true, Bool.not_eq_true']
  constructor
  · intro h1
    apply YModel.Sem.eq_of_bits (hA.1 r hr') hr'
    intro u hu
    by_contra hne
    have h2 : (movedM N).testBit r = true := hm.2 ⟨u, hu, by
      rw [hbit u hu]
      revert hne
      cases (benesPerm 17 N r).testBit u <;> cases r.testBit u <;> decide⟩
    rw [h2] at h1
    exact absurd h1 (by decide)
  · intro he
    cases hmb : (movedM N).testBit r with
    | false => rfl
    | true =>
      obtain ⟨u, hu, h2⟩ := hm.1 hmb
      rw [hbit u hu, he] at h2
      revert h2
      cases r.testBit u <;> decide

end CFSG.KC.LyModel

end
