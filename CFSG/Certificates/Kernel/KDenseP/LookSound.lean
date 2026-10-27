module

public import Certificates.Data.Kernel.KDenseP.Look
public import CFSG.Certificates.Kernel.KDense.StepSound

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense CFSG.KC.KStep

theorem kok_cons {a : ℕ} {t : List ℕ} : kok (a :: t) = true ↔ a < 31 ∧ kok t = true := by
  change andB (Nat.blt a 31) (kok t) = true ↔ _
  rw [andB_eq', Bool.and_eq_true, Nat.blt_eq]

theorem kcode_cons (a : ℕ) (t : List ℕ) : kcode (a :: t) = a + 1 + 32 * kcode t := rfl

theorem kcode_nil : kcode [] = 0 := rfl

theorem kcode_inj : ∀ {l m : List ℕ}, kok l = true → kok m = true → kcode l = kcode m → l = m
  | [], [], _, _, _ => rfl
  | [], b :: m, _, _, h => by
    rw [kcode_nil, kcode_cons] at h
    omega
  | a :: l, [], _, _, h => by
    rw [kcode_nil, kcode_cons] at h
    omega
  | a :: l, b :: m, hl, hm, h => by
    rw [kok_cons] at hl hm
    rw [kcode_cons, kcode_cons] at h
    have hab : a = b := by omega
    have hc : kcode l = kcode m := by omega
    rw [hab, kcode_inj hl.2 hm.2 hc]

theorem listEq_self : ∀ l : List ℕ, listEq l l = true
  | [] => rfl
  | x :: l => by
    change andB (Nat.beq x x) (listEq l l) = true
    simp only [andB_eq', Nat.beq_refl, listEq_self l, Bool.and_self]

theorem findIdx_of {l : List ℕ} : ∀ {ls : List (List ℕ)} {i : ℕ} (hi : i < ls.length),
    ls[i] = l → (∀ j (hj : j < i), ls[j]'(by omega) ≠ l) → findIdx l ls = (true, i)
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: ls, i, hi, he, hj => by
    change Bool.rec (motive := fun _ => Bool × Nat)
      (Prod.rec (motive := fun _ => Bool × Nat) (fun f i => (f, Nat.add i (nat_lit 1))) (findIdx l ls))
      (true, nat_lit 0) (listEq x l) = (true, i)
    rcases i with _ | i
    · have hx : x = l := he
      rw [hx, listEq_self]
    · have hx : listEq x l = false := by
        rcases h : listEq x l
        · rfl
        · exact absurd (listEq_eq' h) (hj 0 (by omega))
      have ih := findIdx_of (ls := ls) (i := i) (by simp at hi; omega) (by simpa using he)
        (fun j hj' => by simpa using hj (j + 1) (by omega))
      rw [hx, ih]

theorem tabChk_spec {CT SC PI N : ℕ} : ∀ {ks : List (List ℕ)} {j : ℕ}, tabChk CT SC PI N ks j = true →
    ∀ i (hi : i < ks.length), kok ks[i] = true ∧ fldW CT 128 (j + i) = kcode ks[i] ∧
      fldW PI 11 (bsr SC N (kcode ks[i]) 11 0) = j + i
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: ks, j, h, i, hi => by
    change andB (andB (kok x) (andB (Nat.beq (fldW CT 128 j) (kcode x))
        (Nat.beq (fldW PI 11 (bsr SC N (kcode x) 11 0)) j))) (tabChk CT SC PI N ks (j + 1)) = true at h
    rw [andB_eq', andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Nat.beq_eq, Nat.beq_eq] at h
    rcases i with _ | i
    · exact ⟨h.1.1, h.1.2.1, h.1.2.2⟩
    · have hi' : i < ks.length := by simp at hi; omega
      obtain ⟨h1, h2, h3⟩ := tabChk_spec h.2 i hi'
      have e : j + (i + 1) = j + 1 + i := by omega
      rw [e]
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem lookT_eq {CT SC PI N : ℕ} {ks : List (List ℕ)} (hT : tabChk CT SC PI N ks 0 = true)
    (hN : N ≤ ks.length) (l : List ℕ) : lookT CT SC PI N ks l = findIdx l ks := by
  change Bool.rec (motive := fun _ => Bool × ℕ) (findIdx l ks) (true, fldW PI 11 (bsr SC N (kcode l) 11 0))
    (andB (Nat.blt (fldW PI 11 (bsr SC N (kcode l) 11 0)) N) (andB (kok l)
      (Nat.beq (fldW CT 128 (fldW PI 11 (bsr SC N (kcode l) 11 0))) (kcode l)))) = findIdx l ks
  generalize hI : fldW PI 11 (bsr SC N (kcode l) 11 0) = i
  rcases hc : andB (Nat.blt i N) (andB (kok l) (Nat.beq (fldW CT 128 i) (kcode l)))
  · rfl
  · rw [andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨hiN, hkl, hcl⟩ := hc
    have hi : i < ks.length := by omega
    obtain ⟨hk, hct, -⟩ := tabChk_spec hT i hi
    rw [Nat.zero_add] at hct
    have he : ks[i] = l := kcode_inj hk hkl (by rw [← hct, hcl])
    change (true, i) = findIdx l ks
    refine (findIdx_of hi he fun j hj hjl => ?_).symm
    obtain ⟨-, -, hpj⟩ := tabChk_spec hT j (by omega)
    rw [hjl, hI, Nat.zero_add] at hpj
    omega

theorem chunkOKN_of_look {n lg q : ℕ} {F : Fix} {MT : MonoTab} {look : List ℕ → Bool × ℕ}
    (hl : look = fun k => findIdx k MT.keys) {words : ℕ → List CFSG.Monster.AxisCount.Native.Gen}
    {S : ℕ → St} {c : ℕ} (h : chunkOKNL n lg q F MT look words S c = true) :
    chunkOKN n lg q F MT words S c = true := by
  subst hl
  rwa [chunkOKNL_findIdx] at h

end CFSG.KC.KDenseP

end
