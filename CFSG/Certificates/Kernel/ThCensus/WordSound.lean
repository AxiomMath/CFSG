module

public import CFSG.Certificates.Kernel.ThCensus.Sound
public import Certificates.Data.Kernel.ThCensus.LetDefs
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Th.Spec.Big

public section

namespace CFSG.KC.ThCensus.Sound

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus

theorem bitsN_two (J o : ℕ) : bitsN J o 2 = J / 2 ^ o % 4 := by
  change (J >>> o) &&& ((1 <<< 2) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem nfX_cons {e : ℕ} (he : e < 4) (l : List ℕ) : nfX (e :: l) = e + 4 * nfX l := by
  change e ||| (nfX l <<< 2) = _
  have he' : e < 2 ^ 2 := he
  rw [Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt he',
    Nat.add_comm]

theorem nfX_digit : ∀ l : List ℕ, (∀ e ∈ l, e < 4) → ∀ k, bitsN (nfX l) (2 * k) 2 = l.getD k 0
  | [], _, k => by
    rw [bitsN_two]
    change 0 / 2 ^ (2 * k) % 4 = 0
    simp
  | e :: l, h, k => by
    have he := h e (List.mem_cons_self ..)
    have hl : ∀ e ∈ l, e < 4 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [nfX_cons he]
    rcases k with _ | k
    · rw [bitsN_two]
      simp only [Nat.mul_zero, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · have ih := nfX_digit l hl k
      rw [bitsN_two] at ih ⊢
      have e2 : 2 * (k + 1) = 2 + 2 * k := by omega
      have e4 : (e + 4 * nfX l) / 2 ^ 2 = nfX l := by
        norm_num
        omega
      rw [List.getD_cons_succ, ← ih, e2, pow_add, ← Nat.div_div_eq_div_mul, e4]

theorem nfNum_digit : ∀ l : List ℕ, (∀ e ∈ l, e < 3) → ∀ k, permNfNum l / 3 ^ k % 3 = l.getD k 0
  | [], _, k => by
    change 0 / 3 ^ k % 3 = 0
    simp
  | e :: l, h, k => by
    have he := h e (List.mem_cons_self ..)
    have hl : ∀ e ∈ l, e < 3 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hc : permNfNum (e :: l) = e + 3 * permNfNum l := rfl
    rw [hc]
    rcases k with _ | k
    · simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · rw [List.getD_cons_succ, ← nfNum_digit l hl k, pow_succ', ← Nat.div_div_eq_div_mul]
      congr 2
      omega

section Group

variable {G : Type*} [Group G]

@[expose] def prodL (g : ℕ → G) (D : ℕ → ℕ) : ℕ → G
  | 0 => 1
  | m + 1 => prodL g D m * g m ^ D m

theorem prodL_nfFrom (g : ℕ → G) (D : ℕ → ℕ) :
    ∀ t s n, (∀ i < t, n / 3 ^ i % 3 = D (s + i)) →
      prodL g D s * nfFrom g t s n = prodL g D (s + t)
  | 0, s, n, _ => by
    rw [Nat.add_zero]
    exact mul_one _
  | t + 1, s, n, h => by
    have h0 := h 0 (by omega)
    rw [pow_zero, Nat.div_one, Nat.add_zero] at h0
    have h1 : ∀ i < t, n / 3 / 3 ^ i % 3 = D (s + 1 + i) := by
      intro i hi
      rw [Nat.div_div_eq_div_mul, ← pow_succ', h (i + 1) (by omega)]
      congr 1
      omega
    rw [nfFrom_succ, ← mul_assoc, h0]
    have e : prodL g D s * g s ^ D s = prodL g D (s + 1) := rfl
    rw [e, prodL_nfFrom g D t (s + 1) (n / 3) h1]
    congr 1
    omega

theorem nfFrom_nfNum (g : ℕ → G) {l : List ℕ} (hl : ∀ e ∈ l, e < 3) :
    nfFrom g 10 0 (permNfNum l) = prodL g (fun k => l.getD k 0) 10 := by
  have h := prodL_nfFrom g (fun k => l.getD k 0) 10 0 (permNfNum l)
    (fun i _ => by rw [Nat.zero_add]; exact nfNum_digit l hl i)
  rw [← h]
  exact (one_mul _).symm

end Group

theorem lt3_of_rec : ∀ l : List ℕ, List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (Nat.blt e 3) ih) l = true → ∀ e ∈ l, e < 3
  | [], _, e, he => absurd he List.not_mem_nil
  | x :: l, h, e, he => by
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 h
    rcases List.mem_cons.1 he with rfl | he
    · exact Nat.blt_eq.mp h1
    · exact lt3_of_rec l h2 e he

theorem nfOK_lt {l : List ℕ} (h : nfOK l = true) : ∀ e ∈ l, e < 3 :=
  lt3_of_rec l (Dce.andB_iff.1 h).2

theorem nfsOK_spec : ∀ L : List (List ℕ), nfsOK L = true → ∀ l ∈ L, nfOK l = true
  | [], _, l, hl => absurd hl List.not_mem_nil
  | x :: L, h, l, hl => by
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 h
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h1
    · exact nfsOK_spec L h2 l hl

section Mat

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {G : Type*} [Group G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}

theorem rhsPc_succ (PW : ℕ → ℕ) (c rm ONE x m : ℕ) :
    rhsPc PW c rm ONE (m + 1) 3 2 x = Bool.rec (motive := fun _ => ℕ)
      (mulB c rm (rhsPc PW c rm ONE m 3 2 x) (PW (m * (3 - 1) + bitsN x (2 * m) 2 - 1)))
      (rhsPc PW c rm ONE m 3 2 x) (Nat.beq (bitsN x (2 * m) 2) 0) := rfl

theorem rhsPc_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {PW : ℕ → ℕ} {g : ℕ → G}
    (hpw : ∀ k < 10, ∀ e, 1 ≤ e → e < 3 → pkMat (PW (k * (3 - 1) + e - 1)) = φ (g k ^ e))
    (x : ℕ) : ∀ m ≤ 10, (∀ k < m, bitsN x (2 * k) 2 < 3) →
      pkMat (rhsPc PW c rm ONE m 3 2 x) = φ (prodL g (fun k => bitsN x (2 * k) 2) m)
  | 0, _, _ => by
    change pkMat ONE = φ 1
    rw [pkMat_one hk, map_one]
  | m + 1, hm, hd => by
    have ih := rhsPc_spec hk hpw x m (by omega) (fun k hk' => hd k (by omega))
    rw [rhsPc_succ]
    have e : prodL g (fun k => bitsN x (2 * k) 2) (m + 1) =
        prodL g (fun k => bitsN x (2 * k) 2) m * g m ^ bitsN x (2 * m) 2 := rfl
    rw [e]
    by_cases h0 : bitsN x (2 * m) 2 = 0
    · rw [h0, pow_zero, mul_one]
      exact ih
    · have hb : Nat.beq (bitsN x (2 * m) 2) 0 = false :=
        Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
      rw [hb]
      change pkMat (mulB c rm _ _) = _
      rw [pkMat_mulB hk, ih, hpw m (by omega) _ (Nat.pos_of_ne_zero h0) (hd m (by omega)), map_mul]

theorem nfM_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {PW : ℕ → ℕ} {g : ℕ → G}
    (hpw : ∀ k < 10, ∀ e, 1 ≤ e → e < 3 → pkMat (PW (k * (3 - 1) + e - 1)) = φ (g k ^ e))
    {l : List ℕ} (hl : nfOK l = true) :
    pkMat (nfM PW c rm ONE l) = φ (nfFrom g 10 0 (permNfNum l)) := by
  have h3 := nfOK_lt hl
  have h4 : ∀ e ∈ l, e < 4 := fun e he => by have := h3 e he; omega
  have hd : ∀ k, bitsN (nfX l) (2 * k) 2 = l.getD k 0 := nfX_digit l h4
  have hdl : ∀ k, l.getD k 0 < 3 := by
    intro k
    rw [List.getD_eq_getElem?_getD]
    cases hk' : l[k]? with
    | none => simp
    | some v => exact h3 v (List.mem_of_getElem? hk')
  have e := rhsPc_spec hk hpw (nfX l) 10 le_rfl (fun k _ => by rw [hd]; exact hdl k)
  change pkMat (rhsPc PW c rm ONE 10 3 2 (nfX l)) = _
  rw [e, nfFrom_nfNum g h3]
  congr 2
  funext k
  exact hd k

theorem letR_cases (r0 r1 r2 r3 x : ℕ) (hx : x < 4) :
    (x = 0 ∧ letR r0 r1 r2 r3 x = r0) ∨ (x = 1 ∧ letR r0 r1 r2 r3 x = r1) ∨
      (x = 2 ∧ letR r0 r1 r2 r3 x = r2) ∨ (x = 3 ∧ letR r0 r1 r2 r3 x = r3) := by
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem wordR_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {RB : ℕ → ℕ} {r0 r1 r2 r3 q : ℕ}
    (hlet : ∀ x < q, x < 4 → ∃ u : G, φ u = pkMat (RB (letR r0 r1 r2 r3 x))) :
    ∀ n w S, wordLetOK q n w = true → ∀ v : G, pkMat S = φ v →
      ∃ W : G, pkMat (wordR RB c rm r0 r1 r2 r3 n w S) = φ W
  | 0, _, _, _, v, hv => ⟨v, hv⟩
  | n + 1, w, S, hw, v, hv => by
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 hw
    have hx3 : Nat.land w 3 < 4 := by
      have : Nat.land w 3 ≤ 3 := Nat.and_le_right
      omega
    obtain ⟨u, hu⟩ := hlet _ (Nat.blt_eq.mp h1) hx3
    have e : wordR RB c rm r0 r1 r2 r3 (n + 1) w S =
        wordR RB c rm r0 r1 r2 r3 n (Nat.shiftRight w 2)
          (mulB c rm S (RB (letR r0 r1 r2 r3 (Nat.land w 3)))) := by
      change CFSG.KC.Loop.strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e]
    exact wordR_spec hk hlet n _ _ h2 (v * u) (by rw [pkMat_mulB hk, hv, map_mul, hu])

theorem wordLetOK_four : ∀ n w, wordLetOK 4 n w = true
  | 0, _ => rfl
  | n + 1, w => by
    have h1 : Nat.blt (Nat.land w 3) 4 = true := by
      rw [Nat.blt_eq]
      have : Nat.land w 3 ≤ 3 := Nat.and_le_right
      omega
    change andB (Nat.blt (Nat.land w 3) 4) (wordLetOK 4 n (Nat.shiftRight w 2)) = true
    rw [h1, wordLetOK_four n]
    rfl

theorem conj_of_conjEq (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hφ : Function.Injective φ) {X Y Wm : ℕ} {x y w : G} (hx : pkMat X = φ x) (hy : pkMat Y = φ y)
    (hw : pkMat Wm = φ w) (h : conjEq c rm X Y Wm = true) : w * x = y * w := by
  have h' : Nat.beq 1 (Bool.rec (motive := fun _ => ℕ) 0 1
      (Nat.beq (mulB c rm Wm X) (mulB c rm Y Wm))) = true := by
    have e := h
    unfold conjEq at e
    rw [strictN_eq] at e
    exact e
  have hb : Nat.beq (mulB c rm Wm X) (mulB c rm Y Wm) = true := by
    cases hc : Nat.beq (mulB c rm Wm X) (mulB c rm Y Wm)
    · rw [hc] at h'
      exact absurd h' (by decide)
    · rfl
  apply hφ
  have e := congrArg pkMat (Nat.eq_of_beq_eq_true hb)
  rw [pkMat_mulB hk, pkMat_mulB hk, hx, hy, hw, ← map_mul, ← map_mul] at e
  exact e

theorem clsM_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {RB : ℕ → ℕ} {rz rs ru : ℕ} {Z S U : G} (hZ : φ Z = pkMat (RB rz)) (hS : φ S = pkMat (RB rs))
    (hU : φ U = pkMat (RB ru)) {k : ℕ} (hk6 : k < 6) :
    ∃ C : G, (C = Z ∨ C = Z ^ 2 ∨ C = S ∨ C = S ^ 2 ∨ C = U ∨ C = U ^ 2) ∧
      pkMat (clsM RB c rm rz rs ru k) = φ C := by
  have sq : ∀ (r : ℕ) (X : G), φ X = pkMat (RB r) → pkMat (mulB c rm (RB r) (RB r)) = φ (X ^ 2) :=
    fun r X h => by rw [pkMat_mulB hk, ← h, pow_two, map_mul]
  interval_cases k
  · exact ⟨Z, Or.inl rfl, hZ.symm⟩
  · exact ⟨Z ^ 2, Or.inr (Or.inl rfl), sq rz Z hZ⟩
  · exact ⟨S, Or.inr (Or.inr (Or.inl rfl)), hS.symm⟩
  · exact ⟨S ^ 2, Or.inr (Or.inr (Or.inr (Or.inl rfl))), sq rs S hS⟩
  · exact ⟨U, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hU.symm⟩
  · exact ⟨U ^ 2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), sq ru U hU⟩

end Mat

end CFSG.KC.ThCensus.Sound

end
