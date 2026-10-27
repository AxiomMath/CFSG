module

public import Certificates.Data.Kernel.He7222.Good
public import Mathlib.Logic.Function.Iterate
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.He7222.ChainSound
public import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.KC.OrbRow CFSG.KS.PF

theorem powF_eq (f : ℕ → ℕ) : ∀ e q, powF f e q = f^[e] q
  | 0, _ => rfl
  | e + 1, q => by
    have h : powF f (e + 1) q = powF f e (f q) := strictN_eqP (f q) _
    rw [h, powF_eq f e (f q), Function.iterate_succ_apply]

@[expose] noncomputable def cycR (f : ℕ → ℕ) (p : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih q l => strictN (f q) (fun q' => nIf(Nat.beq q' p, l, ih q' (Nat.succ l))))

theorem cycN_eq (f : ℕ → ℕ) (p F : ℕ) : cycN f p F = cycR f p F p 1 := rfl

theorem cycR_succ (f : ℕ → ℕ) (p F q l : ℕ) :
    cycR f p (F + 1) q l = if f q = p then l else cycR f p F (f q) (l + 1) := by
  change strictN (f q) (fun q' => nIf(Nat.beq q' p, l, cycR f p F q' (Nat.succ l))) = _
  rw [strictN_eqP]
  rcases Bool.eq_false_or_eq_true (Nat.beq (f q) p) with hb | hb
  · rw [hb, if_pos (Nat.eq_of_beq_eq_true hb)]
  · rw [hb, if_neg (Nat.ne_of_beq_eq_false hb)]

theorem cycR_spec (f : ℕ → ℕ) (p : ℕ) : ∀ F q l, 1 ≤ l → q = f^[l - 1] p →
    (∀ j, 1 ≤ j → j < l → f^[j] p ≠ p) →
    (cycR f p F q l = 0 ∧ ∀ j, l ≤ j → j < l + F → f^[j] p ≠ p) ∨
      (l ≤ cycR f p F q l ∧ cycR f p F q l < l + F ∧ f^[cycR f p F q l] p = p ∧
        ∀ j, 1 ≤ j → j < cycR f p F q l → f^[j] p ≠ p) := by
  intro F
  induction F with
  | zero =>
    intro q l _ _ _
    exact Or.inl ⟨rfl, fun j hj hj' => absurd hj' (by omega)⟩
  | succ F ih =>
    intro q l hl hq hmin
    rw [cycR_succ]
    have hfq : f q = f^[l] p := by
      rw [hq, ← Function.iterate_succ_apply' f (l - 1) p]
      congr 1
      omega
    by_cases hb : f q = p
    · right
      rw [if_pos hb]
      exact ⟨le_rfl, by omega, by rw [← hfq]; exact hb, hmin⟩
    · rw [if_neg hb]
      have hne : f^[l] p ≠ p := by
        rw [← hfq]
        exact hb
      have hmin' : ∀ j, 1 ≤ j → j < l + 1 → f^[j] p ≠ p := fun j hj hj' => by
        rcases Nat.lt_or_ge j l with h1 | h1
        · exact hmin j hj h1
        · rw [show j = l by omega]
          exact hne
      rcases ih (f q) (l + 1) (by omega) (by rw [hfq]; rfl) hmin' with
        ⟨h0, hall⟩ | ⟨h1, h2, h3, h4⟩
      · left
        refine ⟨h0, fun j hj hj' => ?_⟩
        rcases Nat.lt_or_ge j (l + 1) with h5 | h5
        · rw [show j = l by omega]
          exact hne
        · exact hall j h5 (by omega)
      · right
        exact ⟨by omega, by omega, h3, h4⟩

theorem cycN_spec (f : ℕ → ℕ) (p F : ℕ) :
    (cycN f p F = 0 ∧ ∀ j, 1 ≤ j → j ≤ F → f^[j] p ≠ p) ∨
      (1 ≤ cycN f p F ∧ cycN f p F ≤ F ∧ f^[cycN f p F] p = p ∧
        ∀ j, 1 ≤ j → j < cycN f p F → f^[j] p ≠ p) := by
  rw [cycN_eq]
  rcases cycR_spec f p F p 1 le_rfl rfl (fun j hj hj' => absurd hj' (by omega)) with
    ⟨h0, hall⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h0, fun j hj hj' => hall j hj (by omega)⟩
  · exact Or.inr ⟨h1, by omega, h3, h4⟩

theorem iterate_mul_eq {f : ℕ → ℕ} {p l : ℕ} (h : f^[l] p = p) : ∀ q, f^[l * q] p = p
  | 0 => rfl
  | q + 1 => by rw [Nat.mul_succ, Function.iterate_add_apply, h, iterate_mul_eq h q]

theorem cycN_dvd {f : ℕ → ℕ} {p F e : ℕ} (he0 : 0 < e) (heF : e ≤ F) (he : f^[e] p = p) :
    0 < cycN f p F ∧ cycN f p F ∣ e := by
  rcases cycN_spec f p F with ⟨_, hall⟩ | ⟨h1, -, h3, h4⟩
  · exact absurd he (hall e he0 heF)
  refine ⟨h1, ?_⟩
  set l := cycN f p F
  have hdm := Nat.div_add_mod e l
  have hm : f^[e % l] p = p := by
    have := he
    rw [← hdm, Nat.add_comm, Function.iterate_add_apply, iterate_mul_eq h3] at this
    exact this
  by_contra hnd
  have hpos : 0 < e % l := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
  exact h4 (e % l) hpos (Nat.mod_lt e h1) hm

theorem dvK_of_dvd {e l : ℕ} (h : l ∣ e) : dvK e l = true := by
  change Nat.beq (e % l) 0 = true
  rw [Nat.mod_eq_zero_of_dvd h]
  rfl

theorem okK_of_pow {f : ℕ → ℕ} {e : ℕ} (he : e ∈ [25, 343, 17]) (hf : ∀ p < 5, f^[e] p = p) :
    okK f = true := by
  have he0 : 0 < e := by simp at he; omega
  have heF : e ≤ 343 := by simp at he; omega
  have hd : ∀ p < 5, cycN f p 343 ∣ e := fun p hp => (cycN_dvd he0 heF (hf p hp)).2
  unfold okK
  simp only [strictB_eqP]
  have hd5 : dv5 e (cycN f 0 343) (cycN f 1 343) (cycN f 2 343) (cycN f 3 343) (cycN f 4 343) =
      true := by
    unfold dv5
    simp only [bAnd_iff]
    exact ⟨dvK_of_dvd (hd 0 (by omega)), dvK_of_dvd (hd 1 (by omega)), dvK_of_dvd (hd 2 (by omega)),
      dvK_of_dvd (hd 3 (by omega)), dvK_of_dvd (hd 4 (by omega))⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · have h3 : dv3 (cycN f 0 343) = true := by
      unfold dv3
      rw [dvK_of_dvd (hd 0 (by omega))]
    rw [h3]
    change bIf(dv5 25 _ _ _ _ _, true, _) = true
    rw [hd5]
  · have h3 : dv3 (cycN f 0 343) = true := by
      unfold dv3
      rw [dvK_of_dvd (hd 0 (by omega))]
      cases dvK 25 (cycN f 0 343) <;> rfl
    rw [h3]
    change bIf(dv5 25 _ _ _ _ _, true, bIf(dv5 343 _ _ _ _ _, true, _)) = true
    rw [hd5]
    cases dv5 25 (cycN f 0 343) (cycN f 1 343) (cycN f 2 343) (cycN f 3 343) (cycN f 4 343) <;> rfl
  · have h3 : dv3 (cycN f 0 343) = true := by
      unfold dv3
      rw [dvK_of_dvd (hd 0 (by omega))]
      cases dvK 25 (cycN f 0 343) <;> cases dvK 343 (cycN f 0 343) <;> rfl
    rw [h3]
    change bIf(dv5 25 _ _ _ _ _, true, bIf(dv5 343 _ _ _ _ _, true, dv5 17 _ _ _ _ _)) = true
    rw [hd5]
    cases dv5 25 (cycN f 0 343) (cycN f 1 343) (cycN f 2 343) (cycN f 3 343) (cycN f 4 343) <;>
      cases dv5 343 (cycN f 0 343) (cycN f 1 343) (cycN f 2 343) (cycN f 3 343) (cycN f 4 343) <;> rfl

theorem basK_sound {w m : ℕ} {f : ℕ → ℕ} {tau p : ℕ} {S SI : ℕ → ℕ} {d : List ℤ}
    {rec : List ℕ} : ∀ {B : List (List ℤ)} {q : ℕ}, basK w m f tau p S SI d rec B q = true →
    ∀ i < B.length, lettersK 2 (B.getD i []) = true ∧ ∀ x < 5,
      wpK w m S SI d (wpK w m S SI (B.getD i []) (wpIK w m S SI d x)) =
        prodO w m f tau p (getS rec (q + i)) x
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | b :: B, q, h, i, hi => by
    have h' : strictB (getS rec q) (fun mk => bAnd(lettersK (nat_lit 2) b,
        bAnd(allN (nat_lit 5) (fun x =>
          Nat.beq (wpK w m S SI d (wpK w m S SI b (wpIK w m S SI d x))) (prodO w m f tau p mk x)),
          basK w m f tau p S SI d rec B (Nat.succ q)))) = true := h
    rw [strictB_eqP, bAnd_iff, bAnd_iff] at h'
    obtain ⟨hl, ha, hrest⟩ := h'
    rcases i with _ | i
    · refine ⟨hl, fun x hx => ?_⟩
      exact Nat.eq_of_beq_eq_true (allN_spec ha x hx)
    · have := basK_sound hrest i (by simpa using hi)
      rw [show q + (i + 1) = Nat.succ q + i by omega]
      exact this

theorem goodK_sound {w m : ℕ} {f : ℕ → ℕ} {tau : ℕ} {S SI : ℕ → ℕ} {DW R5 R7 : List (List ℤ)}
    {rec : List ℕ} (h : goodK w m f tau S SI DW R5 R7 rec = true) :
    0 < getS rec 0 ∧ (∀ q < 5, f^[getS rec 0] q = q) ∧
    ((getS rec 1 = 0 ∧ getS rec 2 < getS rec 0 ∧ getS rec 3 < 5 ∧
        oK w m f tau (getS rec 0) (getS rec 2) (pg w m tau (getS rec 3)) ≠
          pg w m tau (oK w m f tau (getS rec 0) (getS rec 2) (getS rec 3))) ∨
      (getS rec 1 = 1 ∧ getS rec 3 ≤ 1 ∧ getS rec 2 < lenWI DW ∧
        lettersK 3 (getWI DW (getS rec 2)) = true ∧
        lenS rec = 4 + lenWI (selB (getS rec 3) R5 R7) ∧
        basK w m f tau (getS rec 0) S SI (getWI DW (getS rec 2)) rec (selB (getS rec 3) R5 R7) 4 =
          true)) := by
  unfold goodK at h
  rw [strictB_eqP, bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  obtain ⟨hp, hpow, hcase⟩ := h
  refine ⟨hp, fun q hq => by rw [← powF_eq]; exact Nat.eq_of_beq_eq_true (allN_spec hpow q hq), ?_⟩
  rw [bIf_iff] at hcase
  rcases hcase with ⟨h1, hc⟩ | ⟨h1, hc⟩
  · left
    rw [strictB_eqP, strictB_eqP, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, bIf_iff] at hc
    obtain ⟨hj, hq, hc⟩ := hc
    refine ⟨Nat.eq_of_beq_eq_true h1, hj, hq, fun he => ?_⟩
    rcases hc with ⟨hc, hf⟩ | ⟨hc, -⟩
    · exact absurd hf (by simp)
    · rw [he, Nat.beq_refl] at hc
      exact absurd hc (by simp)
  · right
    rw [bAnd_iff, strictB_eqP, bAnd_iff, Nat.ble_eq, strictB_eqP, bAnd_iff, Nat.blt_eq, bAnd_iff,
      bAnd_iff] at hc
    obtain ⟨h1', hk, hc, hl, hlen, hb⟩ := hc
    exact ⟨Nat.eq_of_beq_eq_true h1', hk, hc, hl, Nat.eq_of_beq_eq_true hlen, hb⟩

theorem goodLW_sound {w m : ℕ} {KTs : List (List ℕ)} {gs : List ℕ} {tau : ℕ} {S SI : ℕ → ℕ}
    {DW R5 R7 : List (List ℤ)} {FT GD : List (List ℕ)} :
    ∀ (L : List (List ℕ)) (t : ℕ), L = FT.drop t → t ≤ FT.length →
    List.rec (motive := fun _ => Nat → Bool)
      (fun t => Nat.beq t (lenLN GD))
      (fun kt _ ih t => bAnd(goodK w m (fun q => evK w m gs (evK w m (stkK KTs kt) q)) tau S SI DW
        R5 R7 (getLs GD t), strictB (Nat.succ t) ih)) L t = true →
    lenLN GD = FT.length ∧ ∀ j, t ≤ j → j < FT.length →
      goodK w m (fun q => evK w m gs (evK w m (stkK KTs (FT.getD j [])) q)) tau S SI DW R5 R7
        (getLs GD j) = true := by
  intro L
  induction L with
  | nil =>
    intro t hL ht h
    have hT : FT.length ≤ t := List.drop_eq_nil_iff.mp hL.symm
    have := Nat.eq_of_beq_eq_true (show Nat.beq t (lenLN GD) = true from h)
    exact ⟨by omega, fun j hj hj' => absurd hj' (by omega)⟩
  | cons kt L ih =>
    intro t hL ht h
    have htF : t < FT.length := by
      rcases Nat.lt_or_ge t FT.length with h1 | h1
      · exact h1
      · have : FT.drop t = [] := List.drop_eq_nil_iff.mpr h1
        rw [this] at hL
        exact absurd hL (List.cons_ne_nil _ _)
    have hkt : FT.getD t [] = kt := by
      rw [List.getD_eq_getElem?_getD, ← List.head?_drop, ← hL, List.head?_cons, Option.getD_some]
    have hL' : L = FT.drop (t + 1) := by
      have := congrArg List.tail hL
      rw [List.tail_cons, List.tail_drop] at this
      exact this
    have h' : bAnd(goodK w m (fun q => evK w m gs (evK w m (stkK KTs kt) q)) tau S SI DW
        R5 R7 (getLs GD t), strictB (Nat.succ t) (List.rec (motive := fun _ => Nat → Bool)
          (fun t => Nat.beq t (lenLN GD))
          (fun kt _ ih t => bAnd(goodK w m (fun q => evK w m gs (evK w m (stkK KTs kt) q)) tau S SI
            DW R5 R7 (getLs GD t), strictB (Nat.succ t) ih)) L)) = true := h
    rw [bAnd_iff, strictB_eqP (Nat.succ t)] at h'
    obtain ⟨hlen, hall⟩ := ih (t + 1) hL' htF h'.2
    refine ⟨hlen, fun j hj hjF => ?_⟩
    rcases Nat.lt_or_ge t j with htj | htj
    · exact hall j htj hjF
    have : j = t := by omega
    subst this
    rw [hkt]
    exact h'.1

theorem goodLK_sound {w m : ℕ} {KTs : List (List ℕ)} {gs : List ℕ} {tau : ℕ} {S SI : ℕ → ℕ}
    {DW R5 R7 : List (List ℤ)} {FT GD : List (List ℕ)}
    (h : goodLK w m KTs gs tau S SI DW R5 R7 FT GD = true) :
    lenLN GD = FT.length ∧ ∀ j < FT.length,
      goodK w m (fun q => evK w m gs (evK w m (stkK KTs (FT.getD j [])) q)) tau S SI DW R5 R7
        (getLs GD j) = true := by
  obtain ⟨h1, h2⟩ := goodLW_sound FT 0 rfl (Nat.zero_le _) h
  exact ⟨h1, fun j hj => h2 j (Nat.zero_le _) hj⟩

end CFSG.KC.HeChain

end
