module

public import Certificates.Data.Kernel.Q8WitP2
public import CFSG.Certificates.Kernel.Q8WitPSound
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CFSG.KC.L34KSnd (pg_pcomp' pg_pidn' canon_lt)

variable {n w : ℕ}

theorem strictB_eqQ (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem beq_false_of_xyx {x y p : ℕ} (hx : PP n w x) (hy : Cn n w y) (hp : p < n)
    (h : (!Nat.beq (pg w (mask w) x (pg w (mask w) y (pg w (mask w) x p)))
      (pg w (mask w) y p)) = true) :
    Nat.beq (pcomp n w (mask w) y x) (pcomp n w (mask w) (pinvS n w (mask w) x) y) = false := by
  cases e : Nat.beq (pcomp n w (mask w) y x) (pcomp n w (mask w) (pinvS n w (mask w) x) y)
  · rfl
  · exfalso
    have hq := congrArg (fun t => pg w (mask w) t p) (Nat.eq_of_beq_eq_true e)
    rw [pg_pcomp' hy hp, pg_pcomp' (PP.inv hx).1 hp] at hq
    obtain ⟨-, hw, -, -⟩ := CFSG.KS.PF.canon_facts hx.1
    obtain ⟨u, hu, hxu⟩ := CFSG.KS.PinvS.surj_of_injK hx.2 _ (canon_lt hy hp)
    rw [← hxu, CFSG.KS.PinvS.pg_pinvS (by omega) hx.2 hu] at hq
    rw [hq, hxu, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem wit4PK_of_R {x y s c ci f P N : ℕ} (hc : commK n w c s = true)
    (h : wit4RK n w x y s c ci f P N = true) : wit4PK n w x y s c ci f P N = true := by
  unfold wit4PK
  unfold wit4RK at h
  rw [hc, Bool.true_and]
  exact h

theorem tabsK_of_sqs {N : ℕ} {T SQ : ℕ → ℕ} (h : sqsK n w N T SQ = true) :
    tabsK n w N T SQ (fun i => pinvS n w (mask w) (T i)) = true := by
  unfold sqsK at h
  unfold tabsK
  rw [allNP_iff] at h ⊢
  intro i hi
  rw [h i hi, Nat.beq_refl, Bool.true_and]

theorem q8WitFreeK_of_P2 {N nc nm ID : ℕ} {T SQ D C CI MK MZ R RM RF RO RN : ℕ → ℕ}
    (hsz : szOK n w = true) (hT : ∀ i < N, PP n w (T i)) (hS : ∀ i < N, Cn n w (SQ i))
    (hC : ∀ k < nc, Cn n w (C k)) (hCI : ∀ k < nc, Cn n w (CI k)) (hID : ID = pidn n w)
    (hM : commTabK n w N nc nm SQ C MK MZ = true)
    (h : q8WitFreeP2 n w N ID T SQ D nm C CI MK MZ R RM RF RO RN = true) :
    q8WitFreeK n w N T SQ (fun i => pinvS n w (mask w) (T i)) nc C CI = true := by
  unfold commTabK at hM
  rw [allNP_iff] at hM
  unfold q8WitFreeP2 at h
  unfold q8WitFreeK
  rw [allNP_iff] at h ⊢
  intro i hi
  have hi' := h i hi
  rw [strictB_eqQ] at hi'
  simp only [Bool.or_eq_true] at hi' ⊢
  rcases hi' with (hi' | hi') | hi'
  · rw [← hID]
    exact Or.inl (Or.inl hi')
  · left
    right
    unfold sq4K at hi'
    simp only [Bool.and_eq_true] at hi'
    obtain ⟨⟨-, hp⟩, hne⟩ := hi'
    have hp' := Nat.blt_eq.mp hp
    rw [Bool.not_eq_true']
    refine beq_false_of_pg (w := w) (i := Nat.sub (D i) 1) ?_
    rw [pg_pcomp' (hS i hi) hp', pg_pidn' hsz hp']
    exact not_beq hne
  right
  rw [strictB_eqQ, strictB_eqQ, allNP_iff] at hi'
  rw [allNP_iff]
  intro j hj
  have hj' := hi' j hj
  simp only [Bool.or_eq_true] at hj' ⊢
  rcases hj' with hj' | hj'
  · exact Or.inl (Or.inl hj')
  generalize fldK 14 (R i) j = v at hj'
  unfold pairP2 at hj'
  cases hv : Nat.ble v 8192
  · rw [hv, cond_false] at hj'
    simp only [Bool.and_eq_true] at hj'
    obtain ⟨⟨hm, hz⟩, hw4⟩ := hj'
    have hm' := Nat.blt_eq.mp hm
    have hMm := hM _ hm'
    simp only [Bool.and_eq_true] at hMm
    obtain ⟨⟨hk, -⟩, hcomm⟩ := hMm
    have hk' := Nat.blt_eq.mp hk
    rw [Nat.eq_of_beq_eq_true hz] at hcomm
    right
    rw [anyNP_eq, List.any_eq_true]
    refine ⟨MK (RM (Nat.sub v 8193)), List.mem_range.2 hk', ?_⟩
    rw [Bool.or_eq_true]
    exact Or.inl (wit4K_of_P hsz (hT i hi).1 (hT j hj).1 (hS i hi) (hC _ hk') (hCI _ hk')
      (wit4PK_of_R hcomm hw4))
  · rw [hv, cond_true] at hj'
    simp only [Bool.and_eq_true] at hj'
    obtain ⟨⟨-, hp⟩, hne⟩ := hj'
    have hp' := Nat.blt_eq.mp hp
    left
    right
    rw [Bool.not_eq_true']
    exact beq_false_of_xyx (hT i hi) (hT j hj).1 hp' hne

end CFSG.KC.Q8Wit

end
