module

public import Certificates.Data.Kernel.S1277KSv
public import CFSG.Certificates.Kernel.S1277KSigSound
public import CFSG.Certificates.Kernel.S1277KCandSound
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSSurv

public section

namespace CFSG.KS.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Gm
  CFSG.KC.S1277Sv CFSG.KC.Enum CFSG.KS.S1277Lat CFSG.KS.S1277Mod CFSG.KS.S1277Sig
  CFSG.KS.S1277Gm CFSG.KS.S1277Cand CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Surv
  Certificates.Data.S1277Sig

theorem appP_eq_app6 (x v : ℕ) : appP x v = app6 x v := by
  simp only [appP, app6, Nat.shiftRight_eq_div_pow, mul_mod_two_eq]
  norm_num [Nat.div_div_eq_div_mul, Nat.xor_assoc]

theorem mulQ_eq (x y : ℕ) : mulQ x y = mulS x y := by
  simp only [mulQ, mulS, appP_eq_app6, Nat.shiftRight_eq_div_pow]

theorem oneQ_eq : oneQ = oneS := rfl

theorem sixteen_dvd {Γ : Type} [Group Γ] [Finite Γ] {R P : Subgroup Γ} (hPR : P ≤ R)
    (hP : Nat.card P = 8) {x : Γ} (hxR : x ∈ R) (hxP : x ∉ P) (hx2 : x * x ∈ P)
    (hn : ∀ p ∈ P, x * p * x⁻¹ ∈ P) : 16 ∣ Nat.card R := by
  classical
  have hn' : ∀ p ∈ P, x⁻¹ * p * x ∈ P := by
    intro p hp
    have e : x⁻¹ * p * x = (x * x)⁻¹ * (x * p * x⁻¹) * (x * x) := by group
    rw [e]
    exact P.mul_mem (P.mul_mem (P.inv_mem hx2) (hn p hp)) hx2
  let X : Subgroup Γ :=
    { carrier := {y | y ∈ P ∨ x⁻¹ * y ∈ P}
      one_mem' := Or.inl P.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (P.mul_mem ha hb)
        · right
          have e : x⁻¹ * (a * b) = (x⁻¹ * a * x) * (x⁻¹ * b) := by group
          rw [e]
          exact P.mul_mem (hn' a ha) hb
        · right
          have e : x⁻¹ * (a * b) = (x⁻¹ * a) * b := by group
          rw [e]
          exact P.mul_mem ha hb
        · left
          have e : a * b = (x * x) * (x⁻¹ * (x⁻¹ * a) * x) * (x⁻¹ * b) := by group
          rw [e]
          exact P.mul_mem (P.mul_mem hx2 (hn' _ ha)) hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (P.inv_mem ha)
        · right
          have e : x⁻¹ * a⁻¹ = (x⁻¹ * (x⁻¹ * a)⁻¹ * x) * (x * x)⁻¹ := by group
          rw [e]
          exact P.mul_mem (hn' _ (P.inv_mem ha)) (P.inv_mem hx2) }
  have hXR : X ≤ R := by
    rintro y (hy | hy)
    · exact hPR hy
    · have e : y = x * (x⁻¹ * y) := by group
      rw [e]
      exact R.mul_mem hxR (hPR hy)
  have hxp : ∀ p ∈ P, x * p ∉ P := by
    intro p hp h
    apply hxP
    have e : x = x * p * p⁻¹ := by group
    rw [e]
    exact P.mul_mem h (P.inv_mem hp)
  let f : ↥P ⊕ ↥P → ↥X := fun s => match s with
    | .inl p => ⟨p.1, Or.inl p.2⟩
    | .inr p => ⟨x * p.1, Or.inr (by rw [← mul_assoc, inv_mul_cancel, one_mul]; exact p.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [f, Subtype.mk.injEq] at h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact absurd (h ▸ a.2) (hxp b.1 b.2)
      · exact absurd (h.symm ▸ b.2) (hxp a.1 a.2)
      · exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h))
    · rintro ⟨y, hy | hy⟩
      · exact ⟨.inl ⟨y, hy⟩, rfl⟩
      · refine ⟨.inr ⟨x⁻¹ * y, hy⟩, ?_⟩
        simp only [f, Subtype.mk.injEq]
        group
  have hX : Nat.card X = 16 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, hP]
  rw [← hX]
  exact Subgroup.card_dvd_of_le hXR

section P

variable {φ : ℕ → ℕ} {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))}

theorem incL_nodup : ∀ (l : List ℕ) (b : ℕ), incL b l = true → (∀ a ∈ l, b < a) ∧ l.Nodup
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩
  | a :: l, b, h => by
    have h' : Nat.blt b a = true ∧ incL a l = true := by
      rw [← Bool.and_eq_true]
      exact h
    obtain ⟨h1, h2⟩ := incL_nodup l a h'.2
    have hba : b < a := by simpa using h'.1
    refine ⟨fun c hc => ?_, List.nodup_cons.2 ⟨fun ha => absurd (h1 a ha) (lt_irrefl a), h2⟩⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hba
    · exact hba.trans (h1 c hc)

noncomputable def pSub (hR : R ≤ Sig 6 φ) {sl pl pi : List ℕ} (hpl : ∀ y ∈ pl, pkSet R y)
    (h : pChk sl pl pi = true) : Subgroup (Equiv.Perm (Fin (2 ^ 6))) where
  carrier := {σ | σ ∈ R ∧ pk σ ∈ pl}
  one_mem' := by
    refine ⟨R.one_mem, ?_⟩
    rw [pChk] at h
    simp only [Bool.and_eq_true] at h
    rw [pk_one, ← oneQ_eq]
    exact memL_iff.1 h.1.1.1.2
  mul_mem' := by
    rintro σ τ ⟨hσ, hσp⟩ ⟨hτ, hτp⟩
    refine ⟨R.mul_mem hσ hτ, ?_⟩
    rw [pChk] at h
    simp only [Bool.and_eq_true] at h
    rw [pk_mul (hR hσ).1, ← mulQ_eq]
    exact memL_iff.1 ((allL_iff.1 ((allL_iff.1 h.1.1.2) _ hσp)) _ hτp)
  inv_mem' := by
    rintro σ ⟨hσ, hσp⟩
    rw [pChk] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨i, hi, hiσ⟩ := List.getElem_of_mem hσp
    have hlen := Nat.eq_of_beq_eq_true h.1.1.1.1.1
    have hinv := Nat.eq_of_beq_eq_true ((allL_iff.1 h.1.2) i (List.mem_range.2 (by omega)))
    have hgi : pl.getD i 0 = pk σ := by rw [List.getD_eq_getElem _ _ hi, hiσ]
    rw [hgi] at hinv
    by_cases hj : pi.getD i 0 < pl.length
    · rw [List.getD_eq_getElem _ _ hj] at hinv
      obtain ⟨τ, hτ, hτp⟩ := hpl _ (List.getElem_mem hj)
      rw [← hτp, mulQ_eq, ← pk_mul (hR hσ).1, oneQ_eq, ← pk_one] at hinv
      have h1 : σ * τ = 1 :=
        pk_injective (hR (R.mul_mem hσ hτ)) (Sig 6 φ).one_mem hinv
      rw [inv_eq_of_mul_eq_one_right h1]
      exact ⟨hτ, hτp ▸ List.getElem_mem hj⟩
    · rw [List.getD_eq_default _ _ (by omega)] at hinv
      exfalso
      revert hinv
      simp [mulQ, appP, oneQ]

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem pkSet_mulQ (hR : R ≤ Sig 6 φ) {x y : ℕ} (hx : pkSet R x) (hy : pkSet R y) :
    pkSet R (mulQ x y) := by
  rw [mulQ_eq]
  exact pkSet_mul hR hx hy

theorem wordQ_mem (hR : R ≤ Sig 6 φ) {gl : List ℕ} (hgl : ∀ g ∈ gl, pkSet R g) :
    ∀ (w : List ℕ), (∀ j ∈ w, j < gl.length) → pkSet R (wordQ gl w) := by
  have key : ∀ (w : List ℕ), (∀ j ∈ w, j < gl.length) → ∀ x, pkSet R x →
      pkSet R (List.rec (motive := fun _ => ℕ → ℕ) (fun x => x)
        (fun j _ ih x => strictN (mulQ x (gl.getD j 0)) ih) w x) := by
    intro w
    induction w with
    | nil => intro _ x hx; exact hx
    | cons j w ih =>
      intro hw x hx
      change pkSet R (strictN (mulQ x (gl.getD j 0)) (List.rec (motive := fun _ => ℕ → ℕ)
        (fun x => x) (fun j _ ih x => strictN (mulQ x (gl.getD j 0)) ih) w))
      rw [strictN_eq]
      refine ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _ (pkSet_mulQ hR hx ?_)
      have hj := hw j List.mem_cons_self
      rw [List.getD_eq_getElem _ _ hj]
      exact hgl _ (List.getElem_mem hj)
  intro w hw
  exact key w hw oneQ (oneQ_eq ▸ pkSet_one)

theorem not_witX (hR : R ≤ Sig 6 φ) {sl pl pi : List ℕ} (hpl : ∀ y ∈ pl, pkSet R y)
    (h : pChk sl pl pi = true) (h16 : ¬ 16 ∣ Nat.card R) {x : ℕ} (hx : pkSet R x)
    (hw : witX pl x = true) : False := by
  classical
  let P := pSub hR hpl h
  have hPR : P ≤ R := fun σ hσ => hσ.1
  have hpP : ∀ y, pkSet P y ↔ y ∈ pl := by
    intro y
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact hσ.2
    · intro hy
      obtain ⟨σ, hσ, rfl⟩ := hpl y hy
      exact ⟨σ, ⟨hσ, hy⟩, rfl⟩
  have hPc : Nat.card P = 8 := by
    rw [pChk] at h
    simp only [Bool.and_eq_true] at h
    rw [card_range_eq_of_pkSet (hPR.trans hR) (incL_nodup pl 0 h.1.1.1.1.2).2 hpP]
    exact Nat.eq_of_beq_eq_true h.1.1.1.1.1
  obtain ⟨ξ, hξ, rfl⟩ := hx
  rw [witX, witY] at hw
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨hnot, hsq⟩, hnorm⟩ := hw
  refine h16 (sixteen_dvd hPR hPc hξ ?_ ?_ ?_)
  · intro hP
    have := memL_iff.2 hP.2
    rw [hnot] at this
    exact absurd this (by simp)
  · refine ⟨R.mul_mem hξ hξ, ?_⟩
    rw [pk_mul (hR hξ).1, ← mulQ_eq]
    exact memL_iff.1 hsq
  · intro p hp
    have h1 := memL_iff.1 ((allL_iff.1 hnorm) _ hp.2)
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 h1
    obtain ⟨τ, hτ, rfl⟩ := (hpP q).2 hq
    rw [mulQ_eq, mulQ_eq, ← pk_mul (hR hξ).1, ← pk_mul (hR (hPR hτ)).1] at hqe
    have h2 : τ * ξ = ξ * p := pk_injective (hR (R.mul_mem (hPR hτ) hξ))
      (hR (R.mul_mem hξ (hPR hp))) hqe
    have e : ξ * p * ξ⁻¹ = τ := by
      rw [← h2]
      group
    rw [e]
    exact hτ

theorem not_witQ (hR : R ≤ Sig 6 φ) {sl pl pi : List ℕ} (hpl : ∀ y ∈ pl, pkSet R y)
    (h : pChk sl pl pi = true) (h16 : ¬ 16 ∣ Nat.card R) {gl w : List ℕ}
    (hgl : ∀ g ∈ gl, pkSet R g) (hw : witQ pl gl w = true) : False := by
  rw [witQ, Bool.and_eq_true, strictB_eq] at hw
  exact not_witX hR hpl h h16
    (wordQ_mem hR hgl w fun j hj => by simpa using (allL_iff.1 hw.1) j hj) hw.2

theorem treeQ_mem (hR : R ≤ Sig 6 φ) {el par lt dp gl : List ℕ}
    (h : treeQ el par lt dp gl = true) (hgl : ∀ g ∈ gl, pkSet R g) : ∀ a ∈ el, pkSet R a := by
  have key : ∀ n i, dp.getD i 0 < n → i < el.length → pkSet R (el.getD i 0) := by
    intro n
    induction n with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ n ih =>
      intro i hi hil
      have hc := (allL_iff.1 h) i (List.mem_range.2 hil)
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hc
      rcases hc with h1 | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · rw [Nat.eq_of_beq_eq_true h1, oneQ_eq]
        exact pkSet_one
      · rw [← Nat.eq_of_beq_eq_true h4]
        refine pkSet_mulQ hR (ih _ (by omega) h1) ?_
        rw [List.getD_eq_getElem _ _ h2]
        exact hgl _ (List.getElem_mem h2)
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  rw [← List.getD_eq_getElem _ 0 hi]
  exact key _ i (Nat.lt_succ_self _) hi

end P

end CFSG.KS.S1277Sv

end
