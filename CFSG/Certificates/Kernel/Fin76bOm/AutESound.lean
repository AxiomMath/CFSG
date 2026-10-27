module

public import Certificates.Data.Kernel.Fin76bOm.AutE
public import CFSG.Certificates.Kernel.Fin76bAut.Card
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.AutETable

theorem autEFact_of_fixAll {H : Type*} [Group H]
    (h : ∀ b a : MulAut H, b ^ 3 = 1 → b ≠ 1 → a * b = b * a → (∀ e, b e = e → a e = e) →
      ∃ d, b d = d ∧ ∃ j : ℕ, ∀ e, a e = d * (b ^ j) e * d⁻¹) : AutEFact H := by
  intro b a hb3 hb1 hab ⟨d, hd, hin⟩
  have hba : ∀ x, a (b x) = b (a x) := fun x => by
    have := congrArg (fun f : MulAut H => f x) hab
    simpa only [MulAut.mul_apply] using this
  let a' := MulAut.conj d⁻¹ * a
  have ha' : ∀ x, a' x = d⁻¹ * a x * d := fun x => by
    simp [a', MulAut.conj_apply]
  have hcomm : a' * b = b * a' := by
    ext x
    simp only [MulAut.mul_apply]
    rw [ha', ha', hba, map_mul, map_mul, map_inv, hd]
  have hfix : ∀ e, b e = e → a' e = e := fun e he => by
    rw [ha', hin e he]
    group
  obtain ⟨d', hd', j, hj⟩ := h b a' hb3 hb1 hcomm hfix
  refine ⟨d * d', by rw [map_mul, hd, hd'], j, fun e => ?_⟩
  have ha : a e = d * a' e * d⁻¹ := by
    rw [ha']
    group
  rw [ha, hj]
  group

theorem eAnyN_spec {n : ℕ} {f : ℕ → Bool} (h : eAnyN n f = true) : ∃ i < n, f i = true := by
  by_contra hc
  push Not at hc
  have hall : allN n (fun i => bIf(f i, false, true)) = true :=
    allN_iff.2 fun i hi => by rw [Bool.eq_false_iff.2 (hc i hi)]
  unfold eAnyN at h
  rw [hall] at h
  exact Bool.false_ne_true h

theorem eAEK_spec {ET : ℕ → ℕ} {cnt : ℕ} {T : ℕ → ℕ} (h : eAEK ET cnt T = true) {i k : ℕ}
    (hi : i < cnt) (hk : k < cnt) (hcube : ∀ a < 32, eG (T i) (eG (T i) (eG (T i) a)) = a)
    (hne : ∃ a < 32, eG (T i) a ≠ a) (hfix : ∀ x < 32, eG (T i) x = x → eG (T k) x = x)
    (hcomm : ∀ x < 32, eG (T i) (eG (T k) x) = eG (T k) (eG (T i) x)) :
    ∃ d < 32, eG (T i) d = d ∧ ∃ j < 3, ∀ e < 32,
      eMul ET (eG (T k) e) d = eMul ET d (eAEPw (T i) j e) := by
  have hc : eAECube (T i) = true := allN_iff.2 fun a ha => beq_t.2 (hcube a ha)
  have hid : eAEId (T i) = false := by
    obtain ⟨a, ha, hne⟩ := hne
    cases h' : eAEId (T i)
    · rfl
    · exact absurd (beq_t.1 (allN_iff.1 h' a ha)) hne
  have hf : eAEFix (T i) (T k) = true := allN_iff.2 fun x hx => by
    cases hb : Nat.beq (eG (T i) x) x
    · rfl
    · exact beq_t.2 (hfix x hx (beq_t.1 hb))
  have hm : eAEComm (T i) (T k) = true := allN_iff.2 fun x hx => beq_t.2 (hcomm x hx)
  have h1 := allN_iff.1 h i hi
  simp only [strictB_eq, hc, hid, bIf_eq, if_true, Bool.false_eq_true, ↓reduceIte] at h1
  have h2 := allN_iff.1 h1 k hk
  simp only [strictB_eq, hf, hm, bIf_eq, if_true] at h2
  unfold eAEConc at h2
  obtain ⟨d, hd, hd2⟩ := eAnyN_spec h2
  simp only [bAnd_eq, Bool.and_eq_true] at hd2
  obtain ⟨j, hj, hj2⟩ := eAnyN_spec hd2.2
  exact ⟨d, hd, beq_t.1 hd2.1, j, hj, fun e he => beq_t.1 (allN_iff.1 hj2 e he)⟩

open CFSG.KC.Fin76bU in
theorem eAEIsoU_spec {R P Q : ℕ} (h : eAEIsoU R P Q = true) :
    fldU 5 R 0 = 0 ∧
      (∀ a < 32, ∀ b < 32, fldU 5 R (mU P a b) = mU Q (fldU 5 R a) (fldU 5 R b)) ∧
      ∀ a < 32, ∀ b < 32, fldU 5 R a = fldU 5 R b → a = b := by
  unfold eAEIsoU at h
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff] at h
  refine ⟨beq_t.1 h.1, fun a ha b hb => beq_t.1 (h.2 a ha b hb).1, fun a ha b hb hab => ?_⟩
  have h2 := (h.2 a ha b hb).2
  rw [beq_t.2 hab] at h2
  exact beq_t.1 h2

theorem autEFact_of_eAEK {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H}
    (R : Realizes H 32 M elt) {ET : ℕ → ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
    {cnt : ℕ} {T : ℕ → ℕ} (hrec : ∀ φ : MulAut H, ∃ i < cnt, ∀ a < 32, sg R φ a = eG (T i) a)
    (h : eAEK ET cnt T = true) : AutEFact H := by
  have hmul : ∀ x y, x < 32 → y < 32 → elt (eMul ET x y) = elt x * elt y := fun x y hx hy => by
    rw [← hM x hx y hy]
    exact R.mul x y hx hy
  refine autEFact_of_fixAll fun b a hb3 hb1 hab hfix => ?_
  obtain ⟨i, hi, hbi⟩ := hrec b
  obtain ⟨k, hk, hak⟩ := hrec a
  have lb : ∀ x < 32, eG (T i) x < 32 := fun x hx => by
    rw [← hbi x hx]
    exact sg_lt R b x
  have la : ∀ x < 32, eG (T k) x < 32 := fun x hx => by
    rw [← hak x hx]
    exact sg_lt R a x
  have eb : ∀ x < 32, elt (eG (T i) x) = b (elt x) := fun x hx => by
    rw [← hbi x hx]
    exact sg_elt R b x
  have ea : ∀ x < 32, elt (eG (T k) x) = a (elt x) := fun x hx => by
    rw [← hak x hx]
    exact sg_elt R a x
  have hcube : ∀ x < 32, eG (T i) (eG (T i) (eG (T i) x)) = x := by
    intro x hx
    apply R.inj _ _ (lb _ (lb _ (lb x hx))) hx
    rw [eb _ (lb _ (lb x hx)), eb _ (lb x hx), eb x hx]
    have := congrArg (fun f : MulAut H => f (elt x)) hb3
    simpa only [pow_three, MulAut.mul_apply, MulAut.one_apply] using this
  have hne : ∃ x < 32, eG (T i) x ≠ x := by
    by_contra hc
    push Not at hc
    apply hb1
    ext y
    obtain ⟨x, hx, rfl⟩ := R.surj y
    rw [← eb x hx, hc x hx, MulAut.one_apply]
  have hfix' : ∀ x < 32, eG (T i) x = x → eG (T k) x = x := by
    intro x hx hxx
    apply R.inj _ _ (la x hx) hx
    rw [ea x hx]
    apply hfix
    rw [← eb x hx, hxx]
  have hcomm' : ∀ x < 32, eG (T i) (eG (T k) x) = eG (T k) (eG (T i) x) := by
    intro x hx
    apply R.inj _ _ (lb _ (la x hx)) (la _ (lb x hx))
    rw [eb _ (la x hx), ea x hx, ea _ (lb x hx), eb x hx]
    have := congrArg (fun f : MulAut H => f (elt x)) hab
    simp only [MulAut.mul_apply] at this
    exact this.symm
  have hpw : ∀ j, ∀ x < 32, eAEPw (T i) j x < 32 ∧ elt (eAEPw (T i) j x) = (b ^ j) (elt x) := by
    intro j x hx
    induction j with
    | zero => exact ⟨hx, by rw [pow_zero, MulAut.one_apply]; rfl⟩
    | succ j ih =>
      have hs : eAEPw (T i) (j + 1) x = eG (T i) (eAEPw (T i) j x) := rfl
      rw [hs]
      exact ⟨lb _ ih.1, by rw [eb _ ih.1, ih.2, pow_succ', MulAut.mul_apply]⟩
  obtain ⟨d, hd, hdfix, j, -, he⟩ := eAEK_spec h hi hk hcube hne hfix' hcomm'
  refine ⟨elt d, by rw [← eb d hd, hdfix], j, fun y => ?_⟩
  obtain ⟨e, he', rfl⟩ := R.surj y
  have hkey := congrArg elt (he e he')
  rw [hmul _ _ (la e he') hd, hmul _ _ hd (hpw j e he').1, ea e he', (hpw j e he').2] at hkey
  exact eq_mul_inv_of_mul_eq hkey

end CFSG.KS.EAut

end
