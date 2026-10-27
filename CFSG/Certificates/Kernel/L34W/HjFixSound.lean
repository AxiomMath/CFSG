module

public import Certificates.Data.Kernel.L34W.HjFix
public import Certificates.Data.GrSLitL34FactsCF23HeFixCheck
public import CFSG.Certificates.Kernel.L34W.FixSound

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.ComponentClassification.GSThmB.CF23L34

theorem inKB_1285 : ∀ a b : ZMod 4,
    inKB (kbOfMask 1285) a b = (a.val % 2 == 0 && b.val % 2 == 0) := by
  decide

theorem eqC2_eq (x y : MElt) : eqC2 x y = eqKB (kbOfMask 1285) x y := by
  unfold eqC2 eqKB
  rw [inKB_1285, Bool.and_assoc]

theorem eqC_1285 (x y : ℕ) : eqC 1285 x y = eqC2 (dec x) (dec y) := by
  rw [eqC_eq, eqC2_eq]

theorem dec_one : dec 1 = hjTau := by decide

theorem hjGood_eq : hjGood = [dec 68, dec 133, dec 197] := by decide

variable {T A G Y : ℕ → ℕ}

theorem sq1M_eq (hG : GensG G) (hy : yOK G Y = true) {t i : ℕ} (ht : t < 64) (hi : i < 36) :
    sq1M t i = invPt 42 6 (Y (64 * i + t)) := by
  obtain ⟨hc, he⟩ := yK_eq hG t hi
  have e : sq1M t i = (comp 42 (yTab t i) (yTab t i) == idTab 42) := rfl
  rw [e, Y_eq hy ht hi, he]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, CFSG.KC.L34KSnd.invPt_iff hc]

theorem tg_ne (hG : GensG G) (hy : yOK G Y = true) {k : ℕ} (hk : k < 64)
    (h : bNot (Nat.beq (Y k) (pidn 42 6)) = true) : (wordTab (tg k) == idTab 42) = false := by
  have e := Y_eq hy hk (by norm_num : 0 < 36)
  rw [Nat.mul_zero, Nat.zero_add] at e
  obtain ⟨hc, he⟩ := yK_eq hG k (by norm_num : 0 < 36)
  have hr := tabRep_yTab (t := k) (by norm_num : 0 < 36)
  cases hb : (wordTab (tg k) == idTab 42)
  · rfl
  · exfalso
    have h1 : wordPerm (tg k) = 1 := ((tabRep_wordTab (tg k)).beq_iff TabRep.idTab).1 hb
    have hp : repPerm 0 = 1 := rfl
    have h2 : yTab k 0 = idTab 42 := (hr.eq_iff TabRep.idTab).2 (by rw [yPerm, h1, hp, one_mul])
    rw [he, CFSG.KC.L34KSnd.unpack_eq_idTab_iff hc] at h2
    rw [e, h2, bNot_iff, Nat.beq_refl] at h
    exact Bool.noConfusion h

theorem lab_spec (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) {g gi i' t i c k : ℕ}
    (ht : t < 64) (hi : i < 36) (hc : c < 1024) (hk : (dec c).1 = k)
    (hw : (wordTab (tg k) == idTab 42) = false)
    (eb : ∀ x, betaW T A g gi i' x = betaC T A t i x) (h : hjLab T A g gi i' c = true) :
    (!(wordTab (tg (dec c).1) == idTab 42) && eqC2 (mulM (dec c) (dec c)) oneM &&
      eqC2 (betaYM t i (dec c)) (dec c)) = true := by
  unfold hjLab at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [eqC_1285, dec_mulC hT hc hc, dec_zero] at h1
  rw [eb, eqC_1285, dec_betaC hT hA hb ht hi hc] at h2
  rw [hk, hw, h1, h2]
  rfl

theorem one_spec (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) (w4 : (wordTab (tg 4) == idTab 42) = false)
    (w8 : (wordTab (tg 8) == idTab 42) = false) (w12 : (wordTab (tg 12) == idTab 42) = false)
    {t i : ℕ} (ht : t < 64) (hi : i < 36) (h : hjOne T A Y (64 * i + t) = true) :
    (!sq1M t i || !eqC2 (betaYM t i hjTau) hjTau || hjFixM t i) = true := by
  rw [sq1M_eq hG hy ht hi]
  unfold hjOne at h
  simp only [strictB_eq] at h
  rcases bIf_iff.1 h with ⟨hq, h⟩ | ⟨hq, -⟩
  swap
  · rw [hq]
    rfl
  rw [hq]
  generalize hg : Nat.mul (nat_lit 16) (Nat.mod (64 * i + t) (nat_lit 64)) = g at h
  generalize hi' : Nat.div (64 * i + t) (nat_lit 64) = i' at h
  have e1 : (64 * i + t) % 64 = t := by omega
  have e2 : (64 * i + t) / 64 = i := by omega
  have eb : ∀ x, betaW T A g (invC T g) i' x = betaC T A t i x := by
    intro x
    subst hg hi'
    unfold betaC
    change betaW T A (16 * ((64 * i + t) % 64)) (invC T (16 * ((64 * i + t) % 64)))
      ((64 * i + t) / 64) x = _
    rw [e1, e2]
    rfl
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨hτ, -⟩
  · have key : hjFixM t i = true := by
      unfold hjFixM
      rw [hjGood_eq]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rcases bIf_iff.1 h with ⟨h68, -⟩ | ⟨-, h⟩
      · rw [lab_spec hT hA hb ht hi (by norm_num) (by decide) w4 eb h68]
        rfl
      rcases bIf_iff.1 h with ⟨h133, -⟩ | ⟨-, h197⟩
      · rw [lab_spec hT hA hb ht hi (by norm_num) (by decide) w8 eb h133]
        simp
      · rw [lab_spec hT hA hb ht hi (by norm_num) (by decide) w12 eb h197]
        simp
    rw [key]
    simp
  · rw [eb, eqC_1285, dec_betaC hT hA hb ht hi (by norm_num), dec_one] at hτ
    rw [hτ]
    rfl

theorem hjFixOK_of (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) (h : hjK T A Y = true) : hjFixOK = true := by
  unfold hjK at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨h4, h8, h12⟩, hall⟩ := h
  have w4 := tg_ne hG hy (by norm_num) h4
  have w8 := tg_ne hG hy (by norm_num) h8
  have w12 := tg_ne hG hy (by norm_num) h12
  unfold hjFixOK
  simp only [List.all_eq_true, List.mem_range]
  intro i hi t ht
  exact one_spec hT hA hb hG hy w4 w8 w12 ht hi (allN_spec hall (64 * i + t) (by omega))

end CFSG.KC.L34W

end
