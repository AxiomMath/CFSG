
module

public import Certificates.Data.Kernel.L34Cov.Sigma
public import CFSG.Certificates.Kernel.L34W.FixSound
public import CFSG.Certificates.Kernel.L34Cov.CodesSound
import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.L34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
open Pointwise

variable {G Y : ℕ → ℕ}

theorem pg_of_tabRep {p : ℕ} {g : Equiv.Perm (Fin 42)} (h : TabRep (unpack 42 6 p) g) (x : Fin 42) :
    pg 6 (mask 6) p x.val = (g x).val := by
  rw [← CFSG.KC.BfsPin.unpack_get' x.isLt]
  exact h.apply x

theorem wordK_eq (hG : GensG G) (w : List ℕ) :
    Cn (pword (gS G) w (pidn 42 6)) ∧ TabRep (unpack 42 6 (pword (gS G) w (pidn 42 6))) (wordPerm w) := by
  have h : Cn (pword (gS G) w (pidn 42 6)) ∧ wordTab w = unpack 42 6 (pword (gS G) w (pidn 42 6)) := by
    unfold wordTab
    rw [idTab42]
    exact pword_spec (gS G) genT w _ cn_pidn fun j _ => genT_gS hG j
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  exact tabRep_wordTab w

theorem repPerm_zero : repPerm 0 = 1 := rfl

theorem tabRep_Y0 (hG : GensG G) (hy : yOK G Y = true) {t : ℕ} (ht : t < 64) :
    Cn (Y t) ∧ TabRep (unpack 42 6 (Y t)) (wordPerm (tg t)) := by
  have h := tabRep_Y hG hy ht (show 0 < 36 by norm_num)
  rw [show 64 * 0 + t = t by omega, yPerm, repPerm_zero, mul_one] at h
  exact h

theorem tabRep_repK (hG : GensG G) {i : ℕ} (hi : i < 36) :
    Cn (repK G i) ∧ TabRep (unpack 42 6 (repK G i)) (repPerm i) := by
  obtain ⟨c, e⟩ := repK_eq hG hi
  refine ⟨c, ?_⟩
  rw [← e]
  exact tabRep_repTab hi

theorem eq_of_beq_unpack {p q r s : ℕ} {g h : Equiv.Perm (Fin 42)} (hp : Cn p) (hq : Cn q) (hr : Cn r)
    (hs : Cn s) (rp : TabRep (unpack 42 6 p) g) (rq : TabRep (unpack 42 6 q) h)
    {g' h' : Equiv.Perm (Fin 42)} (rr : TabRep (unpack 42 6 r) g') (rs : TabRep (unpack 42 6 s) h')
    (e : Nat.beq (pcomp 42 6 (mask 6) p q) (pcomp 42 6 (mask 6) r s) = true) : g * h = g' * h' := by
  have e1 := congrArg (unpack 42 6) (Nat.eq_of_beq_eq_true e)
  rw [← CFSG.KC.L34KSnd.comp_unpack' hp hq, ← CFSG.KC.L34KSnd.comp_unpack' hr hs] at e1
  exact ((rp.comp rq).eq_iff (rr.comp rs)).1 e1

theorem decL_lift : ∀ c < 4, FreeGroup.lift genAB (FreeGroup.mk [decL c]) =
    if c = 0 then aS else if c = 1 then aS⁻¹ else if c = 2 then bS else bS⁻¹ := by
  intro c hc
  interval_cases c
  · rw [show decL 0 = ((0 : Fin 2), true) from rfl, lift_genAB_single]
    simp [genAB]
  · rw [show decL 1 = ((0 : Fin 2), false) from rfl, lift_genAB_single]
    simp [genAB]
  · rw [show decL 2 = ((1 : Fin 2), true) from rfl, lift_genAB_single]
    simp [genAB]
  · rw [show decL 3 = ((1 : Fin 2), false) from rfl, lift_genAB_single]
    simp [genAB]

theorem abPerm_cons (c : ℕ) (w : List ℕ) : abPerm ((c :: w).map decL) =
    FreeGroup.lift genAB (FreeGroup.mk [decL c]) * abPerm (w.map decL) := by
  rw [abPerm, abPerm, List.map_cons, ← List.singleton_append, ← FreeGroup.mul_mk, map_mul]

theorem abPerm_nil : abPerm (([] : List ℕ).map decL) = 1 := by
  rw [List.map_nil, abPerm, ← FreeGroup.one_eq_mk, map_one]

theorem pword_ab {AB : ℕ → ℕ} (hAB : ∀ c < 4, Cn (AB c) ∧
    TabRep (unpack 42 6 (AB c)) (FreeGroup.lift genAB (FreeGroup.mk [decL c]))) :
    ∀ (w : List ℕ) (p : ℕ) (g : Equiv.Perm (Fin 42)), (∀ c ∈ w, c < 4) → Cn p →
      TabRep (unpack 42 6 p) g →
        Cn (pword AB w p) ∧ TabRep (unpack 42 6 (pword AB w p)) (g * abPerm (w.map decL))
  | [], p, g, _, hp, hg => by
    rw [abPerm_nil, mul_one]
    exact ⟨hp, hg⟩
  | c :: w, p, g, hw, hp, hg => by
    obtain ⟨hc, rc⟩ := hAB c (hw c List.mem_cons_self)
    rw [pword_cons]
    have h2 : TabRep (unpack 42 6 (pcomp 42 6 (mask 6) p (AB c)))
        (g * FreeGroup.lift genAB (FreeGroup.mk [decL c])) := by
      rw [← CFSG.KC.L34KSnd.comp_unpack' hp hc]
      exact hg.comp rc
    have ih := pword_ab hAB w _ _ (fun c' h' => hw c' (List.mem_cons_of_mem _ h'))
      (CFSG.KC.BfsPin.canonK_pcomp hp hc) h2
    rw [abPerm_cons, ← mul_assoc]
    exact ih

theorem inv_of_invOK {g gi : ℕ} {x : Equiv.Perm (Fin 42)} (hg : Cn g) (rg : TabRep (unpack 42 6 g) x)
    (h : sgInvOK g gi = true) : Cn gi ∧ TabRep (unpack 42 6 gi) x⁻¹ := by
  unfold sgInvOK at h
  rw [bAnd_iff] at h
  have hc : Cn gi := h.1
  have e : pcomp 42 6 (mask 6) g gi = pidn 42 6 := Nat.eq_of_beq_eq_true h.2
  exact ⟨hc, rg.inv (CFSG.KC.L34KSnd.size_unpack _) (CFSG.KC.L34KSnd.comp_inv_of_pcomp hg hc e)⟩

theorem conj_of_mul {H : Type*} [Group H] {r s t : H} (h : 1 * s * r = r * t) : s = r * t * r⁻¹ := by
  rw [one_mul] at h
  rw [← h, mul_inv_cancel_right]

theorem ab_spec (hG : GensG G) {AB : ℕ → ℕ} {UA UB : List (List ℕ)} (h : sgAbOK G AB UA UB = true)
    (hA : ∀ i, uA i = (UA.getD i []).map decL ∧ codesOK (UA.getD i []) = true)
    (hB : ∀ i, uB i = (UB.getD i []).map decL ∧ codesOK (UB.getD i []) = true) {i : ℕ}
    (hi : i < 36) :
    abPerm (uA i) = repPerm i * aS * (repPerm i)⁻¹ ∧ abPerm (uB i) = repPerm i * bS * (repPerm i)⁻¹ := by
  unfold sgAbOK at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨h0, h2⟩, ⟨h1, h3⟩, hc⟩ := h
  have e0 : AB 0 = pword (gS G) wa (pidn 42 6) := Nat.eq_of_beq_eq_true h0
  have e2 : AB 2 = pword (gS G) wb (pidn 42 6) := Nat.eq_of_beq_eq_true h2
  have ra : Cn (AB 0) ∧ TabRep (unpack 42 6 (AB 0)) aS := by
    rw [e0]
    exact wordK_eq hG wa
  have rb : Cn (AB 2) ∧ TabRep (unpack 42 6 (AB 2)) bS := by
    rw [e2]
    exact wordK_eq hG wb
  have ra' := inv_of_invOK ra.1 ra.2 h1
  have rb' := inv_of_invOK rb.1 rb.2 h3
  have hAB : ∀ c < 4, Cn (AB c) ∧
      TabRep (unpack 42 6 (AB c)) (FreeGroup.lift genAB (FreeGroup.mk [decL c])) := by
    intro c hc4
    rw [decL_lift c hc4]
    interval_cases c
    · exact ra
    · exact ra'
    · exact rb
    · exact rb'
  have hr := CFSG.KS.PK.allN_iff.1 hc i hi
  rw [L34W.strictB_eq, bAnd_iff] at hr
  obtain ⟨hrc, hrt⟩ := tabRep_repK hG hi
  have one : ∀ (w : List ℕ) (u : List (Fin 2 × Bool)) (g : ℕ) (x : Equiv.Perm (Fin 42)),
      u = w.map decL → codesOK w = true → Cn g → TabRep (unpack 42 6 g) x →
      sgConjW AB w (repK G i) g = true → abPerm u = repPerm i * x * (repPerm i)⁻¹ := by
    intro w u g x hu hw hg rg hcw
    obtain ⟨cw, rw'⟩ := pword_ab hAB w (pidn 42 6) 1 (codesOK_spec hw) cn_pidn
      (by rw [← idTab42]; exact TabRep.idTab)
    rw [hu]
    exact conj_of_mul (eq_of_beq_unpack cw hrc hrc hg rw' hrt hrt rg hcw)
  exact ⟨one _ _ _ _ (hA i).1 (hA i).2 ra.1 ra.2 hr.1, one _ _ _ _ (hB i).1 (hB i).2 rb.1 rb.2 hr.2⟩

theorem cj_spec {A T : ℕ → ℕ} (hG : GensG G) (hy : yOK G Y = true) (hA : AlOf A)
    (hb : boundsOK T A = true) (h : sgCjOK G Y A = true) {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    (alphaEntry i k).1 < 64 ∧
      repPerm i * wordPerm (tg k) * (repPerm i)⁻¹ = wordPerm (tg (alphaEntry i k).1) := by
  have em : (alphaEntry i k).1 = ent A i k / 48 := by
    rw [hA i k hi (by omega)]
    rfl
  have hm : ent A i k / 48 < 64 := by
    have := bounds_A hb hi (show k < 66 by omega)
    omega
  rw [em]
  refine ⟨hm, ?_⟩
  have h1 := CFSG.KS.PK.allN_iff.1 h i hi
  rw [L34W.strictB_eq] at h1
  have h2 := CFSG.KS.PK.allN_iff.1 h1 k hk
  obtain ⟨hrc, hrt⟩ := tabRep_repK hG hi
  obtain ⟨cy, ry⟩ := tabRep_Y0 hG hy hk
  obtain ⟨cz, rz⟩ := tabRep_Y hG hy hm hi
  have e1 := congrArg (unpack 42 6) (Nat.eq_of_beq_eq_true h2)
  change unpack 42 6 (pcomp 42 6 (mask 6) (repK G i) (Y k)) = unpack 42 6 (Y (64 * i + ent A i k / 48))
    at e1
  rw [← CFSG.KC.L34KSnd.comp_unpack' hrc cy] at e1
  have e2 := ((hrt.comp ry).eq_iff rz).1 e1
  rw [yPerm] at e2
  rw [e2, mul_inv_cancel_right]

theorem wT0_cover : ∀ w ∈ wT₀, ∃ g < 4, wT₀.getD g [] = w := by decide

theorem wT0_mem : ∀ g < 4, wT₀.getD g [] ∈ wT₀ := by decide

theorem t0_vals (hG : GensG G) (h : sgFixOK G = true) {g : ℕ} (hg : g < 4) :
    wordPerm (wT₀.getD g []) 2 = 2 ∧ wordPerm (wT₀.getD g []) 23 = 23 := by
  unfold sgFixOK at h
  rw [bAnd_iff] at h
  have h1 := CFSG.KS.PK.allN_iff.1 h.1 g hg
  rw [L34W.strictB_eq, bAnd_iff] at h1
  obtain ⟨-, r⟩ := wordK_eq hG (wT₀.getD g [])
  have v2 := pg_of_tabRep r 2
  have v23 := pg_of_tabRep r 23
  have a2 : pg 6 (mask 6) (sgT0K G g) 2 = 2 := Nat.eq_of_beq_eq_true h1.1
  have a23 : pg 6 (mask 6) (sgT0K G g) 23 = 23 := Nat.eq_of_beq_eq_true h1.2
  unfold sgT0K at a2 a23
  exact ⟨Fin.ext (v2.symm.trans a2), Fin.ext (v23.symm.trans a23)⟩

theorem fix_T0 (hG : GensG G) (h : sgFixOK G = true) : ∀ t ∈ T0, t 2 = 2 ∧ t 23 = 23 := by
  intro t ht
  have hle : T0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 42)) (2 : Fin 42) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 42)) (23 : Fin 42) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨g, hg, rfl⟩ := wT0_cover w hw
    obtain ⟨v2, v23⟩ := t0_vals hG h hg
    exact ⟨MulAction.mem_stabilizer_iff.2 v2, MulAction.mem_stabilizer_iff.2 v23⟩
  have := hle ht
  exact ⟨MulAction.mem_stabilizer_iff.1 this.1, MulAction.mem_stabilizer_iff.1 this.2⟩

theorem moved_T0 (hG : GensG G) (h : sgFixOK G = true) (p : Fin 42) (h2 : p ≠ 2) (h23 : p ≠ 23) :
    ∃ t ∈ T0, t p ≠ p := by
  unfold sgFixOK at h
  rw [bAnd_iff] at h
  have h1 := CFSG.KS.PK.allN_iff.1 h.2 p.val p.isLt
  have n2 : Nat.beq p.val 2 = false := by
    cases e : Nat.beq p.val 2
    · rfl
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) h2
  have n23 : Nat.beq p.val 23 = false := by
    cases e : Nat.beq p.val 23
    · rfl
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) h23
  change bIf(Nat.beq p.val 2, true, bIf(Nat.beq p.val 23, true,
    bNot (allN 4 fun g => Nat.beq (pg 6 (mask 6) (sgT0K G g) p.val) p.val))) = true at h1
  rw [n2, n23] at h1
  have h3 := bNot_iff.1 h1
  by_contra hne
  push Not at hne
  have : allN 4 (fun g => Nat.beq (pg 6 (mask 6) (sgT0K G g) p.val) p.val) = true := by
    refine CFSG.KS.PK.allN_iff.2 fun g hg => ?_
    obtain ⟨-, r⟩ := wordK_eq hG (wT₀.getD g [])
    have v := pg_of_tabRep r p
    have hmem : wordPerm (wT₀.getD g []) ∈ T0 :=
      Subgroup.subset_closure ⟨_, wT0_mem g hg, rfl⟩
    unfold sgT0K
    rw [v, hne _ hmem]
    exact Nat.beq_refl _
  rw [this] at h3
  exact Bool.noConfusion h3

@[expose] def pairSet (a b : ℕ) : Finset (Fin 42) := Finset.univ.filter fun x => x.val = a ∨ x.val = b

theorem mem_pairSet {a b : ℕ} {x : Fin 42} : x ∈ pairSet a b ↔ x.val = a ∨ x.val = b := by
  simp [pairSet]

theorem pairSet_comm (a b : ℕ) : pairSet a b = pairSet b a := by
  ext x
  rw [mem_pairSet, mem_pairSet, or_comm]

theorem smul_pairSet (g : Equiv.Perm (Fin 42)) {a b : ℕ} (ha : a < 42) (hb : b < 42) :
    g • pairSet a b = pairSet (g ⟨a, ha⟩).val (g ⟨b, hb⟩).val := by
  ext y
  rw [Finset.mem_smul_finset, mem_pairSet]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_pairSet] at hx
    rcases hx with hx | hx
    · left
      rw [Equiv.Perm.smul_def, show x = ⟨a, ha⟩ from Fin.ext hx]
    · right
      rw [Equiv.Perm.smul_def, show x = ⟨b, hb⟩ from Fin.ext hx]
  · rintro (hy | hy)
    · exact ⟨⟨a, ha⟩, mem_pairSet.2 (Or.inl rfl), (Fin.ext hy).symm⟩
    · exact ⟨⟨b, hb⟩, mem_pairSet.2 (Or.inr rfl), (Fin.ext hy).symm⟩

theorem pairSet_inj {a b a' b' : ℕ} (hab : a < b) (hb : b < 42) (hab' : a' < b') (hb' : b' < 42)
    (h : pairSet a b = pairSet a' b') : a = a' ∧ b = b' := by
  have m : ∀ x < 42, (x = a ∨ x = b) ↔ (x = a' ∨ x = b') := fun x hx => by
    have := congrArg (fun s => (⟨x, hx⟩ : Fin 42) ∈ s) h
    simp only [mem_pairSet] at this
    exact Iff.of_eq this
  have h1 := (m a (by omega)).1 (Or.inl rfl)
  have h2 := (m b hb).1 (Or.inr rfl)
  have h3 := (m a' (by omega)).2 (Or.inl rfl)
  have h4 := (m b' hb').2 (Or.inr rfl)
  omega

theorem stab_of_normal (hG : GensG G) (h : sgFixOK G = true) {y : Equiv.Perm (Fin 42)}
    (hN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) : y • pairSet 2 23 = pairSet 2 23 := by
  have hfix := fix_T0 hG h
  have key : ∀ p : Fin 42, (p = 2 ∨ p = 23) → y⁻¹ p = 2 ∨ y⁻¹ p = 23 := by
    intro p hp
    by_contra hne
    push Not at hne
    obtain ⟨t, ht, htm⟩ := moved_T0 hG h (y⁻¹ p) hne.1 hne.2
    have hf : (y * t * y⁻¹) p = p := by
      rcases hp with rfl | rfl
      · exact (hfix _ (hN t ht)).1
      · exact (hfix _ (hN t ht)).2
    apply htm
    have e : y⁻¹ ((y * t * y⁻¹) p) = t (y⁻¹ p) := by
      simp [Equiv.Perm.mul_apply]
    rw [← e, hf]
  have hsub : pairSet 2 23 ⊆ y • pairSet 2 23 := by
    intro p hp
    rw [Finset.mem_smul_finset]
    have hp' : p = 2 ∨ p = 23 := by
      rw [mem_pairSet] at hp
      rcases hp with hp | hp
      · exact Or.inl (Fin.ext hp)
      · exact Or.inr (Fin.ext hp)
    refine ⟨y⁻¹ p, ?_, by simp [Equiv.Perm.smul_def]⟩
    rcases key p hp' with e | e
    · rw [e]
      exact mem_pairSet.2 (Or.inl rfl)
    · rw [e]
      exact mem_pairSet.2 (Or.inr rfl)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])).symm

theorem pg_G (hG : GensG G) {j x : ℕ} (hj : j < 6) (hx : x < 42) :
    pg 6 (mask 6) (G j) x = (genR j ⟨x, hx⟩).val := by
  have r := tabRep_genR hj
  rw [(hG j hj).1] at r
  exact pg_of_tabRep r ⟨x, hx⟩

theorem orb_mem (hG : GensG G) {O : ℕ → ℕ} (h : sgOrbOK G O = true) :
    ∀ k < 105, ∃ g ∈ R, g • pairSet 2 23 = pairSet (sgOF O k 2) (sgOF O k 3) ∧
      sgOF O k 2 < 42 ∧ sgOF O k 3 < 42 := by
  unfold sgOrbOK at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨r2, r23⟩, hs, -⟩ := h
  have e2 : sgOF O 0 2 = 2 := Nat.eq_of_beq_eq_true r2
  have e23 : sgOF O 0 3 = 23 := Nat.eq_of_beq_eq_true r23
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · refine ⟨1, R.one_mem, ?_, ?_, ?_⟩
      · rw [one_smul, e2, e23]
      · rw [e2]
        norm_num
      · rw [e23]
        norm_num
    · have hk4 : k < 104 := by omega
      have h1 : sgOStep G O (k + 1) = true := CFSG.KS.PK.allN_iff.1 hs k hk4
      unfold sgOStep at h1
      simp only [L34W.strictB_eq, bAnd_iff, Nat.blt_eq] at h1
      obtain ⟨⟨hp, hj⟩, ⟨hab, hb⟩, himg⟩ := h1
      obtain ⟨g, hg, hgx, ha', hb'⟩ := ih _ hp (by omega)
      refine ⟨genR (sgOF O (k + 1) 1) * g, R.mul_mem (genR_mem _) hg, ?_, by omega, hb⟩
      rw [mul_smul, hgx, smul_pairSet _ ha' hb', ← pg_G hG hj ha', ← pg_G hG hj hb']
      rcases bIf_iff.1 himg with ⟨h2, -⟩ | ⟨-, h2⟩
      · rw [bAnd_iff] at h2
        rw [Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2]
      · rw [bAnd_iff] at h2
        rw [Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2, pairSet_comm]

theorem orb_inj (hG : GensG G) {O : ℕ → ℕ} (h : sgOrbOK G O = true) {k k' : ℕ} (hk : k < 105)
    (hk' : k' < 105) (e : pairSet (sgOF O k 2) (sgOF O k 3) = pairSet (sgOF O k' 2) (sgOF O k' 3)) :
    k = k' := by
  have hlt : ∀ m < 105, sgOF O m 2 < sgOF O m 3 ∧ sgOF O m 3 < 42 := by
    intro m hm
    have h' := h
    unfold sgOrbOK at h'
    simp only [bAnd_iff] at h'
    obtain ⟨⟨r2, r23⟩, hs, -⟩ := h'
    rcases m with _ | m
    · rw [Nat.eq_of_beq_eq_true r2, Nat.eq_of_beq_eq_true r23]
      norm_num
    · have hm4 : m < 104 := by omega
      have h1 : sgOStep G O (m + 1) = true := CFSG.KS.PK.allN_iff.1 hs m hm4
      unfold sgOStep at h1
      simp only [L34W.strictB_eq, bAnd_iff, Nat.blt_eq] at h1
      exact h1.2.1
  have hd : ∀ m < 105, ∀ m' < m, sgOKey O m' ≠ sgOKey O m := by
    intro m hm m' hm'
    have h' := h
    unfold sgOrbOK at h'
    simp only [bAnd_iff] at h'
    have h1 := CFSG.KS.PK.allN_iff.1 h'.2.2 m hm
    rw [L34W.strictB_eq] at h1
    have h2 := CFSG.KS.PK.allN_iff.1 h1 m' hm'
    exact Nat.ne_of_beq_eq_false (bNot_iff.1 h2)
  obtain ⟨a1, b1⟩ := hlt k hk
  obtain ⟨a2, b2⟩ := hlt k' hk'
  obtain ⟨ea, eb⟩ := pairSet_inj a1 b1 a2 b2 e
  have ek : sgOKey O k = sgOKey O k' := by
    unfold sgOKey
    change 64 * sgOF O k 2 + sgOF O k 3 = 64 * sgOF O k' 2 + sgOF O k' 3
    rw [ea, eb]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · exact hd k' hk' k hl ek
  · exact hd k hk k' hl ek.symm

theorem stab_Y (hG : GensG G) (hy : yOK G Y = true) (h : sgStabOK Y = true) {t i : ℕ}
    (ht : t < 64) (hi : i < 36) : yPerm t i • pairSet 2 23 = pairSet 2 23 := by
  have hn : 64 * i + t < 2304 := by omega
  have h1 := CFSG.KS.PK.allN_iff.1 h (64 * i + t) hn
  simp only [L34W.strictB_eq] at h1
  obtain ⟨-, r⟩ := tabRep_Y hG hy ht hi
  have v2 := pg_of_tabRep r 2
  have v23 := pg_of_tabRep r 23
  rw [smul_pairSet _ (show 2 < 42 by norm_num) (show 23 < 42 by norm_num)]
  change pairSet (yPerm t i 2).val (yPerm t i 23).val = _
  change pg 6 (mask 6) (Y (64 * i + t)) 2 = _ at v2
  change pg 6 (mask 6) (Y (64 * i + t)) 23 = _ at v23
  rw [← v2, ← v23]
  rcases bIf_iff.1 h1 with ⟨h2, -⟩ | ⟨-, h2⟩
  · rw [bAnd_iff] at h2
    rw [Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2]
  · rw [bAnd_iff] at h2
    rw [Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2, pairSet_comm]

theorem Y_inj {P Q : ℕ → ℕ} (h : sgSortOK Y P Q = true) {n n' : ℕ} (hn : n < 2304) (hn' : n' < 2304)
    (e : Y n = Y n') : n = n' := by
  unfold sgSortOK at h
  rw [bAnd_iff] at h
  have mono : ∀ k k', k < k' → k' < 2304 → Y (P k) < Y (P k') := by
    intro k k' hkk hk'
    induction k' with
    | zero => omega
    | succ m ih =>
      have hm2 : m < 2303 := by omega
      have hm := Nat.blt_eq.mp (CFSG.KS.PK.allN_iff.1 h.1 m hm2)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hkk with hl | hl
      · exact lt_trans (ih hl (by omega)) hm
      · rw [hl]
        exact hm
  have q : ∀ x < 2304, Q x < 2304 ∧ P (Q x) = x := by
    intro x hx
    have h1 := CFSG.KS.PK.allN_iff.1 h.2 x hx
    rw [L34W.strictB_eq, bAnd_iff] at h1
    exact ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2⟩
  obtain ⟨q1, p1⟩ := q n hn
  obtain ⟨q2, p2⟩ := q n' hn'
  by_contra hne
  have hq : Q n ≠ Q n' := fun e' => hne (by rw [← p1, ← p2, e'])
  rcases Nat.lt_or_gt_of_ne hq with hl | hl
  · have := mono _ _ hl q2
    rw [p1, p2, e] at this
    exact lt_irrefl _ this
  · have := mono _ _ hl q1
    rw [p1, p2, e] at this
    exact lt_irrefl _ this

theorem yPerm_inj (hG : GensG G) (hy : yOK G Y = true) {P Q : ℕ → ℕ} (h : sgSortOK Y P Q = true)
    {t i t' i' : ℕ} (ht : t < 64) (hi : i < 36) (ht' : t' < 64) (hi' : i' < 36)
    (e : yPerm t i = yPerm t' i') : t = t' ∧ i = i' := by
  obtain ⟨c1, r1⟩ := tabRep_Y hG hy ht hi
  obtain ⟨c2, r2⟩ := tabRep_Y hG hy ht' hi'
  rw [e] at r1
  have e1 := CFSG.KC.L34KSnd.unpack_inj' c1 c2 (r1.tab_eq r2)
  have := Y_inj h (by omega) (by omega) e1
  omega

theorem exists_decomp_of {O P Q : ℕ → ℕ} (hG : GensG G)
    (hy : yOK G Y = true) (hfix : sgFixOK G = true) (horb : sgOrbOK G O = true)
    (hst : sgStabOK Y = true) (hso : sgSortOK Y P Q = true) {y : Equiv.Perm (Fin 42)}
    (hyR : y ∈ R) (hN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) :
    ∃ i < 36, ∃ t < 64, y = wordPerm (tg t) * repPerm i := by
  classical
  let x₀ : Finset (Fin 42) := pairSet 2 23
  let Stab : Subgroup R := MulAction.stabilizer R x₀
  have horb105 : 105 ≤ (MulAction.orbit R x₀).ncard := by
    let f : Fin 105 → Finset (Fin 42) := fun k => pairSet (sgOF O k 2) (sgOF O k 3)
    have hf : Function.Injective f := fun k k' e => Fin.ext (orb_inj hG horb k.isLt k'.isLt e)
    have hsub : Set.range f ⊆ MulAction.orbit R x₀ := by
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, hg, hgx, -⟩ := orb_mem hG horb k k.isLt
      exact ⟨⟨g, hg⟩, hgx⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  have hcard : Nat.card Stab ≤ 2304 := by
    have h1 := Stab.card_mul_index
    have h2 : Stab.index = (MulAction.orbit R x₀).ncard := MulAction.index_stabilizer R x₀
    rw [h2, card_R] at h1
    by_contra hc
    push Not at hc
    have : 2305 * 105 ≤ Nat.card Stab * (MulAction.orbit R x₀).ncard :=
      Nat.mul_le_mul hc horb105
    omega
  let F : Fin 64 × Fin 36 → Stab := fun p =>
    ⟨⟨yPerm p.1 p.2, yPerm_mem_R _ _⟩, by
      change (yPerm p.1 p.2) • x₀ = x₀
      exact stab_Y hG hy hst p.1.isLt p.2.isLt⟩
  have hF : Function.Injective F := by
    intro p p' e
    have e' : yPerm p.1 p.2 = yPerm p'.1 p'.2 := congrArg (fun z : Stab => ((z : R) : Equiv.Perm (Fin 42))) e
    obtain ⟨e1, e2⟩ := yPerm_inj hG hy hso p.1.isLt p.2.isLt p'.1.isLt p'.2.isLt e'
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  have hbij := hF.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card (α := Fin 64 × Fin 36), Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    exact hcard)
  have hyS : (⟨y, hyR⟩ : R) ∈ Stab := by
    change y • x₀ = x₀
    exact stab_of_normal hG hfix hN
  obtain ⟨⟨t, i⟩, hti⟩ := hbij.2 ⟨⟨y, hyR⟩, hyS⟩
  refine ⟨i.val, i.isLt, t.val, t.isLt, ?_⟩
  have := congrArg (fun z : Stab => ((z : R) : Equiv.Perm (Fin 42))) hti
  exact this.symm

end CFSG.KC.L34Cov

end
