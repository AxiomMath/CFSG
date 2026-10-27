module

public import Certificates.Data.Kernel.Spor.BTupM
public import CFSG.Certificates.Kernel.Spor.BTupRSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

theorem btMulF_succ (k : Nat) (R RT : Nat → Nat) (D a q : Nat) :
    btMulF k R RT (D + 1) a q =
      btMulF k R RT D (btPos RT k a (btLab (btRec R q))) (btPar (btRec R q)) := by
  change strictN (btRec R q) (fun r => strictN (btPos RT k a (btLab r)) (fun a' =>
    btMulF k R RT D a' (btPar r))) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.strictN_eq]

theorem btClsSl_spec {k cnt r0 kw km cntL lo len : Nat} {K R RT KL TG E : Nat → Nat}
    (h : btClsSlK k cnt r0 kw km cntL K R RT KL TG E lo len = true) {i : Nat} (h1 : lo ≤ i)
    (h2 : i < lo + len) (hi : i < cnt) : btClsK k cnt r0 kw km cntL K R RT KL TG E i = true := by
  unfold btClsSlK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, if_pos (Nat.blt_eq.mpr hi)] at h'
  exact h'

section Mul

variable {n w d kw km k cnt base : Nat} {G K R POS S RT : Nat → Nat}
  {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n}
  (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
  (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
  (hfix : ∀ h ∈ genSub n k gp, (∀ t, h (b t) = b t) → h = 1)
  (hb : ∀ t : Fin d, pg w (mask w) base t = b t)
  (hS : ∀ j < k, ∀ t : Fin d, pg w (mask w) (btKey kw km K (S j)) t = gp j (b t))
  (hr : ∀ i < cnt, btRtK k k cnt S R POS RT i = true)
include hg hp hfix hb hS hr

theorem btMul_dep : ∀ D q, q < cnt → btDep (btRec R q) = D → ∀ a < cnt,
    ∀ ha ∈ genSub n k gp, (∀ t : Fin d, pg w (mask w) (btKey kw km K a) t = ha (b t)) →
    ∀ hq ∈ genSub n k gp, (∀ t : Fin d, pg w (mask w) (btKey kw km K q) t = hq (b t)) →
    btMulF k R RT D a q < cnt ∧
      ∀ t : Fin d, pg w (mask w) (btKey kw km K (btMulF k R RT D a q)) t = (ha * hq) (b t) := by
  intro D
  induction D with
  | zero =>
    intro q hq hD a ha x hx hxe y hy hye
    have h1 : y = 1 := hfix y hy fun t => Fin.ext (by
      rw [← hye t, (ptFacts (hp q hq)).root hD, hb t])
    refine ⟨ha, fun t => ?_⟩
    rw [h1, mul_one]
    exact hxe t
  | succ D ih =>
    intro q hq hD a ha x hx hxe y hy hye
    obtain ⟨hpar, hlab, hdep, hmov⟩ := (ptFacts (hp q hq)).tree (by omega)
    set p := btPar (btRec R q)
    set l := btLab (btRec R q)
    rw [btMulF_succ]
    obtain ⟨ha', hae'⟩ := btRt_spec (y := gp) hg hp hfix hb hS hr ha hx hxe hlab
    have hy' : (gp l)⁻¹ * y ∈ genSub n k gp :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (gp_mem hlab)) hy
    have hye' : ∀ t : Fin d, pg w (mask w) (btKey kw km K p) t = ((gp l)⁻¹ * y) (b t) := by
      intro t
      have hlt : pg w (mask w) (btKey kw km K p) t < n := (ptFacts (hp p hpar)).lt t t.2
      have e1 : gp l ⟨_, hlt⟩ = y (b t) := Fin.ext (by
        rw [← hg l hlab, ← hye t, hmov t t.2])
      rw [Equiv.Perm.mul_apply, ← e1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    obtain ⟨h1, h2⟩ := ih p hpar (by omega) _ ha' _ (Subgroup.mul_mem _ hx (gp_mem hlab)) hae'
      _ hy' hye'
    refine ⟨h1, fun t => ?_⟩
    rw [h2 t, mul_assoc, mul_inv_cancel_left]

theorem btMul_spec {a q : Nat} (ha : a < cnt) (hq : q < cnt) {x y : Equiv.Perm (Fin n)}
    (hx : x ∈ genSub n k gp) (hxe : ∀ t : Fin d, pg w (mask w) (btKey kw km K a) t = x (b t))
    (hy : y ∈ genSub n k gp) (hye : ∀ t : Fin d, pg w (mask w) (btKey kw km K q) t = y (b t)) :
    btMul k R RT a q < cnt ∧
      ∀ t : Fin d, pg w (mask w) (btKey kw km K (btMul k R RT a q)) t = (x * y) (b t) :=
  btMul_dep hg hp hfix hb hS hr _ q hq rfl a ha x hx hxe y hy hye

omit hg hp hb hS hr in
theorem ext_of_base {x y : Equiv.Perm (Fin n)} (hx : x ∈ genSub n k gp)
    (hy : y ∈ genSub n k gp) (e : ∀ t, x (b t) = y (b t)) : x = y := by
  have h1 := hfix (y⁻¹ * x) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hx) fun t => by
    rw [Equiv.Perm.mul_apply, e t, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  exact (inv_mul_eq_one.1 h1).symm

theorem btConj_spec {cnt' : Nat} {E : Nat → Nat} {i p : Nat} (hi : i < cnt)
    (hcj : btConjK k cnt R RT E i p = true) {e : Equiv.Perm (Fin n)} (heH : e ∈ genSub n k gp)
    (he : ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = e (b t)) (hw : 0 < w)
    (_ : cnt' = cnt) :
    9 ≤ Nat.card ↥{x : Equiv.Perm (Fin n) | ∃ g ∈ genSub n k gp, x = g * e * g⁻¹} := by
  unfold btConjK at hcj
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hcj
  have hs : ∀ s < 9, btEf E p (s + 1) < cnt ∧ btEf E p (10 + s) < cnt ∧
      (s ≠ 0 → btEf E p (9 + s) < btEf E p (10 + s)) ∧
      btMul k R RT (btEf E p (s + 1)) i =
        btMul k R RT (btEf E p (10 + s)) (btEf E p (s + 1)) := by
    intro s hs9
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hcj.2 s hs9
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, fun hs0 => ?_, Nat.beq_eq.mp h4⟩
    have hs0' : Nat.beq s (nat_lit 0) = false := by
      cases e : Nat.beq s (nat_lit 0)
      · rfl
      · exact absurd (Nat.beq_eq.mp e) hs0
    rw [CFSG.KS.Raw.Orb.bIf_eq, hs0', if_neg Bool.false_ne_true] at h3
    have e9 : Nat.add 9 s = 9 + s := rfl
    rw [e9] at h3
    exact Nat.blt_eq.mp h3
  choose! el hel hkey using fun j (hj : j < cnt) => btKey_mem hg hb hp (kw := kw) (km := km) hj
  have hmono : ∀ a c, a < c → c < 9 → btEf E p (10 + a) < btEf E p (10 + c) := by
    intro a c hac hc
    induction c with
    | zero => omega
    | succ c ih =>
      have hstep := (hs (c + 1) hc).2.2.1 (by omega)
      have e' : 9 + (c + 1) = 10 + c := by omega
      rw [e'] at hstep
      rcases Nat.lt_succ_iff_lt_or_eq.1 hac with h' | h'
      · exact lt_trans (ih h' (by omega)) hstep
      · subst h'
        exact hstep
  have hconj : ∀ s < 9, el (btEf E p (10 + s)) =
      el (btEf E p (s + 1)) * e * (el (btEf E p (s + 1)))⁻¹ := by
    intro s hs9
    obtain ⟨hg', hc', -, heq⟩ := hs s hs9
    obtain ⟨-, k1⟩ := btMul_spec hg hp hfix hb hS hr hg' hi (hel _ hg') (hkey _ hg') heH he
    obtain ⟨-, k2⟩ := btMul_spec hg hp hfix hb hS hr hc' hg' (hel _ hc') (hkey _ hc')
      (hel _ hg') (hkey _ hg')
    have hm : el (btEf E p (s + 1)) * e = el (btEf E p (10 + s)) * el (btEf E p (s + 1)) :=
      ext_of_base hfix (Subgroup.mul_mem _ (hel _ hg') heH)
        (Subgroup.mul_mem _ (hel _ hc') (hel _ hg')) fun t => Fin.ext (by
          rw [← k1 t, ← k2 t, heq])
    rw [hm, mul_inv_cancel_right]
  let f : Fin 9 → ↥{x : Equiv.Perm (Fin n) | ∃ g ∈ genSub n k gp, x = g * e * g⁻¹} :=
    fun s => ⟨el (btEf E p (10 + s.val)), el (btEf E p (s.val + 1)),
      hel _ (hs s.val s.2).1, hconj s.val s.2⟩
  have hf : Function.Injective f := by
    intro s s' hss
    have hv : el (btEf E p (10 + s.val)) = el (btEf E p (10 + s'.val)) :=
      congrArg Subtype.val hss
    have hidx := btKey_inj hw hp (hs s.val s.2).2.1 (hs s'.val s'.2).2.1 fun t => by
      rw [hkey _ (hs s.val s.2).2.1, hkey _ (hs s'.val s'.2).2.1, hv]
    apply Fin.ext
    rcases Nat.lt_trichotomy s.val s'.val with h' | h' | h'
    · exact absurd hidx (Nat.ne_of_lt (hmono _ _ h' s'.2))
    · exact h'
    · exact absurd hidx.symm (Nat.ne_of_lt (hmono _ _ h' s.2))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin] at this

theorem btCls_sound {r0 cntL : Nat} {KL TG E : Nat → Nat} {L : Subgroup (Equiv.Perm (Fin n))}
    (hw : 0 < w) (hc : btHdK cnt = true) (hh : btClsHdK cnt r0 R = true)
    (hcl : ∀ i < cnt, btClsK k cnt r0 kw km cntL K R RT KL TG E i = true)
    (hL : ∀ q < cntL, ∃ l ∈ L, ∀ t : Fin d, pg w (mask w) (btKey kw km KL q) t = l (b t))
    (hext : ∀ x ∈ genSub n k gp, ∀ l ∈ L, (∀ t, x (b t) = l (b t)) → x = l)
    {e : Equiv.Perm (Fin n)} (heH : e ∈ genSub n k gp) (he2 : e * e = 1) (he1 : e ≠ 1)
    (heL : e ∉ L) :
    9 ≤ Nat.card ↥{x : Equiv.Perm (Fin n) | ∃ g ∈ genSub n k gp, x = g * e * g⁻¹} := by
  obtain ⟨i, hi, he⟩ := btKey_cover hg hb hp hc heH
  have h := hcl i hi
  unfold btClsK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq,
    CFSG.KS.Raw.Orb.bIf_eq] at h
  split_ifs at h with h0
  · rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨l, hl, hle⟩ := hL _ (Nat.blt_eq.mp h.1)
    refine absurd ?_ heL
    rw [hext e heH l hl fun t => Fin.ext (by rw [← he t, Nat.beq_eq.mp h.2, hle t])]
    exact hl
  · rw [CFSG.KS.Raw.Orb.bIf_eq] at h
    split_ifs at h with h1
    · rw [CFSG.KS.Raw.Orb.bIf_eq] at h
      split_ifs at h with h2
      exfalso
      unfold btClsHdK at hh
      rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hh
      have hr0 : r0 < cnt := Nat.blt_eq.mp hh.1
      obtain ⟨hm, km'⟩ := btMul_spec hg hp hfix hb hS hr hi hi heH he heH he
      refine h2 (Nat.beq_eq.mpr (btKey_inj hw hp hm hr0 fun t => ?_))
      rw [km' t, he2, (ptFacts (hp r0 hr0)).root (Nat.beq_eq.mp hh.2), hb t]
      rfl
    · rw [CFSG.KS.Raw.Orb.bIf_eq] at h
      split_ifs at h with h2
      exact btConj_spec hg hp hfix hb hS hr hi h heH he hw rfl

end Mul

end CFSG.KS.BTup

end
