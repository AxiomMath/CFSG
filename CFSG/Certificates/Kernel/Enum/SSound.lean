module

public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

@[expose] noncomputable def sDepth (T : Nat → Nat) (sh lm rb rm nw iw i : Nat) : Nat :=
  fld(rget T sh lm rb rm i, Nat.add nw (Nat.add iw (nat_lit 4)), nat_lit 255)

theorem sClos_sound {T : Nat → Nat} {sh lm rb rm m pm iw im nS r e oR : Nat} {G : Nat → Nat} :
    ∀ {k : Nat}, sClos T sh lm rb rm n w m pm iw im nS G k r e oR = true →
      ∀ j < k, ∃ R < nS, eq2 n w m (rperm T sh lm rb rm pm R) e (G j) = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, h, j, hj => by
    have e1 : sClos T sh lm rb rm n w m pm iw im nS G (k + 1) r e oR =
        Bool.rec (motive := fun _ => Bool) false (sClos T sh lm rb rm n w m pm iw im nS G k r e oR)
          (strictB fld(r, Nat.add oR (Nat.mul iw k), im) (fun Rj =>
            bAnd(Nat.blt Rj nS, eq2 n w m (rperm T sh lm rb rm pm Rj) e (G k)))) := rfl
    rw [e1] at h
    simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq, Nat.blt_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact sClos_sound h3 j hjk
    · have : j = k := by omega
      subst this
      exact ⟨_, h1, h2⟩

theorem sChk_sound {T : Nat → Nat} {sh lm rb rm m nw pm iw im nS idn k : Nat} {G : Nat → Nat}
    {fInv : Bool} {LT : Nat → Nat} {lsh llm lrb lrm nL : Nat} {fWit : Bool} {ob : Nat}
    {C : Nat → Nat} {nC : Nat} {Y : Nat → Nat} {nK i : Nat}
    (h : sChk T sh lm rb rm n w m nw pm iw im nS idn G k fInv LT lsh llm lrb lrm nL fWit ob C nC Y
      nK i = true) :
    (i ≠ 0 → rperm T sh lm rb rm pm (i - 1) < rperm T sh lm rb rm pm i) ∧
    (sDepth T sh lm rb rm nw iw i = 0 → rperm T sh lm rb rm pm i = idn) ∧
    (sDepth T sh lm rb rm nw iw i ≠ 0 → ∃ par < nS, ∃ lab < k,
      sDepth T sh lm rb rm nw iw par = sDepth T sh lm rb rm nw iw i - 1 ∧
      eq2 n w m (rperm T sh lm rb rm pm i) (rperm T sh lm rb rm pm par) (G lab) = true) ∧
    (∀ j < k, ∃ R < nS,
      eq2 n w m (rperm T sh lm rb rm pm R) (rperm T sh lm rb rm pm i) (G j) = true) ∧
    (fInv = true → eq2 n w m idn (rperm T sh lm rb rm pm i) (rperm T sh lm rb rm pm i) = true →
      rperm T sh lm rb rm pm i ≠ idn →
      ∃ ix < nL, rperm LT lsh llm lrb lrm pm ix = rperm T sh lm rb rm pm i) := by
  unfold sChk at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq] at h
  obtain ⟨hA, hB, hC, hD, -⟩ := h
  refine ⟨fun hi => ?_, fun hd => ?_, fun hd => ?_, sClos_sound hC, fun hf hinv hne => ?_⟩
  · have hc : Nat.beq i (nat_lit 0) = false := by
      cases hb : Nat.beq i (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hi
    have h1 := bIf_false hc hA
    rw [Nat.blt_eq] at h1
    exact h1
  · have hc : Nat.beq (sDepth T sh lm rb rm nw iw i) (nat_lit 0) = true := (beq_iff _ _).2 hd
    exact Nat.eq_of_beq_eq_true (bIf_true hc hB)
  · have hc : Nat.beq (sDepth T sh lm rb rm nw iw i) (nat_lit 0) = false := by
      cases hb : Nat.beq (sDepth T sh lm rb rm nw iw i) (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hd
    have h0 := bIf_false hc hB
    simp only [Bool.and_eq_true, Nat.blt_eq] at h0
    obtain ⟨h1, h2, h3, h4⟩ := h0
    exact ⟨_, h1, _, h2, Nat.eq_of_beq_eq_true h3, h4⟩
  · have hc : Nat.beq (rperm T sh lm rb rm pm i) idn = false := by
      cases hb : Nat.beq (rperm T sh lm rb rm pm i) idn
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hne
    have hc' : (eq2 n w m idn (rperm T sh lm rb rm pm i) (rperm T sh lm rb rm pm i) &&
        Bool.rec (motive := fun _ => Bool) true false (Nat.beq (rperm T sh lm rb rm pm i) idn)) =
        true := by
      rw [hinv, hc]
      rfl
    have h0 := bIf_true hc' (bIf_true hf hD)
    simp only [PK.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at h0
    exact ⟨_, h0.1, Nat.eq_of_beq_eq_true h0.2⟩

theorem sRange_iff {T : Nat → Nat} {sh lm rb rm m nw pm iw im nS idn k : Nat} {G : Nat → Nat}
    {fInv : Bool} {LT : Nat → Nat} {lsh llm lrb lrm nL : Nat} {fWit : Bool} {ob : Nat}
    {C : Nat → Nat} {nC : Nat} {Y : Nat → Nat} {nK lo cnt : Nat} :
    sRange T sh lm rb rm n w m nw pm iw im nS idn G k fInv LT lsh llm lrb lrm nL fWit ob C nC Y nK
      lo cnt = true ↔ ∀ j < cnt, sChk T sh lm rb rm n w m nw pm iw im nS idn G k fInv LT lsh llm
        lrb lrm nL fWit ob C nC Y nK (lo + j) = true := by
  unfold sRange
  exact PK.allN_iff

theorem rperm_shr {T : Nat → Nat} {sh lm rb rm j : Nat} :
    rperm T sh lm rb rm (mask (n * w)) j >>> (n * w) = 0 := by
  unfold rperm
  rw [PK.land_mask, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem sList_prep {T : Nat → Nat} {sh lm rb rm nw iw im nS idn k : Nat} {G : Nat → Nat}
    {fInv : Bool} {LT : Nat → Nat} {lsh llm lrb lrm nL : Nat} {fWit : Bool} {ob : Nat}
    {C : Nat → Nat} {nC : Nat} {Y : Nat → Nat} {nK : Nat} {gG : Nat → Equiv.Perm (Fin n)}
    (hS : ∀ i < nS, sChk T sh lm rb rm n w (mask w) nw (mask (n * w)) iw im nS idn G k fInv LT
      lsh llm lrb lrm nL fWit ob C nC Y nK i = true)
    (hw : 0 < w) (hid : PRep n w idn 1) (hG : ∀ j < k, PRep n w (G j) (gG j)) :
    ∃ Ev : Nat → Equiv.Perm (Fin n),
      (∀ i < nS, PRep n w (rperm T sh lm rb rm (mask (n * w)) i) (Ev i) ∧
        Ev i ∈ Subgroup.closure {x | ∃ j < k, x = gG j}) ∧
      (∀ i < nS, ∀ j < k, ∃ R < nS, Ev R = Ev i * gG j) ∧
      (∀ i < nS, ∀ i' < nS, Ev i = Ev i' → i = i') ∧
      (fInv = true → ∀ U : Nat → Equiv.Perm (Fin n),
        (∀ ix < nL, PRep n w (rperm LT lsh llm lrb lrm (mask (n * w)) ix) (U ix)) →
        ∀ i < nS, Ev i * Ev i = 1 → Ev i ≠ 1 → ∃ ix < nL, U ix = Ev i) := by
  classical
  set pm := mask (n * w)
  set H := Subgroup.closure {x : Equiv.Perm (Fin n) | ∃ j < k, x = gG j}
  have hdep : ∀ d, ∀ i < nS, sDepth T sh lm rb rm nw iw i = d →
      ∃ g : Equiv.Perm (Fin n), PRep n w (rperm T sh lm rb rm pm i) g ∧ g ∈ H := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      refine ⟨1, ?_, H.one_mem⟩
      rw [(sChk_sound (hS i hi)).2.1 hd]
      exact hid
    | succ d ih =>
      intro i hi hd
      obtain ⟨par, hpar, lab, hlab, hpd, he⟩ := (sChk_sound (hS i hi)).2.2.1 (by omega)
      obtain ⟨g, hg, hgH⟩ := ih par hpar (by omega)
      exact ⟨g * gG lab, eq2_prep he hg (hG lab hlab),
        H.mul_mem hgH (Subgroup.subset_closure ⟨lab, hlab, rfl⟩)⟩
  have hex : ∀ i, ∃ g : Equiv.Perm (Fin n), i < nS →
      PRep n w (rperm T sh lm rb rm pm i) g ∧ g ∈ H := fun i => by
    by_cases hi : i < nS
    · obtain ⟨g, hg⟩ := hdep _ i hi rfl
      exact ⟨g, fun _ => hg⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose Ev hEv using hex
  have hmono : ∀ i' < nS, ∀ i < i', rperm T sh lm rb rm pm i < rperm T sh lm rb rm pm i' := by
    intro i'
    induction i' with
    | zero => exact fun _ i hi => absurd hi (Nat.not_lt_zero i)
    | succ i' ih =>
      intro hi' i hi
      have h1 := (sChk_sound (hS (i' + 1) hi')).1 (Nat.succ_ne_zero i')
      rw [Nat.add_sub_cancel] at h1
      rcases Nat.lt_or_ge i i' with hii | hii
      · exact Nat.lt_trans (ih (by omega) i hii) h1
      · have : i = i' := by omega
        subst this
        exact h1
  refine ⟨Ev, fun i hi => hEv i hi, fun i hi j hj => ?_, fun i hi i' hi' e => ?_,
    fun hf U hU i hi hinv hne => ?_⟩
  · obtain ⟨R, hR, hRe⟩ := (sChk_sound (hS i hi)).2.2.2.1 j hj
    exact ⟨R, hR, prep_unique (hEv R hR).1 (eq2_prep hRe (hEv i hi).1 (hG j hj))⟩
  · have hf : rperm T sh lm rb rm pm i = rperm T sh lm rb rm pm i' :=
      PF.eq_of_fields hw rperm_shr rperm_shr fun p hp => by
        rw [prep_at (hEv i hi).1 hp, prep_at (hEv i' hi').1 hp, e]
    rcases Nat.lt_trichotomy i i' with h | h | h
    · exact absurd hf (Nat.ne_of_lt (hmono i' hi' i h))
    · exact h
    · exact absurd hf.symm (Nat.ne_of_lt (hmono i hi i' h))
  · have hinv' : eq2 n w (mask w) idn (rperm T sh lm rb rm pm i) (rperm T sh lm rb rm pm i) =
        true := eq2_iff.2 fun p hp => by
      have e1 := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨p, hp⟩ : Fin n) : Nat)) hinv
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e1
      rw [prep_at hid hp, prep_at (hEv i hi).1 hp, (hEv i hi).1, Equiv.Perm.one_apply]
      exact e1.symm
    have hne' : rperm T sh lm rb rm pm i ≠ idn := fun e => by
      have h1 := (hEv i hi).1
      rw [e] at h1
      exact hne (prep_unique h1 hid)
    obtain ⟨ix, hix, he⟩ := (sChk_sound (hS i hi)).2.2.2.2 hf hinv' hne'
    have hp := hU ix hix
    rw [he] at hp
    exact ⟨ix, hix, prep_unique hp (hEv i hi).1⟩

end CFSG.KC.EnumSound

end
