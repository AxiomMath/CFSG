module

public import CFSG.Certificates.Kernel.FrameE78.Glue
public import Certificates.Data.Kernel.FrameE78RootK
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78.Refl CFSG.KS.PK Matrix

theorem ln_addV3 {n p : ℕ} (u v : ℕ) (hp : p < n) :
    ln (addV3 n u v) p = (ln u p + ln v p) % 3 := by
  have h := ln_pack (fun p => ln u p + ln v p) n p
  rw [if_pos hp] at h
  exact h

theorem dec_addV3 (n u v : ℕ) : dec n (addV3 n u v) = dec n u + dec n v := by
  funext p
  rw [Pi.add_apply, dec_apply, dec_apply, dec_apply, ln_addV3 u v p.isLt, ZMod.natCast_mod,
    Nat.cast_add]

private theorem mask_fold (RP w : ℕ) : ∀ (l : List ℕ) (s : ℕ),
    (l.foldr (fun a s => Nat.lor s (Nat.lor (Nat.shiftLeft 1 (rC RP a))
      (Nat.shiftLeft 1 (negL (rC RP a))))) s).testBit w = true →
    s.testBit w = true ∨ ∃ a ∈ l, w = rC RP a ∨ w = negL (rC RP a)
  | [], s, h => Or.inl h
  | a :: l, s, h => by
    rw [List.foldr_cons] at h
    change ((_ ||| ((1 <<< rC RP a) ||| (1 <<< negL (rC RP a)))) : ℕ).testBit w = true at h
    rw [Nat.testBit_or, Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Nat.testBit_two_pow] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · rcases mask_fold RP w l s h with h | ⟨b, hb, e⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, e⟩
    · exact Or.inr ⟨a, List.mem_cons_self .., Or.inl h.symm⟩
    · exact Or.inr ⟨a, List.mem_cons_self .., Or.inr h.symm⟩

theorem rtMask_sound {m RP w : ℕ} (h : (rtMask m RP).testBit w = true) :
    w = 0 ∨ ∃ a < m, w = rC RP a ∨ w = negL (rC RP a) := by
  unfold rtMask at h
  rw [foldN_eq] at h
  rcases mask_fold RP w _ 1 h with h | ⟨a, ha, e⟩
  · left
    have e1 : (1 : ℕ) = 2 ^ 0 := rfl
    rw [e1, Nat.testBit_two_pow] at h
    exact (of_decide_eq_true h).symm
  · exact Or.inr ⟨a, List.mem_range.1 ha, e⟩

theorem rtCnt_eq (n m RP Tm y : ℕ) : rtCnt n m RP Tm y =
    ((Finset.range m).filter fun a => Tm.testBit a = true ∧ dot3 n (rc RP a) y = 0).card := by
  unfold rtCnt
  rw [cntN_eq]
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by
    simp only [bAnd_eq, Bool.and_eq_true, bitB_eq]
    exact and_congr Iff.rfl beqT)

theorem rtPlane_sound {n m RP M x xn Tm y : ℕ} (h : rtPlane n m RP M x xn Tm y = true)
    (h13 : 13 ≤ rtCnt n m RP Tm y) :
    M.testBit y = true ∨ M.testBit (addV3 n y x) = true ∨ M.testBit (addV3 n y xn) = true := by
  unfold rtPlane at h
  rw [bIf_eq, if_neg (fun e => absurd (bltT.1 e) (Nat.not_lt.2 h13)), orB_eq, orB_eq, bitB_eq,
    bitB_eq, bitB_eq] at h
  simpa only [Bool.or_eq_true] using h

theorem rtRep_sound {n m RP V b Tm lo len : ℕ} (h : rtRep n m RP V b Tm lo len = true)
    (ht : cntN m (bitB Tm) = 21 ∨ cntN m (bitB Tm) = 36) :
    ∀ j < len, rtPlane n m RP (rtMask m RP) (vget V b) (negL (vget V b)) Tm (vget V (lo + j)) =
      true := by
  unfold rtRep at h
  have hc : orB (Nat.beq (cntN m (bitB Tm)) (nat_lit 21))
      (Nat.beq (cntN m (bitB Tm)) (nat_lit 36)) = true := by
    rw [orB_eq, Bool.or_eq_true, beqT, beqT]
    exact ht
  rw [strictB_eq, bIf_eq, if_pos hc, strictB_eq, strictB_eq, strictB_eq] at h
  exact fun j hj => allN_iff.1 h j hj

@[expose] def RootP {n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod 3)) (x : Fin n → ZMod 3) : Prop :=
  ((fixSet C x).ncard = 21 ∨ (fixSet C x).ncard = 36) →
    ∀ y, 13 ≤ (fixSet C x ∩ fixSet C y).ncard →
      ∃ c : ZMod 3, ∃ t, ConjDer (sS C) t ∧ t *ᵥ (y + c • x) = -(y + c • x)

variable {n : ℕ} {C : Matrix (Fin n) (Fin n) (ZMod 3)}

theorem rootP_neg {x : Fin n → ZMod 3} (h : RootP C x) : RootP C (-x) := by
  intro hx y hy
  rw [fixSet_neg] at hx hy
  obtain ⟨c, t, ht, e⟩ := h hx y hy
  refine ⟨-c, t, ht, ?_⟩
  rwa [neg_smul_neg]

theorem rootP_smul {m : ℕ} {R : ℕ → Fin n → ZMod 3} (hR : RootData C m R) (i : Fin n)
    {x : Fin n → ZMod 3} (h : RootP C x) : RootP C (sS C i *ᵥ x) := by
  have hs := hR.sS_sq i
  have hfix : ∀ z, fixSet C (sS C i *ᵥ z) = conjEquiv hs '' fixSet C z :=
    fun z => fixSet_smul hR i z
  have hss : ∀ z, sS C i *ᵥ (sS C i *ᵥ z) = z := fun z => by
    rw [mulVec_mulVec, hs, one_mulVec]
  intro hx y hy
  rw [hfix, Set.ncard_image_of_injective _ (conjEquiv hs).injective] at hx
  have hy' : fixSet C y = conjEquiv hs '' fixSet C (sS C i *ᵥ y) := by
    rw [← hfix, hss]
  rw [hfix, hy', ← Set.image_inter (conjEquiv hs).injective,
    Set.ncard_image_of_injective _ (conjEquiv hs).injective] at hy
  obtain ⟨c, t, ht, e⟩ := h hx _ hy
  refine ⟨c, sS C i * t * sS C i, ConjDer.conj i ht, ?_⟩
  calc (sS C i * t * sS C i) *ᵥ (y + c • (sS C i *ᵥ x))
      = sS C i *ᵥ (t *ᵥ (sS C i *ᵥ y + c • x)) := by
        simp only [← mulVec_mulVec, mulVec_add, mulVec_smul, hss]
    _ = -(y + c • (sS C i *ᵥ x)) := by
        rw [e]
        simp only [mulVec_neg, mulVec_add, mulVec_smul, hss]

theorem rootP_reach {C a m : ℕ} {R : ℕ → Fin n → ZMod 3} (hR : RootData (Cm n C) m R)
    (ha : VOK n a) (hd : RootP (Cm n C) (dec n a)) {y : ℕ} (hy : SReach n C a y) :
    VOK n y ∧ RootP (Cm n C) (dec n y) := by
  induction hy with
  | root => exact ⟨ha, hd⟩
  | @step y j _ ih =>
    refine ⟨VOK_sV ih.1, ?_⟩
    rw [dec_sV ih.1.2]
    exact rootP_smul hR j ih.2

private theorem ncard_roots {m : ℕ} {R : ℕ → Fin n → ZMod 3} (hR : RootData C m R)
    (p : ℕ → Prop) [DecidablePred p] :
    ((fun a => rf C (R a)) '' {a | a < m ∧ p a}).ncard = ((Finset.range m).filter p).card := by
  rw [Set.InjOn.ncard_image fun a ha b hb e => hR.rf_inj ha.1 hb.1 e, ← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

theorem fixSet_inter (hC : C.IsSymm) {m : ℕ} {R : ℕ → Fin n → ZMod 3} (hR : RootData C m R)
    (x y : Fin n → ZMod 3) : fixSet C x ∩ fixSet C y =
      (fun a => rf C (R a)) '' {a | a < m ∧ (R a ⬝ᵥ x = 0 ∧ R a ⬝ᵥ y = 0)} := by
  ext r
  constructor
  · rintro ⟨⟨hr, hx⟩, -, hy⟩
    obtain ⟨a, ha, rfl⟩ := (conjDer_iff hC hR r).1 hr
    exact ⟨a, ⟨ha, (rf_fix (hR.norm a ha) x).1 hx, (rf_fix (hR.norm a ha) y).1 hy⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hx, hy⟩, rfl⟩
    have hd := (conjDer_iff hC hR _).2 ⟨a, ha, rfl⟩
    exact ⟨⟨hd, (rf_fix (hR.norm a ha) x).2 hx⟩, hd, (rf_fix (hR.norm a ha) y).2 hy⟩

theorem rf_neg_eig {c : Fin n → ZMod 3} (hc : Refl.bf C c c = 2) :
    rf C c *ᵥ (C *ᵥ c) = -(C *ᵥ c) := by
  rw [rf_mulVec]
  unfold Refl.bf at hc
  rw [hc]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

private theorem ln_zero' (q : ℕ) : ln 0 q = 0 := by
  rw [ln_eq, Nat.zero_div]

private theorem dec_zero' (n : ℕ) : dec n 0 = 0 := by
  funext q
  rw [dec_apply, ln_zero', Nat.cast_zero]
  rfl

private theorem VOK_zero' (n : ℕ) : VOK n 0 :=
  ⟨Nat.pow_pos (by decide : 0 < 4), fun q _ => by rw [ln_zero']; decide⟩

private theorem rtNormV_lead {x : ℕ} (hn : n ≤ 8) (hx : VOK n x) (hx0 : x ≠ 0) :
    VOK n (normV n x) ∧ lead n (normV n x) = 1 := by
  rcases lead_spec n x with ⟨-, h0⟩ | ⟨q0, hq0, hl, hne, hbelow⟩
  · exact absurd (VOK_ext hx (VOK_zero' n) fun q hq => by rw [h0 q hq, ln_zero']) hx0
  · have hle := hx.2 q0 hq0
    rw [normV_ite]
    by_cases h2 : lead n x = 2
    · rw [if_pos h2]
      refine ⟨VOK_negL hn hx, ?_⟩
      have hneg : ∀ q < n, (ln (negL x) q = 0 ↔ ln x q = 0) := fun q hq => by
        rw [ln_negL (by omega) (hx.2 q hq)]
        have := hx.2 q hq
        omega
      rcases lead_spec n (negL x) with ⟨-, h0⟩ | ⟨q1, hq1, hl1, hne1, hbelow1⟩
      · exact absurd ((hneg q0 hq0).1 (h0 q0 hq0)) hne
      · rcases lt_trichotomy q1 q0 with h | rfl | h
        · exact absurd ((hneg q1 hq1).2 (hbelow q1 h)) hne1
        · rw [hl1, ln_negL (by omega) hle, ← hl, h2]
        · exact absurd ((hneg q0 hq0).1 (hbelow1 q0 h)) hne
    · rw [if_neg h2]
      refine ⟨hx, ?_⟩
      rw [hl] at h2 ⊢
      omega

private theorem neg_eig {t : Matrix (Fin n) (Fin n) (ZMod 3)} {w : Fin n → ZMod 3}
    (h : t *ᵥ w = -w) : t *ᵥ (-w) = -(-w) := by
  rw [mulVec_neg, h]

theorem rootP_rep {C m RP N V b Tm : ℕ} (hC : (Cm n C).IsSymm) (hn : n ≤ 8) (hn0 : 0 < n)
    (hR : RootData (Cm n C) m (Rv n RP)) (h1 : rootOK n C m RP = true)
    (hp : ptsOK n N V = true) (hb : b < N) (htx : txOK n m RP (vget V b) Tm = true)
    (hrt : rtRep n m RP V b Tm 0 N = true) : RootP (Cm n C) (dec n (vget V b)) := by
  have hr := rootOK_sound hn h1
  have hs := (ptsOK_sound hn hp).2
  obtain ⟨-, hT⟩ := txOK_sound htx
  have hT' : ∀ a < m, (Tm.testBit a = true ↔ Rv n RP a ⬝ᵥ dec n (vget V b) = 0) :=
    fun a ha => (hT a ha).trans (dot3_zero_iff _ _ _)
  have hcx : (fixSet (Cm n C) (dec n (vget V b))).ncard = cntN m (bitB Tm) := by
    rw [fixSet_eq hC hR, ncard_roots hR, cntN_eq]
    exact congrArg Finset.card (Finset.filter_congr fun a ha => by
      rw [bitB_eq, hT' a (Finset.mem_range.1 ha)])
  have heig : ∀ w, (rtMask m RP).testBit w = true →
      ∃ t, ConjDer (sS (Cm n C)) t ∧ t *ᵥ dec n w = -dec n w := by
    intro w hw
    rcases rtMask_sound hw with rfl | ⟨a, ha, rfl | rfl⟩
    · refine ⟨sS (Cm n C) ⟨0, hn0⟩, ConjDer.base _, ?_⟩
      rw [dec_zero', mulVec_zero, neg_zero]
    · have hd := (conjDer_iff hC hR _).2 ⟨a, ha, rfl⟩
      refine ⟨_, hd, ?_⟩
      rw [(hr a ha).2.1, dec_cvec]
      exact rf_neg_eig (hR.norm a ha)
    · have hd := (conjDer_iff hC hR _).2 ⟨a, ha, rfl⟩
      refine ⟨_, hd, ?_⟩
      have hl : ∀ q < n, ln (rC RP a) q ≤ 2 := fun q hq => by
        rw [(hr a ha).2.1, ln_cvec C _ hq]
        omega
      rw [dec_negL hn hl, (hr a ha).2.1, dec_cvec]
      exact neg_eig (rf_neg_eig (hR.norm a ha))
  intro hx y hy
  have hcnt : cntN m (bitB Tm) = 21 ∨ cntN m (bitB Tm) = 36 := by
    rw [← hcx]
    exact hx
  have hrt' : ∀ j < N,
      rtPlane n m RP (rtMask m RP) (vget V b) (negL (vget V b)) Tm (vget V j) = true :=
    fun j hj => by
      have h := rtRep_sound hrt hcnt j hj
      rwa [Nat.zero_add] at h
  by_cases hy0 : y = 0
  · refine ⟨0, sS (Cm n C) ⟨0, hn0⟩, ConjDer.base _, ?_⟩
    rw [hy0, zero_smul, add_zero, mulVec_zero, neg_zero]
  have hY := VOK_enc n y
  have hY0 : enc n y ≠ 0 := fun e => hy0 (by rw [← dec_enc n y, e, dec_zero'])
  obtain ⟨hzv, hzl⟩ := rtNormV_lead hn hY hY0
  obtain ⟨p, hpN, hpz⟩ := ptsOK_complete hn hp hzv hzl
  have hz := (hs p hpN).1
  have hx' := (hs b hb).1
  have hzy : dec n (vget V p) = y ∨ dec n (vget V p) = -y := by
    rw [hpz]
    rcases normV_eq n (enc n y) with e | e <;> rw [e]
    · exact Or.inl (dec_enc n y)
    · exact Or.inr (by rw [dec_negL hn hY.2, dec_enc n y])
  have hfz : fixSet (Cm n C) (dec n (vget V p)) = fixSet (Cm n C) y := by
    rcases hzy with e | e <;> rw [e]
    exact fixSet_neg y
  have h13 : 13 ≤ rtCnt n m RP Tm (vget V p) := by
    rw [← hfz, fixSet_inter hC hR, ncard_roots hR] at hy
    rw [rtCnt_eq]
    refine le_of_le_of_eq hy (congrArg Finset.card (Finset.filter_congr fun a ha => ?_))
    exact and_congr (hT' a (Finset.mem_range.1 ha)).symm
      (dot3_zero_iff n (rc RP a) (vget V p)).symm
  have hpl := rtPlane_sound (hrt' p hpN) h13
  have hk : ∃ k : ZMod 3, ∃ t, ConjDer (sS (Cm n C)) t ∧
      t *ᵥ (dec n (vget V p) + k • dec n (vget V b)) =
        -(dec n (vget V p) + k • dec n (vget V b)) := by
    rcases hpl with h | h | h
    · obtain ⟨t, ht, e⟩ := heig _ h
      refine ⟨0, t, ht, ?_⟩
      rwa [zero_smul, add_zero]
    · obtain ⟨t, ht, e⟩ := heig _ h
      refine ⟨1, t, ht, ?_⟩
      rwa [one_smul, ← dec_addV3]
    · obtain ⟨t, ht, e⟩ := heig _ h
      refine ⟨-1, t, ht, ?_⟩
      rwa [neg_one_smul, ← dec_negL hn hx'.2, ← dec_addV3]
  obtain ⟨k, t, ht, e⟩ := hk
  rcases hzy with hzy | hzy
  · exact ⟨k, t, ht, by rw [← hzy]; exact e⟩
  · refine ⟨-k, t, ht, ?_⟩
    have e2 : y + (-k) • dec n (vget V b) = -(dec n (vget V p) + k • dec n (vget V b)) := by
      rw [hzy, neg_add, neg_neg, neg_smul]
    rw [e2]
    exact neg_eig e

theorem root_facts {C N V k lv m RP CL PT : ℕ} {S D bs cs : List ℕ} {RR Q : List (List ℕ)}
    (hn : n ≤ 8) (hn0 : 0 < n) (hnm : n ≤ m) (hm : m ≠ 21 ∧ m ≠ 36) (hC : (Cm n C).IsSymm)
    (h1 : rootOK n C m RP = true) (h2 : simpleOK n RP = true) (h3 : closOK n m RP CL = true)
    (h4 : parOK n m CL PT = true) (h5 : distOK m RP = true)
    (hp : ptsOK n N V = true) (hg : ∀ j < n, genJ n C N S V j = true)
    (ht : ∀ t < k, getS bs t < N ∧
      rowsK N 12 4095 S n lv (getS D t) (getS bs t) (getS cs t) (getLs RR t) = true)
    (hc : coverOK N k D = true) (hrep : ∀ t < k, repK n m RP V (getS bs t) (getLs Q t) = true)
    (hrt : ∀ t < k, rtRep n m RP V (getS bs t) (getS (getLs Q t) 0) 0 N = true) :
    ∀ x : Fin n → ZMod 3, RootP (Cm n C) x := by
  have hR := rootData_of hn hnm h1 h2 h3 h4 h5
  intro x
  by_cases hx : x = 0
  · intro h0
    exfalso
    have e : (fixSet (Cm n C) x).ncard = m := by
      rw [fixSet_eq hC hR, ncard_roots hR, hx]
      simp [dotProduct_zero]
    rw [e] at h0
    omega
  have hX := VOK_enc n x
  have hX0 : enc n x ≠ 0 := fun e => hx (by rw [← dec_enc n x, e, dec_zero'])
  obtain ⟨t, htk, y, hy, hyr, hxy⟩ := cover_reach hn hp hg ht hc hX hX0
  have hb := (ht t htk).1
  have hd0 := rootP_rep hC hn hn0 hR h1 hp hb (repK_sound (hrep t htk)).1 (hrt t htk)
  have hvb := ((ptsOK_sound hn hp).2 _ hb).1
  obtain ⟨-, hdy⟩ := rootP_reach hR hvb hd0 hyr
  rw [← dec_enc n x]
  rcases hxy with e | e
  · rw [e]
    exact hdy
  · rw [e, dec_negL hn hy.2]
    exact rootP_neg hdy

end CFSG.KC.FrameE78

end
