module

public import Certificates.Data.Kernel.SporSch.HNXPt
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Cert

public section

set_option maxRecDepth 100000

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.Ord Finset Matrix

theorem letB_eq' (v : Nat) (k : Nat → Bool) : letB v k = k v := by cases v <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem eq_zero_of_lanes {x : Nat} (hx : x < 2 ^ (13 * 133))
    (h : ∀ l < 133, x / 2 ^ (13 * l) % 2 ^ 13 = 0) : x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.zero_testBit]
  by_cases hb : b < 13 * 133
  · have e := h (b / 13) (by omega)
    have key : x.testBit b = (x / 2 ^ (13 * (b / 13)) % 2 ^ 13).testBit (b % 13) := by
      rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt b (by norm_num)), Bool.true_and,
        ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
      congr 1
      omega
    rw [key, e, Nat.zero_testBit]
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

theorem listA_eq {CM3 M : Nat} (hc : constsOK CM3 M = true) (T : Nat → Nat) (FL c : Nat)
    (hc64 : c ≤ 64) :
    listA T M FL c = ∑ r ∈ range 64,
      (if r < c then xv T (fldW FL (21 * r) 21) else 0) * 2 ^ (1729 * r) := by
  unfold constsOK at hc
  have hM : M = Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 399)) (nat_lit 1) :=
    Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 hc).2
  have hf : ∀ r < 64, Nat.land (getRec T 464 (fldW FL (Nat.mul 21 r) 21)) M < 2 ^ 1729 := by
    intro r _
    rw [hM]
    change getRec T 464 _ &&& ((1 <<< 399) - 1) < _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega)
      (by omega))
  unfold listA
  refine (lanes_rec_or hf c hc64).trans (Finset.sum_congr rfl fun r _ => ?_)
  congr 2
  rw [hM]
  change getRec T 464 (fldW FL (21 * r) 21) &&& ((1 <<< 399) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  unfold xv
  rw [fldW_eq (getRec T 464 _) 0 399, Nat.pow_zero, Nat.div_one]

theorem canon_ent {V : Nat} (hV : Canon 5 133 13 V) : ∀ k < 133, ∀ l < 133, ent13 V k l < 5 :=
  fun k _ l hl => by
    have h2 := hV.2 (133 * k + l) (by nlinarith)
    unfold CFSG.KS.Ord.lane at h2
    unfold ent13
    rwa [show 13 * (133 * k + l) = 1729 * k + 13 * l by ring] at h2

theorem listA_lane {CM3 M W : Nat} (hc : constsOK CM3 M = true) (hv : Canon 5 133 13 W)
    (T : Nat → Nat) {FL c : Nat} (hc64 : c ≤ 64) {k : Nat} (hk : k < c) {l : Nat} (hl : l < 133) :
    fldW (mulC CM3 (listA T M FL c) (trM W)) (1729 * k) 1729 / 2 ^ (13 * l) % 2 ^ 13 =
      (∑ j ∈ range 133, xe T (fldW FL (21 * k) 21) j * ent13 W l j) % 5 := by
  rw [row_lane _ _ _ hl, mulC_lane hc (a := fun r => if r < c then xv T (fldW FL (21 * r) 21) else 0)
    (listA_eq hc T FL c hc64) (fun r _ => by
      split
      · exact lanes_xv_lt T _
      · exact Nat.two_pow_pos _)
    (g := fun j l => ent13 W l j) (by rw [trM_eq])
    (fun j hj l hl => canon_ent hv l hl j hj) k (by omega) l hl]
  simp only [if_pos hk]
  rfl

theorem ptsImg_rows {T : Nat → Nat} {MS CM3 M G FL IL c : Nat}
    (h : ptsImg T MS CM3 M G FL IL c = true) {k : Nat} (hk : k < c) :
    fldW (mulC CM3 (listA T M FL c) G) (Nat.mul (nat_lit 1729) k) (nat_lit 1729) =
      spread MS (fldW (getRec T (nat_lit 464) (fldW IL (Nat.mul (nat_lit 21) k) (nat_lit 21)))
        (nat_lit 0) (nat_lit 399)) := by
  unfold ptsImg at h
  rw [letB_eq'] at h
  generalize mulC CM3 (listA T M FL c) G = Y at h ⊢
  exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h k hk)

theorem ptsImg_sound {T : Nat → Nat} {MS CM3 M W FL IL c : Nat} (hc : constsOK CM3 M = true)
    (hm : masksOK MS = true) (hv : Canon 5 133 13 W) (hc64 : c ≤ 64)
    (h : ptsImg T MS CM3 M (trM W) FL IL c = true) :
    ∀ k < c, xvec T (fldW IL (21 * k) 21) =
      ordMat 5 133 13 1729 W *ᵥ xvec T (fldW FL (21 * k) 21) := by
  intro k hk
  have e : fldW (mulC CM3 (listA T M FL c) (trM W)) (1729 * k) 1729 =
      spread MS (xv T (fldW IL (21 * k) 21)) := ptsImg_rows h hk
  refine xvec_img fun l hl => ?_
  have e1 : fldW (mulC CM3 (listA T M FL c) (trM W)) (1729 * k) 1729 / 2 ^ (13 * l) % 2 ^ 13 =
      spread MS (xv T (fldW IL (21 * k) 21)) / 2 ^ (13 * l) % 2 ^ 13 := by rw [e]
  rw [listA_lane hc hv T hc64 hk hl, spread_lane hm (lanes_xv_lt T _) l hl] at e1
  exact e1.symm

theorem lanes_zero_iff {V : Nat} (hV : Canon 5 133 13 V) (x : Fin 133 → ZMod 5) (u : Nat → Nat)
    (hu : ∀ j (hj : j < 133), (u j : ZMod 5) = x ⟨j, hj⟩) :
    (∀ l < 133, (∑ j ∈ range 133, u j * ent13 V l j) % 5 = 0) ↔ ordMat 5 133 13 1729 V *ᵥ x = 0 := by
  constructor
  · intro h
    funext l
    have e := h l.val l.isLt
    change ∑ j : Fin 133, ordMat 5 133 13 1729 V l j * x j = 0
    have e2 : ((∑ j ∈ range 133, u j * ent13 V l j : Nat) : ZMod 5) = 0 := by
      rw [← ZMod.natCast_mod, e, Nat.cast_zero]
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun j => ((u j * ent13 V l j : Nat) : ZMod 5))]
      at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_mul, hu j j.isLt, mul_comm]
    rfl
  · intro h l hl
    have e := congrFun h ⟨l, hl⟩
    change ∑ j : Fin 133, ordMat 5 133 13 1729 V ⟨l, hl⟩ j * x j = 0 at e
    have e2 : ((∑ j ∈ range 133, u j * ent13 V l j : Nat) : ZMod 5) = 0 := by
      rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun j => ((u j * ent13 V l j : Nat) : ZMod 5)),
        ← e]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_mul, hu j j.isLt, mul_comm]
      rfl
    have := congrArg ZMod.val e2
    rwa [ZMod.val_natCast, ZMod.val_zero] at this

theorem zeroRows_eq (Y : Nat) : ∀ c, zeroRows Y c =
    ((range c).filter fun r => fldW Y (1729 * r) 1729 = 0).card
  | 0 => rfl
  | c + 1 => by
    change Nat.add (zeroRows Y c) (Bool.rec (motive := fun _ => Nat) 0 1
      (Nat.beq (fldW Y (1729 * c) 1729) 0)) = _
    rw [zeroRows_eq Y c, Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    cases hb : Nat.beq (fldW Y (1729 * c) 1729) 0
    · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
      rfl
    · rw [if_pos (Nat.eq_of_beq_eq_true hb)]
      rfl

theorem fixLeaf_one {T : Nat → Nat} {CM3 M V : Nat} (hc : constsOK CM3 M = true)
    (hV : Canon 5 133 13 V) {b c : Nat} (hc64 : c ≤ 64) :
    fixLeaf T 464 CM3 M [trM V] b c =
      ((range c).filter fun r => ordMat 5 133 13 1729 V *ᵥ xvec T (64 * b + r) = 0).card := by
  have e0 : fixLeaf T 464 CM3 M [trM V] b c = zeroRows (mulC CM3 (leafA (T b) 464 c M) (trM V)) c := by
    unfold fixLeaf
    rw [strictN_eq']
    change (zeroRows (mulC CM3 (leafA (T b) 464 c M) (trM V)) c <<< 0) ||| 0 = _
    rw [Nat.shiftLeft_zero, Nat.or_zero]
  rw [e0, zeroRows_eq]
  have hent := canon_ent hV
  refine congrArg Finset.card (Finset.filter_congr fun r hr => ?_)
  have hr' := Finset.mem_range.1 hr
  have hlane : ∀ l < 133, fldW (mulC CM3 (leafA (T b) 464 c M) (trM V)) (1729 * r) 1729 /
      2 ^ (13 * l) % 2 ^ 13 = (∑ j ∈ range 133, xe T (64 * b + r) j * ent13 V l j) % 5 := by
    intro l hl
    rw [row_lane _ _ _ hl, mulC_lane hc (a := fun r => if r < c then T b / 2 ^ (464 * r) % 2 ^ 399
      else 0) (leafA_eq hc (T b) c hc64) (fun r _ => by
        split
        · exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact Nat.two_pow_pos _)
      (g := fun j l => ent13 V l j) (by rw [trM_eq])
      (fun j hj l hl => hent l hl j hj) r (by omega) l hl]
    simp only [if_pos hr']
    unfold xe
    rw [xv_leaf T b r (by omega)]
  rw [← lanes_zero_iff hV (xvec T (64 * b + r)) (xe T (64 * b + r)) (fun j _ => rfl)]
  constructor
  · intro h l hl
    rw [← hlane l hl, h, Nat.zero_div, Nat.zero_mod]
  · intro h
    refine eq_zero_of_lanes (by rw [fldW_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
      fun l hl => ?_
    rw [hlane l hl]
    exact h l hl

theorem fixSum_eq (T : Nat → Nat) (CM3 M G lo : Nat) : ∀ n, fixSum T CM3 M G lo n =
    ∑ i ∈ range n, fixLeaf T 464 CM3 M [G] (lo + i) (hnxC (lo + i))
  | 0 => rfl
  | n + 1 => by
    change CFSG.KC.Loop.strictN (fixSum T CM3 M G lo n) (fun a => Nat.add a
      (fixLeaf T 464 CM3 M [G] (Nat.add lo n) (hnxC (Nat.add lo n)))) = _
    rw [strictN_eq', fixSum_eq T CM3 M G lo n, Finset.sum_range_succ]
    rfl

theorem card_fix_eq {T : Nat → Nat} {CM3 M V : Nat} (hc : constsOK CM3 M = true)
    (hV : Canon 5 133 13 V) :
    ((range 1140000).filter fun i => ordMat 5 133 13 1729 V *ᵥ xvec T i = 0).card =
      ∑ b ∈ range 17813, fixLeaf T 464 CM3 M [trM V] b (hnxC b) := by
  rw [Finset.card_filter, ← sum_leaves]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fixLeaf_one hc hV (hnxC_le b), Finset.card_filter]

theorem fixSum_add (T : Nat → Nat) (CM3 M G : Nat) {a n v : Nat}
    (h : fixSum T CM3 M G a n = v) {u : Nat}
    (hu : ∑ b ∈ range a, fixLeaf T 464 CM3 M [G] b (hnxC b) = u) :
    ∑ b ∈ range (a + n), fixLeaf T 464 CM3 M [G] b (hnxC b) = u + v := by
  rw [Finset.sum_range_add, hu, ← h, fixSum_eq]

theorem wordC_sound {R : Nat → Nat} : ∀ cs : List Nat, (∀ c ∈ cs, Canon 5 133 13 (R c)) →
    Canon 5 133 13 (wordC R cs) ∧
      ordMat 5 133 13 1729 (wordC R cs) = (cs.map fun c => ordMat 5 133 13 1729 (R c)).prod
  | [], _ => ⟨(one_sound CFSG.KD.OrdHN.consts).1, one_ord⟩
  | c :: cs, h => by
    obtain ⟨h1, h2⟩ := wordC_sound cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    obtain ⟨h3, h4⟩ := mm_sound (h c List.mem_cons_self) h1
    refine ⟨h3, ?_⟩
    change ordMat 5 133 13 1729 (CFSG.KC.LL.HN.mm (R c) (wordC R cs)) = _
    rw [h4, h2, List.map_cons, List.prod_cons]

theorem lanesEq_sound {W : Nat} {Y : Nat → Nat} (h : lanesEq W Y = true) :
    ∀ r < 133, ∀ c < 133, ent13 W r c = lane5 (Y r) c := by
  intro r hr c hc
  unfold lanesEq at h
  have h1 := CFSG.KS.allN_spec h r hr
  beta_reduce at h1
  rw [letB_eq', letB_eq'] at h1
  have h2 : fldW (fldW W (1729 * r) 1729) (13 * c) 13 = lane5 (Y r) c :=
    Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h1 c hc)
  rw [← h2, fldW_eq, fldW_eq, lanes_dm _ _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl

end CFSG.KS.SporSch.HNXP

end
