module

public import Certificates.Data.Kernel.FourJBfsB
public import Certificates.Data.Kernel.FourJoinedK
public import CFSG.Certificates.Kernel.Spor.PEnumBSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.FourJB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnumB CFSG.KC.BfsPin

noncomputable def treeWB (n w : Nat) (G PAR LAB : Nat → Nat) (c : Nat) : Nat :=
  if c = 0 then pidn n w else
    if h : PAR c < c then pcomp n w (mask w) (G (LAB c)) (treeWB n w G PAR LAB (PAR c))
    else pidn n w
termination_by c

variable {n w : Nat} {G PAR LAB : Nat → Nat}

theorem treeWB_zero : treeWB n w G PAR LAB 0 = pidn n w := by
  rw [treeWB]
  simp

theorem treeWB_pos {c : Nat} (hc : c ≠ 0) (hp : PAR c < c) :
    treeWB n w G PAR LAB c = pcomp n w (mask w) (G (LAB c)) (treeWB n w G PAR LAB (PAR c)) := by
  rw [treeWB]
  simp [hc, hp]

theorem baseFaith_ext {bs cs : List Nat} {M : Nat → Prop} (hF : BaseFaith n w bs M)
    (hsub : ∀ b ∈ bs, b ∈ cs) (hlt : ∀ b ∈ cs, b < n) : BaseFaith n w cs M where
  n_lt := hF.n_lt
  bs_lt := hlt
  canon := hF.canon
  eq := fun X Y hX hY h => hF.eq X Y hX hY fun b hb => h b (hsub b hb)
  comp := hF.comp
  id := hF.id

theorem imgStepK_iff {nc : Nat} {I f : Nat → Nat} {s d : Nat} :
    imgStepK nc I f s d = true ↔ ∀ j < nc, I (d * nc + j) = f (I (s * nc + j)) := by
  unfold imgStepK
  simp only [CFSG.KS.Raw.Orb.allN_iff, Nat.beq_eq, Nat.add_eq, Nat.mul_eq]

theorem bfsBK_spec {cs : List Nat} {nc kp ng N : Nat} {act : Nat → Nat → Nat}
    {POS I S : Nat → Nat} (h : bfsBK cs nc kp ng N act PAR LAB POS I S = true) :
    nc = cs.length ∧ kp < nc ∧ (∀ j < nc, I j = cs.getD j 0) ∧
    (∀ c < N, c ≠ 0 → PAR c < c ∧ LAB c < ng ∧
      ∀ j < nc, I (c * nc + j) = act (LAB c) (I (PAR c * nc + j))) ∧
    (∀ i < N, ∀ k < ng, POS (i * ng + k) < N ∧
      ∀ j < nc, I (POS (i * ng + k) * nc + j) = act k (I (i * nc + j))) ∧
    distinctK N (fun i => I (i * nc + kp)) S = true := by
  unfold bfsBK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.blt_eq.mp h2,
    fun j hj => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h3 j hj),
    fun c hc hc0 => ?_, fun i hi k hk => ?_, h6⟩
  · have e := CFSG.KS.Raw.Orb.allN_iff.1 h4 c hc
    have hb : Nat.beq c 0 = false := Bool.eq_false_iff.2 fun h => hc0 (Nat.eq_of_beq_eq_true h)
    rw [hb] at e
    simp only [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq, imgStepK_iff, Bool.false_eq_true, ↓reduceIte] at e
    exact e
  · have e := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h5 i hi) k hk
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq,
      imgStepK_iff, Nat.add_eq, Nat.mul_eq] at e
    exact e

theorem bfsBK_sound {M : Nat → Prop} {cs : List Nat} {nc kp ng N : Nat}
    {act : Nat → Nat → Nat} {POS I S : Nat → Nat}
    (hF : BaseFaith n w cs M) (hG : ∀ k < ng, M (G k))
    (hact : ∀ k < ng, ∀ x < n, act k x = pg w (mask w) (G k) x)
    (h : bfsBK cs nc kp ng N act PAR LAB POS I S = true) :
    treeWB n w G PAR LAB 0 = pidn n w ∧ (∀ i < N, M (treeWB n w G PAR LAB i)) ∧
    (∀ i < N, ∀ j < nc, pg w (mask w) (treeWB n w G PAR LAB i) (cs.getD j 0) = I (i * nc + j)) ∧
    (∀ i < N, ∀ k < ng, POS (i * ng + k) < N ∧
      treeWB n w G PAR LAB (POS (i * ng + k)) = pcomp n w (mask w) (G k) (treeWB n w G PAR LAB i)) ∧
    (∀ a < N, ∀ b < N, treeWB n w G PAR LAB a = treeWB n w G PAR LAB b → a = b) := by
  obtain ⟨hnc, hkp, h0, htr, hpos, hd⟩ := bfsBK_spec h
  have hgd : ∀ j (hj : j < cs.length), cs.getD j 0 = cs[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hcs : ∀ j < nc, cs.getD j 0 < n := fun j hj => by
    rw [hgd j (by omega)]
    exact hF.bs_lt _ (List.getElem_mem _)
  obtain ⟨hn24, hw, -⟩ := PF.canon_facts (hF.canon _ hF.id)
  have hM : ∀ i < N, M (treeWB n w G PAR LAB i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [treeWB_zero]
        exact hF.id
      · obtain ⟨hp, hl, -⟩ := htr i hi hi0
        rw [treeWB_pos hi0 hp]
        exact hF.comp _ _ (hG _ hl) (ih _ hp (by omega))
  have himg : ∀ i < N, ∀ j < nc,
      pg w (mask w) (treeWB n w G PAR LAB i) (cs.getD j 0) = I (i * nc + j) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi j hj
      by_cases hi0 : i = 0
      · subst hi0
        rw [treeWB_zero, PF.pg_pidn hn24 hw (hcs j hj), Nat.zero_mul, Nat.zero_add, h0 j hj]
      · obtain ⟨hp, hl, he⟩ := htr i hi hi0
        have hx : I (PAR i * nc + j) < n := by
          rw [← ih _ hp (by omega) j hj]
          exact (PF.canon_facts (hF.canon _ (hM _ (by omega)))).2.2.2 _ (hcs j hj)
        rw [treeWB_pos hi0 hp, PF.pg_pcomp hF.n_lt (hcs j hj), ih _ hp (by omega) j hj, he j hj,
          hact _ hl _ hx]
  refine ⟨treeWB_zero, hM, himg, fun i hi k hk => ?_, fun a ha b hb e => ?_⟩
  · obtain ⟨hq, he⟩ := hpos i hi k hk
    refine ⟨hq, hF.eq _ _ (hM _ hq) (hF.comp _ _ (hG k hk) (hM i hi)) fun b hb => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have hj' : j < nc := by omega
    have hx : I (i * nc + j) < n := by
      rw [← himg i hi j hj']
      exact (PF.canon_facts (hF.canon _ (hM i hi))).2.2.2 _ (hcs j hj')
    rw [← hgd j hj, himg _ hq j hj', PF.pg_pcomp hF.n_lt (hcs j hj'), himg i hi j hj',
      he j hj', hact k hk _ hx]
  · refine distinctK_inj hd a ha b hb ?_
    change I (a * nc + kp) = I (b * nc + kp)
    rw [← himg a ha kp hkp, ← himg b hb kp hkp, e]

theorem wordR_M {M : Nat → Prop} {bs : List Nat} (hF : BaseFaith n w bs M) {lf L : Nat → Nat}
    (hl : ∀ l, M (lf l)) : ∀ len o, M (CFSG.KC.FourJ.wordR n w lf L len o)
  | 0, _ => hF.id
  | len + 1, o => hF.comp _ _ (hl (L o)) (wordR_M hF hl len (o + 1))

theorem chaseR_eq {M : Nat → Prop} {bs : List Nat} (hF : BaseFaith n w bs M) {lf L : Nat → Nat} :
    ∀ len o, ∀ x < n, chaseR w lf L len o x = pg w (mask w) (CFSG.KC.FourJ.wordR n w lf L len o) x
  | 0, _, x, hx => by
    obtain ⟨hn24, hw, -⟩ := PF.canon_facts (hF.canon _ hF.id)
    exact (PF.pg_pidn hn24 hw hx).symm
  | len + 1, o, x, hx => by
    change pg w (mask w) (lf (L o)) (chaseR w lf L len (o + 1) x) =
      pg w (mask w) (pcomp n w (mask w) (lf (L o)) (CFSG.KC.FourJ.wordR n w lf L len (o + 1))) x
    rw [PF.pg_pcomp hF.n_lt hx, chaseR_eq hF len (o + 1) x hx]

theorem chaseT_eq {M : Nat → Prop} {bs : List Nat} (hF : BaseFaith n w bs M) {lf O L : Nat → Nat}
    (t x : Nat) (hx : x < n) :
    chaseT w lf O L t x = pg w (mask w) (CFSG.KC.FourJ.wordT n w lf O L t) x :=
  chaseR_eq hF _ _ x hx

end CFSG.KC.FourJB

end
