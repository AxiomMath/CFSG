module

public import Certificates.Data.Kernel.Spor.PEnumBC
public import CFSG.Certificates.Kernel.Spor.PEnumBSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.MulHCaySound
import CFSG.Certificates.Kernel.J2ModelsSound

public section

namespace CFSG.KS.PEnumB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

variable {n w : Nat} {bs : List Nat} {M : Nat → Prop}

theorem penumSlBC_spec {m k cnt lo len : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlBC n w m bs G GI k cnt T PL POS SRT SRI lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → penumPtBC n w m bs G GI k cnt T PL POS SRT SRI i = true := by
  intro i h1 h2 h3
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem penumPtBC_step {m k cnt i : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtBC n w m bs G GI k cnt T PL POS SRT SRI i = true) (hi : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧
      T i = stepK n w m true G GI (labOf PL i) (T (parOf PL i)) := by
  unfold penumPtBC at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨ht, -, -⟩ := h
  have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
  rw [e] at ht
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, Bool.and_eq_true,
    Nat.blt_eq] at ht
  exact ⟨ht.1, ht.2.1, Nat.eq_of_beq_eq_true ht.2.2.1⟩

theorem penumBC_mem (hF : BaseFaith n w bs M) {k cnt cap root : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} (hG : ∀ j < k, M (G j)) (hGI : ∀ j < k, M (GI j))
    (hR : M root) (hh : penumHdK root cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtBC n w (mask w) bs G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, M (T i) := by
  have h0 : T 0 = root := by
    unfold penumHdK at hh
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hh
    exact Nat.eq_of_beq_eq_true hh.2.2.1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [h0]
      exact hR
    · obtain ⟨hp, hl, e⟩ := penumPtBC_step (hb i hi) hi0
      rw [e]
      exact hF.comp _ _ (hF.comp _ _ (hG _ hl) (ih _ hp (by omega))) (hGI _ hl)

theorem penumPtK_eq_BC (hF : BaseFaith n w bs M) {k cnt i : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} (hT : ∀ x < cnt, M (T x)) (hG : ∀ j < k, M (G j))
    (hGI : ∀ j < k, M (GI j)) (hi : i < cnt) :
    penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i =
      penumPtBC n w (mask w) bs G GI k cnt T PL POS SRT SRI i := by
  unfold penumPtK penumPtBC
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq]
  rw [hF.canon _ (hT i hi), Bool.true_and]
  congr 2
  apply allN_congr
  intro j hj
  cases hq : Nat.blt (r32 POS (Nat.add (Nat.mul i k) j)) cnt
  · simp
  · have hq' := Nat.blt_eq.mp hq
    have e : stepK n w (mask w) true G GI j (T i) =
        pcomp n w (mask w) (pcomp n w (mask w) (G j) (T i)) (GI j) := rfl
    rw [e, hF.agreeC3_eq (hT _ hq') (hG j hj) (hT i hi) (hGI j hj)]

theorem penumPtK_of_BC (hF : BaseFaith n w bs M) {k cnt cap root : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} (hG : ∀ j < k, M (G j)) (hGI : ∀ j < k, M (GI j))
    (hR : M root) (hh : penumHdK root cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtBC n w (mask w) bs G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true :=
  fun i hi => by
    rw [penumPtK_eq_BC hF (penumBC_mem hF hG hGI hR hh hb) hG hGI hi]
    exact hb i hi

theorem bkeyLK_congr {m : Nat} {X Y : Nat} (h : ∀ b ∈ bs, pg w m X b = pg w m Y b) :
    bkeyLK w m bs X = bkeyLK w m bs Y := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change Nat.add (Nat.shiftLeft (bkeyLK w m bs X) 12) (pg w m X b) =
      Nat.add (Nat.shiftLeft (bkeyLK w m bs Y) 12) (pg w m Y b)
    rw [ih fun c hc => h c (by simp [hc]), h b (by simp)]

theorem bsortLK_inj {m cnt : Nat} {T HS HSI : Nat → Nat}
    (hs : ∀ i < cnt, bsortLK w m bs cnt T HS HSI i = true) :
    ∀ a < cnt, ∀ a' < cnt, bkeyLK w m bs (T a) = bkeyLK w m bs (T a') → a = a' := by
  refine CFSG.KS.MulH.inj_of_sortH (T := fun i => bkeyLK w m bs (T i)) (S := HS) (SI := HSI)
    fun i hi => ?_
  have h := hs i hi
  unfold bsortLK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h3
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
  simp only [Nat.blt_eq.mpr hc, ↓reduceIte] at h3
  exact Nat.blt_eq.mp h3

theorem penumHd_facts {root cnt cap : Nat} {T PL : Nat → Nat}
    (hh : penumHdK root cnt cap T PL = true) : 0 < cnt ∧ T 0 = root := by
  unfold penumHdK at hh
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact ⟨Nat.blt_eq.mp hh.1, Nat.eq_of_beq_eq_true hh.2.2.1⟩

theorem baseFaith_left {k cnt cap : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    (hn : n < 2 ^ 32) (hbs : ∀ b ∈ bs, b < n)
    (hGc : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hpt : ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, bsortLK w (mask w) bs cnt T HS HSI i = true) :
    BaseFaith n w bs (fun X => ∃ a < cnt, X = T a) := by
  have hhd := penumHd_facts hh
  have hc : ∀ a < cnt, canonK n w (mask w) (n * w) (T a) = true := fun a ha =>
    (CFSG.KS.MulH.penumPt_specH (hpt a ha)).1
  have hcomp : ∀ a < cnt, ∀ b < cnt, ∃ c < cnt, pcomp n w (mask w) (T a) (T b) = T c := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha b hb
      by_cases ha0 : a = 0
      · subst ha0
        refine ⟨b, hb, ?_⟩
        rw [hhd.2]
        exact CFSG.KC.J2Models.pcomp_idL (hc b hb)
      · obtain ⟨hp, hl, e, -⟩ := (CFSG.KS.MulH.penumPt_specH (hpt a ha)).2.1 ha0
        obtain ⟨c, hc', ec⟩ := ih _ hp (by omega) b hb
        have e' : stepK n w (mask w) false G GI (labOf PL a) (T (parOf PL a)) =
            pcomp n w (mask w) (G (labOf PL a)) (T (parOf PL a)) := rfl
        obtain ⟨hq, eq, -⟩ := (CFSG.KS.MulH.penumPt_specH (hpt c hc')).2.2.1 _ hl
        refine ⟨_, hq, ?_⟩
        rw [e, e', CFSG.KS.MulHCay.pcomp_assoc_c (hGc _ hl) (hc b hb), ec, eq]
        rfl
  exact {
    n_lt := hn
    bs_lt := hbs
    canon := fun X ⟨a, ha, e⟩ => by
      subst e
      exact hc a ha
    eq := fun X Y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ h => by
      subst ea eb
      rw [bsortLK_inj hs a ha b hb (bkeyLK_congr h)]
    comp := fun X Y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => by
      subst ea eb
      exact hcomp a ha b hb
    id := ⟨0, hhd.1, hhd.2.symm⟩ }

theorem left_gen_mem {k cnt cap j : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hGc : canonK n w (mask w) (n * w) (G j) = true) (hj : j < k)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hpt : ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true) :
    ∃ a < cnt, G j = T a := by
  have hhd := penumHd_facts hh
  obtain ⟨hq, eq, -⟩ := (CFSG.KS.MulH.penumPt_specH (hpt 0 hhd.1)).2.2.1 j hj
  refine ⟨_, hq, ?_⟩
  rw [eq]
  change G j = pcomp n w (mask w) (G j) (T 0)
  rw [hhd.2, CFSG.KC.J2Models.pcomp_idR hGc]

end CFSG.KS.PEnumB

end
