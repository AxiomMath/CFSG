module

public import Certificates.Data.Kernel.Misc.RuFourth
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.Kernel.Spor.TextAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.WordsInputs
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Monster.B.Co2.PermArr
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.Misc.RuFourth

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSporadicStandard.TwoRu
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.Bridge.SurjD.Native

#kc_generalize FourthGen (rho surj img : String)
    using [CFSG.Sporadic.Recognition.RuMultiplier.ruRhoText ↦ rho,
      CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText ↦ surj,
      CFSG.Sporadic.Bridge.SurjD.Native.ruImgText ↦ img] :
  ∀ {R RI : Nat → Nat} {P0 : List Int} {y x₁ x₂ : Nat},
    (∀ k < 3,
      CFSG.Monster.B.Co2.Native.hexTable 4 16240 (16240 * k) ruRhoText = unpack 16240 14 (R k)) →
    (ruSpec ()).surjWords[0]! = P0 →
    (∀ l < 3, permOK 16240 14 16383 (16240 * 14) (R l) (RI l) = true) →
    letters3 P0 = true → zOK R RI P0 y = true →
    oneP R RI P0 (wordFrom R RI [-3, 2] idP) 320 x₁ = true →
    oneP R RI P0 (wordFrom R RI [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3] idP)
      48 x₂ = true →
    ruFourthCheck = true

open CFSG.Monster.B.Co2.Native (eqA idA invCand)
open CFSG.Sporadic.Schreier.Tits (wordArr wordIn)
open CFSG.LieType.Multipliers.Tits (zword)
open CFSG.Sporadic.Presentation.Ru.Exact (gc)
open CFSG.Monster.B.Co2 (toLetters)

private theorem gc_eq : gc = 3 := rfl

private theorem and_true_of {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

private theorem not_true_of {b : Bool} (h : b = true → False) : (!b) = true := by
  cases b
  · rfl
  · exact absurd rfl h

private theorem eq_false_of_bIf {c : Bool}
    (h : Bool.rec (motive := fun _ => Bool) true false c = true) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

private theorem beq_eq_nat (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

private theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

private theorem rep_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : CFSG.Monster.B.Co2.Rep n t g) : CFSG.Monster.B.Co2.Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

private theorem lettersOK_zword {m : ℕ} (w : List (Fin m × Bool)) :
    CFSG.Monster.B.Co2.Native.lettersOK m (zword w) = true := by
  unfold CFSG.Monster.B.Co2.Native.lettersOK zword
  rw [List.all_map, List.all_eq_true]
  rintro ⟨i, b⟩ -
  have hi := i.2
  cases b
  · show (-(((i : ℕ) : ℤ) + 1) != 0 && decide ((-(((i : ℕ) : ℤ) + 1)).natAbs ≤ m)) = true
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    omega
  · show ((((i : ℕ) : ℤ) + 1) != 0 && decide ((((i : ℕ) : ℤ) + 1).natAbs ≤ m)) = true
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    omega

private theorem zword_append {m : ℕ} (u v : List (Fin m × Bool)) :
    zword (u ++ v) = zword u ++ zword v :=
  List.map_append

private theorem zword_toLetters {m : ℕ} : ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ m) →
    zword (toLetters m w) = w
  | [], _ => rfl
  | z :: w, h => by
    obtain ⟨hz0, hzm⟩ := h z (List.mem_cons.2 (Or.inl rfl))
    have ih := zword_toLetters w fun y hy => h y (List.mem_cons.2 (Or.inr hy))
    have e : toLetters m (z :: w) =
        (⟨z.natAbs - 1, by omega⟩, decide (0 < z)) :: toLetters m w :=
      List.filterMap_cons_some (dif_pos ⟨hz0, hzm⟩)
    rw [e]
    change (if decide (0 < z) = true then ((z.natAbs - 1 : ℕ) : ℤ) + 1
      else -(((z.natAbs - 1 : ℕ) : ℤ) + 1)) :: zword (toLetters m w) = z :: w
    rw [ih]
    congr 1
    rcases lt_or_gt_of_ne hz0 with hneg | hpos
    · rw [if_neg fun hc => absurd (of_decide_eq_true hc) (not_lt.2 hneg.le)]
      omega
    · rw [if_pos (decide_eq_true hpos)]
      omega

private theorem wordIn_wordPow {G : Type*} [Group G] (gs : ℕ → G) (w : List (Fin gc × Bool)) :
    ∀ k : ℕ, wordIn gc gs (zword (wordPow k w)) = wordIn gc gs (zword w) ^ k
  | 0 => by
    rw [pow_zero]
    rfl
  | k + 1 => by
    have e : zword (wordPow (k + 1) w) = zword w ++ zword (wordPow k w) := List.map_append
    rw [e, CFSG.Sporadic.Schreier.Tits.wordIn_append, wordIn_wordPow gs w k, pow_succ']

private theorem lettersK_of_letters3 {j : ℕ} (hj : 3 ≤ j) :
    ∀ wd : List ℤ, letters3 wd = true → lettersK j wd = true
  | [], _ => rfl
  | z :: wd, h => by
    have h' : strictB (Mathieu.icode z) (fun c => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (letters3 wd) (Nat.ble c 7)) (Nat.blt 1 c)) =
        true := h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    rw [Orb.lettersK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq]
    exact ⟨⟨by omega, by omega⟩, lettersK_of_letters3 hj wd h3⟩

private noncomputable def psq (X : ℕ) : ℕ := pcomp 16240 14 (mask 14) X X

private theorem prep_word {R RI : ℕ → ℕ} {gs : ℕ → Equiv.Perm (Fin 16240)}
    (hS : ∀ h < gc, Orb.PRep 16240 14 (R h) (gs h))
    (hSI : ∀ h < gc, Orb.PRep 16240 14 (RI h) (gs h)⁻¹) {wd : List ℤ}
    (hl : lettersK gc wd = true) : Orb.PRep 16240 14 (wordFrom R RI wd idP) (wordIn gc gs wd) :=
  (Orb.prep_wordK (n := 16240) (w := 14) (by norm_num) (by norm_num) hS hSI wd hl).1

private theorem ptWord_eq (R RI : ℕ → ℕ) : ∀ (wd : List ℤ) (x : ℕ), x < 16240 →
    ptWord R RI wd x = pg 14 (mask 14) (wordFrom R RI wd idP) x
  | [], x, hx => (PF.pg_pidn (n := 16240) (w := 14) (by norm_num) (by norm_num) hx).symm
  | z :: wd, x, hx => by
    have e1 : ptWord R RI (z :: wd) x =
        pg 14 (mask 14) (letterP R RI (Mathieu.icode z)) (ptWord R RI wd x) := by
      change strictN (ptWord R RI wd x) (fun y => strictN (Mathieu.icode z) (fun c =>
        pg 14 (mask 14) (letterP R RI c) y)) = _
      rw [Orb.strictN_eq, Orb.strictN_eq]
    have e2 : wordFrom R RI (z :: wd) idP =
        pcomp 16240 14 (mask 14) (letterP R RI (Mathieu.icode z)) (wordFrom R RI wd idP) := by
      change strictN (wordFrom R RI wd idP) (fun T => strictN (Mathieu.icode z) (fun c =>
        pcomp 16240 14 (mask 14) (letterP R RI c) T)) = _
      rw [Orb.strictN_eq, Orb.strictN_eq]
    rw [e1, e2, PF.pg_pcomp (by norm_num) hx, ptWord_eq R RI wd x hx]

private theorem ptWord2 {R RI : ℕ → ℕ} {P0 : List ℤ} {τ : Equiv.Perm (Fin 16240)}
    (hτ : Orb.PRep 16240 14 (wordFrom R RI P0 idP) τ) {x : ℕ} (hx : x < 16240) :
    ptWord R RI P0 (ptWord R RI P0 x) = ((τ * τ) ⟨x, hx⟩ : ℕ) := by
  have h1 : ptWord R RI P0 x = τ ⟨x, hx⟩ := by
    rw [ptWord_eq R RI P0 x hx]
    exact hτ ⟨x, hx⟩
  rw [h1, ptWord_eq R RI P0 _ (τ ⟨x, hx⟩).2]
  exact hτ (τ ⟨x, hx⟩)

private theorem ne_one_of_ne {P : ℕ} {g : Equiv.Perm (Fin 16240)}
    (hP : Orb.PRep 16240 14 P g) (hshr : P >>> (16240 * 14) = 0) (h : P ≠ pidn 16240 14) :
    g ≠ 1 := by
  rintro rfl
  refine h (PF.eq_of_fields (n := 16240) (w := 14) (p := P) (q := pidn 16240 14) (by norm_num)
    hshr (PF.pidn_shr (by norm_num) (by norm_num)) fun i hi => ?_)
  have e : pg 14 (mask 14) P i = i := hP ⟨i, hi⟩
  rw [e, PF.pg_pidn (n := 16240) (w := 14) (by norm_num) (by norm_num) hi]

private theorem foldr_count (f : ℕ → Bool) : ∀ l : List ℕ,
    l.foldr (fun i acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.succ acc) (f i)) 0 =
      (l.filter f).length
  | [] => rfl
  | a :: l => by
    rw [List.foldr_cons, foldr_count f l, List.filter_cons]
    cases f a <;> rfl

private theorem fixCnt_eq (P : ℕ) :
    fixCnt P = ((List.range 16240).filter fun i => Nat.beq (pg 14 (mask 14) P i) i).length := by
  unfold fixCnt
  rw [Orb.foldN_eq]
  exact foldr_count _ _

private theorem fix_count {t : Array ℕ} {P : ℕ} {g : Equiv.Perm (Fin 16240)}
    (ht : CFSG.Monster.B.Co2.Rep 16240 t g) (hP : Orb.PRep 16240 14 P g) :
    ruFix16240 t = fixCnt P := by
  rw [fixCnt_eq]
  unfold ruFix16240 CFSG.Certificates.Native.fixedList
  refine congrArg List.length (List.filter_congr fun i hi => ?_)
  have hi' : i < 16240 := List.mem_range.1 hi
  have e : t[i]! = pg 14 (mask 14) P i := by
    rw [ht.apply hi']
    exact (hP ⟨i, hi'⟩).symm
  rw [e, beq_eq_nat]

private theorem oneP_facts {R RI : ℕ → ℕ} {P0 : List ℤ} {X k x : ℕ}
    (h : oneP R RI P0 X k x = true) :
    pcomp 16240 14 (mask 14) (psq (psq X)) (psq (psq X)) = pidn 16240 14 ∧
      psq (psq X) ≠ pidn 16240 14 ∧ x < 16240 ∧
      pg 14 (mask 14) (psq (psq X)) x ≠ ptWord R RI P0 (ptWord R RI P0 x) ∧
      fixCnt (psq (psq X)) = k := by
  unfold oneP at h
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, PF.false_of_beq (eq_false_of_bIf h2), Nat.blt_eq.mp h3,
    PF.false_of_beq (eq_false_of_bIf h4), Nat.eq_of_beq_eq_true h5⟩

private theorem rep_arr {A : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin 16240)}
    (hAs : gc ≤ A.size) (hA : ∀ i < gc, CFSG.Monster.B.Co2.Rep 16240 A[i]! (gs i))
    (w : List (Fin gc × Bool)) :
    CFSG.Monster.B.Co2.Rep 16240 (wordArr 16240 A (zword w)) (wordIn gc gs (zword w)) :=
  CFSG.Monster.B.Co2.rep_wordA (S := A) (Sinv := A.map (invCand 16240)) hA (fun i hi => by
    rw [CFSG.Sporadic.Schreier.Tits.getElem!_map_of_lt (by omega)]
    exact rep_invCand (hA i hi)) _ (lettersOK_zword w)

private noncomputable def oneA (A : Array (Array ℕ)) (Z w : List (Fin gc × Bool)) (n : ℕ) :
    Bool :=
  CFSG.Monster.B.Co2.Native.lettersOK gc (zword (wordPow 8 w)) &&
    CFSG.Monster.B.Co2.Native.lettersOK gc (zword (wordPow 4 w)) &&
    eqA 16240 (wordArr 16240 A (zword (wordPow 8 w))) (idA 16240) &&
    !eqA 16240 (wordArr 16240 A (zword (wordPow 4 w))) (idA 16240) &&
    !eqA 16240 (wordArr 16240 A (zword (wordPow 4 w))) (wordArr 16240 A (zword Z)) &&
    (ruFix16240 (wordArr 16240 A (zword (wordPow 4 w))) == n)

private noncomputable def checkA (A : Array (Array ℕ)) (Z : List (Fin gc × Bool)) : Bool :=
  CFSG.Monster.B.Co2.Native.lettersOK gc (zword Z) &&
    !eqA 16240 (wordArr 16240 A (zword Z)) (idA 16240) &&
    oneA A Z ruFourthW1 320 && oneA A Z ruFourthW2 48

private theorem one_ok {R RI : ℕ → ℕ} {P0 : List ℤ} {A : Array (Array ℕ)}
    {gs : ℕ → Equiv.Perm (Fin 16240)} {τ σ : Equiv.Perm (Fin 16240)}
    {Z W : List (Fin gc × Bool)} {X n x : ℕ} (hAs : gc ≤ A.size)
    (hA : ∀ i < gc, CFSG.Monster.B.Co2.Rep 16240 A[i]! (gs i))
    (hτ : Orb.PRep 16240 14 (wordFrom R RI P0 idP) τ) (hZ : wordIn gc gs (zword Z) = τ * τ)
    (hX : Orb.PRep 16240 14 X σ) (hσ : wordIn gc gs (zword W) = σ)
    (h : oneP R RI P0 X n x = true) : oneA A Z W n = true := by
  obtain ⟨e8, n4, hx, hxz, hfix⟩ := oneP_facts h
  have hX2 : Orb.PRep 16240 14 (psq X) (σ * σ) := Orb.prep_pcomp (by norm_num) hX hX
  have hX4 : Orb.PRep 16240 14 (psq (psq X)) (σ * σ * (σ * σ)) :=
    Orb.prep_pcomp (by norm_num) hX2 hX2
  have hX8 : Orb.PRep 16240 14 (pcomp 16240 14 (mask 14) (psq (psq X)) (psq (psq X)))
      (σ * σ * (σ * σ) * (σ * σ * (σ * σ))) := Orb.prep_pcomp (by norm_num) hX4 hX4
  have p4 : wordIn gc gs (zword (wordPow 4 W)) = σ * σ * (σ * σ) := by
    rw [wordIn_wordPow, hσ]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have p8 : wordIn gc gs (zword (wordPow 8 W)) = σ * σ * (σ * σ) * (σ * σ * (σ * σ)) := by
    rw [wordIn_wordPow, hσ]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h8 : σ * σ * (σ * σ) * (σ * σ * (σ * σ)) = 1 := by
    refine Equiv.ext fun y => Fin.ext ?_
    rw [← hX8 y, e8, PF.pg_pidn (n := 16240) (w := 14) (by norm_num) (by norm_num) y.2]
    rfl
  have h4 : σ * σ * (σ * σ) ≠ 1 :=
    ne_one_of_ne hX4 (PF.pcomp_shr (n := 16240) (w := 14) (psq X) (psq X) (by norm_num)
      (by norm_num)) n4
  have h4z : σ * σ * (σ * σ) ≠ τ * τ := by
    intro e
    apply hxz
    rw [ptWord2 hτ hx, ← e]
    exact hX4 ⟨x, hx⟩
  have r8 := rep_arr hAs hA (wordPow 8 W)
  have r4 := rep_arr hAs hA (wordPow 4 W)
  have rZ := rep_arr hAs hA Z
  rw [p8] at r8
  rw [p4] at r4
  rw [hZ] at rZ
  unfold oneA
  refine and_true_of (and_true_of (and_true_of (and_true_of (and_true_of (lettersOK_zword _)
    (lettersOK_zword _)) ?_) ?_) ?_) ?_
  · exact (CFSG.Monster.B.Co2.eqA_iff r8 CFSG.Monster.B.Co2.rep_idA).2 h8
  · exact not_true_of fun e => h4 ((CFSG.Monster.B.Co2.eqA_iff r4 CFSG.Monster.B.Co2.rep_idA).1 e)
  · exact not_true_of fun e => h4z ((CFSG.Monster.B.Co2.eqA_iff r4 rZ).1 e)
  · rw [beq_iff_eq]
    exact (fix_count r4 hX4).trans hfix

private theorem fourth_core {R RI : ℕ → ℕ} {P0 S0 : List ℤ} {y x₁ x₂ : ℕ}
    {A : Array (Array ℕ)} (hAs : A.size = 3) (hA : ∀ k < 3, A[k]! = unpack 16240 14 (R k))
    (hS0 : S0 = P0) (hp : ∀ l < 3, permOK 16240 14 16383 (16240 * 14) (R l) (RI l) = true)
    (h3 : letters3 P0 = true) (hz : zOK R RI P0 y = true)
    (h1 : oneP R RI P0 (wordFrom R RI [-3, 2] idP) 320 x₁ = true)
    (h2 : oneP R RI P0 (wordFrom R RI [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3] idP)
      48 x₂ = true) :
    checkA A (toLetters gc S0 ++ toLetters gc S0) = true := by
  rw [hS0]
  have hp' : ∀ l < 3, permOK 16240 14 (mask 14) (16240 * 14) (R l) (RI l) = true := hp
  obtain ⟨gs, hgs⟩ : ∃ gs : ℕ → Equiv.Perm (Fin 16240), ∀ l < 3,
      CFSG.Monster.B.Co2.Rep 16240 (unpack 16240 14 (R l)) (gs l) ∧
        CFSG.Monster.B.Co2.Rep 16240 (unpack 16240 14 (RI l)) (gs l)⁻¹ :=
    ⟨fun l => CFSG.Monster.B.Co2.permOfArr 16240 (unpack 16240 14 (R l)), fun l hl =>
      CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack (hp' l hl))⟩
  have hS : ∀ h < gc, Orb.PRep 16240 14 (R h) (gs h) := fun h hh =>
    Orb.prep_of_rep (hgs h (lt_of_lt_of_eq hh gc_eq)).1
  have hSI : ∀ h < gc, Orb.PRep 16240 14 (RI h) (gs h)⁻¹ := fun h hh =>
    Orb.prep_of_rep (hgs h (lt_of_lt_of_eq hh gc_eq)).2
  have hA' : ∀ i < gc, CFSG.Monster.B.Co2.Rep 16240 A[i]! (gs i) := fun i hi => by
    rw [hA i (lt_of_lt_of_eq hi gc_eq)]
    exact (hgs i (lt_of_lt_of_eq hi gc_eq)).1
  have hAs' : gc ≤ A.size := le_of_eq (gc_eq.trans hAs.symm)
  have hlP : lettersK gc P0 = true := lettersK_of_letters3 gc_eq.ge P0 h3
  have hτ : Orb.PRep 16240 14 (wordFrom R RI P0 idP) (wordIn gc gs P0) := prep_word hS hSI hlP
  have hlP' : CFSG.Monster.B.Co2.Native.lettersOK gc P0 = true :=
    (Orb.prep_wordK (n := 16240) (w := 14) (by norm_num) (by norm_num) hS hSI P0 hlP).2
  have hZP : zword (toLetters gc P0) = P0 := zword_toLetters P0 fun z hz => by
    have := List.all_eq_true.1 hlP' z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    exact this
  have hZ : wordIn gc gs (zword (toLetters gc P0 ++ toLetters gc P0)) =
      wordIn gc gs P0 * wordIn gc gs P0 := by
    rw [zword_append, hZP, CFSG.Sporadic.Schreier.Tits.wordIn_append]
  have hz' : y < 16240 ∧ ptWord R RI P0 (ptWord R RI P0 y) ≠ y := by
    unfold zOK at hz
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at hz
    exact ⟨Nat.blt_eq.mp hz.1, PF.false_of_beq (eq_false_of_bIf hz.2)⟩
  have hτ2 : wordIn gc gs P0 * wordIn gc gs P0 ≠ 1 := by
    intro e
    apply hz'.2
    rw [ptWord2 hτ hz'.1, e]
    rfl
  have rZ := rep_arr hAs' hA' (toLetters gc P0 ++ toLetters gc P0)
  rw [hZ] at rZ
  have hW1 : zword ruFourthW1 = [-3, 2] := by decide
  have hW2 : zword ruFourthW2 = [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3] := by
    decide
  have hX1 := prep_word hS hSI (wd := [-3, 2]) (lettersK_of_letters3 gc_eq.ge _ rfl)
  have hX2 := prep_word hS hSI (wd := [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3])
    (lettersK_of_letters3 gc_eq.ge _ rfl)
  unfold checkA
  refine and_true_of (and_true_of (and_true_of (lettersOK_zword _) ?_)
    (one_ok hAs' hA' hτ hZ hX1 (congrArg (wordIn gc gs) hW1) h1))
    (one_ok hAs' hA' hτ hZ hX2 (congrArg (wordIn gc gs) hW2) h2)
  exact not_true_of fun e => hτ2 ((CFSG.Monster.B.Co2.eqA_iff rZ CFSG.Monster.B.Co2.rep_idA).1 e)

private theorem arr3_get {α : Type} [Inhabited α] {a b c : α} {F : ℕ → α} (h0 : a = F 0)
    (h1 : b = F 1) (h2 : c = F 2) : ∀ k < 3, #[a, b, c][k]! = F k := by
  intro k hk
  interval_cases k
  · exact h0
  · exact h1
  · exact h2

theorem fourthK_sound_gen (rho surj img : String) : FourthGen rho surj img := by
  intro R RI P0 y x₁ x₂ hR hP0 hp h3 hz h1 h2
  exact fourth_core (A := #[CFSG.Monster.B.Co2.Native.hexTable 4 16240 0 rho,
    CFSG.Monster.B.Co2.Native.hexTable 4 16240 16240 rho,
    CFSG.Monster.B.Co2.Native.hexTable 4 16240 32480 rho]) rfl
    (arr3_get (F := fun k => unpack 16240 14 (R k)) (hR 0 (by norm_num)) (hR 1 (by norm_num))
      (hR 2 (by norm_num))) hP0 hp h3 hz h1 h2

end CFSG.KC.Misc.RuFourth

end
