module

public import CFSG.Certificates.Kernel.Misc.RuInvCov
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH

public section

namespace CFSG.KC.Misc.RuInv.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.RuStd
open CFSG.EvenSporadicStandard.TwoRu.HypOne CFSG.EvenSporadicStandard.HypOne

@[expose] def cG (a0 a1 : Array ℕ) : Array Table :=
  #[tblOfArr (slotRunA 4060 ruCProg a0 a1).1, tblOfArr (slotRunA 4060 ruCProg a0 a1).2.1]

@[expose] def cGI (a0 a1 : Array ℕ) : Array Table :=
  #[tblOfArr (ruInv (slotRunA 4060 ruCProg a0 a1).1), tblOfArr (ruInv (slotRunA 4060 ruCProg a0 a1).2.1)]

@[expose] def rep0 (a0 a1 : Array ℕ) : Table := tblOfArr (powA 4060 (slotRunA 4060 ruCProg a0 a1).1 10)

@[expose] def repW (a0 a1 : Array ℕ) (w : List ℤ) : Table :=
  wordT 4060 (letterTab (cG a0 a1) (cGI a0 a1)) w

@[expose] def clW (a0 a1 : Array ℕ) (r : Table) : Array Table × Array ℕ × Array ℕ :=
  conjClosureH 4060 (cG a0 a1) (cGI a0 a1) r 700

@[expose] def allW (a0 a1 : Array ℕ) : Array Table :=
  (clW a0 a1 (rep0 a0 a1)).1 ++ (clW a0 a1 (repW a0 a1 ruInvWord1)).1 ++
    (clW a0 a1 (repW a0 a1 ruInvWord2)).1 ++ (clW a0 a1 (repW a0 a1 ruInvWord3)).1 ++
      (clW a0 a1 (repW a0 a1 ruInvWord4)).1

@[expose] def coverW (a0 a1 : Array ℕ) (t : Array ℕ) : Bool :=
  !(ruIsInvolA t && ruFixCount t == 92) ||
    memTH 4060 (allW a0 a1) (hashIndex 4060 (allW a0 a1)) (tblOfArr t)

@[expose] def checkW (a0 a1 : Array ℕ) (S : Array (Array ℕ)) (base : Array ℕ) : Bool :=
  classCheckOf 4060 (cG a0 a1) (cGI a0 a1) (rep0 a0 a1) (clW a0 a1 (rep0 a0 a1)) 1 &&
    classCheckOf 4060 (cG a0 a1) (cGI a0 a1) (repW a0 a1 ruInvWord1)
      (clW a0 a1 (repW a0 a1 ruInvWord1)) 30 &&
    classCheckOf 4060 (cG a0 a1) (cGI a0 a1) (repW a0 a1 ruInvWord2)
      (clW a0 a1 (repW a0 a1 ruInvWord2)) 240 &&
    classCheckOf 4060 (cG a0 a1) (cGI a0 a1) (repW a0 a1 ruInvWord3)
      (clW a0 a1 (repW a0 a1 ruInvWord3)) 480 &&
    classCheckOf 4060 (cG a0 a1) (cGI a0 a1) (repW a0 a1 ruInvWord4)
      (clW a0 a1 (repW a0 a1 ruInvWord4)) 640 &&
    all2 4060 (rawLevels 4060 S base) (coverW a0 a1)

structure Enum (L : Array Table) (X : Set G) : Prop where
  mem : ∀ i < L.size, ∃ g ∈ X, CFSG.Sporadic.Th.Rep 4060 L[i]! g
  surj : ∀ g ∈ X, ∃ i < L.size, CFSG.Sporadic.Th.Rep 4060 L[i]! g
  inj : ∀ a < L.size, ∀ b < L.size, ∀ g : G, CFSG.Sporadic.Th.Rep 4060 L[a]! g →
    CFSG.Sporadic.Th.Rep 4060 L[b]! g → a = b

theorem append_get_left {A B : Array Table} {i : Nat} (h : i < A.size) : (A ++ B)[i]! = A[i]! := by
  rw [getElem!_pos (A ++ B) i (by simp; omega), Array.getElem_append_left h, getElem!_pos A i h]

theorem append_get_right {A B : Array Table} {i : Nat} (h1 : A.size ≤ i) (h2 : i < A.size + B.size) :
    (A ++ B)[i]! = B[i - A.size]! := by
  rw [getElem!_pos (A ++ B) i (by simpa using h2), Array.getElem_append_right h1,
    getElem!_pos B (i - A.size) (by omega)]

theorem Enum.append {A B : Array Table} {X Y : Set G} (hA : Enum A X) (hB : Enum B Y)
    (hXY : Disjoint X Y) : Enum (A ++ B) (X ∪ Y) := by
  refine ⟨fun i hi => ?_, fun g hg => ?_, fun a ha b hb g h1 h2 => ?_⟩
  · rw [Array.size_append] at hi
    by_cases h : i < A.size
    · obtain ⟨g, hg, hr⟩ := hA.mem i h
      exact ⟨g, Or.inl hg, by rw [append_get_left h]; exact hr⟩
    · obtain ⟨g, hg, hr⟩ := hB.mem (i - A.size) (by omega)
      exact ⟨g, Or.inr hg, by rw [append_get_right (by omega) hi]; exact hr⟩
  · rcases hg with hg | hg
    · obtain ⟨i, hi, hr⟩ := hA.surj g hg
      exact ⟨i, by simp; omega, by rw [append_get_left hi]; exact hr⟩
    · obtain ⟨i, hi, hr⟩ := hB.surj g hg
      refine ⟨A.size + i, by simp; omega, ?_⟩
      rw [append_get_right (by omega) (by omega), Nat.add_sub_cancel_left]
      exact hr
  · rw [Array.size_append] at ha hb
    by_cases ha' : a < A.size <;> by_cases hb' : b < A.size
    · rw [append_get_left ha'] at h1
      rw [append_get_left hb'] at h2
      exact hA.inj a ha' b hb' g h1 h2
    · rw [append_get_left ha'] at h1
      rw [append_get_right (by omega) hb] at h2
      obtain ⟨g1, hg1, r1⟩ := hA.mem a ha'
      obtain ⟨g2, hg2, r2⟩ := hB.mem (b - A.size) (by omega)
      have e1 := CFSG.KS.ClassOne.rep_unique h1 r1
      have e2 := CFSG.KS.ClassOne.rep_unique h2 r2
      subst e1
      subst e2
      exact (Set.disjoint_left.1 hXY hg1 hg2).elim
    · rw [append_get_right (by omega) ha] at h1
      rw [append_get_left hb'] at h2
      obtain ⟨g1, hg1, r1⟩ := hB.mem (a - A.size) (by omega)
      obtain ⟨g2, hg2, r2⟩ := hA.mem b hb'
      have e1 := CFSG.KS.ClassOne.rep_unique h1 r1
      have e2 := CFSG.KS.ClassOne.rep_unique h2 r2
      subst e1
      subst e2
      exact (Set.disjoint_left.1 hXY hg2 hg1).elim
    · rw [append_get_right (by omega) ha] at h1
      rw [append_get_right (by omega) hb] at h2
      have := hB.inj (a - A.size) (by omega) (b - A.size) (by omega) g h1 h2
      omega

@[expose] def Xr (E : Nat → Nat) (lo hi : Nat) : Set G := {z | ∃ j, lo ≤ j ∧ j < hi ∧ PRep 4060 12 (E j) z}

section Entries

variable {E Hs : Nat → Nat} {P : Nat}
  (hhash : ∀ j < 1391, hashE E Hs j = true) (hkeys : keysK Hs P 1391 = true)
include hhash hkeys

theorem rec_unique {j j' : Nat} (hj : j < 1391) (hj' : j' < 1391) {z : G}
    (h : PRep 4060 12 (E j) z) (h' : PRep 4060 12 (E j') z) : j = j' := by
  have a := hhash j hj
  have b := hhash j' hj'
  unfold hashE at a b
  rw [Nat.blt_eq.mpr hj] at a
  rw [Nat.blt_eq.mpr hj'] at b
  have ea := Nat.eq_of_beq_eq_true a
  have eb := Nat.eq_of_beq_eq_true b
  rw [hkeyP_eq h] at ea
  rw [hkeyP_eq h'] at eb
  exact keysK_inj hkeys j hj j' hj' (ea.symm.trans eb)

theorem hkeyOf_inj {hi : Nat} (hhi : hi ≤ 1391) : Set.InjOn (CFSG.Sporadic.SmallOddCore.hkeyOf 4060) (Xr E 0 hi) := by
  rintro z ⟨j, -, hj, hz⟩ z' ⟨j', -, hj', hz'⟩ e
  have a := hhash j (by omega)
  have b := hhash j' (by omega)
  unfold hashE at a b
  rw [Nat.blt_eq.mpr (by omega : j < 1391)] at a
  rw [Nat.blt_eq.mpr (by omega : j' < 1391)] at b
  have ea := Nat.eq_of_beq_eq_true a
  have eb := Nat.eq_of_beq_eq_true b
  rw [hkeyP_eq hz] at ea
  rw [hkeyP_eq hz'] at eb
  have hjj := keysK_inj hkeys j (by omega) j' (by omega) (ea.symm.trans (by rw [e]; exact eb))
  subst hjj
  exact prep_unique hz hz'

theorem xr_disjoint {a b c : Nat} (hc : c ≤ 1391) : Disjoint (Xr E a b) (Xr E b c) := by
  rw [Set.disjoint_left]
  rintro z ⟨j, -, hj, hz⟩ ⟨j', hj', hj'c, hz'⟩
  have := rec_unique hhash hkeys (by omega) (by omega) hz hz'
  omega

end Entries

theorem xr_union (E : Nat → Nat) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    Xr E a b ∪ Xr E b c = Xr E a c := by
  ext z
  constructor
  · rintro (⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩)
    · exact ⟨j, h1, by omega, h3⟩
    · exact ⟨j, by omega, h2, h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    by_cases h : j < b
    · exact Or.inl ⟨j, h1, h, h3⟩
    · exact Or.inr ⟨j, by omega, h2, h3⟩

theorem cG_size (a0 a1 : Array ℕ) : (cG a0 a1).size = 2 := rfl

section OneClass

variable {E Hs : Nat → Nat} {P C0 C1 CI0 CI1 nx : Nat} {x0 x1 : G} {a0 a1 : Array ℕ}
  (h0 : PRep 4060 12 C0 x0) (h1 : PRep 4060 12 C1 x1) (hi0 : PRep 4060 12 CI0 x0⁻¹)
  (hi1 : PRep 4060 12 CI1 x1⁻¹)
  (hg : ∀ l < (cG a0 a1).size, CFSG.Sporadic.Th.Rep 4060 (cG a0 a1)[l]! (gam x0 x1 l) ∧
    CFSG.Sporadic.Th.Rep 4060 (cGI a0 a1)[l]! (gam x0 x1 l)⁻¹)
  (hconj : ∀ j < 1391, conjE E (gen2 C0 C1) (gen2 CI0 CI1) nx j = true)
  (hhash : ∀ j < 1391, hashE E Hs j = true) (hkeys : keysK Hs P 1391 = true)
  {lo N : Nat} (hcls : ∀ j, lo ≤ j → j < lo + N → clsLo j = lo ∧ clsHi j = lo + N)
  (hloN : lo + N ≤ 1391) (hN0 : 0 < N) (hreach : reachK nx lo N = true)
include h0 h1 hi0 hi1 hg hconj hhash hkeys hcls hloN hN0 hreach

theorem class_ok {y : G} (hy : PRep 4060 12 (E lo) y) {r : Table}
    (hr : CFSG.Sporadic.Th.Rep 4060 r y) (hN : N ≤ 700) :
    classCheckOf 4060 (cG a0 a1) (cGI a0 a1) r (clW a0 a1 r) N = true ∧
      Enum (clW a0 a1 r).1 (Xr E lo (lo + N)) := by
  classical
  have hreach' := class_reach h0 h1 hi0 hi1 hconj hcls hloN hreach hy
  choose! σ hσc hσ using hreach'
  have hX : ∀ z, z ∈ Xr E lo (lo + N) ↔ ∃ b < N, PRep 4060 12 (E (lo + b)) z := by
    intro z
    constructor
    · rintro ⟨j, h1', h2', h3'⟩
      exact ⟨j - lo, by omega, by rw [show lo + (j - lo) = j by omega]; exact h3'⟩
    · rintro ⟨b, hb, hz⟩
      exact ⟨lo + b, by omega, by omega, hz⟩
  have hXs : Xr E lo (lo + N) = σ '' {b | b < N} := by
    ext z
    rw [hX]
    constructor
    · rintro ⟨b, hb, hz⟩
      exact ⟨b, hb, prep_unique (hσ b hb) hz⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, hσ b hb⟩
  have hσinj : Set.InjOn σ {b | b < N} := by
    intro b hb b' hb' e
    have := rec_unique hhash hkeys (j := lo + b) (j' := lo + b') (by simp at hb; omega)
      (by simp at hb'; omega) (hσ b hb)
      (by rw [e]; exact hσ b' hb')
    omega
  have hcard : (Xr E lo (lo + N)).ncard = N := by
    rw [hXs, hσinj.ncard_image,
      show {b | b < N} = ((Finset.range N : Finset Nat) : Set Nat) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  have hfin : (Xr E lo (lo + N)).Finite := by
    rw [hXs]
    exact (Set.finite_lt_nat N).image σ
  have hcl : ∀ l < (cG a0 a1).size, ∀ z ∈ Xr E lo (lo + N),
      gam x0 x1 l * z * (gam x0 x1 l)⁻¹ ∈ Xr E lo (lo + N) := by
    intro l hl z hz
    rw [cG_size] at hl
    rw [hX] at hz ⊢
    obtain ⟨b, hb, hz⟩ := hz
    obtain ⟨a1', a2'⟩ := class_step h0 h1 hi0 hi1 hconj hcls hloN hb hz l hl
    exact ⟨_, a1', a2'⟩
  have hsub : Xr E lo (lo + N) ⊆ cl x0 x1 y := by
    intro z hz
    rw [hX] at hz
    obtain ⟨b, hb, hz⟩ := hz
    rw [prep_unique hz (hσ b hb)]
    exact hσc b hb
  have hmin : ∀ g ∈ Xr E lo (lo + N), ∀ D : Set G, D.Finite → g ∈ D →
      (∀ l < (cG a0 a1).size, ∀ z ∈ D, gam x0 x1 l * z * (gam x0 x1 l)⁻¹ ∈ D) →
      Xr E lo (lo + N) ⊆ D := by
    intro g hgX D _ hgD hD
    rw [cG_size] at hD
    exact hsub.trans (cl_sub (hsub hgX) hgD hD)
  have hy0 : y ∈ Xr E lo (lo + N) := ⟨lo, le_refl _, by omega, hy⟩
  have hinj : Set.InjOn (CFSG.Sporadic.SmallOddCore.hkeyOf 4060) (Xr E lo (lo + N)) :=
    (hkeyOf_inj hhash hkeys (hi := lo + N) hloN).mono fun z (hz : z ∈ Xr E lo (lo + N)) => by
      obtain ⟨j, -, b, c⟩ := hz
      exact ⟨j, Nat.zero_le _, b, c⟩
  obtain ⟨htree, hd, hsize, hin, hall⟩ := CFSG.KS.ClassOneH.conjClosureH_one (by norm_num) hg hfin
    hcl hmin hinj hr hy0 (cap := 700) (by rw [hcard]; exact hN)
  refine ⟨CFSG.KS.ClassOneH.classCheckOf_one (by norm_num) hg hfin hcl hmin hinj hr hy0
    (by rw [hcard]; exact hN) hcard, hin, hall, fun a ha b hb g ra rb => ?_⟩
  have ra' : CFSG.Sporadic.Th.Rep 4060 (conjClosureH 4060 (cG a0 a1) (cGI a0 a1) r 700).1[a]! g := ra
  have rb' : CFSG.Sporadic.Th.Rep 4060 (conjClosureH 4060 (cG a0 a1) (cGI a0 a1) r 700).1[b]! g := rb
  apply hd a ha b hb
  rw [CFSG.Sporadic.SmallOddCore.hkey_eq_hkeyOf ra', CFSG.Sporadic.SmallOddCore.hkey_eq_hkeyOf rb']

end OneClass

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b :=
  Bool.eq_iff_iff.2 ⟨fun h => Nat.beq_eq.mpr (beq_iff_eq.1 h), fun h => beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)⟩

section Cover

variable {E V : Nat → Nat} {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array ℕ)}
  {base : Array ℕ} {L : Array Table}
  (hb : Binds 4060 12 PS kS 2 BP S base)
  (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
  (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP) (hc : rcnt (LR 0) = 2048 ∧ rcnt (LR 1) = 8)
  (hcov : ∀ a < 2048, covA LR TR E V a = true)
  (hmem : ∀ j < 1391, ∀ y : G, PRep 4060 12 (E j) y → ∀ T : Table,
    CFSG.Sporadic.Th.Rep 4060 T y → memTH 4060 L (hashIndex 4060 L) T = true)
include hb hp hl hc hcov hmem

theorem cover_ok : all2 4060 (rawLevels 4060 S base) (fun t => !(ruIsInvolA t && ruFixCount t == 92) ||
    memTH 4060 L (hashIndex 4060 L) (tblOfArr t)) = true := by
  unfold all2
  rw [allLt_iff]
  intro a ha
  rw [allLt_iff]
  intro b hb'
  beta_reduce
  obtain ⟨s0, lev0⟩ := lev2 hb hp hl (i := 0) (by norm_num)
  obtain ⟨s1, lev1⟩ := lev2 hb hp hl (i := 1) (by norm_num)
  rw [s0, hc.1] at ha
  rw [s1, hc.2] at hb'
  obtain ⟨g0, r0, p0⟩ := lev0 a (by rw [hc.1]; exact ha)
  obtain ⟨g1, r1, p1⟩ := lev1 b (by rw [hc.2]; exact hb')
  have ht : Rep 4060 (prod2A 4060 (rawLevels 4060 S base) a b) (g0 * g1) := rep_compA r0 r1
  generalize prod2A 4060 (rawLevels 4060 S base) a b = t at ht
  have hca : covK LR TR E (V (Nat.shiftRight a 5)) (Nat.mul 32 (Nat.shiftRight a 5)) a 1 = true := by
    have := hcov a ha
    unfold covA at this
    rw [Nat.blt_eq.mpr ha] at this
    exact this
  unfold covK at hca
  simp only [strictB_eq'] at hca
  rw [allN_iff] at hca
  have hca0 := hca 0 (by norm_num)
  rw [allN_iff] at hca0
  have hcb := hca0 b hb'
  have p0' : PRep 4060 12 (TR (Nat.add (roff 4060 48720 (LR 0)) (Nat.add a 0))) g0 := p0
  have p1' : PRep 4060 12 (TR (Nat.add (roff 4060 48720 (LR 1)) b)) g1 := p1
  generalize TR (Nat.add (roff 4060 48720 (LR 0)) (Nat.add a 0)) = T0 at hcb p0'
  generalize TR (Nat.add (roff 4060 48720 (LR 1)) b) = T1 at hcb p1'
  have hget : ∀ y < 4060, t[y]! = apP T0 (apP T1 y) := by
    intro y hy
    rw [ht.apply hy]
    change ((g0 * g1) ⟨y, hy⟩ : Nat) = pg 12 (mask 12) T0 (pg 12 (mask 12) T1 y)
    rw [p1' ⟨y, hy⟩, p0' (g1 ⟨y, hy⟩)]
    rfl
  rcases covOne_cases hcb with ⟨hh, he⟩ | ⟨x, hx, hne⟩ | hcnt
  · have hy := he.symm ▸ (prep_mulP p0' p1')
    rw [hmem _ hh _ hy _ (rep_tblOfArr (by norm_num) ht), Bool.or_true]
  · have hinv : ruIsInvolA t = false := by
      unfold ruIsInvolA
      have : eqA 4060 (compA 4060 t t) (idA 4060) = false := by
        cases e : eqA 4060 (compA 4060 t t) (idA 4060)
        · rfl
        · rw [eqA, allLt_iff] at e
          have := e x hx
          rw [compA_get hx, idA_get hx, beq_iff_eq, hget x hx,
            hget _ (by rw [← hget x hx, ht.apply hx]; exact Fin.isLt _)] at this
          exact absurd this hne
      rw [this, Bool.false_and]
    rw [hinv, Bool.false_and, Bool.not_false, Bool.true_or]
  · have hcount : foldN 4060 (fun x c => nIf(Nat.beq (apP T0 (apP T1 x)) x, Nat.succ c, c)) 0 =
        ((List.range 4060).filter (fun x => Nat.beq (apP T0 (apP T1 x)) x)).length :=
      foldN_count _ _
    have hfix : ruFixCount t ≠ 92 := by
      unfold ruFixCount fixedList
      rw [List.filter_congr (q := fun x => Nat.beq (apP T0 (apP T1 x)) x) (fun x hx => by
        rw [List.mem_range] at hx
        rw [hget x hx, beq_nat]), ← hcount]
      exact hcnt
    have : (ruFixCount t == 92) = false := by
      rw [beq_nat]
      cases e : Nat.beq (ruFixCount t) 92
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hfix
    rw [this, Bool.and_false, Bool.not_false, Bool.true_or]

end Cover

theorem cG_get0 (a0 a1 : Array ℕ) : (cG a0 a1)[0]! = tblOfArr (slotRunA 4060 ruCProg a0 a1).1 := by
  simp [cG]

theorem cG_get1 (a0 a1 : Array ℕ) : (cG a0 a1)[1]! = tblOfArr (slotRunA 4060 ruCProg a0 a1).2.1 := by
  simp [cG]

theorem cGI_get0 (a0 a1 : Array ℕ) :
    (cGI a0 a1)[0]! = tblOfArr (invCand 4060 (slotRunA 4060 ruCProg a0 a1).1) := by
  simp [cGI, ruInv]

theorem cGI_get1 (a0 a1 : Array ℕ) :
    (cGI a0 a1)[1]! = tblOfArr (invCand 4060 (slotRunA 4060 ruCProg a0 a1).2.1) := by
  simp [cGI, ruInv]

theorem rep_letter {a0 a1 : Array ℕ} {x0 x1 : G}
    (hg : ∀ l < (cG a0 a1).size, CFSG.Sporadic.Th.Rep 4060 (cG a0 a1)[l]! (gam x0 x1 l) ∧
      CFSG.Sporadic.Th.Rep 4060 (cGI a0 a1)[l]! (gam x0 x1 l)⁻¹) {w : List ℤ} (hw : Letters2 w) :
    ∀ z ∈ w, CFSG.Sporadic.Th.Rep 4060 (letterTab (cG a0 a1) (cGI a0 a1) z)
      (letG (fun l => if l = 0 then x0 else x1) z) := by
  intro z hz
  unfold letterTab letG
  rcases hw z hz with rfl | rfl | rfl | rfl
  · exact (hg 0 (by rw [cG_size]; norm_num)).1
  · exact (hg 0 (by rw [cG_size]; norm_num)).2
  · exact (hg 1 (by rw [cG_size]; norm_num)).1
  · exact (hg 1 (by rw [cG_size]; norm_num)).2

theorem cls_range {lo N : Nat}
    (h : (lo = 0 ∧ N = 1) ∨ (lo = 1 ∧ N = 30) ∨ (lo = 31 ∧ N = 240) ∨ (lo = 271 ∧ N = 480) ∨
      (lo = 751 ∧ N = 640)) :
    ∀ j, lo ≤ j → j < lo + N → clsLo j = lo ∧ clsHi j = lo + N := by
  intro j h1 h2
  rw [clsLo_eq, clsHi_eq]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    constructor <;> split_ifs <;> omega

theorem checkW_ok {a0 a1 : Array ℕ} {S : Array (Array ℕ)} {base : Array ℕ}
    {A0 A1 AI0 AI1 C0 C1 CI0 CI1 kS BP nx P : Nat} {E PS PSI LR TR TRI Hs V : Nat → Nat}
    (hA0 : a0 = unpack 4060 12 A0) (hA1 : a1 = unpack 4060 12 A1)
    (hpA0 : permOK 4060 12 (mask 12) (4060 * 12) A0 AI0 = true)
    (hpA1 : permOK 4060 12 (mask 12) (4060 * 12) A1 AI1 = true)
    (hslot : slotK cprogK A0 A1 = (C0, C1))
    (hi0 : permOK 4060 12 (mask 12) (4060 * 12) C0 CI0 = true)
    (hi1 : permOK 4060 12 (mask 12) (4060 * 12) C1 CI1 = true)
    (hz : Nat.beq (E 0) (powP C0 10) = true)
    (hw1 : Nat.beq (E 1) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord1) = true)
    (hw2 : Nat.beq (E 31) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord2) = true)
    (hw3 : Nat.beq (E 271) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord3) = true)
    (hw4 : Nat.beq (E 751) (wordP (gen2 C0 C1) (gen2 CI0 CI1) ruInvWord4) = true)
    (hconj : ∀ j < 1391, conjE E (gen2 C0 C1) (gen2 CI0 CI1) nx j = true)
    (hreach : reachK nx 0 1 = true ∧ reachK nx 1 30 = true ∧ reachK nx 31 240 = true ∧
      reachK nx 271 480 = true ∧ reachK nx 751 640 = true)
    (hhash : ∀ j < 1391, hashE E Hs j = true) (hkeys : keysK Hs P 1391 = true)
    (hb : Binds 4060 12 PS kS 2 BP S base)
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP)
    (hc : rcnt (LR 0) = 2048 ∧ rcnt (LR 1) = 8)
    (hcov : ∀ a < 2048, covA LR TR E V a = true) :
    checkW a0 a1 S base = true := by
  obtain ⟨g0, pg0, -⟩ := prep_of_permOK hpA0
  obtain ⟨g1, pg1, -⟩ := prep_of_permOK hpA1
  have ra0 : Rep 4060 a0 g0 := by rw [hA0]; exact rep_unpack pg0
  have ra1 : Rep 4060 a1 g1 := by rw [hA1]; exact rep_unpack pg1
  obtain ⟨-, rc0, rc1⟩ := slotRunA_rep ruCProg ra0 ra1
  obtain ⟨pc0, pc1⟩ := prep_slotK cprogK pg0 pg1
  rw [cprogK_rows, hslot] at pc0 pc1
  generalize (slotRun ruCProg g0 g1).1 = x0 at rc0 pc0
  generalize (slotRun ruCProg g0 g1).2 = x1 at rc1 pc1
  have pci0 : PRep 4060 12 CI0 x0⁻¹ := by
    obtain ⟨g, h1, h2⟩ := prep_of_permOK hi0
    rw [prep_unique pc0 h1]
    exact h2
  have pci1 : PRep 4060 12 CI1 x1⁻¹ := by
    obtain ⟨g, h1, h2⟩ := prep_of_permOK hi1
    rw [prep_unique pc1 h1]
    exact h2
  have hg : ∀ l < (cG a0 a1).size, CFSG.Sporadic.Th.Rep 4060 (cG a0 a1)[l]! (gam x0 x1 l) ∧
      CFSG.Sporadic.Th.Rep 4060 (cGI a0 a1)[l]! (gam x0 x1 l)⁻¹ := by
    intro l hl
    rw [cG_size] at hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [cG_get0, cGI_get0, show gam x0 x1 0 = x0 from if_pos rfl]
      exact ⟨rep_tblOfArr (by norm_num) rc0, rep_tblOfArr (by norm_num) (rep_invCand rc0)⟩
    · rw [cG_get1, cGI_get1, show gam x0 x1 1 = x1 from if_neg (by norm_num)]
      exact ⟨rep_tblOfArr (by norm_num) rc1, rep_tblOfArr (by norm_num) (rep_invCand rc1)⟩
  have hL : ∀ w : List ℤ, Letters2 w → CFSG.Sporadic.Th.Rep 4060 (repW a0 a1 w)
      (CFSG.Sporadic.Th.wordG (letG fun l => if l = 0 then x0 else x1) w) := fun w hw =>
    CFSG.Sporadic.Th.Rep.wordT (by norm_num) w (rep_letter hg hw)
  have hK : ∀ (j : Nat) (w : List ℤ), Letters2 w →
      Nat.beq (E j) (wordP (gen2 C0 C1) (gen2 CI0 CI1) w) = true →
      PRep 4060 12 (E j) (CFSG.Sporadic.Th.wordG (letG fun l => if l = 0 then x0 else x1) w) :=
    fun j w hw h => by
      rw [Nat.eq_of_beq_eq_true h]
      exact prep_wordP pc0 pc1 pci0 pci1 w hw
  have l1 : Letters2 ruInvWord1 := by unfold Letters2 ruInvWord1; decide
  have l2 : Letters2 ruInvWord2 := by unfold Letters2 ruInvWord2; decide
  have l3 : Letters2 ruInvWord3 := by unfold Letters2 ruInvWord3; decide
  have l4 : Letters2 ruInvWord4 := by unfold Letters2 ruInvWord4; decide
  have py0 : PRep 4060 12 (E 0) (x0 ^ 10) := by
    rw [Nat.eq_of_beq_eq_true hz]
    exact prep_powP pc0 10
  have ry0 : CFSG.Sporadic.Th.Rep 4060 (rep0 a0 a1) (x0 ^ 10) :=
    rep_tblOfArr (by norm_num) (rep_powA rc0 10)
  obtain ⟨r0, r1, r2, r3, r4⟩ := hreach
  have c0 := class_ok (lo := 0) (N := 1) pc0 pc1 pci0 pci1 hg hconj hhash hkeys
    (cls_range (by norm_num)) (by norm_num) (by norm_num) r0 py0 ry0 (by norm_num)
  have c1 := class_ok (lo := 1) (N := 30) pc0 pc1 pci0 pci1 hg hconj hhash hkeys
    (cls_range (by norm_num)) (by norm_num) (by norm_num) r1 (hK 1 _ l1 hw1) (hL _ l1) (by norm_num)
  have c2 := class_ok (lo := 31) (N := 240) pc0 pc1 pci0 pci1 hg hconj hhash hkeys
    (cls_range (by norm_num)) (by norm_num) (by norm_num) r2 (hK 31 _ l2 hw2) (hL _ l2) (by norm_num)
  have c3 := class_ok (lo := 271) (N := 480) pc0 pc1 pci0 pci1 hg hconj hhash hkeys
    (cls_range (by norm_num)) (by norm_num) (by norm_num) r3 (hK 271 _ l3 hw3) (hL _ l3) (by norm_num)
  have c4 := class_ok (lo := 751) (N := 640) pc0 pc1 pci0 pci1 hg hconj hhash hkeys
    (cls_range (by norm_num)) (by norm_num) (by norm_num) r4 (hK 751 _ l4 hw4) (hL _ l4) (by norm_num)
  have hall : Enum (allW a0 a1) (Xr E 0 1391) := by
    have e01 := c0.2.append c1.2 (xr_disjoint hhash hkeys (by norm_num))
    rw [xr_union E (by norm_num) (by norm_num)] at e01
    have e02 := e01.append c2.2 (xr_disjoint hhash hkeys (by norm_num))
    rw [xr_union E (by norm_num) (by norm_num)] at e02
    have e03 := e02.append c3.2 (xr_disjoint hhash hkeys (by norm_num))
    rw [xr_union E (by norm_num) (by norm_num)] at e03
    have e04 := e03.append c4.2 (xr_disjoint hhash hkeys (by norm_num))
    rw [xr_union E (by norm_num) (by norm_num)] at e04
    exact e04
  have hd : ∀ a < (allW a0 a1).size, ∀ b < (allW a0 a1).size,
      hkey 4060 (allW a0 a1)[a]! = hkey 4060 (allW a0 a1)[b]! → a = b := by
    intro a ha b hb e
    obtain ⟨ga, hga, ra⟩ := hall.mem a ha
    obtain ⟨gb, hgb, rb⟩ := hall.mem b hb
    rw [CFSG.Sporadic.SmallOddCore.hkey_eq_hkeyOf ra, CFSG.Sporadic.SmallOddCore.hkey_eq_hkeyOf rb] at e
    have := hkeyOf_inj hhash hkeys (le_refl _) hga hgb e
    subst this
    exact hall.inj a ha b hb ga ra rb
  have hmem : ∀ j < 1391, ∀ y : G, PRep 4060 12 (E j) y → ∀ T : Table,
      CFSG.Sporadic.Th.Rep 4060 T y →
        memTH 4060 (allW a0 a1) (hashIndex 4060 (allW a0 a1)) T = true := by
    intro j hj y hy T hT
    obtain ⟨i, hi, ri⟩ := hall.surj y ⟨j, Nat.zero_le _, hj, hy⟩
    exact CFSG.KS.ClassOneH.memTH_of_rep hd hi ri hT
  have hcv := cover_ok hb hp hl hc hcov hmem
  unfold checkW
  rw [c0.1, c1.1, c2.1, c3.1, c4.1]
  exact hcv

end CFSG.KC.Misc.RuInv.P

end
