module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.Certificates.Kernel.LocalQTBaseWProved
public import CFSG.Certificates.Kernel.LocalQTPipeBasic

public section

namespace CFSG.KC.LQT.PPC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem allR_spec' {lo len : Nat} {f : Nat → Bool} (h : allR lo len f = true) :
    ∀ j < len, f (lo + j) = true := by
  induction len with
  | zero => intro j hj; omega
  | succ m ih =>
    have e : allR lo (m + 1) f = andB (f (Nat.add lo m)) (allR lo m f) := rfl
    rw [e, andB_iff] at h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h.2 j hj
    · exact h.1

theorem nthP_eq (l : List (Nat × Nat)) (i : Nat) : nthP l i = l.getD i (0, 0) := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    have e : nthP (x :: t) i = Bool.rec (motive := fun _ => Nat × Nat) (nthP t (Nat.sub i 1)) x
        (Nat.beq i 0) := rfl
    rw [e]
    cases i with
    | zero => rfl
    | succ i =>
      have e1 : Nat.beq (i + 1) 0 = false := rfl
      rw [e1]
      dsimp only
      rw [ih, List.getD_cons_succ]
      rfl

@[expose] def Inj (N : Nat) (t : Array Nat) : Prop := ∀ i < N, ∀ j < N, img t i = img t j → i = j

@[expose] def TabP (N W c : Nat) (t : Array Nat) : Prop := Rep N W c t ∧ Inj N t

theorem rep_of_compK {N W c cs ct : Nat} {S T : Array Nat} (hs : Rep N W cs S) (ht : Rep N W ct T)
    (h : compK N W c cs ct = true) : Rep N W c (compArr S T) := by
  have h1 := allR_spec' h
  refine ⟨by simp [compArr, ht.1], fun i hi => ?_⟩
  have h2 := h1 i hi
  rw [Nat.zero_add, beq_iff] at h2
  rw [img_compArr hs.1 ht.1 (fun j hj => (ht.2 j hj).1) hi]
  refine ⟨(hs.2 _ (ht.2 i hi).1).1, ?_⟩
  rw [h2, (ht.2 i hi).2, (hs.2 _ (ht.2 i hi).1).2]

theorem inj_compArr {N : Nat} {S T : Array Nat} (hs : Rep N 0 0 S ∨ S.size = N)
    (ht : T.size = N) (hT : ∀ i < N, img T i < N) (hSi : Inj N S) (hTi : Inj N T) :
    Inj N (compArr S T) := by
  have hS : S.size = N := by
    rcases hs with h | h
    · exact h.1
    · exact h
  intro i hi j hj h
  rw [img_compArr hS ht hT hi, img_compArr hS ht hT hj] at h
  exact hTi i hi j hj (hSi _ (hT i hi) _ (hT j hj) h)

theorem tabP_of_compK {N W c cs ct : Nat} {S T : Array Nat} (hs : TabP N W cs S)
    (ht : TabP N W ct T) (h : compK N W c cs ct = true) : TabP N W c (compArr S T) :=
  ⟨rep_of_compK hs.1 ht.1 h, inj_compArr (Or.inr hs.1.1) ht.1.1 (fun j hj => (ht.1.2 j hj).1)
    hs.2 ht.2⟩

theorem foldl_slp : ∀ (l : List (Nat × Nat)) (arr : Array (Array Nat)),
    slpValidAux l arr.size = true →
    (l.foldl slpStepA arr).size = arr.size + l.length ∧
    (∀ j < arr.size, (l.foldl slpStepA arr)[j]! = arr[j]!) ∧
    ∀ k < l.length, (l.getD k (0, 0)).1 < arr.size + k ∧ (l.getD k (0, 0)).2 < arr.size + k ∧
      (l.foldl slpStepA arr)[arr.size + k]! =
        compArr (l.foldl slpStepA arr)[(l.getD k (0, 0)).1]!
          (l.foldl slpStepA arr)[(l.getD k (0, 0)).2]!
  | [], arr, _ => ⟨by simp, fun j _ => rfl, fun k hk => by simp at hk⟩
  | p :: l, arr, hv => by
    rw [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hp1, hp2⟩, hv⟩ := hv
    have hs : (slpStepA arr p).size = arr.size + 1 := by simp [slpStepA]
    rw [List.foldl_cons]
    obtain ⟨a1, a2, a3⟩ := foldl_slp l (slpStepA arr p) (by rw [hs]; exact hv)
    have hpush : ∀ j < arr.size, (slpStepA arr p)[j]! = arr[j]! := by
      intro j hj
      unfold slpStepA
      rw [getElem!_pos _ j (by simp; omega), Array.getElem_push_lt hj, ← getElem!_pos arr j hj]
    have hnew : (slpStepA arr p)[arr.size]! = compArr arr[p.1]! arr[p.2]! := by
      unfold slpStepA
      rw [getElem!_pos _ arr.size (by simp), Array.getElem_push_eq]
    refine ⟨by rw [a1, hs]; simp; omega, fun j hj => ?_, fun k hk => ?_⟩
    · rw [a2 j (by omega), hpush j hj]
    · rw [hs] at a3
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero]
        refine ⟨hp1, hp2, ?_⟩
        rw [a2 arr.size (by omega), hnew, a2 p.1 (by omega), a2 p.2 (by omega), hpush _ hp1,
          hpush _ hp2]
      | succ k =>
        simp only [List.getD_cons_succ]
        have := a3 k (by simpa using hk)
        have e : arr.size + (k + 1) = arr.size + 1 + k := by omega
        rw [e]
        refine ⟨by omega, by omega, this.2.2⟩

theorem any_beq_iff (S : List Nat) (a : Nat) : anyL S (Nat.beq a) = true ↔ a ∈ S := by
  rw [anyL_eq, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [beq_iff.1 h]
  · intro h
    exact ⟨a, h, Nat.beq_refl a⟩

theorem slp_nodes {N W : Nat} {Aa Ab : Array Nat} {TF : Nat → Nat} {prog : List (Nat × Nat)}
    {SL : List Nat}
    (h0 : TabP N W (TF 0) Aa) (h1 : TabP N W (TF 1) Ab) (hso : slpOKK prog 2 = true)
    (hsn : slpNeedK prog SL = true)
    (hs : ∀ c < lenA SL, slpChk N W TF prog (getK SL c) = true) :
    ∀ j, (j < 2 ∨ j ∈ SL) → j < prog.length + 2 ∧
      TabP N W (TF j) (slpTabsA Aa Ab prog)[j]! := by
  have hv : slpValidAux prog (#[Aa, Ab] : Array (Array Nat)).size = true :=
    slpOKK_spec' prog 2 hso
  obtain ⟨a1, a2, a3⟩ := foldl_slp prog #[Aa, Ab] hv
  have hsz2 : (#[Aa, Ab] : Array (Array Nat)).size = 2 := rfl
  rw [hsz2] at a1 a2 a3
  have hsz : (slpTabsA Aa Ab prog).size = prog.length + 2 := by
    unfold slpTabsA; rw [a1]; omega
  have hsn' : ∀ j ∈ SL, 2 ≤ j ∧ j < prog.length + 2 ∧
      ((prog.getD (j - 2) (0, 0)).1 < 2 ∨ (prog.getD (j - 2) (0, 0)).1 ∈ SL) ∧
      ((prog.getD (j - 2) (0, 0)).2 < 2 ∨ (prog.getD (j - 2) (0, 0)).2 ∈ SL) := by
    intro j hj
    unfold slpNeedK at hsn
    rw [allL_iff] at hsn
    have := hsn j hj
    have e : (fun p : Nat × Nat => andB (orB (Nat.blt p.1 2) (anyL SL (Nat.beq p.1)))
        (orB (Nat.blt p.2 2) (anyL SL (Nat.beq p.2)))) (nthP prog (Nat.sub j 2)) =
        andB (orB (Nat.blt (prog.getD (j - 2) (0, 0)).1 2)
          (anyL SL (Nat.beq (prog.getD (j - 2) (0, 0)).1)))
        (orB (Nat.blt (prog.getD (j - 2) (0, 0)).2 2)
          (anyL SL (Nat.beq (prog.getD (j - 2) (0, 0)).2))) := by
      rw [show Nat.sub j 2 = j - 2 from rfl, nthP_eq]
    rw [andB_iff, andB_iff, e, andB_iff, orB_iff, orB_iff] at this
    simp only [blt_iff, any_beq_iff, lenA_eq] at this
    obtain ⟨h1, h2, h3, h4⟩ := this
    exact ⟨Nat.le_of_ble_eq_true h1, by simpa using h2, h3, h4⟩
  show ∀ j, (j < 2 ∨ j ∈ SL) → j < prog.length + 2 ∧
      TabP N W (TF j) (prog.foldl slpStepA #[Aa, Ab])[j]!
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases hj with hj | hj
    · refine ⟨by omega, ?_⟩
      have e : ∀ m < 2, (prog.foldl slpStepA #[Aa, Ab])[m]! = (#[Aa, Ab] : Array (Array Nat))[m]! := by
        intro m hm
        exact a2 m hm
      interval_cases j
      · rw [e 0 (by omega)]; exact h0
      · rw [e 1 (by omega)]; exact h1
    · obtain ⟨hj2, hjl, hp1, hp2⟩ := hsn' j hj
      refine ⟨hjl, ?_⟩
      obtain ⟨c, hc, hcj⟩ : ∃ c, ∃ hc : c < SL.length, SL[c] = j := List.mem_iff_getElem.1 hj
      have hchk := hs c (by rw [lenA_eq]; exact hc)
      rw [getK_eq, List.getD_eq_getElem _ _ hc, hcj] at hchk
      have hk : j - 2 < prog.length := by omega
      obtain ⟨b1, b2, b3⟩ := a3 (j - 2) hk
      have hj' : 2 + (j - 2) = j := by omega
      rw [hj'] at b3
      have key : ∀ m, (m < 2 ∨ m ∈ SL) → m < j → TabP N W (TF m) (prog.foldl slpStepA #[Aa, Ab])[m]! :=
        fun m hm hmj => (ih m hmj hm).2
      have t1 := key _ hp1 (by omega)
      have t2 := key _ hp2 (by omega)
      have hchk' : compK N W (TF j) (TF (prog.getD (j - 2) (0, 0)).1)
          (TF (prog.getD (j - 2) (0, 0)).2) = true := by
        have e : slpChk N W TF prog j = andB (Nat.ble 2 j)
            (compK N W (TF j) (TF (prog.getD (j - 2) (0, 0)).1)
              (TF (prog.getD (j - 2) (0, 0)).2)) := by
          unfold slpChk
          rw [show Nat.sub j 2 = j - 2 from rfl, nthP_eq]
        rw [e, andB_iff] at hchk
        exact hchk.2
      rw [b3]
      exact tabP_of_compK t1 t2 hchk'

theorem omegaOf_zero (N : Nat) (Aa Ab par gen : Array Nat) (f : Nat) :
    omegaOf N Aa Ab par gen f 0 = Array.range N := by
  cases f <;> simp [omegaOf]

theorem omegaOf_succ (N : Nat) (Aa Ab par gen : Array Nat) (f x : Nat) (hx : x ≠ 0) :
    omegaOf N Aa Ab par gen (f + 1) x =
      compArr (if gen.getD x 0 = 0 then Aa else Ab) (omegaOf N Aa Ab par gen f (par.getD x 0)) := by
  simp [omegaOf, hx]

theorem omegaOf_fuel {N : Nat} (Aa Ab par gen : Array Nat)
    (hpar : ∀ y < N, 0 < y → par.getD y 0 < y) :
    ∀ (f f' x : Nat), x < N → x ≤ f → x ≤ f' →
      omegaOf N Aa Ab par gen f x = omegaOf N Aa Ab par gen f' x := by
  intro f
  induction f with
  | zero =>
    intro f' x _ hx _
    have : x = 0 := by omega
    subst this
    rw [omegaOf_zero, omegaOf_zero]
  | succ f ih =>
    intro f' x hxN hx hx'
    by_cases h0 : x = 0
    · subst h0; rw [omegaOf_zero, omegaOf_zero]
    · obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
      rw [omegaOf_succ _ _ _ _ _ _ _ h0, omegaOf_succ _ _ _ _ _ _ _ h0]
      have hp := hpar x hxN (by omega)
      rw [ih g _ (by omega) (by omega) (by omega)]

theorem omegaOf_self {N : Nat} (Aa Ab par gen : Array Nat)
    (hpar : ∀ y < N, 0 < y → par.getD y 0 < y) {x : Nat} (hx : x < N) (hx0 : x ≠ 0) :
    omegaOf N Aa Ab par gen x x =
      compArr (if gen.getD x 0 = 0 then Aa else Ab)
        (omegaOf N Aa Ab par gen (par.getD x 0) (par.getD x 0)) := by
  obtain ⟨g, hg⟩ : ∃ g, x = g + 1 := ⟨x - 1, by omega⟩
  have hp := hpar x hx (by omega)
  have e := omegaOf_succ N Aa Ab par gen g x hx0
  have e1 : omegaOf N Aa Ab par gen x x = omegaOf N Aa Ab par gen (g + 1) x := by rw [← hg]
  rw [e1, e]
  exact congrArg _ (omegaOf_fuel Aa Ab par gen hpar g (par.getD x 0) (par.getD x 0) (by omega)
    (by omega) (by omega))

noncomputable def needLoop (W PK : Nat) (M : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih seen => andB (andB (Nat.blt 0 x)
      (CFSG.KC.LQT.P.letB (imgW W PK x) fun p => orB (Nat.beq p 0) (anyL seen (Nat.beq p))))
      (ih (List.cons x seen))) M

theorem needLoop_spec (W PK : Nat) : ∀ (M seen : List Nat), needLoop W PK M seen = true →
    ∀ x ∈ M, 0 < x ∧ (imgW W PK x = 0 ∨ imgW W PK x ∈ seen ∨ imgW W PK x ∈ M)
  | [], _, _, x, hx => by simp at hx
  | y :: t, seen, h, x, hx => by
    have e : needLoop W PK (y :: t) seen = andB (andB (Nat.blt 0 y)
        (orB (Nat.beq (imgW W PK y) 0) (anyL seen (Nat.beq (imgW W PK y)))))
        (needLoop W PK t (y :: seen)) := by
      have e0 : needLoop W PK (y :: t) seen = andB (andB (Nat.blt 0 y)
        (CFSG.KC.LQT.P.letB (imgW W PK y) fun p => orB (Nat.beq p 0) (anyL seen (Nat.beq p))))
        (needLoop W PK t (y :: seen)) := rfl
      rw [e0, letB_eq]
    rw [e, andB_iff, andB_iff, orB_iff, blt_iff, beq_iff, any_beq_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := needLoop_spec W PK t (y :: seen) h3
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · obtain ⟨a1, a2⟩ := ih x hx
      refine ⟨a1, ?_⟩
      rcases a2 with a2 | a2 | a2
      · exact Or.inl a2
      · rcases List.mem_cons.1 a2 with a2 | a2
        · exact Or.inr (Or.inr (by rw [a2]; exact List.mem_cons_self))
        · exact Or.inr (Or.inl a2)
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ a2))

theorem om_nodes {N W : Nat} {Aa Ab par gen : Array Nat} {TF MF : Nat → Nat} {PRK GNK : Nat}
    {ML : List Nat} (hN : 0 < N)
    (h0 : TabP N W (TF 0) Aa) (h1 : TabP N W (TF 1) Ab)
    (hPK : Rep N W PRK par) (hGK : Rep N W GNK gen)
    (hpar : ∀ y < N, 0 < y → par.getD y 0 < y)
    (hid : idK N W (MF 0) = true) (hM : needP W PRK ML = true)
    (hm : ∀ c < lenA ML, omChk N W TF MF PRK GNK (getK ML c) = true) :
    ∀ x, (x = 0 ∨ x ∈ ML) → x < N ∧ TabP N W (MF x) (omegaOf N Aa Ab par gen x x) := by
  have base : TabP N W (MF 0) (omegaOf N Aa Ab par gen 0 0) := by
    rw [omegaOf_zero]
    have hr : ∀ i < N, CFSG.QuasithinUnique.K1.SporadicPerm.img (Array.range N) i = i := by
      intro i hi
      simp [CFSG.QuasithinUnique.K1.SporadicPerm.img, Array.getD_eq_getD_getElem?, hi]
    refine ⟨⟨by simp, fun i hi => ⟨by rw [hr i hi]; exact hi, ?_⟩⟩, ?_⟩
    · have := allR_spec' hid i hi
      rw [Nat.zero_add, beq_iff] at this
      rw [this, hr i hi]
    · intro i hi j hj h
      rwa [hr i hi, hr j hj] at h
  have hM' : needLoop W PRK ML [] = true := hM
  have hspec := needLoop_spec W PRK ML [] hM'
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rintro (rfl | hx)
    · exact ⟨hN, base⟩
    · obtain ⟨c, hc, hcx⟩ : ∃ c, ∃ hc : c < ML.length, ML[c] = x := List.mem_iff_getElem.1 hx
      have hchk := hm c (by rw [lenA_eq]; exact hc)
      rw [getK_eq, List.getD_eq_getElem _ _ hc, hcx] at hchk
      unfold omChk at hchk
      rw [andB_iff, andB_iff, blt_iff, blt_iff] at hchk
      obtain ⟨hx0, hxN, hcomp⟩ := hchk
      refine ⟨hxN, ?_⟩
      have hp : imgW W PRK x = par.getD x 0 := (hPK.2 x hxN).2
      have hg : imgW W GNK x = gen.getD x 0 := (hGK.2 x hxN).2
      have hpx := hpar x hxN hx0
      obtain ⟨_, hsp⟩ := hspec x hx
      have hpin : par.getD x 0 = 0 ∨ par.getD x 0 ∈ ML := by
        rcases hsp with h | h | h
        · exact Or.inl (by rw [← hp]; exact h)
        · exact absurd h (by simp)
        · exact Or.inr (by rw [← hp]; exact h)
      obtain ⟨_, tp⟩ := ih _ hpx hpin
      rw [hp] at hcomp
      rw [omegaOf_self Aa Ab par gen hpar hxN (by omega)]
      by_cases hg0 : gen.getD x 0 = 0
      · have hb : Nat.beq (imgW W GNK x) 0 = true := by rw [hg]; exact beq_iff.2 hg0
        rw [hb] at hcomp
        change compK N W (MF x) (TF 0) (MF (par.getD x 0)) = true at hcomp
        rw [if_pos hg0]
        exact tabP_of_compK h0 tp hcomp
      · have hb : Nat.beq (imgW W GNK x) 0 = false := by
          rw [hg]
          exact Bool.eq_false_iff.2 (fun h => hg0 (beq_iff.1 h))
        rw [hb] at hcomp
        change compK N W (MF x) (TF 1) (MF (par.getD x 0)) = true at hcomp
        rw [if_neg hg0]
        exact tabP_of_compK h1 tp hcomp

end CFSG.KC.LQT.PPC
