module

public import CFSG.Certificates.Kernel.O8ModelDefs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.F2WordSound
import CFSG.Certificates.Kernel.O8TilProved

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.KC.Enum (pidn pg permOK pcomp)
open CFSG.Monster.B.Co2 PA

private theorem perm_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    CFSG.KC.Enum.allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

private theorem one_nIf (c : Bool) :
    Nat.beq (nat_lit 1) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) c) = c := by
  cases c <;> rfl

private theorem fget_lt2 (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq_pg, Orb.pg_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

private theorem land127 (e : ℕ) : Nat.land e 127 = e % 128 := Nat.and_two_pow_sub_one_eq_mod e 7

private theorem canon_eq {n w P Q : ℕ} (hw : 0 < w) (hP : P >>> (n * w) = 0)
    (hQ : Q >>> (n * w) = 0) : eqA n (unpack n w P) (unpack n w Q) = Nat.beq P Q := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    unfold eqA at h
    rw [allLt_iff] at h
    have e : P = Q := PF.eq_of_fields hw hP hQ fun i hi => by
      have := h i hi
      rwa [beq_iff_eq, Orb.unpack_get hi, Orb.unpack_get hi] at this
    rw [e]
    exact Nat.beq_refl Q
  · intro h
    rw [Nat.eq_of_beq_eq_true h]
    exact eqA_self _

private theorem compA_unpack {n w P Q : ℕ} (h32 : n < 2 ^ 32) (hP : P >>> (n * w) = 0) :
    compA n (unpack n w P) (unpack n w Q) = unpack n w (pcomp n w (mask w) P Q) := by
  apply arr_ext (by simp [compA]) (unpack_size _ _ _)
  intro i hi
  rw [compA_get hi, Orb.unpack_get hi, unpack_get' hP, Orb.unpack_get hi, PF.pg_pcomp h32 hi]

private theorem conj_unpack {n w L LI X : ℕ} (h32 : n < 2 ^ 32) (hw : 0 < w)
    (hp : permOK n w (mask w) (n * w) L LI = true) :
    conjA n (unpack n w L) (unpack n w X) = unpack n w (pc n w (pc n w L X) LI) := by
  obtain ⟨hL, -, -⟩ := Orb.permOK_facts hp
  have hr := rep_permOfArr (Orb.isInvA_unpack hp)
  apply arr_ext (by simp [conjA, compA]) (unpack_size _ _ _)
  intro i hi
  have hinv : (invCand n (unpack n w L))[i]! = pg w (mask w) LI i := by
    rw [(rep_invCand hr.1).apply hi, ← hr.2.apply hi, Orb.unpack_get hi]
  rw [conjA, compA_get hi, hinv, compA_unpack h32 hL, unpack_get' (PF.pcomp_shr _ _ h32 hw),
    Orb.unpack_get hi]
  change _ = pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) L X) LI) i
  rw [PF.pg_pcomp h32 hi]

private theorem idA_unpack {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    idA n = unpack n w (pidn n w) :=
  arr_eq_of_rep (by simp [idA]) (unpack_size _ _ _) rep_idA (Orb.rep_unpack (Orb.prep_pidn hn hw))

private theorem isInvol_unpack {n w S : ℕ} (h32 : n < 2 ^ 32) (hn : n < 16777216)
    (hw' : n + 1 < 2 ^ w) (hS : S >>> (n * w) = 0) :
    isInvol n (unpack n w S) = isInvolK n w S := by
  have hw := PF.w_pos hw'
  unfold isInvol
  rw [idA_unpack hn hw', canon_eq hw hS (PF.pidn_shr hn hw'), compA_unpack h32 hS,
    canon_eq hw (PF.pcomp_shr _ _ h32 hw) (PF.pidn_shr hn hw'), isInvolK, ctAndB_eq, ctNotB_eq]
  rfl

private theorem toArray_getD' (l : List Bool) (c : ℕ) : l.toArray.getD c false = l.getD c false := by
  by_cases h : c < l.length
  · simp [Array.getD, h]
  · simp [Array.getD, h]

private theorem getD_ofFn'' {α : Type} {m : ℕ} (f : Fin m → α) (x : α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f).getD i x = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

private theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

private theorem getD_snoc (pre : List Bool) (b : Bool) (c : ℕ) :
    (pre ++ [b]).getD c false = (pre.getD c false || (b && c == pre.length)) := by
  rcases lt_trichotomy c pre.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have h1 : pre.length ≤ c := by omega
    have h2 : (pre ++ [b]).length ≤ c := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2,
      Nat.ne_of_gt h]

private theorem getD_lt {pre : List Bool} {c : ℕ} (h : pre.getD c false = true) : c < pre.length := by
  by_contra hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

private theorem filter_or_length (l : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i ∈ l, ¬(p i = true ∧ q i = true)) :
    (l.filter fun i => p i || q i).length = (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

private theorem selB_snoc (pre : List Bool) (b : Bool) (x : Option (ℕ × ℕ)) :
    selB (pre ++ [b]).toArray x = (selB pre.toArray x || (b && x.map Prod.fst == some pre.length)) := by
  rcases x with _ | ⟨c, j⟩
  · simp [selB]
  · simp only [selB, toArray_getD', getD_snoc, Option.map_some]
    cases b <;> simp

private theorem selB_lt {pre : List Bool} {x : Option (ℕ × ℕ)} (h : selB pre.toArray x = true) :
    ∃ c j, x = some (c, j) ∧ c < pre.length := by
  rcases x with _ | ⟨c, j⟩
  · simp [selB] at h
  · simp only [selB, toArray_getD'] at h
    exact ⟨c, j, rfl, getD_lt h⟩

private theorem enumK_zero (NC ADJ SZ : ℕ) (leaf : ℕ → Bool) (m s : ℕ) :
    enumK NC ADJ SZ leaf 0 m s = orB (notB (Nat.beq s 63)) (leaf m) := rfl

private theorem enumK_succ (NC ADJ SZ : ℕ) (leaf : ℕ → Bool) (r m s : ℕ) :
    enumK NC ADJ SZ leaf (r + 1) m s = andB (enumK NC ADJ SZ leaf r m s)
      (orB (notB (andB (adjAt ADJ NC (NC - (r + 1)) (NC - (r + 1)))
          (allN (NC - (r + 1)) fun c' => orB (notB (bit m c')) (adjAt ADJ NC c' (NC - (r + 1))))))
        (enumK NC ADJ SZ leaf r (Nat.lor m (pw2 (NC - (r + 1))))
          (Nat.add s (fget SZ (NC - (r + 1)) 12)))) := rfl

private theorem enum_gen {NC ADJ SZ : ℕ} {leaf : ℕ → Bool} {ok : List Bool → Bool}
    {sel : List Bool → ℕ}
    (hok : ∀ pre : List Bool, pre.length < NC → ∀ m : ℕ,
      (∀ c, m.testBit c = pre.getD c false) → ok (pre ++ [true]) = true →
      andB (adjAt ADJ NC pre.length pre.length)
        (allN pre.length fun c' => orB (notB (bit m c')) (adjAt ADJ NC c' pre.length)) = true)
    (hsel0 : ∀ pre, sel (pre ++ [false]) = sel pre)
    (hsel1 : ∀ pre : List Bool, pre.length < NC →
      sel (pre ++ [true]) = sel pre + fget SZ pre.length 12) :
    ∀ r (pre : List Bool) (m s : ℕ), pre.length + r = NC → (∀ c, m.testBit c = pre.getD c false) →
      s = sel pre → enumK NC ADJ SZ leaf r m s = true →
      ∀ d ∈ enumAux ok r pre, ∃ m' : ℕ, (∀ c, m'.testBit c = d.getD c false) ∧
        (sel d ≠ 63 ∨ leaf m' = true) := by
  intro r
  induction r with
  | zero =>
    intro pre m s _ hm hs h d hd
    simp only [enumAux, List.mem_singleton] at hd
    subst hd
    refine ⟨m, hm, ?_⟩
    rw [enumK_zero, ctOrB_eq, ctNotB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · left
      rw [← hs]
      exact Nat.ne_of_beq_eq_false h
    · exact Or.inr h
  | succ r ih =>
    intro pre m s hl hm hs h d hd
    have ht : NC - (r + 1) = pre.length := by omega
    rw [enumK_succ, ht, ctAndB_eq, ctOrB_eq, ctNotB_eq, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨h0, h1⟩ := h
    rw [enumAux] at hd
    rcases List.mem_append.1 hd with hd | hd
    · split at hd
      · refine ih (pre ++ [false]) m s (by simp; omega) (fun c => ?_) (by rw [hsel0]; exact hs) h0
          d hd
        rw [hm c, getD_snoc]
        simp
      · simp at hd
    · split at hd
      · rename_i hokt
        have hc := hok pre (by omega) m hm hokt
        rcases h1 with h1 | h1
        · rw [hc] at h1
          exact absurd h1 (by decide)
        · refine ih (pre ++ [true]) _ _ (by simp; omega) (fun c => ?_)
            (by rw [hsel1 pre (by omega), hs]; rfl) h1 d hd
          change (m ||| pw2 pre.length).testBit c = _
          rw [pw2_eq, Nat.testBit_or, Nat.testBit_two_pow, hm c, getD_snoc]
          by_cases hcl : c = pre.length
          · subst hcl
            simp
          · have hcl' : pre.length ≠ c := Ne.symm hcl
            simp [hcl, hcl']
      · simp at hd

set_option maxRecDepth 100000 in
theorem s5_sound {n w : Nat} {US LS : Array (Array ℕ)} {UB LB a : Array ℕ}
    {cands : List (List ℤ)}
    {SU SIU LRU TRU TRIU SL SIL LRL TRL TRIL : Nat → Nat}
    {kSU nbU BPU kSL kOL nbL BPL CLS REPS NC ADJ SZ A : Nat} {DL : List (List Int)}
    (hU : LevelsK n w SU SIU LRU TRU TRIU kSU kSU nbU BPU [] US UB)
    (hL : LevelsK n w SL SIL LRL TRL TRIL kSL kOL nbL BPL DL LS LB)
    (ha : a.toList = (List.range n).map fun i => fget A i w) (hAc : Nat.shiftRight A (n * w) = 0)
    (hlc : ∀ wd ∈ cands, lettersK kSL wd = true)
    (hcls : allN 4096 (fun i => orB (Nat.beq (clsAt CLS i) 0)
      (notB (Nat.beq (Nat.land (clsAt CLS i) 127) 0))) = true)
    (he : ∀ b < 16, s5ElemOK n w ⟨LRU, TRU, TRIU, BPU, nbU⟩ b = true)
    (hc : ∀ b < 16, s5ClsOK n w ⟨LRU, TRU, TRIU, BPU, nbU⟩ CLS REPS NC b = true)
    (hrep : s5RepOK CLS REPS NC = true)
    (hadj : ∀ b < 6, s5AdjNegOK n w ⟨LRU, TRU, TRIU, BPU, nbU⟩ CLS REPS NC ADJ b = true)
    (hsz : s5SizeOK CLS NC SZ = true) (hNC : NC ≤ 48)
    (h : s5EnumOK n w ⟨LRU, TRU, TRIU, BPU, nbU⟩ ⟨LRL, TRIL, BPL, nbL⟩ SL SIL CLS NC ADJ SZ A cands =
      true) :
    s5CheckG n US UB LS LB a cands (uListK n w ⟨LRU, TRU, TRIU, BPU, nbU⟩) (uClsK CLS REPS NC) =
      true := by
  obtain ⟨cU, hcU⟩ : ∃ c : ChainT, c = ⟨LRU, TRU, TRIU, BPU, nbU⟩ := ⟨_, rfl⟩
  rw [← hcU] at he hc hadj h ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = uListK n w cU := ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨D, hD⟩ : ∃ D, D = uClsK CLS REPS NC := ⟨_, rfl⟩
  rw [← hD]
  obtain ⟨hbU, hhU, hlU⟩ := hU
  obtain ⟨hbL, hhL, hlL⟩ := hL
  have hpU := perm_head hhU
  have hpL := perm_head hhL
  have hbU' := hbU
  obtain ⟨-, hw', h16, -, -, -, -⟩ := hbU'
  have h32 : n < 2 ^ 32 := by omega
  have hn : n < 16777216 := by omega
  have hw : 0 < w := PF.w_pos hw'
  have hSget : ∀ i < 4096, S.getD i #[] = unpack n w (elemT n w cU i) := fun i hi => by
    rw [hS, uListK]
    exact getD_ofFn'' _ _ hi
  have hE : ∀ i < 4096, permOK n w (mask w) (n * w) (elemT n w cU i) (elemInvT n w cU i) = true ∧
      siftCh n w (chOf cU) (elemT n w cU i) = true ∧ idxT n w cU (elemT n w cU i) = i := by
    intro i hi
    have h1 := he (i / 256) (by omega)
    unfold s5ElemOK at h1
    rw [ctAllN_iff] at h1
    have h2 := h1 (i % 256) (Nat.mod_lt _ (by norm_num))
    have e : blk (i / 256) (i % 256) = i := Nat.div_add_mod i 256
    simp only [e, F2W.strictN_eq, one_nIf, ctAndB_eq, Bool.and_eq_true] at h2
    exact ⟨h2.1, h2.2.1, Nat.eq_of_beq_eq_true h2.2.2⟩
  have hcan : ∀ i < 4096, elemT n w cU i >>> (n * w) = 0 := fun i hi =>
    (Orb.permOK_facts (hE i hi).1).1
  have hclsG : ∀ i < 4096, clsOfW D i = decCls (clsAt CLS i) := fun i hi => by
    rw [hD, clsOfW, uClsK]
    exact getD_ofFn'' (fun j : Fin 4096 => decCls (clsAt CLS j.val)) none hi
  have hnc : nClsW D = NC := by
    subst hD
    simp only [nClsW, uClsK, Array.size_ofFn]
  have hrepG : ∀ c < NC, repOfW D c = fget REPS c 12 := fun c hc' => by
    subst hD
    simp only [repOfW, uClsK]
    rw [getD_ofFn'' _ _ hc']
  have hcls' : ∀ i < 4096, clsAt CLS i = 0 ∨ clsAt CLS i % 128 ≠ 0 := fun i hi => by
    have := ctAllN_iff.1 hcls i hi
    rw [ctOrB_eq, ctNotB_eq, Bool.or_eq_true, Bool.not_eq_true', land127] at this
    rcases this with h0 | h0
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)
    · exact Or.inr (Nat.ne_of_beq_eq_false h0)
  have hmem : ∀ i < 4096, ∀ c, ((clsOfW D i).map Prod.fst == some c) =
      Nat.beq (Nat.land (clsAt CLS i) 127) (Nat.succ c) := by
    intro i hi c
    rw [hclsG i hi, land127, Bool.eq_iff_iff, beq_iff_eq,
      show ∀ x y : ℕ, (Nat.beq x y = true) ↔ x = y from
        fun x y => ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl x⟩]
    unfold decCls
    rcases hcls' i hi with h0 | h0
    · simp [h0]
    · have hne : clsAt CLS i ≠ 0 := fun h' => h0 (by rw [h'])
      simp only [hne, if_false, Option.map_some, Option.some.injEq]
      omega
  have hadjK : ∀ c' t, c' < NC → t < NC →
      ((adjTabG n S D).getD c' #[]).getD t false = true → adjAt ADJ NC c' t = true := by
    intro c' t hc' ht htab
    have hT : ∀ c'' < NC, (membersTabW D).getD c'' [] = membersOfW D c'' := fun c'' h' => by
      have h'' : c'' < nClsW D := by rw [hnc]; exact h'
      unfold membersTabW
      exact getD_ofFn'' _ _ h''
    have hc2 : c' < nClsW D := by rw [hnc]; exact hc'
    have ht2 : t < nClsW D := by rw [hnc]; exact ht
    simp only [adjTabG] at htab
    rw [getD_ofFn'' _ _ hc2, getD_ofFn'' _ _ ht2, hT c' hc', hT t ht] at htab
    by_contra hA
    rw [Bool.not_eq_true] at hA
    have h1 := hadj (c' / 8) (by omega)
    unfold s5AdjNegOK at h1
    rw [ctAllN_iff] at h1
    have h2 := h1 (c' % 8) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul 8 (c' / 8)) (c' % 8) = c' := Nat.div_add_mod c' 8
    simp only [e, ctOrB_eq, ctNotB_eq, F2W.strictN_eq, one_nIf, Bool.or_eq_true,
      Bool.not_eq_true', ctAllN_iff] at h2
    rcases h2 with h2 | h2
    · rw [Nat.blt_eq.mpr hc'] at h2
      exact absurd h2 (by decide)
    have h3 := (h2 t ht).resolve_left (by rw [hA]; exact Bool.false_ne_true)
    rw [ctAnyN_iff] at h3
    obtain ⟨y, hy, hy2⟩ := h3
    simp only [ctAndB_eq, Bool.and_eq_true, ctNotB_eq, Bool.not_eq_true'] at hy2
    set r := fget REPS c' 12 with hr
    have hr4 : r < 4096 := fget_lt2 _ _ 12
    have hrc : Nat.beq (Nat.land (clsAt CLS r) 127) (Nat.succ c') = true := by
      have := ctAllN_iff.1 hrep c' hc'
      exact this
    have hrm : r ∈ membersOfW D c' := by
      simp only [membersOfW, List.mem_filter, List.mem_range]
      exact ⟨hr4, by rw [hmem r hr4]; exact hrc⟩
    have hym : y ∈ membersOfW D t := by
      simp only [membersOfW, List.mem_filter, List.mem_range]
      exact ⟨hy, by rw [hmem y hy]; exact hy2.1⟩
    simp only [List.all_eq_true] at htab
    have hq := htab r hrm y hym
    rw [hSget r hr4, hSget y hy, compA_unpack h32 (hcan r hr4), compA_unpack h32 (hcan y hy),
      canon_eq hw (PF.pcomp_shr _ _ h32 hw) (PF.pcomp_shr _ _ h32 hw)] at hq
    have hq2 : Nat.beq (pc n w (elemT n w cU r) (elemT n w cU y))
        (pc n w (elemT n w cU y) (elemT n w cU r)) = false := hy2.2
    exact absurd hq (by rw [Bool.not_eq_true]; exact hq2)
  have hsel0 : ∀ pre : List Bool, sumSelW D (pre ++ [false]) = sumSelW D pre := by
    intro pre
    simp only [sumSelW]
    have e : ∀ i ∈ List.range 4096, selB (pre ++ [false]).toArray (clsOfW D i) =
        selB pre.toArray (clsOfW D i) := fun i _ => by
      rw [selB_snoc]
      simp
    rw [List.filter_congr e]
  have hsel1 : ∀ pre : List Bool, pre.length < NC →
      sumSelW D (pre ++ [true]) = sumSelW D pre + fget SZ pre.length 12 := by
    intro pre hpre
    simp only [sumSelW]
    have e1 : ((List.range 4096).filter fun i => selB (pre ++ [true]).toArray (clsOfW D i)) =
        (List.range 4096).filter fun i => selB pre.toArray (clsOfW D i) ||
          ((clsOfW D i).map Prod.fst == some pre.length) := by
      apply List.filter_congr
      intro i _
      rw [selB_snoc, Bool.true_and]
    rw [e1, filter_or_length]
    · have hs := ctAllN_iff.1 hsz pre.length hpre
      have hq : ((List.range 4096).filter fun i =>
          (clsOfW D i).map Prod.fst == some pre.length).length = fget SZ pre.length 12 := by
        rw [Nat.eq_of_beq_eq_true hs, TilPf.sum4096,
          List.filter_congr (fun i hi => hmem i (List.mem_range.1 hi) _)]
      rw [hq]
    · intro i _ ⟨h1, h2⟩
      obtain ⟨c, j, hx, hcl⟩ := selB_lt h1
      rw [hx] at h2
      simp at h2
      omega
  have hbL' := hbL
  obtain ⟨-, -, -, hLS, hLSj, -, -⟩ := hbL'
  have hrepL : ∀ h < kSL, Rep n (unpack n w (SL h)) (permOfArr n (unpack n w (SL h))) ∧
      Rep n (unpack n w (SIL h)) (permOfArr n (unpack n w (SL h)))⁻¹ := fun h' hh =>
    rep_permOfArr (Orb.isInvA_unpack (Orb.allN_iff.1 hpL h' hh))
  have hS' : ∀ h < kSL, Rep n LS[h]! (permOfArr n (unpack n w (SL h))) := fun h' hh => by
    rw [hLSj h' hh]
    exact (hrepL h' hh).1
  have hSi : ∀ h < kSL, Rep n (rawInvs n LS)[h]! (permOfArr n (unpack n w (SL h)))⁻¹ :=
    fun h' hh => by
      rw [Orb.rawInvs_get (by omega)]
      exact rep_invCand (hS' h' hh)
  have hW : ∀ wd : List ℤ, lettersK kSL wd = true →
      wordA n LS (rawInvs n LS) wd = unpack n w (wordC n w SL SIL wd) := by
    intro wd hwd
    obtain ⟨hPw, hlo⟩ := Orb.prep_wordK (gs := fun h => permOfArr n (unpack n w (SL h)))
      (j := kSL) hn hw' (fun h hh => Orb.prep_of_rep (hrepL h hh).1)
      (fun h hh => Orb.prep_of_rep (hrepL h hh).2) wd hwd
    exact arr_eq_of_rep (wordA_size' _ _ _ _) (unpack_size _ _ _)
      (rep_wordA (gs := fun h => permOfArr n (unpack n w (SL h))) hS' hSi _ hlo)
      (Orb.rep_unpack hPw)
  have hA : a = unpack n w A := unpack_of_toList ha
  have hselK : ∀ (d : List Bool) (m : ℕ), (∀ c, m.testBit c = d.getD c false) → ∀ i < 4096,
      selB d.toArray (clsOfW D i) = selK m (clsAt CLS i) := by
    intro d m hm i hi
    rw [hclsG i hi, selK, ctAndB_eq, ctNotB_eq, F2W.bit_eq, land127, hm]
    unfold decCls
    by_cases h0 : clsAt CLS i = 0
    · simp [h0, selB]
    · have : Nat.beq (clsAt CLS i) 0 = false := beq_false_of_ne h0
      simp [h0, selB, this, toArray_getD']
  unfold s5CheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hS, uListK, Array.size_ofFn]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro i hi
    obtain ⟨hp, hs, -⟩ := hE i hi
    have hr := rep_permOfArr (Orb.isInvA_unpack hp)
    rw [hSget i hi]
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨isInvA_of_rep hr.1 (rep_invCand hr.1), unpack_size _ _ _⟩, ?_⟩
    unfold memG
    have hs' : siftK n w (mask w) (n * w) (pidn n w) LRU TRIU BPU nbU 0 (elemT n w cU i) = true := by
      subst hcU
      exact hs
    exact siftK_sound hbU hpU hlU rfl (range_of_permOK hp) hs'
  · rw [allLt_iff]
    intro i hi
    rw [allLt_iff]
    intro j hj
    rw [hSget i hi, hSget j (by omega), canon_eq hw (hcan i hi) (hcan j (by omega)),
      Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro he'
    have e := Nat.eq_of_beq_eq_true he'
    have h1 := (hE i hi).2.2
    rw [e, (hE j (by omega)).2.2] at h1
    omega
  · rw [allLt_iff]
    intro i hi
    have h1 := hc (i / 256) (by omega)
    unfold s5ClsOK at h1
    rw [ctAllN_iff] at h1
    have h2 := h1 (i % 256) (Nat.mod_lt _ (by norm_num))
    have e : blk (i / 256) (i % 256) = i := Nat.div_add_mod i 256
    simp only [e, F2W.strictN_eq, one_nIf] at h2
    rw [hclsG i hi, hSget i hi]
    unfold decCls
    by_cases h0 : clsAt CLS i = 0
    · rw [if_pos h0]
      simp only [h0, Nat.beq_refl] at h2
      rw [ctNotB_eq] at h2
      simp only [Bool.not_eq_true']
      rw [isInvol_unpack h32 hn hw' (hcan i hi)]
      simpa using h2
    · rw [if_neg h0]
      have hb0 : Nat.beq (clsAt CLS i) 0 = false := beq_false_of_ne h0
      simp only [hb0, ctAndB_eq, Bool.and_eq_true] at h2
      obtain ⟨hcN, hinv, heq⟩ := h2
      rw [land127] at hcN heq
      have hj : Nat.shiftRight (clsAt CLS i) 7 = clsAt CLS i / 128 :=
        Nat.shiftRight_eq_div_pow _ 7
      rw [hj] at heq
      have hcN' : clsAt CLS i % 128 - 1 < NC := Nat.blt_eq.mp hcN
      have hj4 : clsAt CLS i / 128 < 4096 := by
        have : clsAt CLS i < 524288 := fget_lt2 CLS i 19
        omega
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨by rw [hnc]; exact hcN', hj4⟩, ?_⟩, ?_⟩
      · rw [isInvol_unpack h32 hn hw' (hcan i hi)]
        exact hinv
      · rw [hrepG _ hcN', hSget _ hj4, hSget _ (fget_lt2 _ _ 12),
          conj_unpack h32 hw (hE _ hj4).1, Nat.eq_of_beq_eq_true heq]
        exact eqA_self _
  · rw [allLt_iff]
    intro c hc'
    rw [hnc] at hc'
    rw [hrepG c hc']
    exact decide_eq_true (fget_lt2 _ _ 12)
  ·
    rw [List.all_eq_true]
    intro d hd
    rw [hnc] at hd
    unfold s5EnumOK at h
    have hok : ∀ pre : List Bool, pre.length < NC → ∀ m : ℕ,
        (∀ c, m.testBit c = pre.getD c false) → okPreG (adjTabG n S D) (pre ++ [true]) = true →
        andB (adjAt ADJ NC pre.length pre.length)
          (allN pre.length fun c' => orB (notB (bit m c')) (adjAt ADJ NC c' pre.length)) = true := by
      intro pre hpre m hm hokp
      unfold okPreG at hokp
      simp only [List.getLast?_concat, List.length_append, List.length_singleton,
        Nat.add_sub_cancel, Bool.and_eq_true, allLt_iff, Bool.or_eq_true,
        Bool.not_eq_true'] at hokp
      obtain ⟨hself, hall⟩ := hokp
      rw [ctAndB_eq, Bool.and_eq_true, ctAllN_iff]
      refine ⟨hadjK _ _ hpre hpre hself, fun c' hc'' => ?_⟩
      rw [ctOrB_eq, ctNotB_eq, Bool.or_eq_true, Bool.not_eq_true', F2W.bit_eq, hm]
      rcases hall c' hc'' with h' | h'
      · left
        rw [toArray_getD', getD_snoc] at h'
        simpa [Nat.ne_of_lt hc''] using h'
      · exact Or.inr (hadjK _ _ (by omega) hpre h')
    have h0sel : sumSelW D [] = 0 := by
      simp only [sumSelW]
      have e : ∀ i ∈ List.range 4096, selB ([] : List Bool).toArray (clsOfW D i) = false :=
        fun i _ => by rcases clsOfW D i with _ | ⟨c, j⟩ <;> simp [selB]
      rw [List.filter_congr e, List.filter_false]
      rfl
    obtain ⟨m', hm', hres⟩ := enum_gen hok hsel0 hsel1 NC [] 0 0 (by simp)
      (fun c => by simp) h0sel.symm h d hd
    rw [Bool.or_eq_true, bne_iff_ne, ne_eq]
    rcases hres with hres | hres
    · exact Or.inl hres
    right
    have hleaf : ∀ cs : List (List ℤ), List.rec (motive := fun _ => Bool) false
        (fun wd _ ih => orB (finalK n w cU ⟨LRL, TRIL, BPL, nbL⟩ CLS A (wordC n w SL SIL wd)
          (wordC n w SL SIL (List.reverse (List.map (fun x => Int.neg x) wd))) m') ih) cs = true →
        ∃ wd ∈ cs, finalK n w cU ⟨LRL, TRIL, BPL, nbL⟩ CLS A (wordC n w SL SIL wd)
          (wordC n w SL SIL (List.reverse (List.map (fun x => Int.neg x) wd))) m' = true := by
      intro cs
      induction cs with
      | nil => intro h'; exact absurd h' Bool.false_ne_true
      | cons wd cs ih =>
        intro h'
        change orB _ _ = true at h'
        rw [ctOrB_eq, Bool.or_eq_true] at h'
        rcases h' with h' | h'
        · exact ⟨wd, List.mem_cons_self, h'⟩
        · obtain ⟨wd', hwd', h''⟩ := ih h'
          exact ⟨wd', List.mem_cons_of_mem _ hwd', h''⟩
    obtain ⟨wd, hwd, hfin⟩ := hleaf cands hres
    rw [List.any_eq_true]
    refine ⟨wd, hwd, ?_⟩
    unfold finalK at hfin
    simp only [ctAndB_eq, ctOrB_eq, ctNotB_eq, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', ctAllN_iff] at hfin
    obtain ⟨hsL, hpl, hla, hall⟩ := hfin
    set Lw := wordC n w SL SIL wd
    set LI := wordC n w SL SIL (List.reverse (List.map (fun x => Int.neg x) wd))
    have hrl := rep_permOfArr (Orb.isInvA_unpack hpl)
    rw [hW wd (hlc wd hwd)]
    simp only [Bool.and_eq_true, Bool.not_eq_true', allLt_iff, Bool.or_eq_true]
    refine ⟨⟨⟨?_, isInvA_of_rep hrl.1 (rep_invCand hrl.1)⟩, ?_⟩, fun i hi => ?_⟩
    · unfold memG
      exact siftK_sound hbL hpL hlL rfl (range_of_permOK hpl) hsL
    · have hPc : pc n w (pc n w Lw A) LI >>> (n * w) = 0 := PF.pcomp_shr _ _ h32 hw
      rw [hA, conj_unpack h32 hw hpl, canon_eq hw hPc hAc]
      exact hla
    · rw [hselK d m' hm' i hi]
      rcases hall i hi with h' | h'
      · exact Or.inl h'
      · right
        obtain ⟨hkk, hy, hsk⟩ := h'
        have hkk' : idxT n w cU (pc n w (pc n w Lw (elemT n w cU i)) LI) < 4096 := Nat.blt_eq.mp hkk
        rw [List.any_eq_true]
        refine ⟨_, List.mem_range.2 hkk', ?_⟩
        rw [Bool.and_eq_true, hSget i hi, hSget _ hkk', conj_unpack h32 hw hpl,
          ← Nat.eq_of_beq_eq_true hy, hselK d m' hm' _ hkk']
        exact ⟨eqA_self _, hsk⟩

end CFSG.KC.O8

end
