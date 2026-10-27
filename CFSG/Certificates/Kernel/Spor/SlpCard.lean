module

public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.PresCard
import CFSG.Certificates.Kernel.Spor.VOrbSound

public section

namespace CFSG.KS.SC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PC CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen

@[expose] def PermF (n : Nat) (f : Nat → Nat) : Prop :=
  (∀ x < n, f x < n) ∧ ∀ x < n, ∀ y < n, f x = f y → x = y

@[expose] noncomputable def permF (n : Nat) (f : Nat → Nat) : Equiv.Perm (Fin n) := by
  classical
  exact if h : (∀ x < n, f x < n) ∧ Function.Injective (fun x : Fin n => f x.val) then
    Equiv.ofBijective (fun x : Fin n => ⟨f x.val, h.1 x.val x.isLt⟩)
      ((Finite.injective_iff_bijective).1 fun a b e => h.2 (by simpa using e))
  else 1

theorem permOfT_eq (n : Nat) (t : Table) : permOfT n t = permF n (ap t) := rfl

theorem permF_val {n : Nat} {f : Nat → Nat} (h : PermF n f) (x : Fin n) :
    (permF n f x).val = f x.val := by
  unfold permF
  rw [dite_eq_left ⟨h.1, fun a b e => Fin.ext (h.2 a a.isLt b b.isLt e)⟩]
  rfl

theorem permF_congr {n : Nat} {f g : Nat → Nat} (hf : PermF n f) (hfg : ∀ x < n, f x = g x) :
    PermF n g ∧ permF n f = permF n g := by
  have hg : PermF n g := ⟨fun x hx => hfg x hx ▸ hf.1 x hx, fun x hx y hy e => hf.2 x hx y hy
    (by rw [hfg x hx, hfg y hy]; exact e)⟩
  refine ⟨hg, Equiv.ext fun x => Fin.ext ?_⟩
  rw [permF_val hf, permF_val hg, hfg x x.isLt]

theorem permF_id (n : Nat) : PermF n id ∧ permF n id = 1 := by
  have h : PermF n id := ⟨fun x hx => hx, fun x _ y _ e => e⟩
  refine ⟨h, Equiv.ext fun x => Fin.ext ?_⟩
  rw [permF_val h]
  rfl

theorem permF_comp {n : Nat} {f g : Nat → Nat} (hf : PermF n f) (hg : PermF n g) :
    PermF n (fun x => f (g x)) ∧ permF n (fun x => f (g x)) = permF n f * permF n g := by
  have h : PermF n (fun x => f (g x)) := ⟨fun x hx => hf.1 _ (hg.1 x hx), fun x hx y hy e =>
    hg.2 x hx y hy (hf.2 _ (hg.1 x hx) _ (hg.1 y hy) e)⟩
  refine ⟨h, Equiv.ext fun x => Fin.ext ?_⟩
  rw [permF_val h, Equiv.Perm.mul_apply, permF_val hf, permF_val hg]

theorem permF_inv {n : Nat} {f g : Nat → Nat} (hf : PermF n f) (hg : ∀ x < n, g x < n)
    (hgf : ∀ x < n, g (f x) = x) : PermF n g ∧ permF n g = (permF n f)⁻¹ := by
  have hfg : ∀ y < n, f (g y) = y := by
    intro y hy
    have e := permF_val hf ((permF n f)⁻¹ ⟨y, hy⟩)
    have e1 : (permF n f) ((permF n f)⁻¹ ⟨y, hy⟩) = ⟨y, hy⟩ := Equiv.apply_symm_apply _ _
    rw [e1] at e
    have e2 := hgf _ ((permF n f)⁻¹ ⟨y, hy⟩).isLt
    rw [← e] at e2
    rw [e2]
    exact e.symm
  have h : PermF n g := ⟨hg, fun x hx y hy e => by rw [← hfg x hx, ← hfg y hy, e]⟩
  refine ⟨h, ?_⟩
  rw [eq_inv_iff_mul_eq_one]
  refine Equiv.ext fun x => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, permF_val h, permF_val hf, hgf x x.isLt]
  rfl

@[expose] def slpG (G : Int → Nat → Nat) (L : Nat → Nat → Nat) (z : Int) (v : Nat) : Nat :=
  if z.natAbs ≤ 2 then G z v
  else if 0 < z then L (2 * (z.natAbs - 3)) v else L (2 * (z.natAbs - 3) + 1) v

theorem slpLetters_get {n : Nat} {gens : Int → Table} {words : Array (List Int)}
    {G : Int → Nat → Nat} {L : Nat → Nat → Nat} (hn : n < 2 ^ 32)
    (hg : ∀ z, ∀ x < n, ap (gens z) x = G z x ∧ G z x < n)
    (hok : ∀ j < words.size, ∀ z ∈ words[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3))
    (hw : ∀ j < words.size, ∀ x < n, L (2 * j) x = List.foldr (slpG G L) x words[j]!)
    (hinv : ∀ j < words.size, ∀ x < n, L (2 * j) x < n ∧ L (2 * j + 1) x < n ∧
      L (2 * j + 1) (L (2 * j) x) = x) :
    (CFSG.Sporadic.Fi23.Native.slpLetters n gens words).size = 2 * words.size ∧
      ∀ l < 2 * words.size, ∀ x < n,
        ap (CFSG.Sporadic.Fi23.Native.slpLetters n gens words)[l]! x = L l x := by
  have key : ∀ m ≤ words.size, ((words.toList.take m).foldl (fun L' w =>
      let T := wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L') w; (L'.push T).push (invT n T)) #[]).size = 2 * m ∧
      ∀ l < 2 * m, ∀ x < n, ap ((words.toList.take m).foldl (fun L' w =>
        let T := wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L') w; (L'.push T).push (invT n T)) #[])[l]! x =
          L l x := by
    intro m
    induction m with
    | zero => intro _; exact ⟨rfl, fun l hl => absurd hl (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hm), Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (words.toList.take m).foldl (fun L' w =>
        let T := wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L') w; (L'.push T).push (invT n T)) #[] = A at ih1 ih2
      have hwm : words.toList[m]'(by simpa using hm) = words[m]! := by
        rw [getElem!_pos words m (by omega)]
        simp
      rw [hwm]
      let G' : Int → Nat → Nat := fun z x => ap (CFSG.Sporadic.Fi23.Native.slpLetterT gens A z) x
      have hA : ∀ l : Nat, ∀ x < n, ap A[l]! x < n := by
        intro l x hx
        by_cases hl : l < 2 * m
        · rw [ih2 l hl x hx]
          obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' l
          · subst hj
            exact (hinv j (by omega) x hx).1
          · subst hj
            exact (hinv j (by omega) x hx).2.1
        · unfold ap
          rw [getElem!_neg A l (by omega)]
          have : ((default : Table)[x]!).toNat = 0 := by
            have e : (default : Table) = #[] := rfl
            rw [e]
            rfl
          rw [this]
          omega
      have hG' : ∀ z, ∀ x < n, ap (CFSG.Sporadic.Fi23.Native.slpLetterT gens A z) x = G' z x ∧ G' z x < n := by
        intro z x hx
        refine ⟨rfl, ?_⟩
        change ap (CFSG.Sporadic.Fi23.Native.slpLetterT gens A z) x < n
        unfold CFSG.Sporadic.Fi23.Native.slpLetterT
        split
        · rw [(hg z x hx).1]
          exact (hg z x hx).2
        · split
          · exact hA _ x hx
          · exact hA _ x hx
      have hagree : ∀ w : List Int, (∀ z ∈ w, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < m + 3)) →
          ∀ x < n, List.foldr G' x w = List.foldr (slpG G L) x w := by
        intro w
        induction w with
        | nil => intro _ x _; rfl
        | cons z w ihw =>
          intro hz x hx
          have hz0 := hz z List.mem_cons_self
          rw [List.foldr_cons, List.foldr_cons, ihw (fun y hy => hz y (List.mem_cons_of_mem z hy)) x hx]
          have hy : List.foldr (slpG G L) x w < n := by
            rw [← ihw (fun y hy => hz y (List.mem_cons_of_mem z hy)) x hx]
            exact (VO.wordT_ap hn hG' w).2 x hx |>.2
          change ap (CFSG.Sporadic.Fi23.Native.slpLetterT gens A z) _ = slpG G L z _
          unfold CFSG.Sporadic.Fi23.Native.slpLetterT slpG
          by_cases h2 : z.natAbs ≤ 2
          · rw [ite_eq_left h2, ite_eq_left h2]
            exact (hg z _ hy).1
          · rw [ite_eq_right h2, ite_eq_right h2]
            have hlt : z.natAbs < m + 3 := hz0.2.resolve_left h2
            split
            · exact ih2 _ (by omega) _ hy
            · exact ih2 _ (by omega) _ hy
      have hT := VO.wordT_ap hn hG' words[m]!
      have hTm : ∀ x < n, ap (wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens A) words[m]!) x = L (2 * m) x := by
        intro x hx
        rw [(hT.2 x hx).1, hagree _ (hok m (by omega)) x hx, hw m (by omega) x hx]
      have hI := VO.invT_get (f := L (2 * m)) (g := L (2 * m + 1)) hn fun x hx =>
        ⟨hTm x hx, (hinv m (by omega) x hx).1, (hinv m (by omega) x hx).2.2⟩
      refine ⟨by simp [ih1]; omega, fun l hl x hx => ?_⟩
      rcases Nat.lt_or_ge l (2 * m) with h | h
      · rw [TBfs.push_lt (by simp; omega), TBfs.push_lt (by omega), ih2 l h x hx]
      · rcases Nat.lt_or_ge l (2 * m + 1) with h' | h'
        · have : l = 2 * m := by omega
          subst this
          rw [TBfs.push_lt (by simp; omega), ← ih1, TBfs.push_eq, hTm x hx, ih1]
        · have : l = 2 * m + 1 := by omega
          subst this
          have e : (A.push (wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens A) words[m]!)).size = 2 * m + 1 := by simp [ih1]
          rw [← e, TBfs.push_eq, hI.2 x hx, e]
  have hfold : CFSG.Sporadic.Fi23.Native.slpLetters n gens words = (words.toList.take words.size).foldl
      (fun L' w => let T := wordT n (CFSG.Sporadic.Fi23.Native.slpLetterT gens L') w;
        (L'.push T).push (invT n T)) #[] := by
    rw [CFSG.Sporadic.Fi23.Native.slpLetters, ← Array.foldl_toList, ← Array.length_toList,
      List.take_length]
  rw [hfold]
  exact key words.size (Nat.le_refl _)

theorem fold_mem {n : Nat} {K : Subgroup (Equiv.Perm (Fin n))} {h : Int → Nat → Nat} :
    ∀ w : List Int, (∀ z ∈ w, PermF n (h z) ∧ permF n (h z) ∈ K) →
      PermF n (fun x => List.foldr h x w) ∧ permF n (fun x => List.foldr h x w) ∈ K
  | [], _ => by
    obtain ⟨h1, h2⟩ := permF_id n
    exact ⟨h1, by
      change permF n id ∈ K
      rw [h2]
      exact K.one_mem⟩
  | z :: w, hz => by
    obtain ⟨ih1, ih2⟩ := fold_mem w fun y hy => hz y (List.mem_cons_of_mem z hy)
    obtain ⟨hz1, hz2⟩ := hz z List.mem_cons_self
    obtain ⟨c1, c2⟩ := permF_comp hz1 ih1
    exact ⟨c1, by
      change permF n (fun x => h z (List.foldr h x w)) ∈ K
      rw [c2]
      exact K.mul_mem hz2 ih2⟩

theorem slp_mem {n : Nat} {K : Subgroup (Equiv.Perm (Fin n))} {G : Int → Nat → Nat}
    {L : Nat → Nat → Nat} {words : Array (List Int)}
    (hG : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → PermF n (G z) ∧ permF n (G z) ∈ K)
    (hok : ∀ j < words.size, ∀ z ∈ words[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3))
    (hw : ∀ j < words.size, ∀ x < n, L (2 * j) x = List.foldr (slpG G L) x words[j]!)
    (hinv : ∀ j < words.size, ∀ x < n, L (2 * j + 1) x < n ∧ L (2 * j + 1) (L (2 * j) x) = x) :
    ∀ l < 2 * words.size, PermF n (L l) ∧ permF n (L l) ∈ K := by
  have key : ∀ j, j ≤ words.size → ∀ l < 2 * j, PermF n (L l) ∧ permF n (L l) ∈ K := by
    intro j
    induction j with
    | zero => intro _ l hl; omega
    | succ j ih =>
      intro hj l hl
      have ih' := ih (by omega)
      have hw0 : PermF n (L (2 * j)) ∧ permF n (L (2 * j)) ∈ K := by
        have hz : ∀ z ∈ words[j]!, PermF n (slpG G L z) ∧ permF n (slpG G L z) ∈ K := by
          intro z hzw
          obtain ⟨hz0, hz1⟩ := hok j (by omega) z hzw
          unfold slpG
          by_cases ha : z.natAbs ≤ 2
          · simp only [ha, ↓reduceIte]
            exact hG z hz0 ha
          · have hlt : z.natAbs < j + 3 := by omega
            simp only [ha, ↓reduceIte]
            split
            · exact ih' _ (by omega)
            · exact ih' _ (by omega)
        obtain ⟨f1, f2⟩ := fold_mem (K := K) words[j]! hz
        obtain ⟨c1, c2⟩ := permF_congr f1 fun x hx => (hw j (by omega) x hx).symm
        exact ⟨c1, c2 ▸ f2⟩
      rcases Nat.lt_or_ge l (2 * j) with h1 | h1
      · exact ih' l h1
      · rcases (by omega : l = 2 * j ∨ l = 2 * j + 1) with rfl | rfl
        · exact hw0
        · obtain ⟨i1, i2⟩ := permF_inv hw0.1 (fun x hx => (hinv j (by omega) x hx).1)
            fun x hx => (hinv j (by omega) x hx).2
          exact ⟨i1, by rw [i2]; exact K.inv_mem hw0.2⟩
  exact key words.size le_rfl

@[expose] def letV (F0 F0I F1 F1I : Nat → Nat) (l : Nat × Bool) (v : Nat) : Nat :=
  if l.1 = 0 then (if l.2 then F0 v else F0I v) else (if l.2 then F1 v else F1I v)

theorem wordProd_val {n : Nat} {F0 F0I F1 F1I : Nat → Nat} (h0 : PermF n F0) (h1 : PermF n F1)
    (h0i : PermF n F0I ∧ permF n F0I = (permF n F0)⁻¹)
    (h1i : PermF n F1I ∧ permF n F1I = (permF n F1)⁻¹) :
    ∀ (v : List (Nat × Bool)) (x : Fin n),
      ((wordProd (img2 (permF n F0) (permF n F1)) v) x).val =
        List.foldr (letV F0 F0I F1 F1I) x.val v
  | [], x => rfl
  | l :: v, x => by
    have ih := wordProd_val h0 h1 h0i h1i v x
    simp only [wordProd, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, List.foldr_cons] at ih ⊢
    obtain ⟨i, b⟩ := l
    have hy := ((List.map (fun l => if l.2 = true then img2 (permF n F0) (permF n F1) l.1
      else (img2 (permF n F0) (permF n F1) l.1)⁻¹) v).prod x).isLt
    rw [← ih]
    unfold letV img2
    by_cases hi : i = 0 <;> cases b <;> simp only [hi, ↓reduceIte, Bool.false_eq_true]
    · rw [← h0i.2, permF_val h0i.1]
    · rw [permF_val h0]
    · rw [← h1i.2, permF_val h1i.1]
    · rw [permF_val h1]

theorem card_letters_le {n NL : Nat} {letters : Array Table} {L : Nat → Nat → Nat}
    {F0 F0I F1 F1I : Nat → Nat} (P : TauCeti.GroupPresentation) (hP : P.generatorCount = 2)
    [Finite P.Group]
    (h0 : PermF n F0) (h1 : PermF n F1) (h0i : ∀ x < n, F0I x < n ∧ F0I (F0 x) = x)
    (h1i : ∀ x < n, F1I x < n ∧ F1I (F1 x) = x)
    (hrel : ∀ v ∈ P.relatorLetters, ∀ x < n, List.foldr (letV F0 F0I F1 F1I) x v = x)
    (hL : ∀ l < NL, ∀ x < n, ap letters[l]! x = L l x)
    (hmem : ∀ l < NL, PermF n (L l) ∧
      permF n (L l) ∈ Subgroup.closure ({permF n F0, permF n F1} : Set (Equiv.Perm (Fin n)))) :
    Nat.card (Subgroup.closure (Set.range fun l : Fin NL => permOfT n letters[l.val]!)) ≤
      Nat.card P.Group := by
  have g0i := permF_inv h0 (fun x hx => (h0i x hx).1) fun x hx => (h0i x hx).2
  have g1i := permF_inv h1 (fun x hx => (h1i x hx).1) fun x hx => (h1i x hx).2
  have hr : ∀ v ∈ P.relatorLetters, wordProd (img2 (permF n F0) (permF n F1)) v = 1 := by
    intro v hv
    refine Equiv.ext fun x => Fin.ext ?_
    rw [wordProd_val h0 h1 g0i g1i v x, hrel v hv x.val x.isLt]
    rfl
  refine le_trans ?_ (CFSG.KS.Pres.card_closure_le P hP hr)
  apply Subgroup.card_le_of_le
  rw [Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  obtain ⟨m1, m2⟩ := hmem l.val l.isLt
  change permOfT n letters[l.val]! ∈ _
  rw [permOfT_eq, ← (permF_congr m1 fun x hx => (hL l.val l.isLt x hx).symm).2]
  exact m2

end CFSG.KS.SC

end
