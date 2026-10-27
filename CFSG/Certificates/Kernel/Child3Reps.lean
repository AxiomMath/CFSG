module

public import Certificates.Data.Kernel.Child3
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import CFSG.Certificates.Kernel.SporSch.KeyBfsSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.KeyBfs
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

noncomputable abbrev tabP (n w X : Nat) : Table := arrTable n (unpack n w X)

theorem unpack_get' {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem tabP_get {n w X i : Nat} (hi : i < n) :
    (tabP n w X)[i]! = UInt32.ofNat (pg w (mask w) X i) := by
  rw [tabP, arrTable, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, unpack_get' hi]

theorem ap_tabP {n w X i : Nat} (hi : i < n) (hX : pg w (mask w) X i < 2 ^ 32) :
    ap (tabP n w X) i = pg w (mask w) X i := by
  unfold ap
  rw [tabP_get hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hX]

theorem tabP_size (n w X : Nat) : (tabP n w X).size = n := by simp [tabP, arrTable]

theorem compT_tabP {n w P Q : Nat} (hn : n < 2 ^ 32) (hQ : ∀ i < n, pg w (mask w) Q i < n) :
    compT n (tabP n w P) (tabP n w Q) = tabP n w (pcomp n w (mask w) P Q) := by
  apply Array.ext
  · simp [compT, tabP_size]
  · intro i h1 h2
    have hi : i < n := by simpa [compT] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, tabP_get hi, PF.pg_pcomp hn hi, compT,
      getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, tabP_get hi, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (Nat.lt_trans (hQ i hi) hn), tabP_get (hQ i hi)]

theorem conjT_tabP {n w : Nat} {GP GIP : Nat → Nat} {l Y : Nat} (hn : n < 2 ^ 32)
    (hY : ∀ i < n, pg w (mask w) Y i < n) (hGi : ∀ i < n, pg w (mask w) (GIP l) i < n) :
    conjT n (tabP n w (GP l)) (tabP n w (GIP l)) (tabP n w Y) = tabP n w (cj n w GP GIP l Y) := by
  unfold conjT cj
  rw [compT_tabP hn hY, compT_tabP hn hGi]

theorem eq_of_key_tabP {n w X Y : Nat} (hX : canonK n w (mask w) (n * w) X = true)
    (hY : canonK n w (mask w) (n * w) Y = true) (h : key n (tabP n w X) = key n (tabP n w Y)) :
    X = Y := by
  obtain ⟨hn, hw, hX0, hXr⟩ := PF.canon_facts hX
  obtain ⟨-, -, hY0, hYr⟩ := PF.canon_facts hY
  unfold key at h
  rw [List.range_eq_range'] at h
  have hb : ∀ {Z : Nat}, (∀ i < n, pg w (mask w) Z i < n) → ∀ i < n,
      ap (tabP n w Z) i = pg w (mask w) Z i :=
    fun hZ i hi => ap_tabP hi (by have := hZ i hi; omega)
  have hd := CFSG.KS.SporSch.ClsSpec.foldr_digits_inj (ap (tabP n w X)) (ap (tabP n w Y)) n 0 n
    (fun i _ hi => by rw [hb hXr i (by omega), hb hYr i (by omega)]; exact ⟨hXr i (by omega),
      hYr i (by omega)⟩) h
  refine PF.eq_of_fields (PF.w_pos hw) hX0 hY0 fun i hi => ?_
  have := hd i (Nat.zero_le _) (by omega)
  rwa [hb hXr i hi, hb hYr i hi] at this

theorem lget_eq : ∀ (L : List Nat) (i : Nat), lget L i = L.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => lget_eq L i

theorem offR_facts {N : Nat} : ∀ (CS : List Nat) (s : Nat) (O : List Nat),
    List.rec (motive := fun _ => Nat → List Nat → Bool)
      (fun s O => bAnd(Nat.beq s N, List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) O))
      (fun c _ ih s O => List.rec (motive := fun _ => Bool) false
        (fun o O' _ => bAnd(Nat.beq o s, ih (Nat.add s c) O')) O) CS s O = true →
    (∀ i < CS.length, O.getD i 0 = s + (CS.take i).sum) ∧ s + CS.sum = N
  | [], s, O, h => by
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), by simpa using Nat.eq_of_beq_eq_true h1⟩
  | c :: CS, s, O, h => by
    cases O with
    | nil => exact absurd h Bool.false_ne_true
    | cons o O =>
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      obtain ⟨ih1, ih2⟩ := offR_facts CS (s + c) O h2
      refine ⟨fun i hi => ?_, by rw [List.sum_cons, ← ih2]; omega⟩
      rcases i with _ | i
      · simpa using Nat.eq_of_beq_eq_true h1
      · rw [List.getD_cons_succ, ih1 i (by simpa using hi), List.take_succ_cons, List.sum_cons]
        omega

theorem offOK_facts {CS OFF : List Nat} {N : Nat} (h : offOK CS OFF N = true) :
    (∀ i < CS.length, lget OFF i = (CS.take i).sum) ∧ CS.sum = N := by
  obtain ⟨h1, h2⟩ := offR_facts CS 0 OFF h
  exact ⟨fun i hi => by rw [lget_eq, h1 i hi, Nat.zero_add], by simpa using h2⟩

theorem sum_take_succ' (CS : List Nat) {i : Nat} (hi : i < CS.length) :
    (CS.take (i + 1)).sum = (CS.take i).sum + CS.getD i 0 := by
  rw [List.sum_take_succ _ _ hi, List.getD_eq_getElem _ _ hi]

theorem sum_take_mono (CS : List Nat) {a b : Nat} (h : a ≤ b) :
    (CS.take a).sum ≤ (CS.take b).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  omega

theorem sum_take_le (CS : List Nat) (a : Nat) : (CS.take a).sum ≤ CS.sum := by
  conv_rhs => rw [← List.take_append_drop a CS]
  rw [List.sum_append]
  omega

theorem class_unique {CS : List Nat} {i i' j : Nat} (hi : i < CS.length) (hi' : i' < CS.length)
    (h1 : (CS.take i).sum ≤ j) (h2 : j < (CS.take i).sum + CS.getD i 0)
    (h1' : (CS.take i').sum ≤ j) (h2' : j < (CS.take i').sum + CS.getD i' 0) : i = i' := by
  rcases Nat.lt_trichotomy i i' with h | h | h
  · have := sum_take_mono CS (Nat.succ_le_of_lt h)
    rw [sum_take_succ' CS hi] at this
    omega
  · exact h
  · have := sum_take_mono CS (Nat.succ_le_of_lt h)
    rw [sum_take_succ' CS hi'] at this
    omega

theorem lexLtK_iff (a b c d : Nat) : lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold lexLtK LexLt
  by_cases h : a < c
  · have e : Nat.blt a c = true := Nat.blt_eq.mpr h
    rw [e]
    exact iff_of_true rfl (Or.inl h)
  · have e : Nat.blt a c = false := by
      cases e' : Nat.blt a c
      · rfl
      · exact absurd (Nat.blt_eq.mp e') h
    rw [e]
    change bAnd(Nat.beq a c, Nat.blt b d) = true ↔ _
    rw [bAnd_iff, Nat.beq_eq, Nat.blt_eq]
    exact ⟨Or.inr, fun h' => h'.resolve_left h⟩

theorem bIf_false (t e : Bool) : Bool.rec (motive := fun _ => Bool) e t false = e := rfl

theorem bIf_true (t e : Bool) : Bool.rec (motive := fun _ => Bool) e t true = t := rfl

structure RepFacts (n w : Nat) (GP GIP : Nat → Nat) (g : Nat) (CS OFF : List Nat)
    (CI E P L K S SI : Nat → Nat) (N cap j : Nat) : Prop where
  ci_lt : CI j < CS.length
  off_le : lget OFF (CI j) ≤ j
  loc_lt : j - lget OFF (CI j) < lget CS (CI j)
  size_le : lget CS (CI j) ≤ cap
  canon : canonK n w (mask w) (n * w) (E j) = true
  tree : j - lget OFF (CI j) ≠ 0 → P j < j - lget OFF (CI j) ∧ L j < g ∧
    cj n w GP GIP (L j) (E (lget OFF (CI j) + P j)) = E j
  order : j - lget OFF (CI j) ≠ 0 → j - lget OFF (CI j) + 1 < lget CS (CI j) →
    LexLt (P j) (L j) (P (j + 1)) (L (j + 1))
  close : ∀ l < g, K (g * j + l) < lget CS (CI j) ∧
    E (lget OFF (CI j) + K (g * j + l)) = cj n w GP GIP l (E j) ∧
    (K (g * j + l) = 0 ∨ ¬ LexLt (j - lget OFF (CI j)) l (P (lget OFF (CI j) + K (g * j + l)))
      (L (lget OFF (CI j) + K (g * j + l))))
  s_lt : S j < N
  si_lt : SI j < N
  s_si : S (SI j) = j
  sorted : j + 1 < N → E (S j) < E (S (j + 1))

theorem repK_facts {n w g N cap j : Nat} {GP GIP CI E P L K S SI : Nat → Nat} {CS OFF : List Nat}
    (h : repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) :
    RepFacts n w GP GIP g CS OFF CI E P L K S SI N cap j := by
  unfold repK at h
  have e1 : ∀ a b : Nat, Nat.add a b = a + b := fun _ _ => rfl
  have e2 : ∀ a b : Nat, Nat.mul a b = a * b := fun _ _ => rfl
  have e3 : ∀ a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  simp only [PF.strictB_eqP, bAnd_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, e1, e2, e3,
    Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hk0 : j - lget OFF (CI j) ≠ 0 → Nat.beq (j - lget OFF (CI j)) 0 = false := fun hk => by
    cases e : Nat.beq (j - lget OFF (CI j)) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk
  refine ⟨h1, h2, h3, h4, h5, fun hk => ?_, fun hk hk1 => ?_, fun l hl => ?_, h9, h10, h11,
    fun hj => ?_⟩
  · simp only [hk0 hk, bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h6
    exact h6
  · have e' : Nat.blt (j - lget OFF (CI j) + 1) (lget CS (CI j)) = true := Nat.blt_eq.mpr hk1
    simp only [hk0 hk, e'] at h7
    exact (lexLtK_iff _ _ _ _).1 h7
  · have := allN_spec h8 l hl
    simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at this
    obtain ⟨a, b, c⟩ := this
    refine ⟨a, b, ?_⟩
    cases e : Nat.beq (K (g * j + l)) 0
    · simp only [e] at c
      right
      intro hl'
      simp only [(lexLtK_iff _ _ _ _).2 hl'] at c
      exact Bool.false_ne_true c
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · have e' : Nat.blt (j + 1) N = true := Nat.blt_eq.mpr hj
    simp only [e', Nat.blt_eq] at h12
    exact h12

section Records

variable {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat} {CS OFF : List Nat}
  {gens gensInv : Array Table}

theorem E_inj (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) {a b : Nat}
    (ha : a < N) (hb : b < N) (e : E a = E b) : a = b := by
  have F := fun j (hj : j < N) => repK_facts (h j hj)
  have mono : ∀ x y, x < y → y < N → E (S x) < E (S y) := by
    intro x y hxy hy
    induction y with
    | zero => omega
    | succ y ih =>
      have := (F y (by omega)).sorted hy
      rcases Nat.lt_or_ge x y with h1 | h1
      · exact Nat.lt_trans (ih h1 (by omega)) this
      · have : x = y := by omega
        subst this
        exact this
  have ea := (F a ha).s_si
  have eb := (F b hb).s_si
  rcases Nat.lt_trichotomy (SI a) (SI b) with h1 | h1 | h1
  · have := mono _ _ h1 (F b hb).si_lt
    rw [ea, eb, e] at this
    omega
  · rw [← ea, ← eb, h1]
  · have := mono _ _ h1 (F a ha).si_lt
    rw [ea, eb, e] at this
    omega

theorem ci_eq (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) {i k : Nat}
    (hi : i < CS.length) (hk : k < lget CS i) : lget OFF i + k < N ∧ CI (lget OFF i + k) = i := by
  obtain ⟨ho, hs⟩ := offOK_facts hoff
  have hc : lget CS i = CS.getD i 0 := lget_eq CS i
  have hN : lget OFF i + k < N := by
    have := sum_take_le CS (i + 1)
    rw [sum_take_succ' CS hi] at this
    rw [ho i hi]
    omega
  refine ⟨hN, ?_⟩
  have F := repK_facts (h _ hN)
  have hi' := F.ci_lt
  have h1 := F.off_le
  have h2 := F.loc_lt
  rw [ho _ hi'] at h1 h2
  rw [lget_eq CS] at h2
  have hoi := ho i hi
  symm
  exact class_unique hi hi' (by omega) (by omega) h1 (by omega)

variable (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true)
    (hpos : ∀ c ∈ CS, 0 < c)
include hg hgc hoff h hpos

theorem replay_class {i : Nat} (hi : i < CS.length) :
    KReplay n (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size
      (tabP n w (E (lget OFF i))) (lget CS i) (fun k => tabP n w (E (lget OFF i + k)))
      (fun k => if k = 0 then 0 else P (lget OFF i + k))
      (fun k => if k = 0 then 0 else L (lget OFF i + k))
      (fun h l => K (g * (lget OFF i + h) + l)) := by
  have hc0 : 0 < lget CS i := by
    rw [lget_eq, List.getD_eq_getElem _ _ hi]
    exact hpos _ (List.getElem_mem hi)
  have CI' := fun k (hk : k < lget CS i) => ci_eq hoff h hi hk
  have F := fun k (hk : k < lget CS i) => repK_facts (h _ (CI' k hk).1)
  have loc : ∀ k < lget CS i, lget OFF i + k - lget OFF (CI (lget OFF i + k)) = k := by
    intro k hk
    rw [(CI' k hk).2]
    omega
  have hcan : ∀ k < lget CS i, canonK n w (mask w) (n * w) (E (lget OFF i + k)) = true :=
    fun k hk => (F k hk).canon
  obtain ⟨hn, -, -, -⟩ := PF.canon_facts (hcan 0 hc0)
  have hn32 : n < 2 ^ 32 := by omega
  have hst : ∀ l < g, ∀ {Y : Nat}, canonK n w (mask w) (n * w) Y = true →
      conjT n gens[l]! gensInv[l]! (tabP n w Y) = tabP n w (cj n w GP GIP l Y) := by
    intro l hl Y hY
    rw [(hg.2.2 l hl).1, (hg.2.2 l hl).2]
    exact conjT_tabP hn32 (PF.canon_facts hY).2.2.2 (PF.canon_facts (hgc l hl).2).2.2.2
  refine ⟨hc0, by simp, by simp, by simp, fun a ha b hb e => ?_, fun k hk0 hk => ?_,
    fun k hk0 hk => ?_, fun hh hhc l hl => ?_⟩
  · have := eq_of_key_tabP (hcan a ha) (hcan b hb) e
    have := E_inj h (CI' a ha).1 (CI' b hb).1 this
    omega
  · have hk0' : k ≠ 0 := by omega
    obtain ⟨a, b, c⟩ := (F k hk).tree (by rw [loc k hk]; exact hk0')
    rw [loc k hk] at a
    rw [(CI' k hk).2] at c
    simp only [hk0', ↓reduceIte]
    refine ⟨a, hg.1 ▸ b, ?_⟩
    rw [hst _ b (hcan _ (by omega)), c]
  · have hk0' : k ≠ 0 := by omega
    have := (F k (by omega)).order (by rw [loc k (by omega)]; exact hk0')
      (by rw [loc k (by omega), (CI' k (by omega)).2]; exact hk)
    simp only [hk0', Nat.add_one_ne_zero, ↓reduceIte]
    rwa [Nat.add_assoc] at this
  · rw [hg.1] at hl
    have C := (F hh hhc).close l hl
    rw [loc hh hhc, (CI' hh hhc).2] at C
    obtain ⟨a, b, c⟩ := C
    refine ⟨a, ?_, ?_⟩
    · rw [hst l hl (hcan hh hhc), b]
    · by_cases hq : K (g * (lget OFF i + hh) + l) = 0
      · exact Or.inl hq
      · right
        simp only [hq, ↓reduceIte]
        exact c.resolve_left hq

theorem closure_rep {i : Nat} (hi : i < CS.length) :
    conjClosure n gens gensInv (arrTable n (unpack n w (E (lget OFF i)))) cap =
      (Array.ofFn (n := lget CS i) fun k => arrTable n (unpack n w (E (lget OFF i + k.val))),
        Array.ofFn (n := lget CS i) fun k => if k.val = 0 then 0 else P (lget OFF i + k.val),
        Array.ofFn (n := lget CS i) fun k => if k.val = 0 then 0 else L (lget OFF i + k.val)) := by
  have R := replay_class hg hgc hoff h hpos hi
  have hcap : lget CS i ≤ cap := by
    have F := repK_facts (h _ (ci_eq hoff h hi R.pos_cnt).1)
    have := F.size_le
    rwa [(ci_eq hoff h hi R.pos_cnt).2] at this
  rw [conjClosure_eq]
  exact keyBfs_replay R hcap

end Records

theorem ofFn_get' {β : Type} [Inhabited β] {cnt i : Nat} (f : Nat → β) (hi : i < cnt) :
    (Array.ofFn (n := cnt) fun j => f j.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem conjTreeOK_of {n cnt : Nat} {gens gensInv : Array Table} {x : Table} {U : Nat → Table}
    {par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (R : KReplay n (fun j y => conjT n gens[j]! gensInv[j]! y) gens.size x cnt U par lab pos) :
    conjTreeOK n gens gensInv x (Array.ofFn (n := cnt) fun i => U i.val)
      (Array.ofFn (n := cnt) fun i => par i.val) (Array.ofFn (n := cnt) fun i => lab i.val) =
        true := by
  unfold conjTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.size_ofFn]
  refine ⟨⟨R.pos_cnt, ?_⟩, CFSG.Sporadic.Th.allIn_eq_true.2 fun i h1 h2 => ?_⟩
  · rw [ofFn_get' _ R.pos_cnt, R.root_eq]
    exact CFSG.KS.SporSch.ClsSpec.tblEq_self _
  · obtain ⟨a1, a2, a3⟩ := R.tree i (by omega) h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [ofFn_get' _ h2, ofFn_get' _ h2, ofFn_get' _ h2, ofFn_get' _ (by omega), ← a3]
    exact ⟨⟨a1, a2⟩, CFSG.KS.SporSch.ClsSpec.tblEq_self _⟩

theorem map_range_lget (CS : List Nat) : (List.range CS.length).map (fun i => lget CS i) = CS := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [lget_eq, List.getD_eq_getElem _ _ h2]

section Assembly

variable {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat} {CS OFF : List Nat}
  {gens gensInv : Array Table}
  (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true)
    (hpos : ∀ c ∈ CS, 0 < c)
include hg hgc hoff h hpos

theorem repSizes_of_rec {reps : List Table}
    (hreps : reps = (List.range CS.length).map fun i => arrTable n (unpack n w (E (lget OFF i)))) :
    repSizes n gens gensInv reps cap = CS := by
  unfold repSizes
  rw [hreps, List.map_map]
  conv_rhs => rw [← map_range_lget CS]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply]
  rw [closure_rep hg hgc hoff h hpos (List.mem_range.1 hi), Array.size_ofFn]

theorem repsOK_of_rec {X reps : List Table}
    (hreps : reps = (List.range CS.length).map fun i => arrTable n (unpack n w (E (lget OFF i))))
    (hx : X.length = N) :
    repsOK n gens gensInv X reps cap = true := by
  have hCl := fun i (hi : i < CS.length) => closure_rep hg hgc hoff h hpos (cap := cap) hi
  have hR := fun i (hi : i < CS.length) => replay_class hg hgc hoff h hpos hi
  have hlist : reps.map (fun r => (r, conjClosure n gens gensInv r cap)) =
      (List.range CS.length).map (fun i => (arrTable n (unpack n w (E (lget OFF i))),
        (Array.ofFn (n := lget CS i) fun k => arrTable n (unpack n w (E (lget OFF i + k.val))),
        Array.ofFn (n := lget CS i) fun k => if k.val = 0 then 0 else P (lget OFF i + k.val),
        Array.ofFn (n := lget CS i) fun k => if k.val = 0 then 0 else L (lget OFF i + k.val)))) := by
    rw [hreps, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    rw [hCl i (List.mem_range.1 hi)]
  unfold repsOK
  simp only [hlist]
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨fun c hc => ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have := conjTreeOK_of (hR i (List.mem_range.1 hi))
    exact this
  · apply CFSG.KS.SporSch.ClsSpec.keysDistinct_of
    rw [List.flatMap_map, List.map_flatMap, List.nodup_flatMap]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi' := List.mem_range.1 hi
      dsimp only [Function.comp_apply]
      rw [Array.toList_ofFn, List.map_ofFn, List.nodup_ofFn]
      intro a b e
      exact Fin.ext ((hR i hi').inj a a.2 b b.2 e)
    · refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
      have ha' := List.mem_range.1 ha
      have hb' := List.mem_range.1 hb
      rw [Function.onFun, List.disjoint_left]
      dsimp only [Function.comp_apply]
      rw [Array.toList_ofFn, Array.toList_ofFn, List.map_ofFn, List.map_ofFn]
      intro kk h1 h2
      rw [List.mem_ofFn] at h1 h2
      obtain ⟨x, rfl⟩ := h1
      obtain ⟨y, e⟩ := h2
      have ca := ci_eq hoff h ha' x.2
      have cb := ci_eq hoff h hb' y.2
      have hcx := (repK_facts (h _ ca.1)).canon
      have hcy := (repK_facts (h _ cb.1)).canon
      dsimp only [Function.comp_apply] at e
      have hxy := E_inj h cb.1 ca.1 (eq_of_key_tabP hcy hcx e)
      have hca := ca.2
      have hcb := cb.2
      rw [hxy, hca] at hcb
      omega
  · rw [hx, List.map_map]
    have e : List.map ((fun c : Table × Array Table × Array Nat × Array Nat => c.2.1.size) ∘
        fun i => (arrTable n (unpack n w (E (lget OFF i))),
          (Array.ofFn (n := lget CS i) fun k => arrTable n (unpack n w (E (lget OFF i + k.val))),
          Array.ofFn (n := lget CS i) fun k => if k.val = 0 then 0 else P (lget OFF i + k.val),
          Array.ofFn (n := lget CS i) fun k => if k.val = 0 then 0 else L (lget OFF i + k.val))))
        (List.range CS.length) = (List.range CS.length).map (fun i => lget CS i) := by
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, Array.size_ofFn]
    rw [e, map_range_lget]
    exact (offOK_facts hoff).2

end Assembly

end CFSG.KC.Child3

end
