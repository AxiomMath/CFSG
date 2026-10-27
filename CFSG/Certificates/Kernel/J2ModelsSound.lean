module

public import CFSG.Certificates.Kernel.J2ModelsGen
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Child3Inv
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.J2Models

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] def colsStep (F G : Nat → Nat) : Array Nat × Array Nat :=
  (List.range' 0 4725).foldl (fun t i => (t.1.set! i (F i), t.2.set! i (G i)))
    (Array.replicate 4725 0, Array.replicate 4725 0)

@[expose] def colsOuter (yD : Nat → Nat → Nat × Nat) (mtA : Array (Array Nat)) (gn pr : Nat → Nat)
    (r : Array (Array Nat) × Array (Array Nat)) (a : Nat) :
    Array (Array Nat) × Array (Array Nat) :=
  let Yg := (Array.ofFn (n := 3) fun k => Array.ofFn (n := 4725) fun i => yD k.val i.val)[gn a]!
  let s := colsStep (fun i => (mtA[(Yg[i]!).1]!)[(r.1[pr a]!)[(Yg[i]!).2]!]!)
    (fun i => (r.2[pr a]!)[(Yg[i]!).2]!)
  (r.1.push s.1, r.2.push s.2)

@[expose] def colsFold (yD : Nat → Nat → Nat × Nat) (mtA : Array (Array Nat)) (gn pr : Nat → Nat)
    (k : Nat) : Array (Array Nat) × Array (Array Nat) :=
  (List.range' 1 k).foldl (colsOuter yD mtA gn pr)
    (#[Array.replicate 4725 0], #[Array.ofFn (n := 4725) fun i => i.val])

theorem decompColsG_eq_fold (yD : Nat → Nat → Nat × Nat) (mtA : Array (Array Nat))
    (gn pr : Nat → Nat) :
    decompColsG yD mtA gn pr = ((colsFold yD mtA gn pr 127).1, (colsFold yD mtA gn pr 127).2) := by
  unfold decompColsG colsFold colsOuter colsStep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, bind_pure_comp, map_pure, pure_bind, bind_pure]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem colsFold_zero (yD : Nat → Nat → Nat × Nat) (mtA : Array (Array Nat)) (gn pr : Nat → Nat) :
    colsFold yD mtA gn pr 0 =
      (#[Array.replicate 4725 0], #[Array.ofFn (n := 4725) fun i => i.val]) := rfl

theorem single0J {α : Type} [Inhabited α] (x : α) : (#[x] : Array α)[0]! = x := rfl

theorem getElem!_push_ltJ {a : Array (Array Nat)} {x : Array Nat} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp only [Array.size_push]; omega), getElem!_pos a i h,
    Array.getElem_push_lt h]

theorem getElem!_push_eqJ (a : Array (Array Nat)) (x : Array Nat) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp only [Array.size_push]; omega), Array.getElem_push_eq]

theorem getElem!_ofFnJ {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat} (h : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]

theorem arr_eq_ofJ {α : Type} [Inhabited α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ i < a.size, a[i]! = b[i]!) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have e := h i h1
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at e

theorem colsStep_eq (F G : Nat → Nat) :
    colsStep F G = ⟨Array.ofFn (n := 4725) fun i => F i.val, Array.ofFn (n := 4725) fun i => G i.val⟩ := by
  have key : ∀ k ≤ 4725,
      ((List.range' 0 k).foldl (fun (t : Array Nat × Array Nat) i =>
          (⟨t.1.set! i (F i), t.2.set! i (G i)⟩ : Array Nat × Array Nat))
        ⟨Array.replicate 4725 0, Array.replicate 4725 0⟩).1.size = 4725 ∧
      ((List.range' 0 k).foldl (fun (t : Array Nat × Array Nat) i =>
          (⟨t.1.set! i (F i), t.2.set! i (G i)⟩ : Array Nat × Array Nat))
        ⟨Array.replicate 4725 0, Array.replicate 4725 0⟩).2.size = 4725 ∧
      ∀ i < k,
        ((List.range' 0 k).foldl (fun (t : Array Nat × Array Nat) i =>
          (⟨t.1.set! i (F i), t.2.set! i (G i)⟩ : Array Nat × Array Nat))
        ⟨Array.replicate 4725 0, Array.replicate 4725 0⟩).1[i]! = F i ∧
        ((List.range' 0 k).foldl (fun (t : Array Nat × Array Nat) i =>
          (⟨t.1.set! i (F i), t.2.set! i (G i)⟩ : Array Nat × Array Nat))
        ⟨Array.replicate 4725 0, Array.replicate 4725 0⟩).2[i]! = G i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add, Nat.one_mul]
      refine ⟨by rw [Array.size_set!, h1], by rw [Array.size_set!, h2], fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega), Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact h3 i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [h1]; omega),
          Array.getElem!_set!_self _ _ _ (by rw [h2]; omega)]
        exact ⟨rfl, rfl⟩
  have h1 : (colsStep F G).1.size = 4725 := (key 4725 le_rfl).1
  have h2 : (colsStep F G).2.size = 4725 := (key 4725 le_rfl).2.1
  have h3 : ∀ i < 4725, (colsStep F G).1[i]! = F i ∧ (colsStep F G).2[i]! = G i :=
    (key 4725 le_rfl).2.2
  refine Prod.ext ?_ ?_
  · refine arr_eq_ofJ (by rw [h1, Array.size_ofFn]) fun i hi => ?_
    rw [h1] at hi
    rw [(h3 i hi).1, getElem!_ofFnJ _ hi]
  · refine arr_eq_ofJ (by rw [h2, Array.size_ofFn]) fun i hi => ?_
    rw [h2] at hi
    rw [(h3 i hi).2, getElem!_ofFnJ _ hi]

theorem decompColsG_sound {yD : Nat → Nat → Nat × Nat} {mtA : Array (Array Nat)} {gn pr : Nat → Nat}
    {P I : Nat → Nat → Nat}
    (h0 : ∀ i < 4725, P 0 i = 0 ∧ I 0 i = i)
    (hpr : ∀ a < 128, 1 ≤ a → pr a < a)
    (hy : ∀ a < 128, 1 ≤ a → ∀ i < 4725, (yD (gn a) i).2 < 4725)
    (hP : ∀ a < 128, 1 ≤ a → ∀ i < 4725,
      P a i = (mtA[(yD (gn a) i).1]!)[P (pr a) (yD (gn a) i).2]! ∧
        I a i = I (pr a) (yD (gn a) i).2)
    (hgn : ∀ a < 128, gn a < 3) :
    decompColsG yD mtA gn pr =
      (Array.ofFn (n := 128) fun a => Array.ofFn (n := 4725) fun i => P a.val i.val,
        Array.ofFn (n := 128) fun a => Array.ofFn (n := 4725) fun i => I a.val i.val) := by
  have key : ∀ k ≤ 127, (colsFold yD mtA gn pr k).1.size = k + 1 ∧
      (colsFold yD mtA gn pr k).2.size = k + 1 ∧ ∀ a < k + 1,
        (colsFold yD mtA gn pr k).1[a]! = (Array.ofFn (n := 4725) fun i => P a i.val) ∧
        (colsFold yD mtA gn pr k).2[a]! = (Array.ofFn (n := 4725) fun i => I a i.val) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [colsFold_zero]
      refine ⟨rfl, rfl, fun a ha => ?_⟩
      have a0 : a = 0 := by omega
      subst a0
      rw [single0J, single0J]
      refine ⟨arr_eq_ofJ (by rw [Array.size_replicate, Array.size_ofFn]) fun i hi => ?_,
        arr_eq_ofJ (by rw [Array.size_ofFn, Array.size_ofFn]) fun i hi => ?_⟩
      · rw [Array.size_replicate] at hi
        rw [getElem!_ofFnJ _ hi, (h0 i hi).1, getElem!_pos _ i (by rw [Array.size_replicate]; exact hi),
          Array.getElem_replicate]
      · rw [Array.size_ofFn] at hi
        rw [getElem!_ofFnJ _ hi, getElem!_ofFnJ _ hi, (h0 i hi).2]
    | succ k ih =>
      intro hk
      obtain ⟨s1, s2, hc⟩ := ih (by omega)
      have hcf : colsFold yD mtA gn pr (k + 1) =
          colsOuter yD mtA gn pr (colsFold yD mtA gn pr k) (1 + k) := by
        unfold colsFold
        rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul]
      have ha : 1 + k < 128 := by omega
      have h1 : 1 ≤ 1 + k := by omega
      have hq : pr (1 + k) < k + 1 := by have := hpr _ ha h1; omega
      obtain ⟨cq1, cq2⟩ := hc _ hq
      have hY : ∀ i < 4725,
          ((Array.ofFn (n := 3) fun k => Array.ofFn (n := 4725) fun i => yD k.val i.val)[
            gn (1 + k)]!)[i]! = yD (gn (1 + k)) i := by
        intro i hi
        rw [getElem!_ofFnJ _ (hgn _ ha), getElem!_ofFnJ _ hi]
      have col : colsOuter yD mtA gn pr (colsFold yD mtA gn pr k) (1 + k) =
          ⟨(colsFold yD mtA gn pr k).1.push (Array.ofFn (n := 4725) fun i => P (1 + k) i.val),
            (colsFold yD mtA gn pr k).2.push (Array.ofFn (n := 4725) fun i => I (1 + k) i.val)⟩ := by
        unfold colsOuter
        simp only []
        rw [colsStep_eq, cq1, cq2]
        refine Prod.ext (congrArg (colsFold yD mtA gn pr k).1.push ?_)
          (congrArg (colsFold yD mtA gn pr k).2.push ?_)
        · refine Array.ext (by simp) fun i h1' _ => ?_
          have hi : i < 4725 := by simpa using h1'
          simp only [Array.getElem_ofFn]
          rw [hY i hi, getElem!_ofFnJ _ (hy _ ha h1 i hi), (hP _ ha h1 i hi).1]
        · refine Array.ext (by simp) fun i h1' _ => ?_
          have hi : i < 4725 := by simpa using h1'
          simp only [Array.getElem_ofFn]
          rw [hY i hi, getElem!_ofFnJ _ (hy _ ha h1 i hi), (hP _ ha h1 i hi).2]
      rw [hcf, col]
      refine ⟨by rw [Array.size_push, s1], by rw [Array.size_push, s2], fun a ha' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha' with hlt | rfl
      · rw [getElem!_push_ltJ (by rw [s1]; exact hlt), getElem!_push_ltJ (by rw [s2]; exact hlt)]
        exact hc a hlt
      · have e1 := getElem!_push_eqJ (colsFold yD mtA gn pr k).1
          (Array.ofFn (n := 4725) fun i => P (1 + k) i.val)
        have e2 := getElem!_push_eqJ (colsFold yD mtA gn pr k).2
          (Array.ofFn (n := 4725) fun i => I (1 + k) i.val)
        rw [s1] at e1
        rw [s2] at e2
        rw [e1, e2, Nat.add_comm k 1]
        exact ⟨rfl, rfl⟩
  obtain ⟨s1, s2, hc⟩ := key 127 le_rfl
  rw [decompColsG_eq_fold]
  refine Prod.ext ?_ ?_
  · refine arr_eq_ofJ (by rw [s1, Array.size_ofFn]) fun a ha => ?_
    rw [s1] at ha
    rw [(hc a ha).1, getElem!_ofFnJ _ ha]
  · refine arr_eq_ofJ (by rw [s2, Array.size_ofFn]) fun a ha => ?_
    rw [s2] at ha
    rw [(hc a ha).2, getElem!_ofFnJ _ ha]

theorem pcompK_assoc {n w p q r : Nat} (_ : canonK n w (mask w) (n * w) p = true)
    (_ : canonK n w (mask w) (n * w) q = true) (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, hr4⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw))
    (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) fun i hi => ?_
  simp only [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hr4 i hi)]

theorem pcomp_idR {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p := by
  obtain ⟨hn, hw, hp0, -⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]

theorem pcomp_idL {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) (pidn n w) p = p := by
  obtain ⟨hn, hw, hp0, hp4⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hp4 i hi)]

theorem decomp_sound {n w : Nat} {RP EL LP YT : Nat → Nat} {P I mt wit act : Nat → Nat → Nat}
    {yw : List (List Nat)} {gn' pr' : Nat → Nat}
    (hcan : ∀ i < 4725, canonK n w (mask w) (n * w) (RP i) = true)
    (hcanE : ∀ a < 128, canonK n w (mask w) (n * w) (EL a) = true)
    (hcanL : ∀ j < 2, canonK n w (mask w) (n * w) (LP j) = true)
    (hE0 : EL 0 = pidn n w)
    (hT : ∀ a < 128, 1 ≤ a → pr' a < a ∧ gn' a < 3 ∧
      EL a = pcomp n w (mask w) (YT (gn' a)) (EL (pr' a)))
    (hY : ∀ k < 3, (∀ x ∈ yw.getD k [], x < 2) ∧
      YT k = (yw.getD k []).foldr (fun x acc => pcomp n w (mask w) (LP x) acc) (pidn n w))
    (hM : ∀ a < 128, ∀ b < 128, mt a b < 128 ∧
      EL (mt a b) = pcomp n w (mask w) (EL a) (EL b))
    (hC : ∀ i < 4725, ∀ j < 2, act j i < 4725 ∧ wit j i < 128 ∧
      pcomp n w (mask w) (RP i) (LP j) = pcomp n w (mask w) (EL (wit j i)) (RP (act j i)))
    {yD : Nat → Nat → Nat × Nat}
    (hyD : ∀ k < 3, ∀ i < 4725, yD k i =
      (yw.getD k []).foldl (fun pc x => (mt pc.1 (wit x pc.2), act x pc.2)) (0, i))
    (h0 : ∀ i < 4725, P 0 i = 0 ∧ I 0 i = i)
    (hP : ∀ a < 128, 1 ≤ a → ∀ i < 4725,
      P a i = mt (yD (gn' a) i).1 (P (pr' a) (yD (gn' a) i).2) ∧
        I a i = I (pr' a) (yD (gn' a) i).2) :
    ∀ i < 4725, ∀ a < 128, P a i < 128 ∧ I a i < 4725 ∧
      pcomp n w (mask w) (RP i) (EL a) = pcomp n w (mask w) (EL (P a i)) (RP (I a i)) := by
  have hid : canonK n w (mask w) (n * w) (pidn n w) = true := hE0 ▸ hcanE 0 (by norm_num)
  have hF : ∀ l : List Nat, (∀ x ∈ l, x < 2) → canonK n w (mask w) (n * w)
      (l.foldr (fun x acc => pcomp n w (mask w) (LP x) acc) (pidn n w)) = true := by
    intro l
    induction l with
    | nil => intro _; exact hid
    | cons x l ih =>
      intro hl
      exact CFSG.KC.Child3.canon_pcomp (hcanL x (hl x (by simp)))
        (ih fun y hy => hl y (by simp [hy]))
  have hW : ∀ l : List Nat, (∀ x ∈ l, x < 2) → ∀ c < 128, ∀ e < 4725,
      (l.foldl (fun pc x => (mt pc.1 (wit x pc.2), act x pc.2)) (c, e)).1 < 128 ∧
      (l.foldl (fun pc x => (mt pc.1 (wit x pc.2), act x pc.2)) (c, e)).2 < 4725 ∧
      pcomp n w (mask w) (pcomp n w (mask w) (EL c) (RP e))
          (l.foldr (fun x acc => pcomp n w (mask w) (LP x) acc) (pidn n w)) =
        pcomp n w (mask w) (EL (l.foldl (fun pc x => (mt pc.1 (wit x pc.2), act x pc.2)) (c, e)).1)
          (RP (l.foldl (fun pc x => (mt pc.1 (wit x pc.2), act x pc.2)) (c, e)).2) := by
    intro l
    induction l with
    | nil =>
      intro _ c hc e he
      exact ⟨hc, he, pcomp_idR (CFSG.KC.Child3.canon_pcomp (hcanE c hc) (hcan e he))⟩
    | cons x l ih =>
      intro hl c hc e he
      have hx : x < 2 := hl x (by simp)
      have hl' : ∀ y ∈ l, y < 2 := fun y hy => hl y (by simp [hy])
      obtain ⟨ha, hw', hC'⟩ := hC e he x hx
      obtain ⟨hm, hM'⟩ := hM c hc (wit x e) hw'
      simp only [List.foldr_cons, List.foldl_cons]
      have hFl := hF l hl'
      rw [pcompK_assoc (hcanE c hc) (hcan e he) (CFSG.KC.Child3.canon_pcomp (hcanL x hx) hFl),
        ← pcompK_assoc (hcan e he) (hcanL x hx) hFl, hC',
        pcompK_assoc (hcanE (wit x e) hw') (hcan (act x e) ha) hFl,
        ← pcompK_assoc (hcanE c hc) (hcanE (wit x e) hw')
          (CFSG.KC.Child3.canon_pcomp (hcan (act x e) ha) hFl),
        ← hM', ← pcompK_assoc (hcanE (mt c (wit x e)) hm) (hcan (act x e) ha) hFl]
      exact ih hl' _ hm _ ha
  intro i hi a ha
  induction a using Nat.strong_induction_on generalizing i with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with h0a | h1
    · subst h0a
      obtain ⟨e1, e2⟩ := h0 i hi
      rw [e1, e2, hE0, pcomp_idR (hcan i hi), pcomp_idL (hcan i hi)]
      exact ⟨by norm_num, hi, rfl⟩
    · obtain ⟨hq, hg, hEa⟩ := hT a ha h1
      obtain ⟨hPa, hIa⟩ := hP a ha h1 i hi
      have hYT := hF _ (hY (gn' a) hg).1
      rw [← (hY (gn' a) hg).2] at hYT
      have hw0 : (yD (gn' a) i).1 < 128 ∧ (yD (gn' a) i).2 < 4725 ∧
          pcomp n w (mask w) (RP i) (YT (gn' a)) =
            pcomp n w (mask w) (EL (yD (gn' a) i).1) (RP (yD (gn' a) i).2) := by
        have h := hW _ (hY (gn' a) hg).1 0 (by norm_num) i hi
        rw [← (hY (gn' a) hg).2, ← hyD (gn' a) hg i hi, hE0, pcomp_idL (hcan i hi)] at h
        exact h
      obtain ⟨hy1, hy2, hyE⟩ := hw0
      obtain ⟨ip, ii, iE⟩ := ih (pr' a) hq _ hy2 (by omega)
      obtain ⟨hm, hM'⟩ := hM _ hy1 _ ip
      rw [hPa, hIa, hEa, ← pcompK_assoc (hcan i hi) hYT (hcanE (pr' a) (by omega)), hyE,
        pcompK_assoc (hcanE _ hy1) (hcan _ hy2) (hcanE (pr' a) (by omega)), iE,
        ← pcompK_assoc (hcanE _ hy1) (hcanE _ ip) (hcan _ ii), ← hM']
      exact ⟨hm, ii, rfl⟩

end CFSG.KC.J2Models

end
