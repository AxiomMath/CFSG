module

public import Certificates.Data.Kernel.J2Cover
public import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Child3Inv
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KC.J2Cover.Snd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

@[expose] noncomputable def lvTab (n w : Nat) (LR TR : Nat → Nat) (i : Nat) : List Table :=
  (List.range (rcnt (LR i))).map fun k => tabP n w (TR (roff n (n * w) (LR i) + k))

private theorem lvTab_def (n w : Nat) (LR TR : Nat → Nat) (i : Nat) :
    lvTab n w LR TR i = (List.range (rcnt (LR i))).map fun k =>
      tabP n w (TR (roff n (n * w) (LR i) + k)) := rfl

theorem chainTables_eq_lvTab {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    chainTables n S base = (List.range nb).map (lvTab n w LR TR) ∧
      ∀ i < nb, ∀ k < rcnt (LR i), ∀ x < n,
        pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hlev : ∀ i < nb, (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), (∀ x < n, pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n) ∧
        arrTable n (rawLevels n S base)[i]!.tr[k]! = tabP n w (TR (roff n (n * w) (LR i) + k)) := by
    intro i hi
    obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    refine ⟨A.cnt.symm, fun k hk => ⟨fun x hx => ?_, ?_⟩⟩
    · rw [(P k hk).1 ⟨x, hx⟩]
      exact Fin.is_lt _
    · apply Array.ext (by simp [arrTable])
      intro x h1 h2
      have hx : x < n := by simpa [arrTable] using h1
      have R1 : ((rawLevels n S base)[i]!.tr[k]!)[x]! =
          pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x := by
        have R := (A.tr k (by rw [← A.cnt]; exact hk)).1 ⟨x, hx⟩
        rw [(P k hk).1 ⟨x, hx⟩]
        exact R
      rw [← getElem!_pos _ x h1, ← getElem!_pos _ x h2, tabP_get hx, arrTable,
        getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, R1]
  have hsz : (rawLevels n S base).size = nb := by simp [rawLevels, hb.2.2.2.2.2.1]
  refine ⟨?_, fun i hi k hk => ((hlev i hi).2 k hk).1⟩
  unfold chainTables
  dsimp only
  rw [hsz]
  apply List.map_congr_left
  intro i hi
  obtain ⟨c, T⟩ := hlev i (List.mem_range.1 hi)
  rw [c, lvTab_def]
  exact List.map_congr_left fun k hk => (T k (List.mem_range.1 hk)).2

private theorem canonK_pidn {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    canonK n w (mask w) (n * w) (pidn n w) = true :=
  canonK_of hn hw (PF.pidn_shr hn hw) fun i hi => by rw [PF.pg_pidn hn hw hi]; exact hi

private theorem canonK_pcomp_of {n w G Q : Nat} (hG : canonK n w (mask w) (n * w) G = true)
    (hQ : ∀ i < n, pg w (mask w) Q i < n) :
    canonK n w (mask w) (n * w) (pcomp n w (mask w) G Q) = true := by
  obtain ⟨hn, hw, -, hG4⟩ := PF.canon_facts hG
  have hn32 : n < 2 ^ 32 := by omega
  refine canonK_of hn hw (PF.pcomp_shr G Q hn32 (PF.w_pos hw)) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi]
  exact hG4 _ (hQ i hi)

private theorem idT_eq_tabP {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    idT n = tabP n w (pidn n w) := by
  apply Array.ext
  · simp [idT, tabP_size]
  · intro i h1 h2
    have hi : i < n := by simpa [idT] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, tabP_get hi, PF.pg_pidn hn hw hi, idT,
      getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem drop_levels {nb i : Nat} (T : Nat → List Table) (hi : i < nb) :
    ((List.range nb).map T).drop i = T i :: ((List.range nb).map T).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

private theorem drop_levels_end {nb i : Nat} (T : Nat → List Table) (hi : nb ≤ i) :
    ((List.range nb).map T).drop i = [] :=
  List.drop_eq_nil_of_le (by rw [List.length_map, List.length_range]; exact hi)

private theorem foldl_add_map {α : Type} (F : α → Nat) :
    ∀ (T : List α) (acc : Nat), T.foldl (fun c t => c + F t) acc = acc + (T.map F).sum
  | [], acc => by simp
  | t :: T, acc => by
    rw [List.foldl_cons, foldl_add_map F T, List.map_cons, List.sum_cons]
    omega

private theorem filterProducts_length (n : Nat) (f : Table → Bool) :
    ∀ (Ts : List (List Table)) (g : Table) (acc : List Table),
      (filterProducts n f Ts g acc).length = acc.length + countProducts n f Ts g
  | [], g, acc => by
    rw [filterProducts, countProducts]
    split <;> simp
  | T :: Ts, g, acc => by
    have e1 : filterProducts n f (T :: Ts) g acc =
        T.foldl (fun acc t => filterProducts n f Ts (compT n g t) acc) acc := by
      rw [filterProducts]
    have e2 : countProducts n f (T :: Ts) g =
        T.foldl (fun c t => c + countProducts n f Ts (compT n g t)) 0 := by
      rw [countProducts]
    rw [e1, e2, foldl_add_map (fun t => countProducts n f Ts (compT n g t)) T 0,
      foldl_length (fun acc t => filterProducts n f Ts (compT n g t) acc)
        (fun t => countProducts n f Ts (compT n g t))
        (fun acc t => filterProducts_length n f Ts (compT n g t) acc) T acc, Nat.zero_add]

private theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

private theorem foldList_succ (c : Nat) (step : Nat → List Nat → List Nat) (acc : List Nat) :
    foldList (c + 1) step acc = step c (foldList c step acc) := rfl

private theorem prodCntFrom_zero (n w : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) (i g : Nat) :
    prodCntFrom n w 0 LR TR f i g = if f g = true then 1 else 0 := by
  have e : prodCntFrom n w 0 LR TR f i g = Bool.rec (motive := fun _ => Nat) 0 1 (f g) := rfl
  rw [e]
  cases f g <;> rfl

private theorem prodCntFrom_succ (n w m : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) (i g : Nat) :
    prodCntFrom n w (m + 1) LR TR f i g = sumF (rcnt (LR i)) (fun a =>
      prodCntFrom n w m LR TR f (i + 1)
        (pcomp n w (mask w) g (TR (roff n (n * w) (LR i) + a)))) := by
  have e : prodCntFrom n w (m + 1) LR TR f i g =
      CFSG.KC.Enum.strictN (LR i) (fun R => sumF (rcnt R) (fun a =>
        CFSG.KC.Enum.strictN (pcomp n w (mask w) g (TR (roff n (n * w) R + a)))
          (fun h => prodCntFrom n w m LR TR f (i + 1) h))) := rfl
  rw [e]
  simp only [PF.strictN_eqP]

private theorem prodListFrom_zero (n w : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) (i g : Nat)
    (acc : List Nat) :
    prodListFrom n w 0 LR TR f i g acc =
      Bool.rec (motive := fun _ => List Nat) acc (g :: acc) (f g) := rfl

private theorem prodListFrom_succ (n w m : Nat) (LR TR : Nat → Nat) (f : Nat → Bool)
    (i g : Nat) (acc : List Nat) :
    prodListFrom n w (m + 1) LR TR f i g acc = foldList (rcnt (LR i)) (fun a acc' =>
      prodListFrom n w m LR TR f (i + 1)
        (pcomp n w (mask w) g (TR (roff n (n * w) (LR i) + a))) acc') acc := by
  have e : prodListFrom n w (m + 1) LR TR f i g acc =
      strictL (LR i) (fun R => foldList (rcnt R) (fun a acc' =>
        strictL (pcomp n w (mask w) g (TR (roff n (n * w) R + a)))
          (fun h => prodListFrom n w m LR TR f (i + 1) h acc')) acc) := rfl
  rw [e, strictL_eq]
  simp only [strictL_eq]

private theorem foldList_sim {β : Type} (Φ : List Nat → β) (Inv : List Nat → Prop)
    (F : β → Nat → β) (step : Nat → List Nat → List Nat) :
    ∀ (c : Nat), (∀ a < c, ∀ acc, Inv acc → Inv (step a acc) ∧ Φ (step a acc) = F (Φ acc) a) →
      ∀ acc, Inv acc →
        Inv (foldList c step acc) ∧ (List.range c).foldl F (Φ acc) = Φ (foldList c step acc)
  | 0, _, acc, hacc => ⟨hacc, rfl⟩
  | c + 1, h, acc, hacc => by
    obtain ⟨ih1, ih2⟩ := foldList_sim Φ Inv F step c
      (fun a ha => h a (Nat.lt_succ_of_lt ha)) acc hacc
    obtain ⟨h1, h2⟩ := h c (Nat.lt_succ_self c) _ ih1
    rw [foldList_succ, List.range_succ, List.foldl_append, ih2, List.foldl_cons, List.foldl_nil]
    exact ⟨h1, h2.symm⟩

private theorem countProducts_levels {n w nb : Nat} {LR TR : Nat → Nat} {f : Table → Bool}
    {fk : Nat → Bool} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hT : ∀ i < nb, ∀ k < rcnt (LR i), ∀ x < n,
      pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (tabP n w X) = fk X) :
    ∀ (m i G : Nat), i + m = nb → canonK n w (mask w) (n * w) G = true →
      countProducts n f (((List.range nb).map (lvTab n w LR TR)).drop i) (tabP n w G) =
        prodCntFrom n w m LR TR fk i G
  | 0, i, G, him, hG => by
    rw [drop_levels_end _ (by omega), countProducts, prodCntFrom_zero, hf G hG]
  | m + 1, i, G, him, hG => by
    have hn32 : n < 2 ^ 32 := by omega
    have hi : i < nb := by omega
    rw [drop_levels _ hi, countProducts, foldl_add_map, Nat.zero_add, lvTab_def, List.map_map,
      prodCntFrom_succ, sumF_eq]
    congr 1
    apply List.map_congr_left
    intro a ha
    have ha' := List.mem_range.1 ha
    have hQ := hT i hi a ha'
    simp only [Function.comp_apply]
    rw [compT_tabP hn32 hQ]
    exact countProducts_levels hn hw hT hf m (i + 1)
      (pcomp n w (mask w) G (TR (roff n (n * w) (LR i) + a))) (by omega)
      (canonK_pcomp_of hG hQ)

private theorem prodList_levels {n w nb : Nat} {LR TR : Nat → Nat} {f : Table → Bool}
    {fk : Nat → Bool} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hT : ∀ i < nb, ∀ k < rcnt (LR i), ∀ x < n,
      pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (tabP n w X) = fk X) :
    ∀ (m i G : Nat) (acc : List Nat), i + m = nb → canonK n w (mask w) (n * w) G = true →
      (∀ X ∈ acc, canonK n w (mask w) (n * w) X = true) →
      filterProducts n f (((List.range nb).map (lvTab n w LR TR)).drop i) (tabP n w G)
          (acc.map (tabP n w)) = (prodListFrom n w m LR TR fk i G acc).map (tabP n w) ∧
        ∀ X ∈ prodListFrom n w m LR TR fk i G acc, canonK n w (mask w) (n * w) X = true
  | 0, i, G, acc, him, hG, hacc => by
    rw [drop_levels_end _ (by omega), filterProducts, prodListFrom_zero, hf G hG]
    cases h : fk G
    · exact ⟨rfl, hacc⟩
    · refine ⟨rfl, fun X hX => ?_⟩
      have hX' : X ∈ G :: acc := hX
      rcases List.mem_cons.1 hX' with hXG | hX''
      · rw [hXG]
        exact hG
      · exact hacc X hX''
  | m + 1, i, G, acc, him, hG, hacc => by
    have hn32 : n < 2 ^ 32 := by omega
    have hi : i < nb := by omega
    have hstep : ∀ a < rcnt (LR i), ∀ acc' : List Nat,
        (∀ X ∈ acc', canonK n w (mask w) (n * w) X = true) →
        (∀ X ∈ prodListFrom n w m LR TR fk (i + 1)
            (pcomp n w (mask w) G (TR (roff n (n * w) (LR i) + a))) acc',
          canonK n w (mask w) (n * w) X = true) ∧
        (prodListFrom n w m LR TR fk (i + 1)
            (pcomp n w (mask w) G (TR (roff n (n * w) (LR i) + a))) acc').map (tabP n w) =
          filterProducts n f (((List.range nb).map (lvTab n w LR TR)).drop (i + 1))
            (compT n (tabP n w G) (tabP n w (TR (roff n (n * w) (LR i) + a))))
            (acc'.map (tabP n w)) := by
      intro a ha acc' hacc'
      have hQ := hT i hi a ha
      obtain ⟨r1, r2⟩ := prodList_levels hn hw hT hf m (i + 1)
        (pcomp n w (mask w) G (TR (roff n (n * w) (LR i) + a))) acc' (by omega)
        (canonK_pcomp_of hG hQ) hacc'
      refine ⟨r2, ?_⟩
      rw [compT_tabP hn32 hQ, r1]
    have key := foldList_sim (List.map (tabP n w))
      (fun L => ∀ X ∈ L, canonK n w (mask w) (n * w) X = true)
      (fun A k => filterProducts n f (((List.range nb).map (lvTab n w LR TR)).drop (i + 1))
        (compT n (tabP n w G) (tabP n w (TR (roff n (n * w) (LR i) + k)))) A)
      (fun a acc' => prodListFrom n w m LR TR fk (i + 1)
        (pcomp n w (mask w) G (TR (roff n (n * w) (LR i) + a))) acc')
      (rcnt (LR i)) hstep acc hacc
    rw [drop_levels _ hi, filterProducts, prodListFrom_succ, lvTab_def, List.foldl_map]
    exact ⟨key.2, key.1⟩

theorem countProducts_sound' {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {f : Table → Bool} {fk : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (arrTable n (unpack n w X)) = fk X) :
    countProducts n f (chainTables n S base) (idT n) = prodCnt n w nb LR TR fk := by
  have hn : n < 16777216 := by have := hb.2.2.1; omega
  have hw : n + 1 < 2 ^ w := hb.2.1
  obtain ⟨hct, hT⟩ := chainTables_eq_lvTab hb hp hl
  have h := countProducts_levels hn hw hT hf nb 0 (pidn n w) (Nat.zero_add nb)
    (canonK_pidn hn hw)
  rw [List.drop_zero] at h
  rw [hct, idT_eq_tabP hn hw]
  exact h

theorem prodCnt_sound' {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {f : Table → Bool} {fk : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (arrTable n (unpack n w X)) = fk X) :
    (filterProducts n f (chainTables n S base) (idT n) []).length = prodCnt n w nb LR TR fk := by
  rw [filterProducts_length, List.length_nil, Nat.zero_add]
  exact countProducts_sound' hb hp hl hf

theorem prodList_sound' {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {f : Table → Bool} {fk : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (arrTable n (unpack n w X)) = fk X) :
    filterProducts n f (chainTables n S base) (idT n) [] =
        (prodList n w nb LR TR fk).map (fun X => arrTable n (unpack n w X)) ∧
      ∀ X ∈ prodList n w nb LR TR fk, canonK n w (mask w) (n * w) X = true := by
  have hn : n < 16777216 := by have := hb.2.2.1; omega
  have hw : n + 1 < 2 ^ w := hb.2.1
  obtain ⟨hct, hT⟩ := chainTables_eq_lvTab hb hp hl
  have h := prodList_levels hn hw hT hf nb 0 (pidn n w) [] (Nat.zero_add nb)
    (canonK_pidn hn hw) (fun X hX => nomatch hX)
  rw [List.drop_zero] at h
  rw [hct, idT_eq_tabP hn hw]
  exact h

end CFSG.KC.J2Cover.Snd

end
