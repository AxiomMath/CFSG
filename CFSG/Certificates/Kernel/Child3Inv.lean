module

public import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native

theorem canonK_of {n w X : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (h0 : X >>> (n * w) = 0) (hr : ∀ i < n, pg w (mask w) X i < n) :
    canonK n w (mask w) (n * w) X = true := by
  unfold canonK szOK
  rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
  refine ⟨⟨hn, ?_⟩, h0, PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (hr i hi)⟩
  change n + 1 < 1 <<< w
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact hw

theorem canon_pcomp {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    canonK n w (mask w) (n * w) (pcomp n w (mask w) p q) = true := by
  obtain ⟨hn, hw, -, hp4⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hq4⟩ := PF.canon_facts hq
  have hn32 : n < 2 ^ 32 := by omega
  refine canonK_of hn hw (PF.pcomp_shr p q hn32 (PF.w_pos hw)) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi]
  exact hp4 _ (hq4 i hi)

theorem apPowW_one (T : Table) (i : Nat) : apPowW [T] 1 i = ap T i := rfl

theorem apPowW_two (T : Table) (i : Nat) : apPowW [T] 2 i = ap T (ap T i) := rfl

theorem divParts_two : divParts 2 = [1] := by decide

theorem ordTest2_tabP {n w R : Nat} (hR : canonK n w (mask w) (n * w) R = true) :
    ordTest n 2 (tabP n w R) =
      (Nat.beq (pcomp n w (mask w) R R) (pidn n w) && !Nat.beq R (pidn n w)) := by
  obtain ⟨hn, hw, hR0, hRr⟩ := PF.canon_facts hR
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  have hap : ∀ i < n, ap (tabP n w R) i = pg w (mask w) R i :=
    fun i hi => ap_tabP hi (by have := hRr i hi; omega)
  have h2 : powFixW n [tabP n w R] 2 = Nat.beq (pcomp n w (mask w) R R) (pidn n w) := by
    rw [Bool.eq_iff_iff, powFixW, CFSG.Sporadic.Th.allIn_eq_true, Nat.beq_eq]
    constructor
    · intro H
      refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pidn_shr hn hw) fun i hi => ?_
      have := H i (Nat.zero_le _) hi
      rw [apPowW_two, hap i hi, hap _ (hRr i hi), beq_iff_eq] at this
      rw [PF.pg_pcomp hn32 hi, this, PF.pg_pidn hn hw hi]
    · intro H i _ hi
      rw [apPowW_two, hap i hi, hap _ (hRr i hi), beq_iff_eq, ← PF.pg_pcomp hn32 hi, H,
        PF.pg_pidn hn hw hi]
  have h1 : powFixW n [tabP n w R] 1 = Nat.beq R (pidn n w) := by
    rw [Bool.eq_iff_iff, powFixW, CFSG.Sporadic.Th.allIn_eq_true, Nat.beq_eq]
    constructor
    · intro H
      refine PF.eq_of_fields hw0 hR0 (PF.pidn_shr hn hw) fun i hi => ?_
      have := H i (Nat.zero_le _) hi
      rw [apPowW_one, hap i hi, beq_iff_eq] at this
      rw [this, PF.pg_pidn hn hw hi]
    · intro H i _ hi
      rw [apPowW_one, hap i hi, beq_iff_eq, H, PF.pg_pidn hn hw hi]
  unfold ordTest ordW
  rw [divParts_two, List.all_cons, List.all_nil, Bool.and_true, h2, h1]

theorem sumF_eq (f : Nat → Nat) : ∀ m, sumF m f = ((List.range m).map f).sum
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, ← sumF_eq f m]
    change strictN (sumF m f) (fun s' => Nat.add s' (f m)) = _
    rw [PF.strictN_eqP]
    simp

theorem foldl_length {α β : Type} (F : List α → β → List α) (c : β → Nat)
    (hF : ∀ acc t, (F acc t).length = acc.length + c t) :
    ∀ (T : List β) (acc : List α), (T.foldl F acc).length = acc.length + (T.map c).sum
  | [], acc => by simp
  | t :: T, acc => by
    rw [List.foldl_cons, foldl_length F c hF T, hF, List.map_cons, List.sum_cons]
    omega

theorem filterProducts_two_length (n : Nat) (f : Table → Bool) (T0 T1 : List Table) (g : Table) :
    (filterProducts n f [T0, T1] g []).length =
      (T0.map fun t0 => (T1.map fun t1 => if f (compT n (compT n g t0) t1) then 1 else 0).sum).sum := by
  have inner : ∀ (g' : Table) (acc : List Table), (filterProducts n f [T1] g' acc).length =
      acc.length + (T1.map fun t1 => if f (compT n g' t1) then 1 else 0).sum := by
    intro g' acc
    have e : filterProducts n f [T1] g' acc =
        T1.foldl (fun acc t => filterProducts n f [] (compT n g' t) acc) acc := by
      rw [filterProducts]
    rw [e]
    refine foldl_length _ _ (fun acc t => ?_) T1 acc
    rw [filterProducts]
    split <;> simp
  have e : filterProducts n f [T0, T1] g [] =
      T0.foldl (fun acc t => filterProducts n f [T1] (compT n g t) acc) [] := by
    rw [filterProducts]
  rw [e, foldl_length (fun acc t => filterProducts n f [T1] (compT n g t) acc)
    (fun t0 => (T1.map fun t1 => if f (compT n (compT n g t0) t1) then 1 else 0).sum)
    (fun acc t => inner _ acc) T0 [], List.length_nil, Nat.zero_add]

theorem compT_idT_tabP {n w X : Nat} (hn : n < 2 ^ 32) (hX : ∀ i < n, pg w (mask w) X i < n) :
    compT n (idT n) (tabP n w X) = tabP n w X := by
  apply Array.ext
  · simp [compT, tabP_size]
  · intro i h1 h2
    have hi : i < n := by simpa [compT] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, tabP_get hi, compT,
      getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, tabP_get hi, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (Nat.lt_trans (hX i hi) hn), idT,
      getElem!_pos _ _ (by simpa using hX i hi), Array.getElem_ofFn]

theorem nIf_inv (x y : Bool) :
    Bool.rec (motive := fun _ => Nat) 0 1 (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) true false y) x) = if (x && !y) = true then 1 else 0 := by
  cases x <;> cases y <;> rfl

theorem invList2_of {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS 2 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 2 BP) :
    (filterProducts n (ordTest n 2) (chainTables n S base) (idT n) []).length =
      invCount2 n w LR TR := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hn : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hw' : n + 1 < 2 ^ w := hb.2.1
  have hlev : ∀ i < 2, (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧
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
  obtain ⟨c0, T0⟩ := hlev 0 (by omega)
  obtain ⟨c1, T1⟩ := hlev 1 (by omega)
  have hsz : (rawLevels n S base).size = 2 := by simp [rawLevels, hb.2.2.2.2.2.1]
  have hct : chainTables n S base =
      [(List.range (rcnt (LR 0))).map fun a => tabP n w (TR (roff n (n * w) (LR 0) + a)),
        (List.range (rcnt (LR 1))).map fun b => tabP n w (TR (roff n (n * w) (LR 1) + b))] := by
    unfold chainTables
    dsimp only
    rw [hsz, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons, List.map_nil, c0,
      c1]
    have e0 := List.map_congr_left fun k hk => (T0 k (List.mem_range.1 hk)).2
    have e1 := List.map_congr_left fun k hk => (T1 k (List.mem_range.1 hk)).2
    rw [e0, e1]
  rw [hct, filterProducts_two_length]
  unfold invCount2
  simp only [PF.strictN_eqP, sumF_eq, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have ra := (T0 a (List.mem_range.1 ha)).1
  simp only [Function.comp_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb'
  have rb := (T1 b (List.mem_range.1 hb')).1
  simp only [Function.comp_apply]
  have hcan : ∀ {X : Nat}, (∀ x < n, pg w (mask w) X x < n) →
      canonK n w (mask w) (n * w) (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a)) X) = true :=
    fun hX => canonK_of hn hw' (PF.pcomp_shr _ _ hn32 (PF.w_pos hw')) fun i hi => by
      rw [PF.pg_pcomp hn32 hi]
      exact ra _ (hX i hi)
  rw [compT_idT_tabP hn32 ra, compT_tabP hn32 rb, ordTest2_tabP (hcan rb), nIf_inv]
  rfl

end CFSG.KC.Child3

end
