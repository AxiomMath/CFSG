module

public import Certificates.Data.Kernel.LocalComp.Tits
public import CFSG.Certificates.Kernel.LocalCompTits.TabP
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Data.List.Nodup

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native
  CFSG.KC.LocalComp.Tits

theorem nPts_eq : nPts () = 1755 := rfl

theorem getElem!_nat (l : List Nat) (i : Nat) : l[i]! = l.getD i 0 := by
  simp only [getElem!_def, List.getD_eq_getElem?_getD]
  cases l[i]? <;> rfl

theorem eqOn_iff {CP : List Nat} (hc : checkPts = CP.toArray) (P Q : Table) :
    eqOn P Q = true ↔ ∀ p ∈ CP, ap P p = ap Q p := by
  unfold eqOn
  rw [hc, TW.allIn_iff]
  constructor
  · intro h p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have := h i (by simpa using hi)
    rw [getElem!_pos CP.toArray i (by simpa using hi)] at this
    simpa using this
  · intro h i hi
    have hi' : i < CP.length := by simpa using hi
    rw [getElem!_pos CP.toArray i (by simpa using hi)]
    simpa using h _ (List.getElem_mem hi')

theorem eqOnK_iff {CP : List Nat} (A B : Nat) :
    eqOnK 11 CP A B = true ↔ ∀ p ∈ CP, pg 11 (mask 11) A p = pg 11 (mask 11) B p := by
  unfold eqOnK
  simp only [List.all_eq_true, Nat.beq_eq]

theorem eqOn_tabP {N : Nat} {CP : List Nat} (hc : checkPts = CP.toArray) {A B : Nat}
    (hA : Bd N A) (hB : Bd N B) : eqOn (tabP N A) (tabP N B) = eqOnK 11 CP A B := by
  rw [Bool.eq_iff_iff, eqOn_iff hc, eqOnK_iff]
  simp only [ap_tabP hA, ap_tabP hB]


theorem nfT_tabP {X Y Z : Nat} (hX : Gd 1755 X) (hY : Gd 1755 Y)
    (hZ : Gd 1755 Z) (i j k : Nat) :
    nfT (tabP 1755 X) (tabP 1755 Y) (tabP 1755 Z) i j k = tabP 1755 (nfK 1755 11 X Y Z i j k) := by
  have hN : 1755 + 1 < 2048 := by decide
  unfold nfT nfK
  rw [nPts_eq, ← tabP_ppow hN hX i, ← tabP_ppow hN hY j, ← tabP_ppow hN hZ k,
    ← tabP_pcomp (by omega) (gd_ppow hN hX i).mp (gd_ppow hN hY j).mp,
    ← tabP_pcomp (by omega) (gd_pcomp (by omega) (gd_ppow hN hX i) (gd_ppow hN hY j)).mp
      (gd_ppow hN hZ k).mp]

theorem keyK_congr {CP : List Nat} {A B : Nat}
    (h : ∀ p ∈ CP, pg 11 (mask 11) A p = pg 11 (mask 11) B p) :
    keyK 11 CP A = keyK 11 CP B := by
  unfold keyK
  induction CP with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldr_cons]
    rw [h p List.mem_cons_self]
    have := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    rw [this]

theorem keysK_eq (f : Nat → Nat) (l : List Nat) : keysK f l = l.map f := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    simp only [keysK, List.map_cons, ih]
    generalize f u = y
    cases y <;> rfl

theorem distinctK_iff (l : List Nat) : distinctK l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [distinctK]
  | cons x xs ih =>
    simp only [distinctK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', ih,
      List.nodup_cons]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hx => ?_, h2⟩
      have := h1 x hx
      simp at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy => ?_, h2⟩
      have : x ≠ y := fun e => h1 (e ▸ hy)
      cases hh : x.beq y
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hh) this

theorem distinct_of_K {CP : List Nat} (hc : checkPts = CP.toArray) {M : Nat} {F : Nat → Table}
    {G : Nat → Nat} (hF : ∀ u, F u = tabP 1755 (G u)) (hG : ∀ u, Bd 1755 (G u))
    (h : distinctK (keysK (fun v => keyK 11 CP (G v)) (List.range M)) = true) :
    allIn 0 M (fun u => allIn 0 M fun v => u == v || !eqOn (F u) (F v)) = true := by
  rw [keysK_eq, distinctK_iff] at h
  rw [TW.allIn_iff]
  intro u hu
  rw [TW.allIn_iff]
  intro v hv
  by_cases e : u = v
  · simp [e]
  · have hne : eqOn (F u) (F v) = false := by
      rw [Bool.eq_false_iff]
      intro hq
      rw [hF, hF, eqOn_tabP hc (hG u) (hG v), eqOnK_iff] at hq
      apply e
      exact List.inj_on_of_nodup_map h (List.mem_range.2 hu) (List.mem_range.2 hv)
        (keyK_congr hq)
    simp [hne]

theorem lettersOK_eq (D : TitsWitness) : lettersOK D = lettersK D := by
  unfold lettersOK lettersK
  have : allIn 0 (tLetters ()).size (fun k => isManifest (tLetters ())[k]!) =
      (tLetters ()).toList.all isManifest := by
    rw [Bool.eq_iff_iff, TW.allIn_iff, List.all_eq_true]
    constructor
    · intro h w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
      have := h i (by simpa using hi)
      rwa [getElem!_pos (tLetters ()) i (by simpa using hi)] at this
    · intro h i hi
      rw [getElem!_pos (tLetters ()) i hi]
      exact h _ (by simp)
  rw [this]


attribute [local irreducible] compT powT invT idT nfT wT

structure Pk (T : Table) (P : Nat) : Prop where
  tab : T = tabP 1755 P
  gd : Gd 1755 P

theorem Pk.comp {a b : Nat} {TA TB : Table} (hA : Pk TA a) (hB : Pk TB b) :
    Pk (compT 1755 TA TB) (pcomp 1755 11 (mask 11) a b) :=
  ⟨by rw [hA.tab, hB.tab]; exact (tabP_pcomp (by decide) hA.gd.mp hB.gd.mp).symm,
    gd_pcomp (by decide) hA.gd hB.gd⟩

theorem Pk.pow {a : Nat} {TA : Table} (hA : Pk TA a) (k : Nat) :
    Pk (powT 1755 k TA) (ppow 1755 11 (mask 11) (pidn 1755 11) a k) :=
  ⟨by rw [hA.tab]; exact (tabP_ppow (by decide) hA.gd k).symm, gd_ppow (by decide) hA.gd k⟩

theorem Pk.id : Pk (idT 1755) (pidn 1755 11) :=
  ⟨(tabP_pidn (by decide)).symm, gd_pidn (by decide)⟩

structure PermOK (a : Nat) : Prop where
  ok : permOK 1755 11 (mask 11) (1755 * 11) a (pinvS 1755 11 (mask 11) a) = true

theorem Pk.inv {a : Nat} {TA : Table} (hA : Pk TA a) (hp : PermOK a) :
    Pk (invT 1755 TA) (pinvS 1755 11 (mask 11) a) :=
  ⟨by rw [hA.tab]; exact tabP_inv (by decide) hp.ok, (permOK_facts hp.ok).2.1⟩

theorem Pk.nf {x y z : Nat} {X Y Z : Table} (hX : Pk X x) (hY : Pk Y y) (hZ : Pk Z z)
    (i j k : Nat) : Pk (nfT X Y Z i j k) (nfK 1755 11 x y z i j k) :=
  ⟨by
    rw [hX.tab, hY.tab, hZ.tab]
    exact nfT_tabP hX.gd hY.gd hZ.gd i j k, by
    unfold nfK
    exact gd_pcomp (by decide) (gd_pcomp (by decide) (gd_ppow (by decide) hX.gd i)
      (gd_ppow (by decide) hY.gd j)) (gd_ppow (by decide) hZ.gd k)⟩

theorem eqOn_eq {CP : List Nat} (hc : checkPts = CP.toArray) {A B : Table} {a b : Nat}
    (hA : Pk A a) (hB : Pk B b) : eqOn A B = eqOnK 11 CP a b := by
  rw [hA.tab, hB.tab]
  exact eqOn_tabP hc hA.gd.bd hB.gd.bd

theorem invOK_of_Pk {a : Nat} {A : Table} (hA : Pk A a)
    (h : permOK 1755 11 (mask 11) (1755 * 11) a (pinvS 1755 11 (mask 11) a) = true) :
    invOK 1755 A (invT 1755 A) = true := by
  rw [hA.tab]
  exact invOK_tabP h (by decide)

theorem distinct_of_Pk {CP : List Nat} (hc : checkPts = CP.toArray) {M : Nat} {F : Nat → Table}
    {G : Nat → Nat} (hF : ∀ u, Pk (F u) (G u))
    (h : distinctK (keysK (fun v => keyK 11 CP (G v)) (List.range M)) = true) :
    allIn 0 M (fun u => allIn 0 M fun v => u == v || !eqOn (F u) (F v)) = true :=
  distinct_of_K hc (fun u => (hF u).tab) (fun u => (hF u).gd.bd) h

local macro "pk" : tactic =>
  `(tactic| repeat' (first | assumption | exact Pk.id | apply Pk.comp | apply Pk.pow | apply Pk.nf | apply Pk.inv))

theorem wT_eq {TG : Nat → Nat} (hg : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (hTG : ∀ s < 4, permOK 1755 11 (mask 11) (1755 * 11) (TG s) (pinvS 1755 11 (mask 11) (TG s))
      = true) (w : List Int) :
    Pk (wT w) (wordK 1755 11 TG w) := by
  unfold wT
  rw [nPts_eq, hg]
  exact ⟨(wordT_eq rfl (by decide) hTG w).1, (wordT_eq rfl (by decide) hTG w).2⟩

theorem cubicOK_of_K {TG : Nat → Nat} {CP : List Nat} {D : TitsWitness}
    (hg : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (hc : checkPts = CP.toArray) (h : cubicK 1755 11 TG CP D = true) : cubicOK D = true := by
  unfold cubicK at h
  simp only [strictB_eqP, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hl, hlen, hTG, hXp, hYp, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have hTG' : ∀ s < 4, permOK 1755 11 (mask 11) (1755 * 11) (TG s)
      (pinvS 1755 11 (mask 11) (TG s)) = true := fun s hs => allN_spec hTG s hs
  have qX : PermOK _ := ⟨hXp⟩
  have qY : PermOK _ := ⟨hYp⟩
  have pX := wT_eq hg hTG' (texpand D.wx)
  have pY := wT_eq hg hTG' (texpand D.wy)
  have pH := wT_eq hg hTG' (texpand D.wh)
  unfold conjOnK at h12 h13 h14
  unfold cubicOK
  simp only [nPts_eq, getElem!_nat, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
  refine ⟨by rw [lettersOK_eq]; exact hl, by simpa using Nat.eq_of_beq_eq_true hlen,
    invOK_of_Pk pX hXp, invOK_of_Pk pY hYp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eqOn_eq hc (by pk) (by pk)).trans h6
  · exact (eqOn_eq hc (by pk) (by pk)).trans h7
  · exact (eqOn_eq hc (by pk) (by pk)).trans h8
  · exact (eqOn_eq hc (by pk) (by pk)).trans h9
  · exact (eqOn_eq hc (by pk) (by pk)).trans h10
  · exact distinct_of_Pk hc (fun u => by pk) h11
  · exact (eqOn_eq hc (by pk) (by pk)).trans h12
  · exact (eqOn_eq hc (by pk) (by pk)).trans h13
  · exact (eqOn_eq hc (by pk) (by pk)).trans h14


theorem squareOK_of_K {TG : Nat → Nat} {CP : List Nat} {D : TitsWitness}
    (hg : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (hc : checkPts = CP.toArray) (h : squareK 1755 11 TG CP D = true) : squareOK D = true := by
  unfold squareK at h
  simp only [strictB_eqP, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hl, hlen, hTG, h4, h5, h6, h7, h8, h9⟩ := h
  have hTG' : ∀ s < 4, permOK 1755 11 (mask 11) (1755 * 11) (TG s)
      (pinvS 1755 11 (mask 11) (TG s)) = true := fun s hs => allN_spec hTG s hs
  have pX := wT_eq hg hTG' (texpand D.wx)
  have pY := wT_eq hg hTG' (texpand D.wy)
  have pH := wT_eq hg hTG' (texpand D.wh)
  unfold conjOnK at h8 h9
  unfold squareOK
  simp only [nPts_eq, getElem!_nat, Bool.and_eq_true, and_assoc]
  refine ⟨by rw [lettersOK_eq]; exact hl, by simpa using Nat.eq_of_beq_eq_true hlen,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eqOn_eq hc (by pk) (by pk)).trans h4
  · exact (eqOn_eq hc (by pk) (by pk)).trans h5
  · exact (eqOn_eq hc (by pk) (by pk)).trans h6
  · exact distinct_of_Pk hc (fun u => by pk) h7
  · exact (eqOn_eq hc (by pk) (by pk)).trans h8
  · exact (eqOn_eq hc (by pk) (by pk)).trans h9

end CFSG.KC.LocalComp.TitsSound

end
