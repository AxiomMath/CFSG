module

public import Certificates.Data.Kernel.YoshQ.UEF
public import CFSG.Certificates.Kernel.YoshQ.FastSound
public import CFSG.Certificates.Kernel.YoshQ.TabNSound
import CFSG.Certificates.Kernel.Spor.DistinctSound
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS
open scoped commutatorElement

theorem strictB_eqU (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem eqN_trans {x y z : Nat} (h1 : eqN 16 5 x y = true) (h2 : eqN 16 5 y z = true) :
    eqN 16 5 x z = true := by
  unfold eqN at *
  rw [Nat.beq_eq] at *
  exact h1.trans h2

theorem eqN_symm {x y : Nat} (h : eqN 16 5 x y = true) : eqN 16 5 y x = true := by
  unfold eqN at *
  rw [Nat.beq_eq] at *
  exact h.symm

theorem hN_of_eqN {P x y : Nat} (h : eqN 16 5 x y = true) : hN P x = hN P y := by
  unfold eqN at h
  unfold hN
  rw [Nat.beq_eq.mp h]

theorem memT_eq {P M : Nat} {T : Nat → Nat} {lE : List Nat} (hT : ueT P M T lE = true) (t : Nat) :
    memT P M T t = memN 16 5 lE t := by
  unfold ueT at hT
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hT
  obtain ⟨hM, hE⟩ := hT
  unfold memT memN
  rw [strictB_eqU, Co2Shape.hasBit_eq, hM, hmask, testBit_hmaskF]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨e, he, hh⟩, hq⟩
    have h1 := hE e he
    rw [hh] at h1
    exact ⟨e, he, eqN_trans (eqN_symm h1) hq⟩
  · rintro ⟨e, he, hq⟩
    have hh : hN P e = hN P t := hN_of_eqN hq
    have h1 := hE e he
    rw [hh] at h1
    exact ⟨⟨e, he, hh⟩, eqN_trans h1 hq⟩

theorem cInI_eq (c a b : Nat) :
    cInI (pidn 16 5) c a (invN 16 5 a) b (invN 16 5 b) = commInN 16 5 c a b := by
  unfold cInI commInN comN
  rw [strictB_eqU]

theorem allPtU_iff (k : Nat) (f : Nat → Bool) : allPtU k f = true ↔ ∀ p < k, f p = true := by
  induction k with
  | zero => exact ⟨fun _ p hp => absurd hp (Nat.not_lt_zero p), fun _ => rfl⟩
  | succ i ih =>
    change Bool.rec (motive := fun _ => Bool) false (allPtU i f) (f i) = true ↔ _
    cases hf : f i
    · exact ⟨fun h => absurd h Bool.false_ne_true,
        fun h => absurd (h i (Nat.lt_succ_self i)) (by simp [hf])⟩
    · refine ⟨fun h p hp => ?_, fun h => ih.2 fun p hp => h p (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact ih.1 h p hp
      · exact hf

theorem fNU_eq (x j : Nat) : fNU x j = apN 16 5 x j := by
  unfold fNU apN
  cases h : Nat.blt j 16
  · have hj : ¬ j < 16 := fun hj => absurd h (by rw [Nat.blt_eq.mpr hj]; decide)
    exact (pg_mod_ge (n := 16) (by omega)).symm
  · have hj : j < 16 := by simpa using h
    exact (pg_mod (n := 16) hj).symm

theorem apN_pmN (x y j : Nat) : apN 16 5 (pmN 16 5 x y) j = fPU x y j := by
  unfold fPU
  cases h : Nat.blt j 16
  · have hj : ¬ j < 16 := fun hj => absurd h (by rw [Nat.blt_eq.mpr hj]; decide)
    exact pg_mod_ge (n := 16) (by omega)
  · have hj : j < 16 := by simpa using h
    change apN 16 5 (pmN 16 5 x y) j = fNU x (fNU y j)
    rw [fNU_eq, fNU_eq]
    unfold apN pmN
    rw [pg_mod (n := 16) (x := pcomp 16 5 (mask 5) (x % 2 ^ (16 * 5)) y) hj,
      CFSG.KS.PF.pg_pcomp (by norm_num) hj, pg_mod (n := 16) (x := y) hj]

theorem fPU_lt {x y j : Nat} (hj : j < 16) : fPU x y j = apN 16 5 x (apN 16 5 y j) := by
  have h : Nat.blt j 16 = true := by simpa using hj
  unfold fPU
  rw [h]
  change fNU x (fNU y j) = _
  rw [fNU_eq, fNU_eq]

theorem eqN_iff_apN (x y : Nat) :
    eqN 16 5 x y = true ↔ ∀ i < 16, apN 16 5 x i = apN 16 5 y i := by
  unfold eqN apN
  rw [Nat.beq_eq]
  refine ⟨fun h i _ => by rw [h], fun h => ?_⟩
  exact CFSG.KS.PF.eq_of_fields (by decide) (mod_shr (n := 16) (w := 5) x)
    (mod_shr (n := 16) (w := 5) y) h

theorem cInPt_eq (one c a ai b bi : Nat) : cInPt one c a ai b bi = cInI one c a ai b bi := by
  have key : ∀ z, (allPtU 16 fun i => Nat.beq (fPU a b (fPU ai bi i)) (fNU z i)) =
      eqN 16 5 (pmN 16 5 (pmN 16 5 a b) (pmN 16 5 ai bi)) z := by
    intro z
    rw [Bool.eq_iff_iff, allPtU_iff, eqN_iff_apN]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [Nat.beq_eq, ← apN_pmN ai bi, ← apN_pmN a b,
      apN_pmN (pmN 16 5 a b) (pmN 16 5 ai bi) i, fPU_lt hi, fNU_eq]
  unfold cInPt cInI
  simp only [strictB_eqU, key]
  cases eqN 16 5 (pmN 16 5 (pmN 16 5 a b) (pmN 16 5 ai bi)) one <;> rfl

theorem ueV_of_P {c : Nat} {lE LI YL YI MK : List Nat} (h : ueVP c lE LI YL YI MK = true) :
    ueV c lE LI YL YI MK = true := by
  unfold ueVP at h
  unfold ueV
  simpa only [cInPt_eq] using h

theorem goodU_iff (x : Nat) : goodU x = true ↔ ∀ i < 16, apN 16 5 x i < 16 := by
  unfold goodU
  rw [allPtU_iff]
  simp only [Nat.blt_eq, fNU_eq]

theorem apN_lt_of_goodU {x : Nat} (hx : goodU x = true) (j : Nat) : apN 16 5 x j < 16 := by
  by_cases hj : j < 16
  · exact (goodU_iff x).1 hx j hj
  · unfold apN
    rw [pg_mod_ge (n := 16) (by omega)]
    omega

theorem apN_pmN_lt {x y j : Nat} (hj : j < 16) :
    apN 16 5 (pmN 16 5 x y) j = apN 16 5 x (apN 16 5 y j) := by
  rw [apN_pmN, fPU_lt hj]

theorem goodU_pmN {x : Nat} (hx : goodU x = true) (y : Nat) : goodU (pmN 16 5 x y) = true :=
  (goodU_iff _).2 fun i hi => by rw [apN_pmN_lt hi]; exact apN_lt_of_goodU hx _

noncomputable def toFU (x : Nat) : Fin 16 → Fin 16 := fun i => ⟨apN 16 5 x i % 16, by omega⟩

theorem toFU_pmN {x y : Nat} (hy : goodU y = true) : toFU (pmN 16 5 x y) = toFU x ∘ toFU y := by
  funext i
  simp only [toFU, Function.comp_apply, Fin.mk.injEq]
  rw [apN_pmN_lt i.2, Nat.mod_eq_of_lt (apN_lt_of_goodU hy _)]

theorem eqN_iff_toFU {x y : Nat} (hx : goodU x = true) (hy : goodU y = true) :
    eqN 16 5 x y = true ↔ toFU x = toFU y := by
  rw [eqN_iff_apN, funext_iff]
  refine ⟨fun h i => Fin.ext ?_, fun h i hi => ?_⟩
  · simp only [toFU]
    rw [h i i.2]
  · have := congrArg Fin.val (h ⟨i, hi⟩)
    simp only [toFU] at this
    rwa [Nat.mod_eq_of_lt (apN_lt_of_goodU hx _), Nat.mod_eq_of_lt (apN_lt_of_goodU hy _)] at this

theorem apN_pidn : ∀ i < 16, apN 16 5 (pidn 16 5) i = i := by decide +kernel

theorem goodU_pidn : goodU (pidn 16 5) = true :=
  (goodU_iff _).2 fun i hi => by rw [apN_pidn i hi]; exact hi

theorem toFU_pidn : toFU (pidn 16 5) = id := by
  funext i
  exact Fin.ext (by simp only [toFU, id]; rw [apN_pidn i i.2, Nat.mod_eq_of_lt i.2])

theorem invOkU_parts {x xi : Nat} (h : invOkU (pidn 16 5) x xi = true) :
    goodU x = true ∧ goodU xi = true ∧ toFU x ∘ toFU xi = id ∧ toFU xi ∘ toFU x = id := by
  unfold invOkU at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hx, hxi⟩, h1⟩, h2⟩ := h
  rw [eqN_iff_toFU (goodU_pmN hx _) goodU_pidn, toFU_pmN hxi, toFU_pidn] at h1
  rw [eqN_iff_toFU (goodU_pmN hxi _) goodU_pidn, toFU_pmN hx, toFU_pidn] at h2
  exact ⟨hx, hxi, h1, h2⟩

noncomputable def mkPU (x xi : Nat) : Equiv.Perm (Fin 16) :=
  if h : invOkU (pidn 16 5) x xi = true then
    { toFun := toFU x, invFun := toFU xi
      left_inv := fun i => congrFun (invOkU_parts h).2.2.2 i
      right_inv := fun i => congrFun (invOkU_parts h).2.2.1 i }
  else 1

theorem coe_mkPU {x xi : Nat} (h : invOkU (pidn 16 5) x xi = true) :
    ⇑(mkPU x xi) = toFU x ∧ ⇑(mkPU x xi)⁻¹ = toFU xi := by
  unfold mkPU
  split
  · exact ⟨rfl, rfl⟩
  · contradiction

theorem cInI_iff {c x xi y yi : Nat} (hc : invOkU (pidn 16 5) c c = true)
    (hx : invOkU (pidn 16 5) x xi = true) (hy : invOkU (pidn 16 5) y yi = true) :
    cInI (pidn 16 5) c x xi y yi = true ↔
      ⁅mkPU x xi, mkPU y yi⁆ = 1 ∨ ⁅mkPU x xi, mkPU y yi⁆ = mkPU c c := by
  obtain ⟨gx, gxi, -, -⟩ := invOkU_parts hx
  obtain ⟨gy, gyi, -, -⟩ := invOkU_parts hy
  obtain ⟨gc, -, -, -⟩ := invOkU_parts hc
  have ht : toFU (pmN 16 5 (pmN 16 5 x y) (pmN 16 5 xi yi)) =
      ⇑⁅mkPU x xi, mkPU y yi⁆ := by
    rw [commutatorElement_def, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul,
      (coe_mkPU hx).1, (coe_mkPU hx).2, (coe_mkPU hy).1, (coe_mkPU hy).2,
      toFU_pmN (goodU_pmN gxi _), toFU_pmN gy, toFU_pmN gyi]
    rfl
  have gt := goodU_pmN (goodU_pmN gx y) (pmN 16 5 xi yi)
  unfold cInI
  rw [strictB_eqU, Bool.or_eq_true, eqN_iff_toFU gt goodU_pidn, eqN_iff_toFU gt gc, ht,
    toFU_pidn, ← (coe_mkPU hc).1, ← Equiv.Perm.coe_one, DFunLike.coe_fn_eq, DFunLike.coe_fn_eq]

theorem comm_prod_memU {H : Type*} [Group H] {c b : H} (hc : c * c = 1) (S : List H)
    (hS : ∀ g ∈ S, g * c = c * g ∧ (⁅g, b⁆ = 1 ∨ ⁅g, b⁆ = c)) :
    ⁅S.prod, b⁆ = 1 ∨ ⁅S.prod, b⁆ = c := by
  induction S with
  | nil => left; simp
  | cons g S ih =>
    obtain ⟨hgc, hgb⟩ := hS g List.mem_cons_self
    have e : ⁅g * S.prod, b⁆ = g * ⁅S.prod, b⁆ * g⁻¹ * ⁅g, b⁆ := by
      simp only [commutatorElement_def]
      group
    have hcg : g * c * g⁻¹ = c := by rw [hgc]; group
    rw [List.prod_cons, e]
    rcases ih fun g' hg' => hS g' (List.mem_cons_of_mem g hg') with h | h <;> rw [h]
    · simpa using hgb
    · rw [hcg]
      rcases hgb with h' | h' <;> rw [h']
      · right; simp
      · left; exact hc

theorem toFU_evalWU {G : List Nat}
    (hG : ∀ g ∈ G, invOkU (pidn 16 5) g (invN 16 5 g) = true) (w : List Nat)
    (hw : ∀ k ∈ w, k < G.length) :
    goodU (evalWU (pidn 16 5) G w) = true ∧ toFU (evalWU (pidn 16 5) G w) =
      ⇑(w.map fun k => mkPU (G.getD k 0) (invN 16 5 (G.getD k 0))).prod := by
  induction w with
  | nil => exact ⟨goodU_pidn, toFU_pidn⟩
  | cons k w ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k' hk' => hw k' (List.mem_cons_of_mem k hk')
    have hk : G.getD k 0 ∈ G := by
      rw [List.getD_eq_getElem _ _ (hw k List.mem_cons_self)]
      exact List.getElem_mem _
    have hg := hG _ hk
    change goodU (pmN 16 5 (G.getD k 0) (evalWU (pidn 16 5) G w)) = true ∧
      toFU (pmN 16 5 (G.getD k 0) (evalWU (pidn 16 5) G w)) = _
    refine ⟨goodU_pmN (invOkU_parts hg).1 _, ?_⟩
    rw [toFU_pmN ih1, ih2, List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, (coe_mkPU hg).1]

theorem ue5_of_G {c : Nat} {lE LI G : List Nat} {W : List (List Nat)}
    (h : ue5G c lE LI G W = true) : ue5 c lE LI = true := by
  unfold ue5G at h
  simp only [strictB_eqU, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨hc, hE⟩, hG⟩, hl⟩, hW⟩ := h
  unfold ue5
  simp only [strictB_eqU, List.all_eq_true]
  intro p hp q hq
  have hGi : ∀ g ∈ G, invOkU (pidn 16 5) g (invN 16 5 g) = true := fun g hg => (hG g hg).1.1
  have hp1 : p.1 ∈ lE := (List.of_mem_zip hp).1
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp1
  have hz : i < (lE.zip W).length := by rw [List.length_zip]; omega
  have hw := hW _ (List.getElem_mem hz)
  rw [List.getElem_zip, hpi] at hw
  simp only [Nat.blt_eq] at hw
  obtain ⟨hwk, hwe⟩ := hw
  obtain ⟨g1, g2⟩ := toFU_evalWU hGi _ hwk
  have hpP := hE p hp
  have hqP := hE q hq
  rw [cInI_iff hc hpP hqP]
  have hpe : mkPU p.1 p.2 = (W[i].map fun k => mkPU (G.getD k 0) (invN 16 5 (G.getD k 0))).prod := by
    apply DFunLike.coe_injective
    rw [(coe_mkPU hpP).1, ← g2]
    exact ((eqN_iff_toFU (invOkU_parts hpP).1 g1).1 hwe)
  rw [hpe]
  obtain ⟨gc, -, hcc, -⟩ := invOkU_parts hc
  refine comm_prod_memU ?_ _ ?_
  · apply DFunLike.coe_injective
    rw [Equiv.Perm.coe_mul, (coe_mkPU hc).1, hcc, Equiv.Perm.coe_one]
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
    have hkG : G.getD k 0 ∈ G := by
      rw [List.getD_eq_getElem _ _ (hwk k hk)]
      exact List.getElem_mem _
    obtain ⟨⟨hgi, hgc⟩, hgb⟩ := hG _ hkG
    obtain ⟨gg, -, -, -⟩ := invOkU_parts hgi
    refine ⟨?_, (cInI_iff hc hgi hqP).1 ?_⟩
    · apply DFunLike.coe_injective
      rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, (coe_mkPU hc).1, (coe_mkPU hgi).1,
        ← toFU_pmN gc, ← toFU_pmN gg]
      exact (eqN_iff_toFU (goodU_pmN gg _) (goodU_pmN gc _)).1 hgc
    · rw [← cInPt_eq]
      exact hgb q hq

theorem zip_map_selfU {α β : Type} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map fun a => (a, f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem zip_map_self2 {α β γ : Type} (l : List α) (f : α → β) (g : α → γ) :
    l.zip ((l.map f).zip (l.map g)) = l.map fun a => (a, f a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem popN_succ (x n : Nat) : popN x (n + 1) = Nat.land x 1 + popN (Nat.shiftRight x 1) n := rfl

theorem bitsN_cons (b : Bool) (l : List Bool) : bitsN (b :: l) = 2 * bitsN l + cond b 1 0 := rfl

theorem popN_bitsN (l : List Bool) : popN (bitsN l) l.length = (l.filter id).length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have e1 : Nat.land (2 * bitsN l + cond b 1 0) 1 = cond b 1 0 := by
      change (2 * bitsN l + cond b 1 0) &&& 1 = _
      rw [Nat.and_one_is_mod]
      cases b <;> simp [Nat.add_mod]
    have e2 : Nat.shiftRight (2 * bitsN l + cond b 1 0) 1 = bitsN l := by
      change (2 * bitsN l + cond b 1 0) >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow]
      cases b <;> simp <;> omega
    rw [List.length_cons, popN_succ, bitsN_cons, e1, e2, ih]
    cases b <;> simp [List.filter_cons] <;> omega

theorem bitsN_inj : ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length → bitsN l₁ = bitsN l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, h => by
    rw [bitsN_cons, bitsN_cons] at h
    have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> simp at h <;> first | rfl | omega
    subst hb
    have h' : bitsN l₁ = bitsN l₂ := by cases b₁ <;> simp at h <;> omega
    rw [bitsN_inj (by simpa using hl) h']

theorem bne_eq_bitsN {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length) :
    (l₁ != l₂) = !Nat.beq (bitsN l₁) (bitsN l₂) := by
  by_cases h : l₁ = l₂
  · subst h
    simp
  · have h' : bitsN l₁ ≠ bitsN l₂ := fun e => h (bitsN_inj hl e)
    have hb : Nat.beq (bitsN l₁) (bitsN l₂) = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h' (Nat.eq_of_beq_eq_true e)
    rw [hb]
    simpa using h

theorem ueN_of_F {GE GS lE lS LI YL YI MK : List Nat} {c P M : Nat} {T : Nat → Nat}
    (hT : ueT P M T lE = true) (hI : ueI lE LI YL YI = true) (hY : ueY P M T c lS YL = true)
    (h2 : ue2 P M T GE lS = true) (h5 : ue5 c lE LI = true) (hV : ueV c lE LI YL YI MK = true)
    (h8 : ue8 P M T YL YI MK = true) (hR : ueR GE GS c lE lS = true) :
    ueN GE GS c lE lS = true := by
  have hm := memT_eq hT
  unfold ueI at hI
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hI
  obtain ⟨hLI, hYI⟩ := hI
  subst hLI hYI
  unfold ueY at hY
  simp only [strictB_eqU, hm, beq_iff_eq] at hY
  unfold ueV at hV
  simp only [strictB_eqU, Bool.and_eq_true, beq_iff_eq, zip_map_selfU, List.map_map,
    Function.comp_def, cInI_eq] at hV
  obtain ⟨hMK, hpop⟩ := hV
  subst hMK
  unfold ueR at hR
  simp only [strictB_eqU, Bool.and_eq_true] at hR
  obtain ⟨⟨⟨r1, r3⟩, r4⟩, r6⟩ := hR
  unfold ueN
  rw [hY]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨r1, ?_⟩, r3⟩, r4⟩, ?_⟩, r6⟩, ?_⟩, ?_⟩
  · unfold ue2 at h2
    simp only [strictB_eqU, hm] at h2
    exact h2
  · unfold ue5 at h5
    simp only [strictB_eqU, zip_map_selfU, List.all_map, Function.comp_def, cInI_eq] at h5
    exact h5
  · rw [List.all_eq_true]
    intro y hy
    rw [List.all_map, List.all_eq_true] at hpop
    have h := hpop y hy
    simp only [Function.comp_def, Nat.ble_eq] at h
    have hl : lE.length = (lE.map fun x => commInN 16 5 c x y).length := by simp
    rw [hl, popN_bitsN, List.filter_map, List.length_map] at h
    simpa [Function.comp_def] using h
  · unfold ue8 at h8
    simp only [zip_map_self2, zip_map_selfU, List.all_map, Function.comp_def, hm] at h8
    simp only [List.all_map, Function.comp_def]
    rw [List.all_eq_true] at h8 ⊢
    intro y hy
    have h := h8 y hy
    rw [List.all_eq_true] at h ⊢
    intro y' hy'
    rw [bne_eq_bitsN (by simp)]
    exact h y' hy'

end CFSG.KC.YoshQ

end
