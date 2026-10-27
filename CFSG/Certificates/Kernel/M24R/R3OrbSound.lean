module

public import Certificates.Data.Kernel.M24R.R3Orb
public import CFSG.Certificates.Kernel.M24R.R3KSound
public import CFSG.CGT.M24R.R3Count

public section

namespace CFSG.KC.M24R3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KC.BfsPin CFSG.CGT.M24R
  CFSG.CGT.M24R.R3 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Child3 (tabP)
open CFSG.KC (andB orB)

abbrev sgW (z : N0Word) : Equiv.Perm (Fin 24) := FreeGroup.lift n0Perm (FreeGroup.mk z)

theorem sgW_append (z z' : N0Word) : sgW (z ++ z') = sgW z * sgW z' := by
  rw [sgW, sgW, sgW, ← map_mul, FreeGroup.mul_mk]

theorem sgW_inv10 (z : N0Word) : sgW (inv10 z) = (sgW z)⁻¹ := by
  rw [sgW, sgW, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, inv10, List.map_reverse]

theorem sgW_gen (k : Fin 10) : sgW [(k, true)] = n0Perm k := by
  rw [sgW, show FreeGroup.mk [(k, true)] = FreeGroup.of k from rfl, FreeGroup.lift_apply_of]

@[expose] def PRep (p : Nat) (g : Equiv.Perm (Fin 24)) : Prop := PP 24 5 p ∧ Rep 24 (tabP 24 5 p) g

theorem PRep.conj {gi g c : Nat} {a x : Equiv.Perm (Fin 24)} (hgi : PRep gi a⁻¹) (hg : PRep g a)
    (hc : PRep c x) : PRep (pcj 24 5 gi g c) (a⁻¹ * x * a) := by
  refine ⟨PP_pcj hgi.1 hg.1 hc.1, ?_⟩
  rw [KGC31P.pcj,← compT_tabP' (hgi.1.pc hc.1) hg.1, ← compT_tabP' hgi.1 hc.1]
  exact Rep.compT (Rep.compT hgi.2 hc.2) hg.2

theorem glit_eq : ∀ k : Fin 10, kEnt GLIT k = pmk 24 5 (fun i => ap (genTab k) i) ∧
    kEnt GILIT k = pmk 24 5 (fun i => ap (genTabInv k) i) := by
  decide +kernel

theorem ky0_eq : ∀ j : Fin 4, wTab (dExp (yD j)) = tabP 24 5 (kEnt KY0 j) := by
  decide +kernel

theorem ky0_perm : ∀ j : Fin 4,
    permOK 24 5 (mask 5) (24 * 5) (kEnt KY0 j) (pinvS 24 5 (mask 5) (kEnt KY0 j)) = true := by
  decide +kernel

theorem prep_glit (k : Fin 10) : PRep (kEnt GLIT k) (n0Perm k) := by
  rw [(glit_eq k).1]
  refine ⟨PP_of_permOK hsz24 (gen_perm k), ?_⟩
  rw [← gen_eq k]
  exact rep_genTab k

theorem prep_gilit (k : Fin 10) : PRep (kEnt GILIT k) (n0Perm k)⁻¹ := by
  rw [(glit_eq k).2]
  refine ⟨PP_of_permOK hsz24 (genInv_perm k), ?_⟩
  rw [← genInv_eq k]
  exact rep_genTabInv k

theorem prep_ky0 (j : Fin 4) : PRep (kEnt KY0 j) (sgW (dExp (yD j))) :=
  ⟨PP_of_permOK hsz24 (ky0_perm j), ky0_eq j ▸ rep_wTab _⟩

theorem andB_eqO (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eqO (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem allBlk_elim {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    allBlk b f len = true → ∀ l < len, f (Nat.add b l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true at h
    cases hf : f (Nat.add b len)
    · rw [hf] at h
      change false = true at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h1 | rfl
      · exact allBlk_elim h l h1
      · exact hf

theorem orbOK_of_blocks {F : Nat → Nat} (h : ∀ k < 40, orbBlk F (504 * k) 504 = true) :
    ∀ n < 20160, orbOK F n = true := by
  intro n hn
  have e := allBlk_elim (h (n / 504) (by omega)) (n % 504) (Nat.mod_lt _ (by norm_num))
  rwa [show Nat.add (504 * (n / 504)) (n % 504) = n from Nat.div_add_mod n 504] at e

theorem orbOK_spec {F : Nat → Nat} {n : Nat} (h : orbOK F n = true) :
    (n = 0 ∨ rKey (F (n - 1)) < rKey (F n)) ∧ F n >>> 520 = 0 ∧
    ((n = oRoot ∧ rDep (F n) = 0 ∧ rKey (F n) = KY0) ∨
      (n ≠ oRoot ∧ rPar (F n) < 20160 ∧ rGen (F n) < 10 ∧
        rDep (F (rPar (F n))) + 1 = rDep (F n) ∧
        ∀ j < 4, kEnt (rKey (F n)) j = pcj 24 5 (kEnt GILIT (rGen (F n))) (kEnt GLIT (rGen (F n)))
          (kEnt (rKey (F (rPar (F n)))) j))) := by
  unfold orbOK at h
  rw [strictB_eqR3] at h
  unfold recOK at h
  simp only [andB_eqO, orB_eqO, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa [Nat.sub_eq] using h1, h2, ?_⟩
  revert h3
  cases hr : Nat.beq n oRoot
  · intro h3
    dsimp only at h3
    rw [strictB_eqR3] at h3
    unfold cjOK entOK at h3
    simp only [strictB_eqR3, andB_eqO, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h3
    obtain ⟨hp, hg, hd, e0, e1, e2, e3⟩ := h3
    refine Or.inr ⟨fun e => by rw [e, Nat.beq_refl] at hr; exact absurd hr (by decide), hp, hg,
      hd, fun j hj => ?_⟩
    interval_cases j
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  · intro h3
    dsimp only at h3
    simp only [andB_eqO, Bool.and_eq_true, Nat.beq_eq] at h3
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hr, h3⟩

@[expose] noncomputable def oWord (F : Nat → Nat) : Nat → Nat → N0Word
  | _, 0 => []
  | n, d + 1 => oWord F (rPar (F n)) d ++ [(⟨rGen (F n) % 10, Nat.mod_lt _ (by norm_num)⟩, true)]

theorem rep_oWord {F : Nat → Nat} (h : ∀ n < 20160, orbOK F n = true) :
    ∀ d n, n < 20160 → rDep (F n) = d → ∀ j : Fin 4,
      PRep (kEnt (rKey (F n)) j)
        ((sgW (oWord F n d))⁻¹ * sgW (dExp (yD j)) * sgW (oWord F n d))
  | 0, n, hn, hd, j => by
    obtain ⟨-, -, hc⟩ := orbOK_spec (h n hn)
    rcases hc with ⟨-, -, hk⟩ | ⟨-, -, -, hd', -⟩
    · rw [hk]
      simpa [oWord] using prep_ky0 j
    · omega
  | d + 1, n, hn, hd, j => by
    obtain ⟨-, -, hc⟩ := orbOK_spec (h n hn)
    rcases hc with ⟨-, hd0, -⟩ | ⟨-, hp, hg, hd', he⟩
    · omega
    have ih := rep_oWord h d (rPar (F n)) hp (by omega) j
    have hk : (⟨rGen (F n) % 10, Nat.mod_lt _ (by norm_num)⟩ : Fin 10) = ⟨rGen (F n), hg⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hg)
    rw [he j.val j.isLt]
    have key := PRep.conj (prep_gilit ⟨rGen (F n), hg⟩) (prep_glit ⟨rGen (F n), hg⟩) ih
    convert key using 1
    rw [oWord, hk, sgW_append, sgW_gen]
    group

theorem foldl24_acc (acc : Nat) (l : List Nat) :
    l.foldl (fun a d => a * 24 + d) acc = acc * 24 ^ l.length + l.foldl (fun a d => a * 24 + d) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons d l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (0 * 24 + d), List.length_cons, pow_succ]
    ring

theorem foldl24_lt : ∀ l : List Nat, (∀ d ∈ l, d < 24) →
    l.foldl (fun a d => a * 24 + d) 0 < 24 ^ l.length
  | [], _ => by simp
  | d :: l, hl => by
    rw [List.foldl_cons, foldl24_acc, List.length_cons, pow_succ]
    have h1 := foldl24_lt l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have h2 := hl d List.mem_cons_self
    have h3 : 0 < 24 ^ l.length := by positivity
    nlinarith

theorem foldl24_inj : ∀ l l' : List Nat, l.length = l'.length → (∀ d ∈ l, d < 24) →
    (∀ d ∈ l', d < 24) → l.foldl (fun a d => a * 24 + d) 0 = l'.foldl (fun a d => a * 24 + d) 0 →
    l = l'
  | [], [], _, _, _, _ => rfl
  | d :: l, d' :: l', hlen, hl, hl', h => by
    have hlen' : l.length = l'.length := by simpa using hlen
    rw [List.foldl_cons, List.foldl_cons, foldl24_acc, foldl24_acc (0 * 24 + d')] at h
    have a1 := foldl24_lt l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have a2 := foldl24_lt l' fun x hx => hl' x (List.mem_cons_of_mem _ hx)
    rw [← hlen'] at a2 h
    have hB : 0 < 24 ^ l.length := by positivity
    have e1 : (0 * 24 + d) * 24 ^ l.length + l.foldl (fun a d => a * 24 + d) 0 =
        l.foldl (fun a d => a * 24 + d) 0 + 24 ^ l.length * d := by ring
    have e2 : (0 * 24 + d') * 24 ^ l.length + l'.foldl (fun a d => a * 24 + d) 0 =
        l'.foldl (fun a d => a * 24 + d) 0 + 24 ^ l.length * d' := by ring
    rw [e1, e2] at h
    have hd : d = d' := by
      have := congrArg (· / 24 ^ l.length) h
      simp only [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt a1, Nat.div_eq_of_lt a2] at this
      omega
    subst hd
    rw [foldl24_inj l l' hlen' (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) (by omega)]
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen

theorem map_ap_tabP {p : Nat} (hp : PP 24 5 p) :
    (List.range 24).map (ap (tabP 24 5 p)) = (List.range 24).map (pg 5 (mask 5) p) :=
  List.map_congr_left fun i hi => ap_tabP' hp (List.mem_range.1 hi)

theorem tupKey_inj {a b : Fin 4 → Nat} (ha : ∀ j, PP 24 5 (a j)) (hb : ∀ j, PP 24 5 (b j))
    (h : tupKey ((List.finRange 4).map fun j => tabP 24 5 (a j)) =
      tupKey ((List.finRange 4).map fun j => tabP 24 5 (b j))) : ∀ j, a j = b j := by
  have hlt : ∀ {c : Fin 4 → Nat}, (∀ j, PP 24 5 (c j)) →
      ∀ d ∈ tupPts ((List.finRange 4).map fun j => tabP 24 5 (c j)), d < 24 := by
    intro c hc d hd
    simp only [tupPts, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_finRange,
      true_and] at hd
    obtain ⟨_, ⟨j, rfl⟩, i, hi, rfl⟩ := hd
    rw [ap_tabP' (hc j) hi]
    exact (PF.canon_facts (hc j).1).2.2.2 i hi
  have hpts := foldl24_inj _ _ (by simp [tupPts, Function.comp_def]) (hlt ha) (hlt hb) h
  have hfin : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [tupPts, hfin, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, map_ap_tabP (ha _), map_ap_tabP (hb _)] at hpts
  have hl : ∀ c : Nat, ((List.range 24).map (pg 5 (mask 5) c)).length = 24 := fun c => by simp
  obtain ⟨e0, hpts⟩ := List.append_inj hpts (by rw [hl, hl])
  obtain ⟨e1, hpts⟩ := List.append_inj hpts (by rw [hl, hl])
  obtain ⟨e2, e3⟩ := List.append_inj hpts (by rw [hl, hl])
  have fin : ∀ j : Fin 4, (List.range 24).map (pg 5 (mask 5) (a j)) =
      (List.range 24).map (pg 5 (mask 5) (b j)) → a j = b j := by
    intro j e
    have hw := PF.w_pos (PF.canon_facts (ha j).1).2.1
    refine PF.eq_of_fields hw (PF.canon_facts (ha j).1).2.2.1 (PF.canon_facts (hb j).1).2.2.1
      fun i hi => ?_
    have := congrArg (fun l => l[i]?) e
    simpa [List.getElem?_map, List.getElem?_range hi] using this
  intro j
  fin_cases j
  · exact fin 0 e0
  · exact fin 1 e1
  · exact fin 2 e2
  · exact fin 3 e3

theorem conjKey_eq_tabP {z : N0Word} {c : Fin 4 → Nat}
    (hc : ∀ j, PRep (c j) ((sgW z)⁻¹ * sgW (dExp (yD j)) * sgW z)) :
    conjKey z = tupKey ((List.finRange 4).map fun j => tabP 24 5 (c j)) := by
  unfold conjKey yTabs
  rw [List.map_map]
  apply tupKey_map_congr
  intro j _ i hi
  have r1 := Rep.compT (Rep.compT (rep_wTab (inv10 z)) (rep_wTab (dExp (yD j)))) (rep_wTab z)
  rw [Function.comp_apply, r1 i hi, (hc j).2 i hi]
  simp only [sgW, sgW_inv10]

theorem key_eq_of_ents {K K' : Nat} (hK : K >>> 480 = 0) (hK' : K' >>> 480 = 0)
    (h : ∀ j : Fin 4, kEnt K j = kEnt K' j) : K = K' := by
  have hm : mask 120 = M120 := by decide +kernel
  refine PF.eq_of_fields (n := 4) (w := 120) (by norm_num) hK hK' fun i hi => ?_
  have e := h ⟨i, hi⟩
  simp only [kEnt, oFld] at e
  simp only [pg, hm]
  exact e

theorem shr480 {r : Nat} (h : r >>> 520 = 0) : rKey r >>> 480 = 0 := by
  unfold rKey
  change (r >>> 40) >>> 480 = 0
  rw [← Nat.shiftRight_add]
  exact h

theorem orbit_of {F : Nat → Nat} (h : ∀ n < 20160, orbOK F n = true) :
    ∃ Z : List N0Word, Z.length = 20160 ∧ (Z.map conjKey).Nodup := by
  refine ⟨(List.range 20160).map fun n => oWord F n (rDep (F n)), by simp, ?_⟩
  rw [List.map_map]
  refine List.Nodup.map_on (fun n hn m hm e => ?_) List.nodup_range
  rw [List.mem_range] at hn hm
  have hrn := rep_oWord h _ n hn rfl
  have hrm := rep_oWord h _ m hm rfl
  simp only [Function.comp_apply, conjKey_eq_tabP hrn, conjKey_eq_tabP hrm] at e
  have he := tupKey_inj (fun j => (hrn j).1) (fun j => (hrm j).1) e
  have hk := key_eq_of_ents (shr480 (orbOK_spec (h n hn)).2.1) (shr480 (orbOK_spec (h m hm)).2.1)
    he
  have mono : ∀ a b, a < b → b < 20160 → rKey (F a) < rKey (F b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ihb =>
      have step := (orbOK_spec (h (b + 1) hb)).1
      rcases step with h0 | hlt
      · omega
      · rw [Nat.add_sub_cancel] at hlt
        rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab' | rfl
        · exact (ihb hab' (by omega)).trans hlt
        · exact hlt
  rcases Nat.lt_trichotomy n m with hnm | hnm | hnm
  · exact absurd hk (ne_of_lt (mono n m hnm hm))
  · exact hnm
  · exact absurd hk.symm (ne_of_lt (mono m n hnm hn))

end CFSG.KC.M24R3

end
