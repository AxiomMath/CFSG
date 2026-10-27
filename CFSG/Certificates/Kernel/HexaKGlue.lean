
module

public import Certificates.Data.Kernel.HexaK
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaTests

public section

namespace CFSG.KC.HexaK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeSylow
open CFSG.KLie.CT (anyN sumN andB orB notB)

theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl
theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl
theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · exact beq_false_of_ne (Nat.ne_of_beq_eq_false h)
  · exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)

theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · exact (decide_eq_false fun h' => by rw [Nat.blt_eq.mpr h'] at h; cases h).symm
  · exact (decide_eq_true (Nat.blt_eq.mp h)).symm

theorem all_map_congr {α β : Type} {l : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ a ∈ l, p (f a) = q a) : (l.map f).all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih fun a ha => h a (List.mem_cons_of_mem x ha)]

theorem any_map_congr {α β : Type} {l : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ a ∈ l, p (f a) = q a) : (l.map f).any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.any_cons, List.any_cons, h x List.mem_cons_self,
      ih fun a ha => h a (List.mem_cons_of_mem x ha)]

theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  simpa using all_map_congr (f := id) h

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  simpa using any_map_congr (f := id) h

variable {n w : Nat}

theorem _root_.CFSG.KC.BfsPin.PP.conjK {g y : Nat} (hg : PP n w g) (hy : PP n w y) :
    PP n w (conj n w g y) := by
  unfold CFSG.KC.HexaK.conj
  rw [strictN_eq']
  exact hg.mul (hy.mul hg.inv)

theorem _root_.CFSG.KC.BfsPin.PP.conjInvK {g y : Nat} (hg : PP n w g) (hy : PP n w y) :
    PP n w (conjInv n w g y) := by
  unfold CFSG.KC.HexaK.conjInv
  rw [strictN_eq']
  exact hg.inv.mul (hy.mul hg)

theorem _root_.CFSG.KC.BfsPin.PP.commuK {g h : Nat} (hg : PP n w g) (hh : PP n w h) :
    PP n w (commu n w g h) := by
  unfold CFSG.KC.HexaK.commu
  rw [strictN_eq', strictN_eq']
  exact (hg.mul hh).mul (hg.inv.mul hh.inv)

theorem _root_.CFSG.KC.BfsPin.PP.pow4K {a : Nat} (ha : PP n w a) : PP n w (pow4 n w a) :=
  ha.mul (ha.mul (ha.mul (ha.mul (PP.id ha.sz))))

theorem mulN_PP {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    mulN n (unpack n w a) (unpack n w b) = unpack n w (pcomp n w (mask w) a b) := compA_PP ha hb

theorem conjA_PP {g y : Nat} (hg : PP n w g) (hy : PP n w y) :
    conjA n (unpack n w g) (unpack n w y) = unpack n w (conj n w g y) := by
  unfold conjA CFSG.KC.HexaK.conj
  rw [strictN_eq', invCand_PP hg, compA_PP hy hg.inv, compA_PP hg (hy.mul hg.inv)]
  rfl

theorem conjInvA_PP {g y : Nat} (hg : PP n w g) (hy : PP n w y) :
    conjInvA n (unpack n w g) (unpack n w y) = unpack n w (conjInv n w g y) := by
  unfold conjInvA CFSG.KC.HexaK.conjInv
  rw [strictN_eq', invCand_PP hg, compA_PP hy hg, compA_PP hg.inv (hy.mul hg)]
  rfl

theorem commutatorA_PP {g h : Nat} (hg : PP n w g) (hh : PP n w h) :
    commutatorA n (unpack n w g) (unpack n w h) = unpack n w (commu n w g h) := by
  unfold commutatorA CFSG.KC.HexaK.commu
  rw [strictN_eq', strictN_eq', invCand_PP hg, invCand_PP hh, compA_PP hg hh,
    compA_PP hg.inv hh.inv, compA_PP (hg.mul hh) (hg.inv.mul hh.inv)]
  rfl

theorem commN_PP {a b : Nat} (ha : PP n w a) (hb : PP n w b) :
    commN n (unpack n w a) (unpack n w b) = comm n w a b := by
  unfold commN comm
  rw [strictB_eq', strictB_eq', mulN_PP ha hb, mulN_PP hb ha, eqA_PP (ha.mul hb) (hb.mul ha)]
  rfl

theorem eqA_id_PP {a : Nat} (ha : PP n w a) :
    eqA n (unpack n w a) (idA n) = Nat.beq a (pidn n w) := by
  rw [idA_eq ha.sz, eqA_PP ha (PP.id ha.sz)]

theorem powN4_PP {a : Nat} (ha : PP n w a) :
    powN n (unpack n w a) 4 = unpack n w (pow4 n w a) := by
  have hi := PP.id (n := n) (w := w) ha.sz
  change mulN n _ (mulN n _ (mulN n _ (mulN n _ (idA n)))) = _
  rw [idA_eq ha.sz, mulN_PP ha hi, mulN_PP ha (ha.mul hi), mulN_PP ha (ha.mul (ha.mul hi)),
    mulN_PP ha (ha.mul (ha.mul (ha.mul hi)))]
  rfl

theorem inLN_eq {N x : Nat} {T : Nat → Nat} (hx : PP n w x) (hT : ∀ i < N, PP n w (T i)) :
    inLN n ((List.range N).map fun i => unpack n w (T i)) (unpack n w x) = inL N T x := by
  rw [inLN_PP hx hT]
  unfold inL
  rw [strictB_eq', anyN_eq]

@[expose] noncomputable def cI (n w t a : Nat) : Bool :=
  CFSG.KLie.CT.andB (comm n w a t) (CFSG.KLie.CT.andB (Nat.beq (mul n w a a) (pidn n w)) (CFSG.KLie.CT.notB (Nat.beq a (pidn n w))))

theorem invCent_rec (n w t : Nat) (T : Nat → Nat) : ∀ N acc,
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => (fun a => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (a :: acc))
        (cI n w t a)) (T r)) N acc =
      ((List.range N).filter fun j => cI n w t (T j)).map T ++ acc
  | 0, acc => rfl
  | N + 1, acc => by
    change Bool.rec (motive := fun _ => List Nat) _ _ (cI n w t (T N)) = _
    rw [List.range_succ, List.filter_append]
    cases h : cI n w t (T N)
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ N acc = _
      rw [invCent_rec n w t T N acc]
      simp [h]
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ N (T N :: acc) = _
      rw [invCent_rec n w t T N (T N :: acc)]
      simp [h]

theorem invCent_eq (n w N : Nat) (T : Nat → Nat) (t : Nat) :
    invCent n w N T t = ((List.range N).filter fun j => cI n w t (T j)).map T :=
  (invCent_rec n w t T N []).trans (List.append_nil _)

theorem mem_invCent {N t a : Nat} {T : Nat → Nat} (hT : ∀ i < N, PP n w (T i))
    (ha : a ∈ invCent n w N T t) : PP n w a := by
  rw [invCent_eq] at ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
  exact hT j (List.mem_range.1 (List.mem_filter.1 hj).1)

theorem invCentN_eq {N t : Nat} {T : Nat → Nat} (hT : ∀ i < N, PP n w (T i)) (ht : PP n w t) :
    invCentN n ((List.range N).map fun i => unpack n w (T i)) (unpack n w t) =
      (invCent n w N T t).map (unpack n w) := by
  unfold invCentN
  rw [invCent_eq, List.filter_map, List.map_map]
  change List.map (fun i => unpack n w (T i)) _ = List.map (fun i => unpack n w (T i)) _
  congr 1
  apply List.filter_congr
  intro j hj
  have ha := hT j (List.mem_range.1 hj)
  simp only [Function.comp_apply]
  rw [commN_PP ha ht, mulN_PP ha ha, eqA_id_PP (ha.mul ha), eqA_id_PP ha]
  unfold cI
  rw [andB_eq, andB_eq, notB_eq, Bool.and_assoc]
  rfl

theorem noE8N_eq {I : List Nat} (hI : ∀ a ∈ I, PP n w a) :
    noE8N n (I.map (unpack n w)) = noE8 n w I := by
  unfold noE8N noE8
  refine all_map_congr fun a ha => all_map_congr fun b hb => all_map_congr fun c hc => ?_
  have pa := hI a ha
  have pb := hI b hb
  have pc := hI c hc
  rw [commN_PP pa pb, commN_PP pa pc, commN_PP pb pc, eqA_PP pb pa, eqA_PP pc pa, eqA_PP pc pb,
    mulN_PP pa pb, eqA_PP pc (pa.mul pb)]
  simp only [orB_eq, andB_eq, notB_eq, Bool.and_assoc, Bool.or_assoc]
  rfl

theorem pgC_eq (t x : Nat) : pgC n w t x = (unpack n w t)[x]! := by
  rw [unpack_getElem!]
  unfold pgC
  cases h : Nat.blt x n
  · have : ¬ x < n := fun h' => by rw [Nat.blt_eq.mpr h'] at h; cases h
    simp [this]
  · simp [Nat.blt_eq.mp h]

end CFSG.KC.HexaK

end
