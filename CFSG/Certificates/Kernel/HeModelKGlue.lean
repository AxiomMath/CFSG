module

public import Certificates.Data.Kernel.HeModelK
public import CFSG.Certificates.Kernel.HexaKGlue
public import CFSG.Certificates.Kernel.HeAutKLoops
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsTests

public section

namespace CFSG.KC.HeModelK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.HeTri
open CFSG.KLie.CT (anyN andB orB notB)

theorem all_map_intro {α : Type} {N : Nat} {f : Nat → α} {p : α → Bool}
    (h : ∀ i < N, p (f i) = true) : ((List.range N).map f).all p = true :=
  List.all_eq_true.2 fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i (List.mem_range.1 hi)

theorem any_map_intro {α : Type} {N : Nat} {f : Nat → α} {p : α → Bool} {i : Nat} (hi : i < N)
    (h : p (f i) = true) : ((List.range N).map f).any p = true :=
  List.any_eq_true.2 ⟨f i, List.mem_map_of_mem (List.mem_range.2 hi), h⟩

theorem all_map_allN {α : Type} {N : Nat} {f : Nat → α} {p : α → Bool} {q : Nat → Bool}
    (h : ∀ i < N, p (f i) = q i) (hq : allN N q = true) : ((List.range N).map f).all p = true :=
  all_map_intro fun i hi => (h i hi).trans (allN_spec hq i hi)

theorem allN_and {N : Nat} {a b : Nat → Bool} (h : allN N (fun j => a j && b j) = true) :
    allN N a = true ∧ allN N b = true := by
  have h' : ∀ i < N, a i = true ∧ b i = true := fun i hi => by
    have e := allN_spec h i hi
    rwa [Bool.and_eq_true] at e
  rw [allN_eq', allN_eq']
  exact ⟨List.all_eq_true.2 fun i hi => (h' i (List.mem_range.1 hi)).1,
    List.all_eq_true.2 fun i hi => (h' i (List.mem_range.1 hi)).2⟩

theorem anyN_spec {N : Nat} {f : Nat → Bool} (h : anyN N f = true) : ∃ i < N, f i = true := by
  rw [anyN_eq] at h
  obtain ⟨i, hi, e⟩ := List.any_eq_true.1 h
  exact ⟨i, List.mem_range.1 hi, e⟩

theorem any_map_anyN {α : Type} {N : Nat} {f : Nat → α} {p : α → Bool} {q : Nat → Bool}
    (h : ∀ i < N, p (f i) = q i) (hq : anyN N q = true) : ((List.range N).map f).any p = true := by
  obtain ⟨i, hi, e⟩ := anyN_spec hq
  exact any_map_intro hi ((h i hi).trans e)

theorem filter_map_length {α : Type} {N : Nat} {f : Nat → α} {p : α → Bool} {q : Nat → Bool}
    (h : ∀ i < N, p (f i) = q i) :
    (((List.range N).map f).filter p).length = ((List.range N).filter q).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  exact List.filter_congr fun i hi => h i (List.mem_range.1 hi)

theorem length_filter_range_succ (N : Nat) (p : Nat → Bool) :
    ((List.range (N + 1)).filter p).length =
      ((List.range N).filter p).length + Bool.rec (motive := fun _ => Nat) 0 1 (p N) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : p N <;> simp [h]

theorem cntR_eq (f : Nat → Bool) (lo : Nat) : ∀ N,
    cntR f lo N = ((List.range N).filter fun j => f (lo + j)).length
  | 0 => rfl
  | N + 1 => by
    rw [cntR_succ, cntR_eq f lo N, length_filter_range_succ]

theorem cntR_zero (f : Nat → Bool) (N : Nat) : cntR f 0 N = ((List.range N).filter f).length := by
  rw [cntR_eq]
  simp only [Nat.zero_add]

theorem allR_spec {f : Nat → Bool} {lo : Nat} : ∀ {N : Nat}, allR f lo N = true →
    ∀ i < N, f (lo + i) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | N + 1, h, i, hi => by
    have e : allR f lo (N + 1) = (allR f lo N && f (lo + N)) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allR_spec h.1 i hi
    · exact h.2

theorem eqB_true {a b : Bool} (h : eqB a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

variable {n w : Nat}

theorem mul_eq' (a b : Nat) : mul n w a b = pcomp n w (mask w) a b := rfl

theorem inv_eq' (a : Nat) : inv n w a = pinvS n w (mask w) a := rfl

theorem all_commN_eq {g x : Nat} {G : Nat → Nat} (hx : PP n w x) (hG : ∀ j < g, PP n w (G j)) :
    ((List.range g).map fun j => unpack n w (G j)).all (commN n (unpack n w x)) =
      allN g fun j => comm n w x (G j) := by
  rw [allN_eq']
  exact all_map_congr fun j hj => commN_PP hx (hG j (List.mem_range.1 hj))

theorem _root_.CFSG.KC.BfsPin.PP.pwK {a : Nat} (ha : PP n w a) : ∀ k, PP n w (pw n w a k)
  | 0 => PP.id ha.sz
  | k + 1 => by
    change PP n w (strictN (pw n w a k) fun acc => mul n w a acc)
    rw [strictN_eq']
    exact ha.mul (ha.pwK k)

theorem powN_PP {a : Nat} (ha : PP n w a) : ∀ k,
    powN n (unpack n w a) k = unpack n w (pw n w a k)
  | 0 => idA_eq ha.sz
  | k + 1 => by
    change mulN n (unpack n w a) (powN n (unpack n w a) k) =
      unpack n w (strictN (pw n w a k) fun acc => mul n w a acc)
    rw [strictN_eq', powN_PP ha k, mulN_PP ha (ha.pwK k)]
    rfl

theorem normsN_eq {NF g x : Nat} {TF GF : Nat → Nat} (hF : ∀ i < NF, PP n w (TF i))
    (hG : ∀ k < g, PP n w (GF k)) (hx : PP n w x) :
    normsN n ((List.range NF).map fun i => unpack n w (TF i))
      ((List.range g).map fun k => unpack n w (GF k)) (unpack n w x) = normsK n w NF TF g GF x := by
  unfold normsN normsK
  rw [allN_eq']
  refine all_map_congr fun k hk => ?_
  have pk := hG k (List.mem_range.1 hk)
  rw [conjA_PP hx pk, inLN_eq (hx.conjK pk) hF]

theorem shl1 (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := (Nat.shiftLeft_eq 1 k).trans (Nat.one_mul _)

theorem stabW_eq {k : Nat} (hk : 2 ^ k ≤ 32) (x : Nat) :
    stabW k (unpack 32 w x) = stabWK w k x := by
  unfold stabW stabWK
  rw [allN_eq', shl1]
  refine all_congr_mem fun v hv => ?_
  have hv' := List.mem_range.1 hv
  rw [unpack_getElem!, ite_eq_left (by omega), blt_eq_decide]

theorem unipW_eq {k : Nat} (hk : 2 ^ k ≤ 32) (x : Nat) :
    unipW k (unpack 32 w x) = unipWK w k x := by
  have e1 : ((List.range (2 ^ k)).all fun v => (unpack 32 w x)[v]! == v) =
      (List.range (2 ^ k)).all fun v => Nat.beq (pg w (mask w) x v) v := by
    refine all_congr_mem fun v hv => ?_
    have hv' := List.mem_range.1 hv
    rw [unpack_getElem!, ite_eq_left (by omega), beq_nat]
  have e2 : ((List.range 32).all fun v => decide (Nat.xor (unpack 32 w x)[v]! v < 2 ^ k)) =
      (List.range 32).all fun v => Nat.blt (Nat.xor (pg w (mask w) x v) v) (2 ^ k) := by
    refine all_congr_mem fun v hv => ?_
    have hv' := List.mem_range.1 hv
    rw [unpack_getElem!, ite_eq_left hv', blt_eq_decide]
  unfold unipW unipWK
  rw [andB_eq, allN_eq', allN_eq', shl1, e1, e2]

theorem uniqEN_of {NX NE NF FB : Nat} {TX TE TF : Nat → Nat}
    (sX : ∀ i < NX, PP n w (TX i)) (sE : ∀ i < NE, PP n w (TE i)) (sF : ∀ i < NF, PP n w (TF i))
    (hf : flagsK n w NX TX (pidn n w) FB FB = true)
    (hu : allR (ueAt n w NX TX NE TE NF TF FB) 0 NX = true) :
    uniqEN n ((List.range NX).map fun i => unpack n w (TX i))
      ((List.range NE).map fun i => unpack n w (TE i))
      ((List.range NF).map fun i => unpack n w (TF i)) = true := by
  have hb : ∀ i < NX, bitK FB i = Nat.beq (mul n w (TX i) (TX i)) (pidn n w) := by
    intro i hi
    have e := allN_spec hf i hi
    rw [strictB_eq', strictB_eq', andB_eq, Bool.and_eq_true] at e
    exact eqB_true e.2
  have hcnt : ∀ i < NX,
      (((List.range NX).map fun i => unpack n w (TX i)).filter fun y =>
        eqA n (mulN n y y) (idA n) && commN n (unpack n w (TX i)) y).length =
      cntR (fun j => CFSG.KLie.CT.andB (bitK FB j) (comm n w (TX i) (TX j))) 0 NX := by
    intro i hi
    rw [cntR_eq]
    simp only [Nat.zero_add]
    refine filter_map_length fun j hj => ?_
    have pj := sX j hj
    rw [mulN_PP pj pj, eqA_id_PP (pj.mul pj), commN_PP (sX i hi) pj, hb j hj, andB_eq]
    rfl
  unfold uniqEN
  refine all_map_intro fun i hi => ?_
  have pi := sX i hi
  have u := allR_spec hu i hi
  rw [Nat.zero_add] at u
  unfold ueAt at u
  rw [strictB_eq', hb i hi] at u
  rw [mulN_PP pi pi, eqA_id_PP (pi.mul pi), eqA_id_PP pi, inLN_eq pi sE, inLN_eq pi sF, hcnt i hi,
    ← blt_eq_decide]
  simp only [orB_eq, notB_eq, Bool.or_assoc] at u ⊢
  exact u

end CFSG.KC.HeModelK

end
