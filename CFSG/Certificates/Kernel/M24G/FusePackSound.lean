module

public import Certificates.Data.Kernel.M24G.FusePack
public import CFSG.Certificates.Kernel.M24G.KzeroSound
public import CFSG.Certificates.Kernel.M24G.BfsMapSound
import CFSG.Certificates.Kernel.M24G.BfsReplaySound
import CFSG.Certificates.Kernel.M24G.FixOctSound
import all CFSG.Certificates.Kernel.M24G.BfsFacts

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G CFSG.KC.ONanSmall

@[expose] def pkL : List Nat → Nat
  | [] => 0
  | a :: l => a + 32 * pkL l

theorem shift_or_eq (c : Nat) {x : Nat} (hx : x < 32) : (c <<< 5) ||| x = c * 32 + x := by
  have h32 : (2 : Nat) ^ 5 = 32 := rfl
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.lt_of_lt_of_le hx (by decide)), Nat.shiftLeft_eq, h32]

theorem foldl_rev : ∀ r : List Nat, (∀ x ∈ r, x < 32) →
    r.reverse.foldl (fun acc x => (acc <<< 5) ||| x) 0 = pkL r
  | [], _ => rfl
  | a :: r, h => by
    rw [List.reverse_cons, List.foldl_append,
      foldl_rev r (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.foldl_cons, List.foldl_nil,
      shift_or_eq _ (h a List.mem_cons_self), pkL]
    omega

theorem lane_pkL : ∀ r : List Nat, (∀ x ∈ r, x < 32) → ∀ k, pkL r / 32 ^ k % 32 = r.getD k 0
  | [], _, k => by simp [pkL]
  | a :: r, h, 0 => by
    have ha := h a List.mem_cons_self
    simp only [pkL, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | a :: r, h, k + 1 => by
    have ha := h a List.mem_cons_self
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, List.getD_cons_succ,
      ← lane_pkL r (fun x hx => h x (List.mem_cons_of_mem _ hx)) k]
    congr 2
    simp only [pkL]
    omega

theorem mulGoP_pkL (a : Nat) : ∀ r : List Nat, (∀ x ∈ r, x < 32) →
    mulGoP a r.length (pkL r) = pkL (r.map (laneP a))
  | [], _ => rfl
  | x :: r, h => by
    have hx := h x List.mem_cons_self
    have e1 : pkL (x :: r) / 32 = pkL r := by
      simp only [pkL]
      omega
    have e2 : pkL (x :: r) % 32 = x := by
      simp only [pkL]
      omega
    rw [List.length_cons, mulGoP, e1, e2,
      mulGoP_pkL a r (fun y hy => h y (List.mem_cons_of_mem _ hy)), List.map_cons, pkL]
    omega

theorem duadV_lt32 {t : Array Nat} (ht : DuadV t) : ∀ x ∈ t.toList, x < 32 :=
  fun x hx => Nat.lt_trans (ht.2 x hx) (by decide)

theorem key_pkL {t : Array Nat} (ht : DuadV t) : Native.kzeroKey t = pkL t.toList.reverse := by
  rw [kzeroKey_eq]
  unfold kzeroKeyF
  rw [if_pos ht.1, ← foldl_rev _ (fun x hx => duadV_lt32 ht x (List.mem_reverse.1 hx)),
    List.reverse_reverse]

theorem laneP_key {t : Array Nat} (ht : DuadV t) {j : Nat} (hj : j < 24) :
    laneP (Native.kzeroKey t) j = t.toList.getD j 0 := by
  have hlen : t.toList.length = 24 := by rw [Array.length_toList, ht.1]
  rw [key_pkL ht, laneP, lane_pkL _ (fun x hx => duadV_lt32 ht x (List.mem_reverse.1 hx)),
    duad_getD_lt _ _ (by rw [List.length_reverse, hlen]; omega), duad_getD_lt _ _ (by omega),
    List.getElem_reverse]
  congr 1
  omega

theorem kzeroKey_mul {a b : Array Nat} (ha : DuadV a) (hb : DuadV b) :
    Native.kzeroKey (Native.kzeroMul a b) = mulP (Native.kzeroKey a) (Native.kzeroKey b) := by
  have hlen : b.toList.length = 24 := by rw [Array.length_toList, hb.1]
  have hm : DuadV (mulTabF a b) := duadV_mulTabF ha b
  have hlist : (mulTabF a b).toList = b.toList.map fun j => a.toList.getD j 0 := by
    unfold mulTabF
    rw [List.toList_toArray]
    have e := congrArg (List.map fun j => a.toList.getD j 0) (duad_map_getD b.toList hlen)
    rw [List.map_map] at e
    exact e
  have hr : (b.toList.map fun j => a.toList.getD j 0).reverse =
      b.toList.reverse.map fun j => a.toList.getD j 0 := by simp
  have hg := mulGoP_pkL (Native.kzeroKey a) b.toList.reverse
    (fun x hx => duadV_lt32 hb x (List.mem_reverse.1 hx))
  rw [List.length_reverse, hlen] at hg
  rw [kzeroMul_eq, key_pkL hm, key_pkL hb, mulP, hg, hlist, hr]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact (laneP_key ha (hb.2 j (List.mem_reverse.1 hj))).symm

theorem duadV_conj {p : Array Nat × Array Nat} (h1 : DuadV p.1) (x : Array Nat) :
    DuadV (Native.kzeroConj p x) := by
  unfold Native.kzeroConj
  rw [kzeroMul_eq]
  exact duadV_mulTabF h1 _

theorem kzeroKey_conj {p : Array Nat × Array Nat} (h1 : DuadV p.1) (h2 : DuadV p.2)
    {x : Array Nat} (hx : DuadV x) :
    Native.kzeroKey (Native.kzeroConj p x) =
      conjP (Native.kzeroKey p.1, Native.kzeroKey p.2) (Native.kzeroKey x) := by
  have hm : DuadV (Native.kzeroMul x p.2) := by
    rw [kzeroMul_eq]
    exact duadV_mulTabF hx _
  unfold Native.kzeroConj conjP
  rw [kzeroKey_mul h1 hm, kzeroKey_mul hx h2]

theorem fusePairs_V : ∀ p ∈ Native.fusePairs (), DuadV p.1 ∧ DuadV p.2 := by
  have h : ∀ p ∈ Native.fusePairs (), (duadValidT p.1 && duadValidT p.2) = true := by decide
  intro p hp
  have hp' := h p hp
  rw [Bool.and_eq_true] at hp'
  exact ⟨duadV_of _ hp'.1, duadV_of _ hp'.2⟩

theorem fusePairsP_eq :
    (Native.fusePairs ()).map (fun p => (Native.kzeroKey p.1, Native.kzeroKey p.2)) =
      fusePairsP := by
  decide +kernel

theorem conjSteps_forall₂ : ∀ ps : List (Array Nat × Array Nat),
    (∀ p ∈ ps, DuadV p.1 ∧ DuadV p.2) →
    StepsRel Native.kzeroKey DuadV (Native.fuseConjSteps ps)
      ((ps.map (fun p => (Native.kzeroKey p.1, Native.kzeroKey p.2))).map conjP)
  | [], _ => by
    unfold Native.fuseConjSteps
    simp only [List.map_nil, StepsRel]
  | p :: ps, h => by
    have hp := h p List.mem_cons_self
    have ih := conjSteps_forall₂ ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    unfold Native.fuseConjSteps at ih ⊢
    simp only [List.map_cons, StepsRel]
    exact ⟨fun y hy => ⟨duadV_conj hp.1 y, kzeroKey_conj hp.1 hp.2 hy⟩, ih⟩

theorem fuseSteps_forall₂ :
    StepsRel Native.kzeroKey DuadV (Native.fuseConjSteps (Native.fusePairs ())) fuseStepsP := by
  unfold fuseStepsP
  rw [← fusePairsP_eq]
  exact conjSteps_forall₂ _ fusePairs_V

theorem fuseOrbit_map {x : Array Nat} (hx : DuadV x) :
    Native.bfs (fun c => c) fuseStepsP (Native.kzeroKey x) 32000 =
        ((Native.fuseOrbit x).1.map Native.kzeroKey, (Native.fuseOrbit x).2.1,
          (Native.fuseOrbit x).2.2) ∧
      ∀ y ∈ (Native.fuseOrbit x).1, DuadV y := by
  unfold Native.fuseOrbit
  exact bfsM24_map Native.kzeroKey DuadV rfl hx (fun _ _ => rfl) fuseSteps_forall₂ 32000

variable {x : Array Nat} {L : List Nat} {par gen : List Nat} {pos : KTree (Nat × Nat)}

theorem fuseOrbit_of_replay (hx : DuadV x)
    (h : replayOK (fun c => c) fuseStepsP (Native.kzeroKey x) 32000 L par gen pos = true) :
    (Native.fuseOrbit x).1.toList.map Native.kzeroKey = L ∧ (Native.fuseOrbit x).2.1 = par.toArray ∧
      (Native.fuseOrbit x).2.2 = gen.toArray ∧ ∀ y ∈ (Native.fuseOrbit x).1, DuadV y := by
  obtain ⟨e, hV⟩ := fuseOrbit_map hx
  rw [bfs_eq_of_replayOK h] at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  refine ⟨?_, e2.symm, e3.symm, hV⟩
  rw [← Array.toList_map, ← e1, List.toList_toArray]

theorem mem_fuseOrbit (hx : DuadV x)
    (h : replayOK (fun c => c) fuseStepsP (Native.kzeroKey x) 32000 L par gen pos = true)
    {t : Array Nat} (ht : DuadV t) : t ∈ (Native.fuseOrbit x).1.toList ↔ Native.kzeroKey t ∈ L := by
  obtain ⟨e1, -, -, hV⟩ := fuseOrbit_of_replay hx h
  rw [← e1, List.mem_map]
  constructor
  · intro hm
    exact ⟨t, hm, rfl⟩
  · rintro ⟨y, hy, e⟩
    rw [kzeroKey_eq] at e
    rwa [← kzeroKeyF_inj (hV y (Array.mem_toList_iff.1 hy)) ht e]

theorem fuseOrbit_treeValid (hx : DuadV x) :
    Native.treeValid Native.kzeroValid (Native.fuseConjSteps (Native.fusePairs ())) x
      (Native.fuseOrbit x) = true := by
  obtain ⟨-, hV⟩ := fuseOrbit_map hx
  have hT := bfs_tree Native.kzeroKey (Native.fuseConjSteps (Native.fusePairs ())) x 32000
  unfold Native.fuseOrbit at hV ⊢
  generalize Native.bfs Native.kzeroKey (Native.fuseConjSteps (Native.fusePairs ())) x 32000 = r
    at hV hT ⊢
  obtain ⟨A, P, G⟩ := r
  unfold TreeInv at hT
  obtain ⟨t1, t2, t3, t4, t5⟩ := hT
  dsimp only at hV t1 t2 t3 t4 t5
  unfold Native.treeValid Native.kzeroValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff', Bool.or_eq_true]
  refine ⟨⟨⟨⟨t3, t4⟩, t1⟩, t2⟩, fun j hj => ⟨?_, ?_⟩⟩
  · have hm : A[j]! ∈ A := by
      rw [getElem!_pos A j hj]
      exact Array.getElem_mem hj
    exact (hV _ hm).1
  · rcases Nat.eq_zero_or_pos j with rfl | hp0
    · exact Or.inl rfl
    · obtain ⟨u1, u2, u3⟩ := t5 j hp0 hj
      exact Or.inr ⟨⟨u1, u2⟩, u3⟩

end CFSG.KC.M24G
