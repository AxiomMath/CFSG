module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Subgroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.ClosureInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.SetStabilizerPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Injective

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem eq_of_idx_eq
    {g h : Q3}
    (hgh : ∀ i < 920808, idx 920808 g i = idx 920808 h i) : g = h := by
  apply rho_injective
  ext p
  have := hgh p.val p.isLt
  rw [idx_of_lt _ p.isLt, idx_of_lt _ p.isLt, smul_def, smul_def] at this
  exact this

theorem epsElt_mul_self
    (j : Fin 11) :
    epsElt j * epsElt j = 1 := by
  apply eq_of_idx_eq
  intro i hi
  have hinv : invoOK degree objTabs[epsReg j.val]! = true := by
    have := objFacts.epsInv
    simp only [epsInvOK] at this
    exact allIn_zero_iff.1 this j.val j.isLt
  have h := idx_sq_of_invoOK (rep_epsElt j) hinv i hi
  rw [pow_two] at h
  rw [h, idx_one]

theorem idx_mul_of_rep {g h : Q3} {P Q : Table}
    (hg : Rep 920808 P g) (hh : Rep 920808 Q h) {k : ℕ} (hk : k < 920808) :
    idx 920808 (g * h) k = ap P (ap Q k) := by
  rw [idx_mul, ← hh k hk, ← hg _ (by rw [hh k hk]; exact idx_lt h hk)]

theorem epsElt_comm_of_lt
    {i j : Fin 11} (h : j < i) :
    epsElt i * epsElt j = epsElt j * epsElt i := by
  apply eq_of_idx_eq
  intro k hk
  have hcomm : commOK objTabs[epsReg i.val]! objTabs[epsReg j.val]! = true := by
    have := objFacts.epsComm
    simp only [epsCommOK] at this
    exact allIn_zero_iff.1 (allIn_zero_iff.1 this i.val i.isLt) j.val h
  have hk' := allIn_zero_iff.1 hcomm k hk
  rw [beq_iff_eq] at hk'
  rw [idx_mul_of_rep (rep_epsElt i) (rep_epsElt j) hk,
    idx_mul_of_rep (rep_epsElt j) (rep_epsElt i) hk]
  exact hk'

theorem epsElt_comm
    (i j : Fin 11) :
    epsElt i * epsElt j = epsElt j * epsElt i := by
  rcases lt_trichotomy i j with h | h | h
  · exact (epsElt_comm_of_lt h).symm
  · rw [h]
  · exact epsElt_comm_of_lt h

theorem finite_and_card_E0_le :
    Finite E0 ∧ Nat.card E0 ≤ 2 ^ 11 :=
  finite_and_card_closure_range_le epsElt epsElt_mul_self epsElt_comm

structure EpsPairTreeFacts (tabs : Array Table) (T : PairTree) (p q m : ℕ) : Prop where
  size_pos : 0 < m
  root : T.xs[0]! = p ∧ T.ys[0]! = q
  lt : ∀ k < m, T.xs[k]! < degree ∧ T.ys[k]! < degree
  edge : ∀ k, 0 < k → k < m → T.par[k]! < k ∧ T.lab[k]! < 11 ∧
    T.xs[k]! = ap tabs[epsReg T.lab[k]!]! T.xs[T.par[k]!]! ∧
    T.ys[k]! = ap tabs[epsReg T.lab[k]!]! T.ys[T.par[k]!]!
  distinct : ∀ i < m, ∀ j < i, T.xs[i]! ≠ T.xs[j]! ∨ T.ys[i]! ≠ T.ys[j]!

theorem EpsPairTreeFacts.of_pairTreeOK {tabs : Array Table} {T : PairTree} {p q m : ℕ}
    (h : pairTreeOK tabs T p q m = true) : EpsPairTreeFacts tabs T p q m := by
  unfold pairTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, -, hm, hx, hy, hlt, hedge, hdist⟩ := h
  refine ⟨hm, ⟨hx, hy⟩, fun k hk => ?_, fun k hk0 hk => ?_, fun i hi j hj => ?_⟩
  · have := allIn_zero_iff.1 hlt k hk
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  · have := allIn_one_iff.1 hedge k hk0 hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := allIn_zero_iff.1 (allIn_zero_iff.1 hdist i hi) j hj
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    exact this

theorem exists_mem_E0_of_facts
    {T : PairTree} {p q m : ℕ} (hT : EpsPairTreeFacts objTabs T p q m) :
    ∀ k < m, ∃ g ∈ E0, idx 920808 g p = T.xs[k]! ∧ idx 920808 g q = T.ys[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨1, E0.one_mem, by rw [idx_one, hT.root.1], by rw [idx_one, hT.root.2]⟩
    · obtain ⟨hpar, hlab, hx, hy⟩ := hT.edge k hk0 hk
      obtain ⟨g, hgE, hg1, hg2⟩ := ih _ hpar (hpar.trans hk)
      have hltp := hT.lt _ (hpar.trans hk)
      let j : Fin 11 := ⟨T.lab[k]!, hlab⟩
      refine ⟨epsElt j * g, E0.mul_mem (epsElt_mem_E0 j) hgE, ?_, ?_⟩
      · rw [idx_mul, hg1, hx, ← rep_epsElt j _ hltp.1]
      · rw [idx_mul, hg2, hy, ← rep_epsElt j _ hltp.2]

theorem two_pow_le_card_E0 :
    2 ^ 11 ≤ Nat.card E0 := by
  haveI : Finite E0 := finite_and_card_E0_le.1
  have hT : EpsPairTreeFacts objTabs (epsTreeData objTabs 3 6) 3 6 2048 :=
    EpsPairTreeFacts.of_pairTreeOK objFacts.epsTree
  have hex := exists_mem_E0_of_facts hT
  choose! g hgE hg3 hg6 using hex
  have hinj : Function.Injective (fun k : Fin 2048 => (⟨g k.val, hgE k.val k.isLt⟩ : E0)) := by
    intro a b hab
    have hab' : g a.val = g b.val := congrArg Subtype.val hab
    by_contra hne
    have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
    have key : ∀ i j : ℕ, i < 2048 → j < i → g i = g j → False := by
      intro i j hi hj hij
      have h1 := hT.distinct i hi j hj
      rw [← hg3 i hi, ← hg6 i hi, ← hg3 j (hj.trans hi), ← hg6 j (hj.trans hi), hij] at h1
      simp at h1
    rcases lt_or_gt_of_ne hne' with h | h
    · exact key b.val a.val b.isLt h hab'.symm
    · exact key a.val b.val a.isLt h hab'
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem card_E0 :
    Nat.card E0 = 2 ^ 11 :=
  le_antisymm finite_and_card_E0_le.2 two_pow_le_card_E0

theorem card_Ze :
    Nat.card Ze = 2 * Nat.card L0 := by
  have h := card_stabilizer_pair x0_ne_x1 tauElt tauElt_smul_x0 tauElt_smul_x1
  have hL : MulAction.stabilizer Q3 x0 ⊓ MulAction.stabilizer Q3 x1 = L0 := by
    unfold L0
    rw [Zp_eq_stabilizer]
  rw [hL] at h
  exact h

theorem mem_zpLetters_iff {l : ℕ} : l ∈ zpLetters ↔ l ∈ S0 := by
  simp [zpLetters, S0]

theorem lettersGroup_zpLetters : CFSG.Perm.lettersGroup zpLetters genQ = Zp := by
  unfold CFSG.Perm.lettersGroup
  congr 1
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hl' := mem_zpLetters_iff.1 hl
    have hlt : l < nG := by simp [S0] at hl'; unfold nG; omega
    refine ⟨⟨l, hlt⟩, mem_subsetOf_iff.2 hl', ?_⟩
    exact (genQ_of ⟨l, hlt⟩).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, mem_zpLetters_iff.2 (mem_subsetOf_iff.1 hx), genQ_of x⟩

theorem card_orbit_Zp_x1 :
    Nat.card (MulAction.orbit Zp x1) = 31671 := by
  have hz := objFacts.zpTree
  unfold zpTreeOK at hz
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  obtain ⟨hsize, hok⟩ := hz
  have hrep : ∀ l ∈ zpLetters, Rep 920808 (genTabs ())[l]! (genQ l) := by
    intro l hl
    have hl' := mem_zpLetters_iff.1 hl
    exact rep_genQ (by simp [S0] at hl'; omega)
  have hTF := CFSG.Perm.treeOK_facts (n := 920808) hrep hok
  have hcard := hTF.card_orbit
  rw [hsize, lettersGroup_zpLetters] at hcard
  exact hcard

theorem card_L0 :
    Nat.card L0 * 31671 = Nat.card Zp := by
  have h := Subgroup.relIndex_mul_card (H := MulAction.stabilizer Q3 x1) (K := Zp)
  rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq, card_orbit_Zp_x1, inf_comm] at h
  have hL : Nat.card L0 = Nat.card ↥(Zp ⊓ MulAction.stabilizer Q3 x1) := rfl
  rw [hL, Nat.mul_comm]
  exact h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
