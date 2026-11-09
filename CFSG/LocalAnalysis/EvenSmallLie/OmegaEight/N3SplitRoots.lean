module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitFix

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] def filterFix (y : ℕ) (fix : List ℕ) : List ℕ :=
  if fix.length ≤ 24 then fix.filter fun v => mulVecK y v == v
  else
    let T := imgTab y 12
    fix.filter fun v => T.getD v 0 == v

theorem filterFix_eq {y : ℕ} {fix : List ℕ} (h : ∀ v ∈ fix, v < 4096) :
    filterFix y fix = fix.filter fun v => mulVecK y v == v := by
  unfold filterFix
  split_ifs
  · rfl
  · exact List.filter_congr fun v hv => by rw [imgTab_getD y 12 v (h v hv)]

theorem lt_of_mem_filter {p : ℕ → Bool} {fix : List ℕ} (h : ∀ v ∈ fix, v < 4096) :
    ∀ v ∈ fix.filter p, v < 4096 := fun v hv => h v (List.mem_filter.1 hv).1

@[expose] def nodeF (B : ℕ) : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, span, fix, rest =>
    decide (span.length * fix.length ≤ B) &&
      rest.tails.all fun
        | [] => true
        | y :: ys => !(newGen span y) ||
          nodeF B fuel (span ++ span.map (mulK y)) (filterFix y fix)
            (ys.filter fun z => mulK y z == mulK z y)

theorem nodeF_eq (B : ℕ) : ∀ (fuel : ℕ) (span fix rest : List ℕ), (∀ v ∈ fix, v < 4096) →
    nodeF B fuel span fix rest = node B fuel span fix rest
  | 0, _, _, _, _ => rfl
  | fuel + 1, span, fix, rest, h => by
    rw [nodeF, node]
    congr 1
    refine congrArg (rest.tails.all ·) (funext fun l => ?_)
    rcases l with _ | ⟨y, ys⟩
    · rfl
    · simp only
      rw [filterFix_eq h, nodeF_eq B fuel _ _ _ (lt_of_mem_filter h)]

@[expose] def rootCheckF (B r : ℕ) (C base : List ℕ) : Bool :=
  nodeF B 8 [idK, r] (filterFix r base) C

@[expose] def allRootsF (B : ℕ) (I base : List ℕ) : Bool :=
  I.all fun r => rootCheckF B r (commOf I r) base

theorem allRootsF_eq {B : ℕ} {I base : List ℕ} (h : ∀ v ∈ base, v < 4096) :
    allRootsF B I base = allRoots B I base := by
  unfold allRootsF allRoots
  refine congrArg (I.all ·) (funext fun r => ?_)
  rw [rootCheckF, rootCheck, filterFix_eq h, nodeF_eq B 8 _ _ _ (lt_of_mem_filter h)]

theorem lt_of_mem_range {v : ℕ} (hv : v ∈ List.range 4096) : v < 4096 := List.mem_range.1 hv

@[expose] def commAbove (I : List ℕ) (r : ℕ) : List ℕ :=
  I.filter fun z => decide (r < z) && mulK z r == mulK r z

@[expose] def allRootsMin (B : ℕ) (I base : List ℕ) : Bool :=
  I.all fun r => rootCheck B r (commAbove I r) base

@[expose] def allRootsMinF (B : ℕ) (I base : List ℕ) : Bool :=
  I.all fun r => rootCheckF B r (commAbove I r) base

theorem allRootsMinF_eq {B : ℕ} {I base : List ℕ} (h : ∀ v ∈ base, v < 4096) :
    allRootsMinF B I base = allRootsMin B I base := by
  unfold allRootsMinF allRootsMin
  refine congrArg (I.all ·) (funext fun r => ?_)
  rw [rootCheckF, rootCheck, filterFix_eq h, nodeF_eq B 8 _ _ _ (lt_of_mem_filter h)]

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem offender_bound_min {gs : Array (ℕ × ℕ)} {E : Enum} (h : enumOK gs E = true)
    {B : ℕ} {base : List ℕ} {Z : Set Vec12} (hbase : ∀ v < 4096, toVec 12 v ∈ Z → v ∈ base)
    (hchk : allRootsMin B (invsOf E.keys) base = true) {A : Subgroup GL12} (hA : A ≤ grpOf gs)
    (hsq : ∀ a ∈ A, a * a = 1) (hne : A ≠ ⊥) : Nat.card A * Nat.card ↥(Z ∩ fixV A) ≤ B := by
  classical
  have hsorted := pairwise_of_sortedK (Enum.of_enumOK h).2.1
  have hinv : ∀ z ∈ A, z ≠ 1 → ∃ t ∈ invsOf E.keys, Rep t z := by
    intro z hz hz1
    obtain ⟨i, hi, hrep⟩ := Enum.exists_key h (hA hz)
    refine ⟨E.keys.getD i 0, List.mem_filter.2 ⟨mem_toList_of_lt hi, ?_⟩, hrep⟩
    have h1 : E.keys.getD i 0 ≠ idK := fun e => hz1 (hrep.unique (e ▸ rep_one))
    have h2 : mulK (E.keys.getD i 0) (E.keys.getD i 0) = idK :=
      (hrep.mul hrep).key_unique (by rw [hsq z hz]; exact rep_one) (mulK_lt _ _) idK_lt
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    exact ⟨h1, h2⟩
  have hlt : ∀ t ∈ invsOf E.keys, t < 2 ^ 144 := by
    intro t ht
    obtain ⟨ht1, -⟩ := List.mem_filter.1 ht
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem ht1
    simp only [Array.getElem_toList, Array.length_toList] at e hi
    rw [← e]
    have := Enum.key_lt h hi
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this
  have hex : ∃ R, R ∈ invsOf E.keys ∧ ∃ z ∈ A, Rep R z := by
    obtain ⟨⟨r, hrA⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    obtain ⟨R, hRI, hR⟩ := hinv r hrA (by simpa using hr1)
    exact ⟨R, hRI, r, hrA, hR⟩
  obtain ⟨hRI, r, hrA, hR⟩ := Nat.find_spec hex
  have hall := hchk
  simp only [allRootsMin, List.all_eq_true] at hall
  refine bound_of_rootCheck hsq hR hrA (fun z hz hz1 hzr => ?_) ?_
    (fun t ht => hlt t (List.mem_filter.1 ht).1) hbase (hall _ hRI)
  · obtain ⟨t, htI, hrt⟩ := hinv z hz hz1
    refine ⟨t, List.mem_filter.2 ⟨htI, ?_⟩, hrt⟩
    have h1 : t ≠ Nat.find hex := fun e => hzr (hrt.unique (e ▸ hR))
    have h0 : Nat.find hex ≤ t := Nat.find_min' hex ⟨htI, z, hz, hrt⟩
    have hcomm := commute_of_sq hsq hz hrA
    have h2 : mulK t (Nat.find hex) = mulK (Nat.find hex) t :=
      (hrt.mul hR).key_unique (by rw [hcomm]; exact hR.mul hrt) (mulK_lt _ _) (mulK_lt _ _)
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨lt_of_le_of_ne h0 (Ne.symm h1), h2⟩
  · exact (hsorted.filter _).filter _

end CFSG.EvenSmallLie.OmegaEight.N3Split
