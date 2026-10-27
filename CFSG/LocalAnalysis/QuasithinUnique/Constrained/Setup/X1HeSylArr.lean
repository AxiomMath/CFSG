module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylow

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Defs

@[expose] def sylInv (n N : ℕ) (Al : Array (Array ℕ)) : List ℕ :=
  (List.range N).filter fun i =>
    !eqA n Al[i]! (idA n) && eqA n (compA n Al[i]! Al[i]!) (idA n)

@[expose] def sylPairs (n : ℕ) (Al : Array (Array ℕ)) (inv : List ℕ) : List (ℕ × ℕ) :=
  inv.flatMap fun i => (inv.filter fun j => i != j &&
    eqA n (compA n Al[i]! Al[j]!) (compA n Al[j]! Al[i]!)).map fun j => (i, j)

@[expose] def sylVerify (n N : ℕ) (gens : List PArr) (par lab tab : List ℕ)
    (Al : Array (Array ℕ)) (r : ℕ) : Bool :=
  let ng := gens.length
  decide (Al.size = N) && decide (0 < N) && eqA n Al[0]! (idA n) &&
  allLt N (fun k => k == 0 || (decide (par.getD k 0 < k) && decide (lab.getD k 0 < ng) &&
    eqA n Al[k]! (compA n Al[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1))) &&
  allLt N (fun i => allLt ng (fun j =>
    decide (tab.getD (i * ng + j) 0 < N) &&
    eqA n (compA n Al[i]! (gens.getD j (pId n)).1) Al[tab.getD (i * ng + j) 0]!)) &&
  allLt N (fun i => isInvA n Al[i]! (invCand n Al[i]!)) &&
  allLt N (fun i => allLt i (fun j => !eqA n Al[i]! Al[j]!)) &&
  decide ((sylPairs n Al (sylInv n N Al)).length < (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2))

@[expose] def sylBuild (n N : ℕ) (gens : List PArr) (par lab : List ℕ) : Array (Array ℕ) :=
  (List.range N).foldl (fun acc k => acc.push (if k = 0 then idA n else
    compA n acc[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1)) #[]

@[expose] def parseNats (s : String) : List ℕ := (s.splitOn " ").filterMap String.toNat?

end Defs

section Sound

variable {n : ℕ}

theorem RegIn.getD {K : Subgroup (Equiv.Perm (Fin n))} {regs : List PArr} (h : RegIn n K regs)
    (j : ℕ) : ∃ g ∈ K, PRep n (regs.getD j (pId n)) g := by
  by_cases hj : j < regs.length
  · rw [List.getD_eq_getElem regs (pId n) hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨1, K.one_mem, pRep_id⟩

theorem mem_sylInv {N : ℕ} {Al : Array (Array ℕ)} {i : ℕ} :
    i ∈ sylInv n N Al ↔ i < N ∧ ¬ eqA n Al[i]! (idA n) = true ∧
      eqA n (compA n Al[i]! Al[i]!) (idA n) = true := by
  simp [sylInv, List.mem_filter, List.mem_range]

theorem mem_sylPairs {Al : Array (Array ℕ)} {inv : List ℕ} {i j : ℕ} :
    (i, j) ∈ sylPairs n Al inv ↔ i ∈ inv ∧ j ∈ inv ∧ i ≠ j ∧
      eqA n (compA n Al[i]! Al[j]!) (compA n Al[j]! Al[i]!) = true := by
  simp only [sylPairs, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    bne_iff_ne, ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', ⟨hj', hne, hc⟩, rfl, rfl⟩
    exact ⟨hi', hj', hne, hc⟩
  · rintro ⟨hi, hj, hne, hc⟩
    exact ⟨i, hi, j, ⟨hj, hne, hc⟩, rfl, rfl⟩

theorem sylVerify_sound {N a m : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} (hN : N = 2 ^ a)
    (hH : Nat.card H = 2 ^ a * m) (hm : Odd m) {gens : List PArr} (hgens : RegIn n H gens)
    {par lab tab : List ℕ} {Al : Array (Array ℕ)} {r : ℕ}
    (hv : sylVerify n N gens par lab tab Al r = true) :
    ∀ B : Subgroup H, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  classical
  simp only [sylVerify, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨hsz, hN0⟩, h0⟩, hpar⟩, htab⟩, hinv⟩, hnd⟩, hcnt⟩ := hv
  have hgj : ∀ j : ℕ, ∃ g ∈ H, PRep n (gens.getD j (pId n)) g := fun j => hgens.getD j
  choose gp hgpH hgpRep using hgj
  set E : ℕ → Equiv.Perm (Fin n) := fun k => permOfArr n Al[k]! with hE
  have hrep : ∀ k < N, Rep n Al[k]! (E k) := fun k hk => (rep_permOfArr (hinv k hk)).1
  have hE0 : E 0 = 1 := (eqA_iff (hrep 0 hN0) rep_idA).1 h0
  have hstep : ∀ k < N, k ≠ 0 → par.getD k 0 < k ∧ lab.getD k 0 < gens.length ∧
      E k = E (par.getD k 0) * gp (lab.getD k 0) := by
    intro k hk hk0
    have h := hpar k hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hp, hl⟩, he⟩
    · exact absurd h hk0
    · refine ⟨hp, hl, ?_⟩
      have hr2 : Rep n (compA n Al[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1)
          (E (par.getD k 0) * gp (lab.getD k 0)) :=
        rep_compA (hrep _ (hp.trans hk)) (hgpRep _).1
      exact (eqA_iff (hrep k hk) hr2).1 he
  have htabE : ∀ i < N, ∀ j < gens.length, ∃ k < N, E i * gp j = E k := by
    intro i hi j hj
    obtain ⟨hk, he⟩ := htab i hi j hj
    refine ⟨tab.getD (i * gens.length + j) 0, hk, ?_⟩
    have hr2 : Rep n (compA n Al[i]! (gens.getD j (pId n)).1) (E i * gp j) :=
      rep_compA (hrep i hi) (hgpRep j).1
    exact ((eqA_iff hr2 (hrep _ hk)).1 he)
  set rg : List (Equiv.Perm (Fin n)) := (List.range gens.length).map gp with hrg
  have hrgmem : ∀ g ∈ rg, g ∈ H := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact hgpH j
  have hEclos : ∀ k < N, E k ∈ Subgroup.closure {g | g ∈ rg} := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [hE0]
        exact Subgroup.one_mem _
      · obtain ⟨hp, hl, he⟩ := hstep k hk hk0
        rw [he]
        refine Subgroup.mul_mem _ (ih _ hp (hp.trans hk)) (Subgroup.subset_closure ?_)
        exact List.mem_map.2 ⟨_, List.mem_range.2 hl, rfl⟩
  have hEH : ∀ k < N, E k ∈ H := by
    intro k hk
    have : Subgroup.closure {g | g ∈ rg} ≤ H :=
      (Subgroup.closure_le H).2 fun g hg => hrgmem g hg
    exact this (hEclos k hk)
  have hinjE : ∀ i < N, ∀ j < N, E i = E j → i = j := by
    intro i hi j hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h := hnd j hj i hlt
      have hEq : eqA n Al[j]! Al[i]! = true := (eqA_iff (hrep j hj) (hrep i hi)).2 hij.symm
      rw [hEq] at h
      exact absurd h (by simp)
    · have h := hnd i hi j hlt
      have hEq : eqA n Al[i]! Al[j]! = true := (eqA_iff (hrep i hi) (hrep j hj)).2 hij
      rw [hEq] at h
      exact absurd h (by simp)
  obtain ⟨U0, hU0⟩ := exists_subgroup_of_gens rg ((List.range N).map E)
    (List.mem_map.2 ⟨0, List.mem_range.2 hN0, hE0⟩)
    (by
      intro x hx g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, hk, hik⟩ := htabE i (List.mem_range.1 hi) j (List.mem_range.1 hj)
      exact List.mem_map.2 ⟨k, List.mem_range.2 hk, hik.symm⟩)
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hEclos i (List.mem_range.1 hi))
  set E' : ℕ → ↥H := fun k => if h : E k ∈ H then ⟨E k, h⟩ else 1 with hE'
  have hE'val : ∀ k < N, ((E' k : ↥H) : Equiv.Perm (Fin n)) = E k := by
    intro k hk
    simp only [hE']
    split_ifs with h
    · rfl
    · exact absurd (hEH k hk) h
  subst hN
  have hinj' : ∀ i < 2 ^ a, ∀ j < 2 ^ a, E' i = E' j → i = j := by
    intro i hi j hj h
    refine hinjE i hi j hj ?_
    have := congrArg Subtype.val h
    rwa [hE'val i hi, hE'val j hj] at this
  have hU' : ∃ U : Subgroup ↥H, ∀ x, x ∈ U ↔ ∃ i < 2 ^ a, x = E' i := by
    refine ⟨U0.subgroupOf H, fun x => ?_⟩
    rw [Subgroup.mem_subgroupOf, hU0]
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := List.mem_map.1 hx
      refine ⟨i, List.mem_range.1 hi, Subtype.ext ?_⟩
      rw [hE'val i (List.mem_range.1 hi)]
      exact hix.symm
    · rintro ⟨i, hi, rfl⟩
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, (hE'val i hi).symm⟩
  have hpl' : ∀ i < 2 ^ a, ∀ j < 2 ^ a, E' i ≠ 1 → E' i * E' i = 1 → E' j ≠ 1 → E' j * E' j = 1 →
      i ≠ j → E' i * E' j = E' j * E' i →
      (i, j) ∈ sylPairs n Al (sylInv n (2 ^ a) Al) := by
    intro i hi j hj hi1 hi2 hj1 hj2 hij hc
    have hcoe : ∀ x y : ↥H, ((x * y : ↥H) : Equiv.Perm (Fin n)) = (x : Equiv.Perm (Fin n)) * y :=
      fun x y => rfl
    have hi1' : E i ≠ 1 := fun h => hi1 (Subtype.ext (by rw [hE'val i hi, h]; rfl))
    have hj1' : E j ≠ 1 := fun h => hj1 (Subtype.ext (by rw [hE'val j hj, h]; rfl))
    have hi2' : E i * E i = 1 := by
      have := congrArg Subtype.val hi2
      rwa [hcoe, hE'val i hi] at this
    have hj2' : E j * E j = 1 := by
      have := congrArg Subtype.val hj2
      rwa [hcoe, hE'val j hj] at this
    have hc' : E i * E j = E j * E i := by
      have := congrArg Subtype.val hc
      rwa [hcoe, hcoe, hE'val i hi, hE'val j hj] at this
    have hmemInv : ∀ k < 2 ^ a, E k ≠ 1 → E k * E k = 1 → k ∈ sylInv n (2 ^ a) Al := by
      intro k hk hk1 hk2
      rw [mem_sylInv]
      refine ⟨hk, fun h => hk1 ((eqA_iff (hrep k hk) rep_idA).1 h), ?_⟩
      exact (eqA_iff (rep_compA (hrep k hk) (hrep k hk)) rep_idA).2 hk2
    rw [mem_sylPairs]
    refine ⟨hmemInv i hi hi1' hi2', hmemInv j hj hj1' hj2', hij, ?_⟩
    exact (eqA_iff (rep_compA (hrep i hi) (hrep j hj)) (rep_compA (hrep j hj) (hrep i hi))).2 hc'
  exact card_le_of_sylow_idx hH hm E' hinj' hU' _ hpl' r hcnt

end Sound

end CFSG.QuasithinUnique.Setup.X1
