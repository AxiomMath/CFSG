module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDel
public import Certificates.Certificate27823

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

@[expose] def omegaFin (j : ℕ) : Finset (Fin 128) := finOf omegaSets[j]!

@[expose] noncomputable def g0Perm (k : ℕ) : Equiv.Perm (Fin 128) := permOfArr 128 g0Gens[k]!

@[expose] noncomputable def G0 : Subgroup ↥Pg :=
  Subgroup.closure {x : ↥Pg | ∃ k < 3, (x : Equiv.Perm (Fin 128)) = g0Perm k}

@[expose] noncomputable def Stab0 : Subgroup ↥Pg := MulAction.stabilizer ↥Pg (omegaFin 0)


theorem surj_top : omegaClosed = true ∧ g0Check = true ∧ rootsArr.size = 10 ∧
    (List.range 10).all rootCheck = true := by
  have h := Certificates.certificate27823
  unfold surjCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨ho, hg, hr, -, -, hL⟩ := h
  exact ⟨ho, hg, hr, hL⟩

theorem omega_facts :
    (∀ j < 216, omegaSets[j]!.size = 8 ∧ ∀ x ∈ omegaSets[j]!, x < 128) ∧
    sameSet omegaSets[0]! #[0, 21, 32, 53, 64, 85, 96, 117] = true ∧
    (∀ gi < 36, ∀ j < 216, ∃ j' < 216,
      sameSet (imgSet sgsArr[gi]! omegaSets[j]!) omegaSets[j']! = true) := by
  have h := surj_top.1
  unfold omegaClosed at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, Array.all_eq_true_iff_forall_mem, and_assoc] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem omega_sz {j : ℕ} (hj : j < 216) : omegaSets[j]!.size = 8 := (omega_facts.1 j hj).1

theorem omega_lt {j : ℕ} (hj : j < 216) : ∀ x ∈ omegaSets[j]!, x < 128 := (omega_facts.1 j hj).2

theorem omega_lt0 : ∀ x ∈ omegaSets[0]!, x < 128 := omega_lt (by norm_num)

theorem g0_facts : g0Gens.size = 3 ∧
    (∀ k < 3, g0Gens[k]!.size = 128 ∧ isInvA 128 g0Gens[k]! (invCand 128 g0Gens[k]!) = true ∧
      inPg g0Gens[k]! = true ∧ sameSet (imgSet g0Gens[k]! omegaSets[0]!) omegaSets[0]! = true) ∧
    g0Par.size = 216 ∧
    (∀ j < 216, g0Par[j]!.1 = j ∨ (g0Par[j]!.1 < j ∧ g0Par[j]!.2 < 3 ∧
      sameSet (imgSet g0Gens[g0Par[j]!.2]! omegaSets[g0Par[j]!.1]!) omegaSets[j]! = true)) ∧
    (∀ j < 216, g0Par[j]!.1 = j → j ∈ rootsArr) := by
  have h := surj_top.2.1
  unfold g0Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, Array.contains_iff_mem, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun j hj hr => (h5 j hj).resolve_left (fun hne => hne hr)⟩

theorem g0_size : g0Gens.size = 3 := g0_facts.1

theorem rootsArr_size : rootsArr.size = 10 := surj_top.2.2.1

theorem rep_g0 {k : ℕ} (hk : k < 3) : Rep 128 g0Gens[k]! (g0Perm k) :=
  (rep_permOfArr (g0_facts.2.1 k hk).2.1).1

theorem g0Perm_mem {k : ℕ} (hk : k < 3) : g0Perm k ∈ Pg :=
  (inPg_iff (rep_g0 hk)).1 (g0_facts.2.1 k hk).2.2.1

theorem g0Perm_fix {k : ℕ} (hk : k < 3) : g0Perm k • omegaFin 0 = omegaFin 0 :=
  (smul_finOf_iff (rep_g0 hk) omega_lt0 omega_lt0 rfl).2 (g0_facts.2.1 k hk).2.2.2

theorem mem_omega0 (x : Fin 128) : x ∈ omegaFin 0 ↔ ((x : ℕ) = 0 ∨ (x : ℕ) = 21 ∨ (x : ℕ) = 32 ∨
    (x : ℕ) = 53 ∨ (x : ℕ) = 64 ∨ (x : ℕ) = 85 ∨ (x : ℕ) = 96 ∨ (x : ℕ) = 117) := by
  have h := (omega_facts).2.1
  rw [sameSet_iff] at h
  unfold omegaFin
  rw [mem_finOf]
  constructor
  · intro hx
    have := h.1 _ hx
    simpa using this
  · intro hx
    apply h.2.1
    rcases hx with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp [h1]

theorem g0Perm_mem_G0 {k : ℕ} (hk : k < 3) : (⟨g0Perm k, g0Perm_mem hk⟩ : ↥Pg) ∈ G0 :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem G0_le_Stab0 : G0 ≤ Stab0 := by
  unfold G0 Stab0
  rw [Subgroup.closure_le]
  rintro x ⟨k, hk, hx⟩
  show x ∈ MulAction.stabilizer ↥Pg (omegaFin 0)
  rw [MulAction.mem_stabilizer_iff]
  show (x : Equiv.Perm (Fin 128)) • omegaFin 0 = omegaFin 0
  rw [hx]
  exact g0Perm_fix hk

theorem rep_sgs {gi : ℕ} (hgi : gi < 36) : Rep 128 sgsArr[gi]! (permOfArr 128 sgsArr[gi]!) := by
  have hs : sgsArr.size = 36 := by decide
  exact (rep_permOfArr ((chainCheckFacts chain_check).strong_inv gi (hgi.trans_eq hs.symm))).1

theorem omega_gen_smul {gi : ℕ} (hgi : gi < 36) {j : ℕ} (hj : j < 216) :
    ∃ j' < 216, permOfArr 128 sgsArr[gi]! • omegaFin j = omegaFin j' := by
  obtain ⟨j', hj', h⟩ := omega_facts.2.2 gi hgi j hj
  exact ⟨j', hj', (smul_finOf_iff (rep_sgs hgi) (omega_lt hj) (omega_lt hj')
    ((omega_sz hj).trans (omega_sz hj').symm)).2 h⟩

theorem omega_closure_stable {h : Equiv.Perm (Fin 128)}
    (hh : h ∈ Submonoid.closure {g : Equiv.Perm (Fin 128) | g ∈ QPg.original.toList}) :
    ∀ j, j < 216 → ∃ j' < 216, h • omegaFin j = omegaFin j' := by
  induction hh using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨gi, hgi, rfl⟩ := RawSchreierDatum.mem_ofArrays_original.1 hg
    exact fun j hj => omega_gen_smul hgi hj
  | one => exact fun j hj => ⟨j, hj, one_smul _ _⟩
  | mul x y _ _ hx hy =>
    intro j hj
    obtain ⟨j', hj', hyj⟩ := hy j hj
    obtain ⟨k, hk, hxk⟩ := hx j' hj'
    exact ⟨k, hk, by rw [mul_smul, hyj, hxk]⟩

theorem omega_closed (g : ↥Pg) : ∃ j < 216, g • omegaFin 0 = omegaFin j :=
  omega_closure_stable (mem_closure_of_mem_Pg g.2) 0 (by norm_num)

theorem omega_root_aux : ∀ j, j < 216 →
    ∃ r < 10, ∃ s ∈ G0, s • omegaFin rootsArr[r]! = omegaFin j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hroot : g0Par[j]!.1 = j
    · obtain ⟨r, hr, hrj⟩ := Array.mem_iff_getElem.1 (g0_facts.2.2.2.2 j hj hroot)
      have hr10 : r < 10 := by have := rootsArr_size; omega
      refine ⟨r, hr10, 1, Subgroup.one_mem _, ?_⟩
      rw [one_smul, getElem!_pos rootsArr r hr, hrj]
    · obtain ⟨hlt, hc3, hsm⟩ := (g0_facts.2.2.2.1 j hj).resolve_left hroot
      have hp216 : g0Par[j]!.1 < 216 := by omega
      obtain ⟨r, hr, s', hs', hs'eq⟩ := ih _ hlt hp216
      refine ⟨r, hr, ((⟨g0Perm g0Par[j]!.2, g0Perm_mem hc3⟩ : ↥Pg) * s'), mul_mem
        (g0Perm_mem_G0 hc3) hs', ?_⟩
      rw [mul_smul, hs'eq]
      exact (smul_finOf_iff (rep_g0 hc3) (omega_lt hp216) (omega_lt hj)
        ((omega_sz hp216).trans (omega_sz hj).symm)).2 hsm

theorem omega_root {j : ℕ} (hj : j < 216) :
    ∃ r < 10, ∃ s ∈ G0, s • omegaFin rootsArr[r]! = omegaFin j :=
  omega_root_aux j hj

theorem root_facts {r : ℕ} (hr : r < 10) :
    gamReps[r]!.size = 128 ∧ isInvA 128 gamReps[r]! (invCand 128 gamReps[r]!) = true ∧
      inPg gamReps[r]! = true ∧ rootsArr[r]! < 216 ∧
      sameSet (imgSet gamReps[r]! omegaSets[0]!) omegaSets[rootsArr[r]!]! = true ∧
      (inH1 gamReps[r]! = true ∨ treeOK r = true) := by
  have h := List.all_eq_true.1 surj_top.2.2.2 r (List.mem_range.2 hr)
  unfold rootCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, and_assoc] at h
  exact h

theorem rep_gamRep {r : ℕ} (hr : r < 10) : Rep 128 gamReps[r]! (permOfArr 128 gamReps[r]!) :=
  (rep_permOfArr (root_facts hr).2.1).1

theorem gamRep_mem {r : ℕ} (hr : r < 10) : permOfArr 128 gamReps[r]! ∈ Pg :=
  (inPg_iff (rep_gamRep hr)).1 (root_facts hr).2.2.1

@[expose] noncomputable def gamRep (r : ℕ) (hr : r < 10) : ↥Pg :=
  ⟨permOfArr 128 gamReps[r]!, gamRep_mem hr⟩

theorem gamRep_smul {r : ℕ} (hr : r < 10) : gamRep r hr • omegaFin 0 = omegaFin rootsArr[r]! :=
  (smul_finOf_iff (rep_gamRep hr) omega_lt0 (omega_lt (root_facts hr).2.2.2.1)
    ((omega_sz (by norm_num : (0 : ℕ) < 216)).trans (omega_sz (root_facts hr).2.2.2.1).symm)).2
    (root_facts hr).2.2.2.2.1

theorem gamRep_apply {r : ℕ} (hr : r < 10) :
    (((gamRep r hr : ↥Pg) : Equiv.Perm (Fin 128)) ⟨32, by norm_num⟩ : ℕ) = (gamReps[r]!)[32]! :=
  ((rep_gamRep hr) ⟨32, by norm_num⟩).symm

theorem tree_cover {r : ℕ} (hT : treeOK r = true) :
    ∀ j < 216, ∃ k < 216, ((treeData[r]!)[k]!)[0]! = j := by
  unfold treeOK at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, and_assoc] at hT
  exact hT.2.2.2

theorem push_getElem!_lt {xs : Array (Array ℕ)} {x : Array ℕ} {c : ℕ} (hc : c < xs.size) :
    (xs.push x)[c]! = xs[c]! := by
  rw [getElem!_pos (xs.push x) c (by show c < (xs.push x).size; rw [Array.size_push]; omega),
    getElem!_pos xs c hc, Array.getElem_push_lt hc]

theorem push_getElem!_size {xs : Array (Array ℕ)} {x : Array ℕ} {c : ℕ} (hc : c = xs.size) :
    (xs.push x)[c]! = x := by
  subst hc
  simp

theorem gen_elt {r : ℕ} (hr : r < 10) (S : Subgroup ↥Pg) (hS0 : G0 ≤ S) (hSg : gamRep r hr ∈ S)
    {c : ℕ} (hc : c < 4) :
    ∃ γ ∈ S, Rep 128 (g0Gens.push gamReps[r]!)[c]! (γ : Equiv.Perm (Fin 128)) := by
  rcases Nat.lt_or_ge c 3 with hc3 | hc3
  · have hgG : (⟨g0Perm c, g0Perm_mem hc3⟩ : ↥Pg) ∈ G0 := g0Perm_mem_G0 hc3
    have hcl : c < g0Gens.size := by rw [g0_size]; exact hc3
    refine ⟨⟨g0Perm c, g0Perm_mem hc3⟩, hS0 hgG, ?_⟩
    rw [push_getElem!_lt hcl]
    exact rep_g0 hc3
  · obtain rfl : c = 3 := by omega
    refine ⟨gamRep r hr, hSg, ?_⟩
    rw [push_getElem!_size g0_size.symm]
    exact rep_gamRep hr

theorem tree_walk {r : ℕ} (hr : r < 10) (hT : treeOK r = true) (S : Subgroup ↥Pg)
    (hS0 : G0 ≤ S) (hSg : gamRep r hr ∈ S) :
    ∀ k, k < 216 → ∃ s ∈ S, s • omegaFin 0 = omegaFin (((treeData[r]!)[k]!)[0]!) := by
  unfold treeOK at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, and_assoc] at hT
  obtain ⟨-, h0, hrow, -⟩ := hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine ⟨1, S.one_mem, ?_⟩
      have h00 : ((treeData[r]!)[0]!)[0]! = 0 := by rw [h0] <;> rfl
      rw [one_smul, h00]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨-, hp1, hc2, hpos216, hppos, hsm⟩ := hrow k' (by omega)
      obtain ⟨s', hs', hs'eq⟩ := ih _ hp1 (by omega)
      obtain ⟨γ, hγS, hγR⟩ := gen_elt hr S hS0 hSg hc2
      have hsm' := (smul_finOf_iff hγR (omega_lt hppos) (omega_lt hpos216)
        ((omega_sz hppos).trans (omega_sz hpos216).symm)).2 hsm
      refine ⟨γ * s', mul_mem hγS hs', ?_⟩
      rw [mul_smul, hs'eq]
      exact hsm'

theorem treeOK_of_mov {r : ℕ} (hr : r < 10)
    (hmov : ¬ ((gamReps[r]!)[32]! = 32 ∨ (gamReps[r]!)[32]! = 53)) : treeOK r = true := by
  have hH : inH1 gamReps[r]! ≠ true := by
    intro h
    apply hmov
    unfold inH1 at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl (beq_iff_eq.1 h)
    · exact Or.inr (beq_iff_eq.1 h)
  exact (root_facts hr).2.2.2.2.2.resolve_left hH

theorem gamRep_trans {r : ℕ} (hr : r < 10)
    (hmov : ¬ ((gamReps[r]!)[32]! = 32 ∨ (gamReps[r]!)[32]! = 53))
    (S : Subgroup ↥Pg) (hS0 : G0 ≤ S) (hSg : gamRep r hr ∈ S) :
    ∀ j < 216, ∃ s ∈ S, s • omegaFin 0 = omegaFin j := by
  intro j hj
  have hT := treeOK_of_mov hr hmov
  obtain ⟨k, hk, hkj⟩ := tree_cover hT j hj
  obtain ⟨s, hs, hsk⟩ := tree_walk hr hT S hS0 hSg k hk
  exact ⟨s, hs, by rw [hsk, hkj]⟩

end CFSG.EvenSporadicStandard.Fin76b.W16
