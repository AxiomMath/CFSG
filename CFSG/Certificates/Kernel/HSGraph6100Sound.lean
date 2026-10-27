module

public import Certificates.Data.Kernel.HSGraph6100
public import CFSG.Certificates.Kernel.HSIdentSound

public section

namespace CFSG.KC.HSGraph6100

open Certificates.Kernel.HSIdent Certificates.Kernel.HSGraph6100 CFSG.KC.HSIdent
  CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane
  CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.HSGraph

theorem testBit_and_sub_one : ∀ x : Nat, x ≠ 0 → ∃ k, x.testBit k = true ∧
    ∀ b, (x &&& (x - 1)).testBit b = (x.testBit b && decide (b ≠ k)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro hx
  rcases Nat.even_or_odd' x with ⟨m, rfl | rfl⟩
  · have hm : m ≠ 0 := by omega
    obtain ⟨k, hk, hb⟩ := ih m (by omega) hm
    have h2 : 2 * m / 2 = m := by omega
    have h3 : (2 * m - 1) / 2 = m - 1 := by omega
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Nat.testBit_add_one, h2]
      exact hk
    · intro b
      cases b with
      | zero => simp
      | succ b =>
        have hb' := hb b
        rw [Nat.testBit_and] at hb'
        rw [Nat.testBit_and, Nat.testBit_add_one, Nat.testBit_add_one, h2, h3, hb']
        simp
  · have h2 : (2 * m + 1) / 2 = m := by omega
    have h3 : (2 * m + 1 - 1) / 2 = m := by omega
    refine ⟨0, by simp, ?_⟩
    intro b
    cases b with
    | zero => simp
    | succ b =>
      rw [Nat.testBit_and, Nat.testBit_add_one, Nat.testBit_add_one, h2, h3]
      simp

@[expose] def bitsFin (N x : Nat) : Finset (Fin N) := Finset.univ.filter fun j => x.testBit j

theorem card_bitsFin_le (N x : Nat) : (bitsFin N x).card ≤ N :=
  (Finset.card_le_univ _).trans (by simp)

theorem popK_eq {N : Nat} : ∀ (f x : Nat), (∀ b, N ≤ b → x.testBit b = false) →
    (bitsFin N x).card ≤ f → popK f x = (bitsFin N x).card
  | 0, x, _, hc => by
    rw [popK]
    omega
  | f + 1, x, hN, hc => by
    rw [popK]
    by_cases hx : x = 0
    · rw [if_pos hx]
      subst hx
      simp [bitsFin]
    · rw [if_neg hx]
      obtain ⟨k, hk, hb⟩ := testBit_and_sub_one x hx
      have hkN : k < N := by
        by_contra h
        rw [hN k (by omega)] at hk
        exact Bool.false_ne_true hk
      have hS : bitsFin N (x &&& (x - 1)) = (bitsFin N x).erase ⟨k, hkN⟩ := by
        ext j
        simp only [bitsFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hb,
          Bool.and_eq_true, decide_eq_true_eq, ne_eq, Fin.ext_iff]
        tauto
      have hmem : (⟨k, hkN⟩ : Fin N) ∈ bitsFin N x := by simp [bitsFin, hk]
      have hc' := Finset.card_erase_add_one hmem
      have hN' : ∀ b, N ≤ b → (x &&& (x - 1)).testBit b = false := by
        intro b hbN
        rw [hb b, hN b hbN, Bool.false_and]
      rw [popK_eq f (x &&& (x - 1)) hN' (by rw [hS]; omega), hS]
      omega

theorem testBit_rowAux (i : Nat) :
    ∀ n b, (rowAux i n).testBit b = (decide (b < n) && modelAdjN i b)
  | 0, b => by simp [rowAux]
  | n + 1, b => by
    rw [rowAux, Nat.testBit_or, testBit_rowAux i n b]
    rcases Nat.lt_trichotomy b n with hlt | rfl | hgt
    · have h1 : b < n + 1 := by omega
      have h2 : n ≠ b := by omega
      split <;> simp [hlt, h1, h2, Nat.testBit_two_pow]
    · split <;> simp_all [Nat.testBit_two_pow]
    · have h1 : ¬ b < n + 1 := by omega
      have h0 : ¬ b < n := by omega
      have h2 : n ≠ b := by omega
      split <;> simp [h0, h1, h2, Nat.testBit_two_pow]

theorem testBit_rowOf (i b : Nat) : (rowOf i).testBit b = (decide (b < 100) && modelAdjN i b) :=
  testBit_rowAux i 100 b

theorem rowOf_high (i : Nat) : ∀ b, 100 ≤ b → (rowOf i).testBit b = false := by
  intro b hb
  rw [testBit_rowOf, decide_eq_false (by omega), Bool.false_and]

theorem adj_iff_row (i j : Fin 100) :
    (hsGraph hexads).Adj (modelVertAtF i) (modelVertAtF j) ↔ (rowOf i).testBit j = true := by
  rw [testBit_rowOf, Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨fun h => ⟨j.isLt, (modelAdjN_iff i.isLt j.isLt).2 h⟩,
    fun h => (modelAdjN_iff i.isLt j.isLt).1 h.2⟩

theorem modelVertAt_cases {n : Nat} (hn : n < 100) :
    (n = 0 ∧ modelVertAt n = vInf) ∨
      (∃ k, ∃ hk : k < 22, n = k + 1 ∧ modelVertAt n = vPt ⟨k, hk⟩) ∨
      (∃ k, k < 77 ∧ n = k + 23 ∧ modelVertAt n = vBlk (modelBlkAt k)) := by
  rcases vert_cases hn with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Or.inl ⟨rfl, modelVertAt_zero⟩
  · exact Or.inr (Or.inl ⟨k, hk, rfl, modelVertAt_pt hk⟩)
  · exact Or.inr (Or.inr ⟨k, hk, rfl, modelVertAt_blk k⟩)

theorem modelVertAtF_injective_of (h : distinctK hexMask = true) :
    Function.Injective modelVertAtF := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  change modelVertAt i = modelVertAt j at hij
  apply Fin.ext
  change i = j
  rcases modelVertAt_cases hi with ⟨rfl, e1⟩ | ⟨k, hk, rfl, e1⟩ | ⟨k, hk, rfl, e1⟩ <;>
    rcases modelVertAt_cases hj with ⟨rfl, e2⟩ | ⟨l, hl, rfl, e2⟩ | ⟨l, hl, rfl, e2⟩ <;>
    simp only [e1, e2] at hij <;> (try simp at hij) <;> (try omega)
  have hij' : modelBlkAt k = modelBlkAt l := by simpa using hij
  have h2 : hexMask k = hexMask l := congrArg (fun B : {B // B ∈ hexads} => mask B.1) hij'
  have h3 : (k == l || hexMask k != hexMask l) = true :=
    allBelow_sound (allBelow_sound h k hk) l hl
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h3
  rcases h3 with h3 | h3
  · omega
  · exact absurd h2 h3

theorem modelVertAtF_surjective : Function.Surjective modelVertAtF := by
  rintro (_ | a | ⟨B, hB⟩)
  · exact ⟨0, modelVertAt_zero⟩
  · refine ⟨⟨a.val + 1, by omega⟩, ?_⟩
    change modelVertAt (a.val + 1) = _
    rw [modelVertAt_pt a.isLt]
  · obtain ⟨k, hk, hkB⟩ := List.getElem_of_mem (mem_hexads.1 hB)
    have hlen : hexadList.length = 77 := rfl
    refine ⟨⟨k + 23, by omega⟩, ?_⟩
    change modelVertAt (k + 23) = _
    rw [modelVertAt_blk]
    refine congrArg (fun C => (vBlk C : Vert hexads)) (Subtype.ext ?_)
    change hexadList.getD k hexad0 = B
    rw [List.getD_eq_getElem _ _ hk, hkB]

theorem card_set_vert (hinj : Function.Injective modelVertAtF) (S : Set (Vert hexads))
    [Fintype S] (p : Fin 100 → Prop) [DecidablePred p] (hp : ∀ j, modelVertAtF j ∈ S ↔ p j) :
    Fintype.card S = (Finset.univ.filter p).card := by
  rw [← Finset.card_map ⟨modelVertAtF, hinj⟩]
  refine Fintype.card_of_subtype _ fun x => ?_
  obtain ⟨j, rfl⟩ := modelVertAtF_surjective x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨k, hk, hkj⟩
    change modelVertAtF k = modelVertAtF j at hkj
    rw [← hkj, hp]
    exact (Finset.mem_filter.1 hk).2
  · intro h
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hp j).1 h⟩, rfl⟩

theorem srg_of (hinj : Function.Injective modelVertAtF) (h : srgK rowOf = true) :
    (∀ v : Vert hexads, (hsGraph hexads).degree v = 22) ∧
    (∀ v w : Vert hexads, (hsGraph hexads).Adj v w →
      Fintype.card ((hsGraph hexads).commonNeighbors v w) = 0) ∧
    (∀ v w : Vert hexads, v ≠ w → ¬ (hsGraph hexads).Adj v w →
      Fintype.card ((hsGraph hexads).commonNeighbors v w) = 6) := by
  have hpair : ∀ i j : Fin 100, srgPair i j (rowOf i) (rowOf j) = true := fun i j =>
    allBelow_sound (allBelow_sound h i.val i.isLt) j.val j.isLt
  have hcommon : ∀ i j : Fin 100,
      Fintype.card ((hsGraph hexads).commonNeighbors (modelVertAtF i) (modelVertAtF j)) =
        popK 101 (rowOf i &&& rowOf j) := by
    intro i j
    rw [popK_eq (N := 100) 101 _ (fun b hb => by rw [Nat.testBit_and, rowOf_high i b hb,
      Bool.false_and]) ((card_bitsFin_le _ _).trans (by omega))]
    refine card_set_vert hinj _ _ fun k => ?_
    rw [SimpleGraph.mem_commonNeighbors, adj_iff_row, adj_iff_row, Nat.testBit_and,
      Bool.and_eq_true]
  refine ⟨fun v => ?_, fun v w hvw => ?_, fun v w hne hvw => ?_⟩
  · obtain ⟨i, rfl⟩ := modelVertAtF_surjective v
    have hp := hpair i i
    rw [srgPair, if_pos rfl, beq_iff_eq] at hp
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      card_set_vert hinj _ (fun j => (rowOf i).testBit j = true)
        (fun j => by rw [SimpleGraph.mem_neighborSet, adj_iff_row])]
    exact (popK_eq (N := 100) 101 _ (rowOf_high i)
      ((card_bitsFin_le _ _).trans (by omega))).symm.trans hp
  · obtain ⟨i, rfl⟩ := modelVertAtF_surjective v
    obtain ⟨j, rfl⟩ := modelVertAtF_surjective w
    have hij : i.val ≠ j.val := by
      rintro h
      rw [Fin.ext h] at hvw
      exact (hsGraph hexads).loopless.irrefl _ hvw
    have hp := hpair i j
    rw [srgPair, if_neg hij, if_pos ((adj_iff_row i j).1 hvw), beq_iff_eq] at hp
    rw [hcommon, hp]
  · obtain ⟨i, rfl⟩ := modelVertAtF_surjective v
    obtain ⟨j, rfl⟩ := modelVertAtF_surjective w
    have hij : i.val ≠ j.val := fun h => hne (congrArg modelVertAtF (Fin.ext h))
    have hp := hpair i j
    rw [srgPair, if_neg hij, if_neg (fun h => hvw ((adj_iff_row i j).2 h)), beq_iff_eq] at hp
    rw [hcommon, hp]

theorem psi_check_of (h : psiK psiList = true) (i j : Fin 100) :
    (hsGraph hexads).Adj (modelVertAtF (HSGraph.psiFun i)) (modelVertAtF (HSGraph.psiFun j)) ↔
      (hsGraph hexads).Adj (modelVertAtF i) (modelVertAtF j) := by
  have hp : (modelAdjN (psiList.getD i 0 % 100) (psiList.getD j 0 % 100) ==
      modelAdjN i j) = true := allBelow_sound (allBelow_sound h i.val i.isLt) j.val j.isLt
  rw [beq_iff_eq] at hp
  change (hsGraph hexads).Adj (modelVertAt (HSGraph.psiFun i).val)
      (modelVertAt (HSGraph.psiFun j).val) ↔
    (hsGraph hexads).Adj (modelVertAt i.val) (modelVertAt j.val)
  rw [← modelAdjN_iff (HSGraph.psiFun i).isLt (HSGraph.psiFun j).isLt,
    ← modelAdjN_iff i.isLt j.isLt]
  change modelAdjN (psiList.getD i 0 % 100) (psiList.getD j 0 % 100) = true ↔ _
  rw [hp]

theorem sigN_pt {k : Nat} (hk : k < 22) : sigN (k + 1) = (sigmaFun ⟨k, hk⟩).val + 1 := by
  rw [sigN, if_neg (by omega), if_pos (by omega)]
  exact congrArg (fun a : Fin 22 => (sigmaFun a).val + 1)
    (Fin.ext (by change (k + 1 - 1) % 22 = k; omega))

theorem extPerm_modelVertAtF (σ : Equiv.Perm (Fin 22)) (hσ : σ ∈ blockAut hexads)
    (hfun : ⇑σ = sigmaFun) (h : sigK sigN = true) (i : Fin 100) :
    extPerm σ hσ (modelVertAtF i) = modelVertAtF (sigNF sigN i) := by
  obtain ⟨i, hi⟩ := i
  change extPerm σ hσ (modelVertAt i) = modelVertAt (sigN i % 100)
  rcases vert_cases hi with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · have h0 : sigN 0 = 0 := rfl
    rw [h0, Nat.zero_mod, modelVertAt_zero]
    rfl
  · have := (sigmaFun ⟨k, hk⟩).isLt
    rw [modelVertAt_pt hk, extPerm_vPt, hfun, sigN_pt hk, Nat.mod_eq_of_lt (by omega),
      modelVertAt_pt (sigmaFun ⟨k, hk⟩).isLt]
  · have hp : (decide (23 ≤ sigN (k + 23)) && decide (sigN (k + 23) < 100) &&
        hexMask (sigN (k + 23) - 23) == mask ((hexadList.getD k hexad0).image sigmaFun)) = true :=
      allBelow_sound h k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    obtain ⟨m, hm⟩ : ∃ m, sigN (k + 23) = m + 23 := ⟨sigN (k + 23) - 23, by omega⟩
    rw [modelVertAt_blk, extPerm_vBlk, Nat.mod_eq_of_lt h2, hm, modelVertAt_blk]
    rw [hm, Nat.add_sub_cancel] at h3
    refine congrArg (fun C => (vBlk C : Vert hexads)) (Subtype.ext (mask_injective ?_))
    change mask (Finset.map σ.toEmbedding (hexadList.getD k hexad0)) = hexMask m
    rw [h3, Finset.map_eq_image, Equiv.coe_toEmbedding, hfun]

theorem sign_extPerm_of (σ : Equiv.Perm (Fin 22)) (hσ : σ ∈ blockAut hexads)
    (hfun : ⇑σ = sigmaFun) (hinj : Function.Injective modelVertAtF) (hs : sigK sigN = true)
    (hinv : ∀ i, sigNF sigN (sigNF sigN i) = i)
    (hsign : Equiv.Perm.sign (sigPerm sigN hinv) = -1) :
    Equiv.Perm.sign (extPerm (𝓑 := hexads) σ hσ) = -1 := by
  let e : Fin 100 ≃ Vert hexads := Equiv.ofBijective _ ⟨hinj, modelVertAtF_surjective⟩
  have he : extPerm σ hσ = e.permCongr (sigPerm sigN hinv) := by
    ext1 x
    obtain ⟨i, rfl⟩ := modelVertAtF_surjective x
    rw [Equiv.permCongr_apply]
    have h1 : e.symm (modelVertAtF i) = i := e.symm_apply_eq.2 rfl
    rw [h1]
    exact extPerm_modelVertAtF σ hσ hfun hs i
  rw [he, Equiv.Perm.sign_permCongr, hsign]

end CFSG.KC.HSGraph6100
