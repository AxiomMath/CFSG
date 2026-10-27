module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Elementary
public import Certificates.Certificate27010
public import Certificates.Certificate27011
public import Certificates.Certificate27012
public import Certificates.Certificate27013
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott
open CFSG.Quasithin (tπ twoF4S twoF4H twoF4N twoF4P)

theorem rep_prodArr {A : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin 1755)} :
    ∀ {l : List ℕ}, (∀ i ∈ l, Rep 1755 A[i]! (g i)) → Rep 1755 (prodArr A l) (l.map g).prod
  | [], _ => by
    rw [prodArr, List.foldr_nil, List.map_nil, List.prod_nil]
    exact rep_idA
  | i :: l, h => by
    rw [prodArr, List.foldr_cons, List.map_cons, List.prod_cons]
    exact rep_compA (h i (by simp)) (rep_prodArr fun j hj => h j (by simp [hj]))

theorem rep_powA {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    ∀ k, Rep 1755 (powA a k) (g ^ k)
  | 0 => by
    rw [powA, List.replicate_zero, List.foldr_nil, pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [powA, List.replicate_succ, List.foldr_cons, pow_succ']
    exact rep_compA ha (rep_powA ha k)

@[expose] def chainGen (A : Array (Array ℕ)) (i : ℕ) : Equiv.Perm (Fin 1755) :=
  permOfArr 1755 A[i]!

@[expose] def eltOf (gen : ℕ → Equiv.Perm (Fin 1755)) (e : List ℕ × Bool) :
    Equiv.Perm (Fin 1755) :=
  (e.1.map gen).prod * if e.2 then tπ else 1

theorem rep_eltArr {A : Array (Array ℕ)}
    {g : ℕ → Equiv.Perm (Fin 1755)} {e : List ℕ × Bool} (h : ∀ i ∈ e.1, Rep 1755 A[i]! (g i)) :
    Rep 1755 (eltArr A e.1 e.2) (eltOf g e) := by
  obtain ⟨w, o⟩ := e
  refine rep_compA (rep_prodArr h) ?_
  cases o
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
    exact rep_idA
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    exact CFSG.Quasithin.tπ_rep

@[expose] def parrottV (i : ℕ) : Equiv.Perm (Fin 1755) :=
  eltOf titsSGen (parrottWords.getD i ([], false))

@[expose] def parrottU (i : ℕ) : Subgroup (Equiv.Perm (Fin 1755)) :=
  closure (parrottV '' Set.Icc i 12)

@[expose] def reeW₁ : Equiv.Perm (Fin 1755) := (reeWord₁.map (chainGen titsHArrs)).prod

@[expose] def reeW₂ : Equiv.Perm (Fin 1755) := (reeWord₂.map (chainGen titsNArrs)).prod

@[expose] def hatX : Equiv.Perm (Fin 1755) := (hatXWord.map (chainGen titsHArrs)).prod

theorem chainGen_H_rep {i : ℕ} (hi : i < 3) :
    Rep 1755 titsHArrs[i]! (chainGen titsHArrs i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsHArrs_size]; omega)

theorem chainGen_N_rep {i : ℕ} (hi : i < 4) :
    Rep 1755 titsNArrs[i]! (chainGen titsNArrs i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsNArrs_size]; omega)

theorem chainGen_J_rep {i : ℕ} (hi : i < 4) :
    Rep 1755 titsJArrs[i]! (chainGen titsJArrs i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsJArrs_size]; omega)

theorem titsH_eq_closure_chainGen :
    titsH = closure (Set.range fun i : Fin 3 => chainGen titsHArrs i) := by
  rw [← titsQH_facts.2.2.1, titsQH, originalSubgroup_ofArrays]
  rfl

theorem titsN_eq_closure_chainGen :
    titsN = closure (Set.range fun i : Fin 4 => chainGen titsNArrs i) := by
  rw [← titsQN_facts.2.2.1, titsQN, originalSubgroup_ofArrays]
  rfl

theorem titsJ_eq_closure_chainGen :
    titsJ = closure (Set.range fun i : Fin 4 => chainGen titsJArrs i) := by
  rw [← titsQJ_facts.2.2.1, titsQJ, originalSubgroup_ofArrays]
  rfl

theorem chainGen_H_mem {i : ℕ}
    (hi : i < 3) : chainGen titsHArrs i ∈ titsH := by
  rw [titsH_eq_closure_chainGen]
  exact subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem chainGen_N_mem {i : ℕ}
    (hi : i < 4) : chainGen titsNArrs i ∈ titsN := by
  rw [titsN_eq_closure_chainGen]
  exact subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem list_prod_map_mem {G : Type*} [Group G] {K : Subgroup G} {g : ℕ → G} {l : List ℕ}
    (h : ∀ i ∈ l, g i ∈ K) : (l.map g).prod ∈ K :=
  K.list_prod_mem fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i hi

theorem getD_mem_or_eq {α : Type*} {l : List α} {d : α} (i : ℕ) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  rcases lt_or_ge i l.length with h | h
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
  · exact Or.inr (List.getD_eq_default _ _ h)

theorem parrottWords_letters (i : ℕ) : ∀ j ∈ (parrottWords.getD i ([], false)).1, j < 3 := by
  have h : ∀ e ∈ parrottWords, ∀ j ∈ e.1, j < 3 := by decide
  rcases getD_mem_or_eq (l := parrottWords) (d := ([], false)) i with he | he
  · exact h _ he
  · rw [he]
    simp

theorem parrottWords_flag {i : ℕ} (hi : i < 13) :
    (parrottWords.getD i ([], false)).2 = inDelta i := by
  have h : ∀ i < 13, (parrottWords.getD i ([], false)).2 = inDelta i := by decide
  exact h i hi

theorem inDelta_iff {i : ℕ} : inDelta i = true ↔ i ∈ ({1, 4, 5, 6} : Finset ℕ) := by
  simp [inDelta, or_assoc]

theorem vArrs_get {i : ℕ} (hi : i < 13) :
    vArrs[i]! = eltArr titsSArrs (parrottWords.getD i ([], false)).1
      (parrottWords.getD i ([], false)).2 :=
  getElem!_ofFn_of_lt _ hi

theorem rep_vA {i : ℕ}
    (hi : i < 13) : Rep 1755 (vA i) (parrottV i) := by
  rw [vA, vArrs_get hi]
  exact rep_eltArr fun j hj => titsSGen_rep (parrottWords_letters i j hj)

theorem rep_vProd {l : List ℕ}
    (hl : ∀ i ∈ l, i < 13) : Rep 1755 (vProd l) (l.map parrottV).prod :=
  rep_prodArr fun i hi => by
    have h := rep_vA (hl i hi)
    rwa [vA] at h

theorem rep_w1Arr : Rep 1755 w1Arr reeW₁ :=
  rep_prodArr fun i hi => chainGen_H_rep (by
    have h : ∀ j ∈ reeWord₁, j < 3 := by decide
    exact h i hi)

theorem rep_w2Arr : Rep 1755 w2Arr reeW₂ :=
  rep_prodArr fun i hi => chainGen_N_rep (by
    have h : ∀ j ∈ reeWord₂, j < 4 := by decide
    exact h i hi)

theorem rep_xArr : Rep 1755 xArr hatX :=
  rep_prodArr fun i hi => chainGen_H_rep (by
    have h : ∀ j ∈ hatXWord, j < 3 := by decide
    exact h i hi)

theorem parrottV_eq (i : ℕ) :
    parrottV i = ((parrottWords.getD i ([], false)).1.map titsSGen).prod *
      if (parrottWords.getD i ([], false)).2 then tπ else 1 := rfl

theorem parrottS_mem (i : ℕ) :
    ((parrottWords.getD i ([], false)).1.map titsSGen).prod ∈ titsS :=
  list_prod_map_mem fun j hj => titsSGen_mem (parrottWords_letters i j hj)

theorem parrottV_mem_twoF4S
    (i : ℕ) : parrottV i ∈ twoF4S := by
  rw [parrottV_eq]
  cases (parrottWords.getD i ([], false)).2
  · exact Or.inl (by simpa using parrottS_mem i)
  · exact Or.inr (by simpa using parrottS_mem i)

theorem parrottV_mem_titsD_iff
    {i : ℕ} (hi : i ≤ 12) : parrottV i ∈ titsD ↔ i ∉ ({1, 4, 5, 6} : Finset ℕ) := by
  rw [← inDelta_iff, ← parrottWords_flag (by omega), parrottV_eq]
  have hg := titsS_le_titsD (parrottS_mem i)
  cases (parrottWords.getD i ([], false)).2
  · simpa using hg
  · simp only [ite_true, not_true_eq_false, iff_false]
    intro h
    exact CFSG.Quasithin.tπ_not_mem_D (by simpa using titsD.mul_mem (titsD.inv_mem hg) h)

theorem relCheck_eq_true : relCheck = true :=
  Certificates.certificate27010

theorem relCheck_parts :
    sqOK = true ∧ neOneOK = true ∧ commOK = true ∧ commuteOK = true ∧
      eqA 1755 (vA 12) titsZArr = true := by
  have h := relCheck_eq_true
  simp only [relCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem parrottSq_lt (i : ℕ) : ∀ j ∈ parrottSq i, j < 13 := by
  unfold parrottSq
  split_ifs <;> simp

theorem parrottComm_lt : ∀ r ∈ parrottComm, r.1 < 13 ∧ r.2.1 < 13 ∧ ∀ j ∈ r.2.2, j < 13 := by
  decide

theorem parrottV_mul_self
    {i : ℕ} (h1 : 1 ≤ i) (h12 : i ≤ 12) :
    parrottV i * parrottV i = ((parrottSq i).map parrottV).prod := by
  have h := List.all_eq_true.1 relCheck_parts.1 i (List.mem_range'_1.2 ⟨h1, by omega⟩)
  exact eq_of_eqA (rep_compA (rep_vA (by omega)) (rep_vA (by omega)))
    (rep_vProd (parrottSq_lt i)) h

theorem parrottV_ne_one
    {i : ℕ} (h1 : 1 ≤ i) (h12 : i ≤ 12) :
    parrottV i ≠ 1 := by
  have h := List.all_eq_true.1 relCheck_parts.2.1 i (List.mem_range'_1.2 ⟨h1, by omega⟩)
  intro he
  rw [(eqA_iff (rep_vA (by omega)) rep_idA).2 he] at h
  exact Bool.false_ne_true h

theorem parrottV_comm
    {r : ℕ × ℕ × List ℕ} (hr : r ∈ parrottComm) :
    parrottV r.1 * parrottV r.2.1 =
      parrottV r.2.1 * parrottV r.1 * (r.2.2.map parrottV).prod := by
  have h := List.all_eq_true.1 relCheck_parts.2.2.1 r hr
  obtain ⟨h1, h2, h3⟩ := parrottComm_lt r hr
  exact eq_of_eqA (rep_compA (rep_vA h1) (rep_vA h2))
    (rep_compA (rep_compA (rep_vA h2) (rep_vA h1)) (rep_vProd h3)) h

theorem parrottV_commute
    {i j : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 12)
    (hj1 : 1 ≤ j) (hj : j ≤ 12) (hij : listed i j = false) (hji : listed j i = false) :
    parrottV i * parrottV j = parrottV j * parrottV i := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 relCheck_parts.2.2.2.1 i
    (List.mem_range'_1.2 ⟨hi1, by omega⟩)) j (List.mem_range'_1.2 ⟨hj1, by omega⟩)
  rw [hij, hji, Bool.false_or, Bool.false_or] at h
  have := eq_of_eqA (rep_compA (rep_vA (by omega)) (rep_vA (by omega)))
    (rep_compA (rep_compA (rep_vA (by omega)) (rep_vA (by omega))) rep_idA) h
  rwa [mul_one] at this

theorem parrottV_twelve :
    parrottV 12 = titsZ :=
  eq_of_eqA (rep_vA (by norm_num)) titsZ_rep relCheck_parts.2.2.2.2

theorem parrott_squares :
    parrottV 1 * parrottV 1 = parrottV 2 ∧ parrottV 4 * parrottV 4 = parrottV 8 ∧
      parrottV 5 * parrottV 5 = parrottV 12 ∧ parrottV 6 * parrottV 6 = parrottV 11 ∧
      ∀ i, 1 ≤ i → i ≤ 12 → i ∉ ({1, 4, 5, 6} : Finset ℕ) → parrottV i * parrottV i = 1 := by
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h12 hi => ?_⟩
  · simpa [parrottSq] using parrottV_mul_self (i := 1) le_rfl (by norm_num)
  · simpa [parrottSq] using parrottV_mul_self (i := 4) (by norm_num) (by norm_num)
  · simpa [parrottSq] using parrottV_mul_self (i := 5) (by norm_num) (by norm_num)
  · simpa [parrottSq] using parrottV_mul_self (i := 6) (by norm_num) (by norm_num)
  · have hsq : parrottSq i = [] := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [parrottSq, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
    simpa [hsq] using parrottV_mul_self h1 h12

theorem orderOf_parrottV
    {i : ℕ} (h1 : 1 ≤ i) (h12 : i ≤ 12) :
    orderOf (parrottV i) = if i ∈ ({1, 4, 5, 6} : Finset ℕ) then 4 else 2 := by
  obtain ⟨s1, s4, s5, s6, s⟩ := parrott_squares
  have inv : ∀ j, 1 ≤ j → j ≤ 12 → j ∉ ({1, 4, 5, 6} : Finset ℕ) → orderOf (parrottV j) = 2 :=
    fun j hj1 hj12 hj => orderOf_eq_prime (by rw [sq]; exact s j hj1 hj12 hj)
      (parrottV_ne_one hj1 hj12)
  have four : ∀ j k, 1 ≤ k → k ≤ 12 → k ∉ ({1, 4, 5, 6} : Finset ℕ) →
      parrottV j * parrottV j = parrottV k → orderOf (parrottV j) = 4 := by
    intro j k hk1 hk12 hk hjk
    have h4 : parrottV j ^ 2 ^ 2 = 1 := by
      have e : parrottV j ^ 2 ^ 2 = (parrottV j * parrottV j) * (parrottV j * parrottV j) := by
        rw [show (2 : ℕ) ^ 2 = 4 from rfl]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, hjk]
      exact s k hk1 hk12 hk
    have h2 : ¬ parrottV j ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, hjk]
      exact parrottV_ne_one hk1 hk12
    exact orderOf_eq_prime_pow h2 h4
  by_cases hD : i ∈ ({1, 4, 5, 6} : Finset ℕ)
  · rw [ite_eq_left hD]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · exact four 1 2 (by norm_num) (by norm_num) (by decide) s1
    · exact four 4 8 (by norm_num) (by norm_num) (by decide) s4
    · exact four 5 12 (by norm_num) (by norm_num) (by decide) s5
    · exact four 6 11 (by norm_num) (by norm_num) (by decide) s6
  · rw [ite_eq_right hD]
    exact inv i h1 h12 hD

theorem genCheck_eq_true : genCheck = true :=
  Certificates.certificate27011

theorem genCheck_parts :
    (List.range 3).all (fun j => eqA 1755 titsSArrs[j]! (vProd (sInV.getD j []))) = true ∧
      eqA 1755 CFSG.Quasithin.titsPiArr (vProd piInV) = true ∧
      (List.range 3).all
        (fun j => eqA 1755 titsSArrs[j]! (vProd (sInW.getD j []).flatten)) = true ∧
      (List.range' 3 10).all (fun i => inJ (compA 1755 (vA i)
        (if (parrottWords.getD i ([], false)).2 then CFSG.Quasithin.piInv else idA 1755))) =
        true ∧
      (List.range 4).all (fun k => eqA 1755 titsJArrs[k]! (vProd (jInU.getD k []))) = true ∧
      (List.range 32).all (fun a => (List.range 32).all fun b =>
        a == b || !eqA 1755 (vProd (u8Bits a)) (vProd (u8Bits b))) = true := by
  have h := genCheck_eq_true
  unfold genCheck at h
  repeat rw [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, -⟩, h7⟩, h8⟩, -⟩, -⟩, -⟩, h12⟩ := h
  exact ⟨h1, h2, h5, h7, h8, h12⟩

theorem sInV_letters : ∀ j < 3, ∀ i ∈ sInV.getD j [], 1 ≤ i ∧ i ≤ 12 := by decide

theorem jInU_letters : ∀ k < 4, ∀ i ∈ jInU.getD k [], 3 ≤ i ∧ i ≤ 12 := by decide

theorem titsSGen_eq_prod
    {j : ℕ} (hj : j < 3) :
    titsSGen j = ((sInV.getD j []).map parrottV).prod :=
  eq_of_eqA (titsSGen_rep hj)
    (rep_vProd fun i hi => by have := sInV_letters j hj i hi; omega)
    (List.all_eq_true.1 genCheck_parts.1 j (List.mem_range.2 hj))

theorem tπ_eq_prod :
    tπ = parrottV 4 * parrottV 5 * parrottV 4 := by
  have h := eq_of_eqA CFSG.Quasithin.tπ_rep (rep_vProd (l := piInV) (by decide))
    genCheck_parts.2.1
  rw [h]
  simp [piInV, mul_assoc]

theorem prod_mem_parrottU {l : List ℕ} {m : ℕ} (hl : ∀ i ∈ l, m ≤ i ∧ i ≤ 12) :
    (l.map parrottV).prod ∈ parrottU m :=
  list_prod_map_mem fun i hi => subset_closure ⟨i, hl i hi, rfl⟩

theorem tπ_mem_parrottU
    {m : ℕ} (hm : m ≤ 4) : tπ ∈ parrottU m := by
  have h := prod_mem_parrottU (l := [4, 5, 4]) (m := m) (by simp; omega)
  rw [tπ_eq_prod]
  simpa [mul_assoc] using h

theorem twoF4S_eq_closure :
    twoF4S = parrottU 1 := by
  apply le_antisymm
  · have hS : titsS ≤ parrottU 1 := by
      rw [titsS_eq_closure, closure_le]
      rintro _ ⟨j, rfl⟩
      change titsSGen (j : ℕ) ∈ parrottU 1
      rw [titsSGen_eq_prod j.2]
      exact prod_mem_parrottU fun i hi => sInV_letters j j.2 i hi
    rintro x (hx | hx)
    · exact hS hx
    · have := mul_mem (hS hx) (tπ_mem_parrottU (m := 1) (by norm_num))
      simpa using this
  · rw [parrottU, closure_le]
    rintro _ ⟨i, -, rfl⟩
    exact parrottV_mem_twoF4S i

@[expose] def parrottBlocks : Set (Equiv.Perm (Fin 1755)) :=
  {x | ∃ k, 1 ≤ k ∧ k ≤ 12 ∧ k ∉ ({1, 4, 5, 6} : Finset ℕ) ∧ x = parrottV k} ∪
    {x | ∃ i ∈ ({1, 4, 5, 6} : Finset ℕ), ∃ j ∈ ({1, 4, 5, 6} : Finset ℕ),
      x = parrottV i * parrottV j}

theorem parrottBlocks_subset :
    parrottBlocks ⊆ titsS := by
  rintro x (⟨k, hk1, hk12, hk, rfl⟩ | ⟨i, hi, j, hj, rfl⟩)
  · have hf := parrottWords_flag (i := k) (by omega)
    have hk' : inDelta k = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hk (inDelta_iff.1 h)
    rw [parrottV_eq, hf, hk']
    simpa using parrottS_mem k
  · have hiD : i < 13 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega
    have hjD : j < 13 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj; omega
    rw [parrottV_eq, parrottV_eq, parrottWords_flag hiD, parrottWords_flag hjD,
      inDelta_iff.2 hi, inDelta_iff.2 hj, ite_eq_left rfl]
    set gi := ((parrottWords.getD i ([], false)).1.map titsSGen).prod
    set gj := ((parrottWords.getD j ([], false)).1.map titsSGen).prod
    have hconj : tπ * gj * tπ⁻¹ ∈ titsS :=
      (mem_normalizer_iff.1 CFSG.Quasithin.tπ_norm_S gj).1 (parrottS_mem j)
    have e : gi * tπ * (gj * tπ) = gi * (tπ * gj * tπ⁻¹) * (tπ * tπ) := by group
    rw [e]
    exact mul_mem (mul_mem (parrottS_mem i) hconj) CFSG.Quasithin.tπ_sq_S

theorem twoF4P_eq_parrottU_three :
    twoF4P = parrottU 3 := by
  apply le_antisymm
  · have hJ : titsJ ≤ parrottU 3 := by
      rw [titsJ_eq_closure_chainGen, closure_le]
      rintro _ ⟨k, rfl⟩
      have h := eq_of_eqA (chainGen_J_rep k.2)
        (rep_vProd fun i hi => by have := jInU_letters k k.2 i hi; omega)
        (List.all_eq_true.1 genCheck_parts.2.2.2.2.1 k (List.mem_range.2 k.2))
      change chainGen titsJArrs (k : ℕ) ∈ parrottU 3
      rw [h]
      exact prod_mem_parrottU fun i hi => jInU_letters k k.2 i hi
    rintro x (hx | hx)
    · exact hJ hx
    · have := mul_mem (hJ hx) (tπ_mem_parrottU (m := 3) (by norm_num))
      simpa using this
  · rw [parrottU, closure_le]
    rintro _ ⟨i, ⟨hi3, hi12⟩, rfl⟩
    have h := List.all_eq_true.1 genCheck_parts.2.2.2.1 i (List.mem_range'_1.2 ⟨hi3, by omega⟩)
    rw [inJ] at h
    cases hf : (parrottWords.getD i ([], false)).2
    · rw [hf, ite_eq_right Bool.false_ne_true] at h
      have hm := mem_titsJ_of_sift (rep_compA (rep_vA (by omega)) rep_idA) h
      rw [mul_one] at hm
      exact Or.inl hm
    · rw [hf, ite_eq_left rfl] at h
      exact Or.inr (mem_titsJ_of_sift (rep_compA (rep_vA (by omega))
        CFSG.Quasithin.tπ_inv_rep) h)

theorem parrottV_twelve_comm
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 12) :
    parrottV 12 * parrottV j = parrottV j * parrottV 12 := by
  have h : ∀ r ∈ parrottComm, r.1 ≠ 12 ∧ r.2.1 ≠ 12 := by decide
  refine parrottV_commute (by norm_num) le_rfl hj1 hj ?_ ?_
  · rw [listed, Bool.eq_false_iff]
    intro hl
    obtain ⟨r, hr, hr'⟩ := List.any_eq_true.1 hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hr'
    exact (h r hr).1 hr'.1
  · rw [listed, Bool.eq_false_iff]
    intro hl
    obtain ⟨r, hr, hr'⟩ := List.any_eq_true.1 hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hr'
    exact (h r hr).2 hr'.2

theorem parrottV_comm_mem_zpowers
    {i j : ℕ} (hi8 : 8 ≤ i)
    (hi : i ≤ 12) (hj3 : 3 ≤ j) (hj : j ≤ 12) :
    parrottV i * parrottV j * (parrottV i)⁻¹ * (parrottV j)⁻¹ ∈ zpowers titsZ := by
  have h8 : ∀ r ∈ parrottComm, 8 ≤ r.1 → 3 ≤ r.2.1 → r.2.2 = [12] := by decide
  have h7 : ∀ r ∈ parrottComm, r.2.1 ≤ 7 := by decide
  by_cases hl : listed i j = true
  · obtain ⟨r, hr, hr'⟩ := List.any_eq_true.1 hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    have hc := parrottV_comm hr
    rw [h8 r hr hi8 hj3] at hc
    have hz : parrottV r.1 * parrottV r.2.1 * (parrottV r.1)⁻¹ * (parrottV r.2.1)⁻¹ =
        parrottV 12 := by
      have hc' : parrottV r.1 * parrottV r.2.1 = parrottV r.2.1 * parrottV r.1 * parrottV 12 := by
        simpa using hc
      have h12 := parrottV_twelve_comm (j := r.1) (by omega) hi
      calc parrottV r.1 * parrottV r.2.1 * (parrottV r.1)⁻¹ * (parrottV r.2.1)⁻¹
          = parrottV r.2.1 * (parrottV r.1 * parrottV 12) * (parrottV r.1)⁻¹ *
              (parrottV r.2.1)⁻¹ := by rw [hc', mul_assoc (parrottV r.2.1)]
        _ = parrottV r.2.1 * (parrottV 12 * parrottV r.1) * (parrottV r.1)⁻¹ *
              (parrottV r.2.1)⁻¹ := by rw [h12]
        _ = parrottV r.2.1 * parrottV 12 * (parrottV r.2.1)⁻¹ := by group
        _ = parrottV 12 := by
          rw [(parrottV_twelve_comm (j := r.2.1) (by omega) hj).symm]
          group
    rw [hz, parrottV_twelve]
    exact mem_zpowers _
  · have hji : listed j i = false := by
      rw [Bool.eq_false_iff]
      intro hl'
      obtain ⟨r, hr, hr'⟩ := List.any_eq_true.1 hl'
      simp only [Bool.and_eq_true, beq_iff_eq] at hr'
      have := h7 r hr
      omega
    rw [parrottV_commute (by omega) hi (by omega) hj (Bool.eq_false_iff.2 hl) hji]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem parrottU_eight_le_hatE :
    parrottU 8 ≤ hatE := by
  have hzc : ∀ y ∈ parrottU 3, y * titsZ = titsZ * y := by
    have hle : parrottU 3 ≤ centralizer {titsZ} := by
      rw [parrottU, closure_le]
      rintro _ ⟨j, ⟨hj3, hj12⟩, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← parrottV_twelve]
      exact (parrottV_twelve_comm (by omega) hj12).symm
    exact fun y hy => mem_centralizer_singleton_iff.1 (hle hy)
  rw [parrottU, closure_le]
  rintro _ ⟨i, ⟨hi8, hi12⟩, rfl⟩
  refine subset_closure ⟨?_, fun y hy => ?_⟩
  · rw [twoF4P_eq_parrottU_three]
    exact subset_closure ⟨i, ⟨by omega, hi12⟩, rfl⟩
  · rw [twoF4P_eq_parrottU_three] at hy
    set a := parrottV i
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, ⟨hj3, hj12⟩, rfl⟩ := hy
      exact parrottV_comm_mem_zpowers hi8 hi12 hj3 hj12
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      refine mul_mem ihx ?_
      obtain ⟨k, hk⟩ := ihy
      rw [← hk]
      have hxz : x * titsZ ^ k * x⁻¹ = titsZ ^ k := by
        rw [(Commute.zpow_right (show Commute x titsZ from hzc x hx) k).eq, mul_inv_cancel_right]
      rw [hxz]
      exact zpow_mem (mem_zpowers _) k
    | inv x hx ihx =>
      have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [e]
      obtain ⟨k, hk⟩ := ihx
      rw [← hk, ← zpow_neg]
      have hxz : x⁻¹ * titsZ ^ (-k) * x = titsZ ^ (-k) := by
        have hc : Commute x⁻¹ titsZ := (show Commute x titsZ from hzc x hx).inv_left
        rw [(Commute.zpow_right hc (-k)).eq, inv_mul_cancel_right]
      rw [hxz]
      exact zpow_mem (mem_zpowers _) _

theorem le_card_parrottU_eight :
    32 ≤ Nat.card (parrottU 8) := by
  have hbits : ∀ a < 32, ∀ i ∈ u8Bits a, 8 ≤ i ∧ i ≤ 12 := by decide
  let f : Fin 32 → parrottU 8 := fun a =>
    ⟨((u8Bits a).map parrottV).prod, prod_mem_parrottU (hbits a a.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h := List.all_eq_true.1 (List.all_eq_true.1 genCheck_parts.2.2.2.2.2 a
      (List.mem_range.2 a.2)) b (List.mem_range.2 b.2)
    have hne' : ((a : ℕ) == (b : ℕ)) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun h => hne (Fin.ext h)
    rw [hne', Bool.false_or, Bool.not_eq_true'] at h
    have hrep := fun c : Fin 32 => rep_vProd (l := u8Bits c) fun i hi => by
      have := hbits c c.2 i hi; omega
    rw [(eqA_iff (hrep a) (hrep b)).2 (congrArg Subtype.val hab)] at h
    exact absurd h (by decide)
  simpa using Nat.card_le_card_of_injective f hf

theorem hatE_eq_parrottU_eight :
    hatE = parrottU 8 := by
  have hfin : Finite hatE := Finite.of_injective _ Subtype.val_injective
  refine (Subgroup.eq_of_le_of_card_ge parrottU_eight_le_hatE ?_).symm
  rw [card_hatE.2.2.2]
  exact le_card_parrottU_eight

theorem reeCheck_eq_true : reeCheck = true :=
  Certificates.certificate27012

theorem reeCheck_parts :
    reeConj₁.all (fun p => conjEqA w1Arr (vA p.1) (vA p.2)) = true ∧
      reeConj₂.all (fun p => conjEqA w2Arr (vA p.1) (vA p.2)) = true ∧
      eqA 1755 (compA 1755 w1Arr w1Arr) (idA 1755) = true ∧
      (!eqA 1755 w1Arr (idA 1755)) = true ∧
      eqA 1755 (compA 1755 w2Arr w2Arr) (idA 1755) = true ∧
      (!eqA 1755 w2Arr (idA 1755)) = true ∧
      (!eqA 1755 (powA (compA 1755 w1Arr w2Arr) 4) (idA 1755)) = true ∧
      eqA 1755 (powA (compA 1755 w1Arr w2Arr) 8) (idA 1755) = true ∧
      (List.range 3).all (fun k =>
        eqA 1755 titsHArrs[k]! (prodArr (vArrs.push w1Arr) (hInTW.getD k []))) = true ∧
      (List.range 4).all (fun k =>
        eqA 1755 titsNArrs[k]! (prodArr (vArrs.push w2Arr) (nInTW.getD k []))) = true := by
  have h := reeCheck_eq_true
  unfold reeCheck at h
  repeat rw [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, h10⟩, h11⟩, -⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, h11⟩

theorem conj_of_conjEqA
    {wArr : Array ℕ} {w : Equiv.Perm (Fin 1755)} (hw : Rep 1755 wArr w) {a b : ℕ} (ha : a < 13)
    (hb : b < 13) (h : conjEqA wArr (vA a) (vA b) = true) :
    w⁻¹ * parrottV a * w = parrottV b := by
  have h' := eq_of_eqA (rep_compA (rep_vA ha) hw) (rep_compA hw (rep_vA hb)) h
  rw [mul_assoc, h', inv_mul_cancel_left]

theorem ree_conj_two :
    reeW₂⁻¹ * parrottV 12 * reeW₂ = parrottV 11 ∧ reeW₂⁻¹ * parrottV 2 * reeW₂ = parrottV 8 ∧
      reeW₂⁻¹ * parrottV 7 * reeW₂ = parrottV 9 ∧ reeW₂⁻¹ * parrottV 1 * reeW₂ = parrottV 4 ∧
      reeW₂⁻¹ * parrottV 5 * reeW₂ = parrottV 6 := by
  have h := List.all_eq_true.1 reeCheck_parts.2.1
  exact ⟨conj_of_conjEqA rep_w2Arr (by norm_num) (by norm_num) (h (12, 11) (by decide)),
    conj_of_conjEqA rep_w2Arr (by norm_num) (by norm_num) (h (2, 8) (by decide)),
    conj_of_conjEqA rep_w2Arr (by norm_num) (by norm_num) (h (7, 9) (by decide)),
    conj_of_conjEqA rep_w2Arr (by norm_num) (by norm_num) (h (1, 4) (by decide)),
    conj_of_conjEqA rep_w2Arr (by norm_num) (by norm_num) (h (5, 6) (by decide))⟩

theorem reeW_orders :
    reeW₁ ∈ titsH ∧ reeW₂ ∈ titsN ∧ orderOf reeW₁ = 2 ∧ orderOf reeW₂ = 2 ∧
      orderOf (reeW₁ * reeW₂) = 8 := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, -⟩ := reeCheck_parts
  have hw1 : reeW₁ ∈ titsH := list_prod_map_mem fun i hi => chainGen_H_mem (by
    have h : ∀ j ∈ reeWord₁, j < 3 := by decide
    exact h i hi)
  have hw2 : reeW₂ ∈ titsN := list_prod_map_mem fun i hi => chainGen_N_mem (by
    have h : ∀ j ∈ reeWord₂, j < 4 := by decide
    exact h i hi)
  have h12 := rep_compA rep_w1Arr rep_w2Arr
  refine ⟨hw1, hw2, ?_, ?_, ?_⟩
  · have hsq : reeW₁ ^ 2 = 1 := by
      rw [sq]
      exact eq_of_eqA (rep_compA rep_w1Arr rep_w1Arr) rep_idA h3
    refine orderOf_eq_prime hsq fun he => ?_
    rw [(eqA_iff rep_w1Arr rep_idA).2 he] at h4
    exact absurd h4 (by decide)
  · have hsq : reeW₂ ^ 2 = 1 := by
      rw [sq]
      exact eq_of_eqA (rep_compA rep_w2Arr rep_w2Arr) rep_idA h5
    refine orderOf_eq_prime hsq fun he => ?_
    rw [(eqA_iff rep_w2Arr rep_idA).2 he] at h6
    exact absurd h6 (by decide)
  · have e8 : (8 : ℕ) = 2 ^ (2 + 1) := rfl
    rw [e8]
    refine orderOf_eq_prime_pow (p := 2) (n := 2) (fun he => ?_)
      (eq_of_eqA (rep_powA h12 8) rep_idA h8)
    rw [(eqA_iff (rep_powA h12 4) rep_idA).2 he] at h7
    exact absurd h7 (by decide)

theorem xCheck_eq_true : xCheck = true :=
  Certificates.certificate27013

theorem hatX_facts :
    hatX ∈ titsH ∧ orderOf hatX = 5 ∧ parrottV 1 * hatX * (parrottV 1)⁻¹ = hatX ^ 3 ∧
      parrottV 5 * hatX = hatX * parrottV 5 ∧
      ∀ y ∈ twoF4P, y * hatX = hatX * y →
        y = 1 ∨ y = parrottV 5 ∨ y = parrottV 12 ∨ y = parrottV 5 * parrottV 12 := by
  have h := xCheck_eq_true
  unfold xCheck at h
  repeat rw [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hmem : hatX ∈ titsH := list_prod_map_mem fun i hi => chainGen_H_mem (by
    have h : ∀ j ∈ hatXWord, j < 3 := by decide
    exact h i hi)
  have h5' : hatX ^ 5 = 1 := eq_of_eqA (rep_powA rep_xArr 5) rep_idA h1
  have hne : hatX ≠ 1 := fun he => by
    rw [(eqA_iff rep_xArr rep_idA).2 he] at h2
    exact absurd h2 (by decide)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨hmem, orderOf_eq_prime h5' hne, ?_, ?_, fun y hy hyx => ?_⟩
  · have e := eq_of_eqA (rep_compA (rep_vA (by norm_num)) rep_xArr)
      (rep_compA (rep_powA rep_xArr 3) (rep_vA (by norm_num))) h3
    rw [e, mul_inv_cancel_right]
  · have e := eq_of_eqA (rep_compA (rep_vA (by norm_num)) rep_xArr)
      (rep_compA (rep_compA rep_xArr (rep_vA (by norm_num))) rep_idA) h4
    rwa [mul_one] at e
  · obtain ⟨i, rfl⟩ := CFSG.Quasithin.pEl_surj hy
    have hi := allLt_spec h5 i.2
    rw [Bool.or_eq_true, Bool.not_eq_true'] at hi
    have hc : commEqA CFSG.Quasithin.pPel[(i : ℕ)]! xArr (idA 1755) = true :=
      (eqA_iff (rep_compA (CFSG.Quasithin.pEl_rep i) rep_xArr)
        (rep_compA (rep_compA rep_xArr (CFSG.Quasithin.pEl_rep i)) rep_idA)).2 (by
          rw [mul_one]; exact hyx)
    rcases hi with hi | hi
    · rw [hc] at hi
      exact absurd hi (by decide)
    · obtain ⟨c, hcm, hce⟩ := List.any_eq_true.1 hi
      have r := CFSG.Quasithin.pEl_rep i
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with h | h | h | h <;> rw [h] at hce
      · exact Or.inl (eq_of_eqA r rep_idA hce)
      · exact Or.inr (Or.inl (eq_of_eqA r (rep_vA (by norm_num)) hce))
      · exact Or.inr (Or.inr (Or.inl (eq_of_eqA r (rep_vA (by norm_num)) hce)))
      · exact Or.inr (Or.inr (Or.inr
          (eq_of_eqA r (rep_compA (rep_vA (by norm_num)) (rep_vA (by norm_num))) hce)))

end CFSG.LocalAnalysis.EvenBN.Tits.Model
