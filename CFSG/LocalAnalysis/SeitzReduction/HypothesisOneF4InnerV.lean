module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerVBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem list_prod_sq_eq_one {G : Type*} [Group G] :
    ∀ L : List G, (∀ x ∈ L, ∀ y ∈ L, x * y = y * x) → (∀ x ∈ L, x ^ 2 = 1) → L.prod ^ 2 = 1
  | [], _, _ => by simp
  | a :: L, hc, hs => by
    have hL := list_prod_sq_eq_one L (fun x hx y hy => hc x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)) (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    have ha : Commute a L.prod := Commute.list_prod_right _ _ fun y hy =>
      hc a List.mem_cons_self y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons, ha.mul_pow, hs a List.mem_cons_self, hL, one_mul]


@[expose] def f4CentListV : List ℕ :=
  [24, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

@[expose] def f4GenericListV : List ℕ :=
  [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 46, 47]

theorem f4CentListV_lookup : ∀ p ∈ f4CentListV, (24 ≤ p ∧ p ≤ 47) ∧
    (p ≠ 41 → (f4OddCommutatorFactors.lookup (p, 41)).getD [] = []) ∧
    (p ≠ 45 → (f4OddCommutatorFactors.lookup (p, 45)).getD [] = []) := by
  decide +kernel

theorem f4_torus_check_classV :
    (f4Pairing (![-2, 1, 0, 0] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 41) = 0 ∧
      f4Pairing (![-2, 1, 0, 0] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 45) = 0 ∧
      f4Pairing (![0, 0, 1, -2] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 41) = 0 ∧
      f4Pairing (![0, 0, 1, -2] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 45) = 0) ∧
    ∀ p ∈ f4GenericListV,
      f4Pairing (![-2, 1, 0, 0] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2] ∨
        f4Pairing (![0, 0, 1, -2] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2] := by
  decide +kernel


theorem f4x_commute_of_lookup [CharP K 2] {i j : ℕ} (hi : 24 ≤ i ∧ i ≤ 47)
    (hj : 24 ≤ j ∧ j ≤ 47) (hl : i ≠ j → (f4OddCommutatorFactors.lookup (i, j)).getD [] = [])
    (s t : K) : f4x K i s * f4x K j t = f4x K j t * f4x K i s := by
  by_cases hij : i = j
  · subst hij
    simp only [f4x]
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have h := f4x_commutator_eq hi hj hij s t
    rw [hl hij, List.map_nil, List.prod_nil] at h
    exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem f4x_commute_classV [CharP K 2] {p : ℕ} (hp : p ∈ f4CentListV) (d : K) :
    f4x K p d * (f4x K 41 1 * f4x K 45 1) = (f4x K 41 1 * f4x K 45 1) * f4x K p d := by
  obtain ⟨hp', h41, h45⟩ := f4CentListV_lookup p hp
  rw [← mul_assoc, f4x_commute_of_lookup hp' ⟨by norm_num, by norm_num⟩ h41, mul_assoc,
    f4x_commute_of_lookup hp' ⟨by norm_num, by norm_num⟩ h45, mul_assoc]

theorem rootDiagUnit_commute_classV {a : Fin Tag.F4.rank → Kˣ}
    (h41 : rootChar a (orbitCertRoot .F4 41) = 1) (h45 : rootChar a (orbitCertRoot .F4 45) = 1) :
    rootDiagUnit .F4 a * (f4x K 41 1 * f4x K 45 1) =
      (f4x K 41 1 * f4x K 45 1) * rootDiagUnit .F4 a := by
  rw [← mul_assoc, f4x, rootDiagUnit_commute_pinnedX_one
    (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h41, mul_assoc, f4x,
    rootDiagUnit_commute_pinnedX_one (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h45, mul_assoc]

@[expose] def f4SupportOf (L : List ℕ) (n : ℕ) : List ℕ :=
  f4PosList.filter fun i => decide (i ∉ L.take n)

theorem f4_take_succ_of {L : List ℕ} {c : ℕ → K} {n : ℕ} (hD : ∀ j ∈ L.take n, c j = 0)
    (h : c (L.getD n 0) = 0) : ∀ j ∈ L.take (n + 1), c j = 0 := by
  intro j hj
  rw [List.take_add_one, List.mem_append] at hj
  rcases hj with hj | hj
  · exact hD j hj
  · simp only [Option.mem_toList] at hj
    rw [List.getD_eq_getElem?_getD, hj, Option.getD_some] at h
    exact h

theorem f4_row_of [Finite K] [CharP K 2] (L : List ℕ) (c : ℕ → K) {v : ℕ → K} (n : ℕ)
    (hD : ∀ j ∈ L.take n, c j = 0) {k : ℕ} {wp : List ℕ} {E : List (ℕ × ℕ × ℕ × ℕ)}
    (hok : (f4RowOK k (f4SupportOf L n) wp && f4Contribs k (f4SupportOf L n) wp == E) = true)
    (hcomm : ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
      (wp.map fun p => f4x K p (v p)).prod⁆ = 1) :
    (E.map fun m => c m.1 ^ m.2.1 * v m.2.2.1 ^ m.2.2.2).sum = 0 := by
  rw [Bool.and_eq_true, beq_iff_eq] at hok
  rw [← hok.2]
  rw [← list_prod_map_filter_of_eq_one f4PosList (fun i => decide (i ∉ L.take n)) _
    (fun i _ hi => by
      simp only [decide_eq_false_iff_not, not_not] at hi
      rw [hD i hi, f4x_zero])] at hcomm
  exact f4_row hok.1 c v hcomm

@[expose] def f4KillOrderV : List ℕ :=
  [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42]

@[expose] def f4TestListV : List ℕ := [29, 30, 32, 35, 36, 37]

theorem f4TestListV_spec :
    ∀ p ∈ f4TestListV, (24 ≤ p ∧ p ≤ 47) ∧ 3 ≤ height (orbitCertRoot .F4 p) := by
  decide

theorem f4_coords_eq_zero_of_commute_classV [Finite K] [CharP K 2] (c : ℕ → K)
    (h : ∀ p ∈ f4TestListV, ⁅(f4PosList.map fun i => f4x K i (c i)).prod, f4x K p 1⁆ = 1) :
    ∀ i ∈ f4KillOrderV, c i = 0 := by
  have hw : ∀ p ∈ f4TestListV, ⁅(f4PosList.map fun i => f4x K i (c i)).prod,
      ([p].map fun q => f4x K q ((fun _ => (1 : K)) q)).prod⁆ = 1 := fun p hp => by
    simpa using h p hp
  have h29 := hw 29 (by decide)
  have h30 := hw 30 (by decide)
  have h32 := hw 32 (by decide)
  have h35 := hw 35 (by decide)
  have h36 := hw 36 (by decide)
  have h37 := hw 37 (by decide)
  have hD0 : ∀ j ∈ f4KillOrderV.take 0, c j = 0 := by simp
  have k24 : c 24 = 0 := by
    simpa using f4_row_of f4KillOrderV c 0 hD0 (k := 31) (E := [(24, 1, 30, 1)])
      (by decide +kernel) h30
  have hD1 := f4_take_succ_of hD0 k24
  have k25 : c 25 = 0 := by
    simpa using f4_row_of f4KillOrderV c 1 hD1 (k := 31) (E := [(25, 1, 29, 1)])
      (by decide +kernel) h29
  have hD2 := f4_take_succ_of hD1 k25
  have k26 : c 26 = 0 := by
    simpa using f4_row_of f4KillOrderV c 2 hD2 (k := 38) (E := [(26, 1, 35, 1)])
      (by decide +kernel) h35
  have hD3 := f4_take_succ_of hD2 k26
  have k27 : c 27 = 0 := by
    simpa using f4_row_of f4KillOrderV c 3 hD3 (k := 40) (E := [(27, 1, 37, 1)])
      (by decide +kernel) h37
  have hD4 := f4_take_succ_of hD3 k27
  have k28 : c 28 = 0 := by
    simpa using f4_row_of f4KillOrderV c 4 hD4 (k := 41) (E := [(28, 1, 36, 1)])
      (by decide +kernel) h36
  have hD5 := f4_take_succ_of hD4 k28
  have k29 : c 29 = 0 := by
    simpa using f4_row_of f4KillOrderV c 5 hD5 (k := 41) (E := [(29, 1, 35, 1)])
      (by decide +kernel) h35
  have hD6 := f4_take_succ_of hD5 k29
  have k30 : c 30 = 0 := by
    simpa using f4_row_of f4KillOrderV c 6 hD6 (k := 43) (E := [(30, 1, 36, 1)])
      (by decide +kernel) h36
  have hD7 := f4_take_succ_of hD6 k30
  have k31 : c 31 = 0 := by
    simpa using f4_row_of f4KillOrderV c 7 hD7 (k := 43) (E := [(31, 1, 35, 1)])
      (by decide +kernel) h35
  have hD8 := f4_take_succ_of hD7 k31
  have k32 : c 32 = 0 := by
    simpa using f4_row_of f4KillOrderV c 8 hD8 (k := 44) (E := [(32, 1, 35, 1)])
      (by decide +kernel) h35
  have hD9 := f4_take_succ_of hD8 k32
  have k33 : c 33 = 0 := by
    simpa using f4_row_of f4KillOrderV c 9 hD9 (k := 36) (E := [(33, 1, 29, 1)])
      (by decide +kernel) h29
  have hD10 := f4_take_succ_of hD9 k33
  have k34 : c 34 = 0 := by
    simpa using f4_row_of f4KillOrderV c 10 hD10 (k := 40) (E := [(34, 1, 30, 1)])
      (by decide +kernel) h30
  have hD11 := f4_take_succ_of hD10 k34
  have k35 : c 35 = 0 := by
    simpa using f4_row_of f4KillOrderV c 11 hD11 (k := 41) (E := [(35, 1, 29, 1)])
      (by decide +kernel) h29
  have hD12 := f4_take_succ_of hD11 k35
  have k36 : c 36 = 0 := by
    simpa using f4_row_of f4KillOrderV c 12 hD12 (k := 43) (E := [(36, 1, 30, 1)])
      (by decide +kernel) h30
  have hD13 := f4_take_succ_of hD12 k36
  have k37 : c 37 = 0 := by
    simpa using f4_row_of f4KillOrderV c 13 hD13 (k := 43) (E := [(37, 1, 29, 1)])
      (by decide +kernel) h29
  have hD14 := f4_take_succ_of hD13 k37
  have k38 : c 38 = 0 := by
    simpa using f4_row_of f4KillOrderV c 14 hD14 (k := 44) (E := [(38, 1, 29, 1)])
      (by decide +kernel) h29
  have hD15 := f4_take_succ_of hD14 k38
  have k39 : c 39 = 0 := by
    simpa using f4_row_of f4KillOrderV c 15 hD15 (k := 45) (E := [(39, 1, 30, 1)])
      (by decide +kernel) h30
  have hD16 := f4_take_succ_of hD15 k39
  have k40 : c 40 = 0 := by
    simpa using f4_row_of f4KillOrderV c 16 hD16 (k := 46) (E := [(40, 1, 32, 1)])
      (by decide +kernel) h32
  have hD17 := f4_take_succ_of hD16 k40
  have k42 : c 42 = 0 := by
    simpa using f4_row_of f4KillOrderV c 17 hD17 (k := 46) (E := [(42, 1, 30, 1)])
      (by decide +kernel) h30
  have hD18 := f4_take_succ_of hD17 k42
  rw [show f4KillOrderV.take 18 = f4KillOrderV by decide] at hD18
  exact hD18

theorem sq_eq_one_of_commute_classV [Finite K] [CharP K 2] {z : ModGL .F4 K}
    (hz : z ∈ posUnipotent .F4 K) (h : ∀ p ∈ f4TestListV, z * f4x K p 1 = f4x K p 1 * z) :
    z ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := exists_f4_coords hz
  have h0 := f4_coords_eq_zero_of_commute_classV c fun p hp => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact h p hp
  have hcover : ∀ i ∈ f4PosList, decide (i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ)) = false →
      i ∈ f4KillOrderV := by
    decide
  have hA : ∀ i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ), ∀ j ∈ ([41, 43, 44, 45, 46, 47] : List ℕ),
      (24 ≤ i ∧ i ≤ 47) ∧ (24 ≤ j ∧ j ≤ 47) ∧
        (i ≠ j → (f4OddCommutatorFactors.lookup (i, j)).getD [] = []) := by
    decide +kernel
  rw [← list_prod_map_filter_of_eq_one f4PosList
    (fun i => decide (i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ))) _
    (fun i hi hne => by rw [h0 i (hcover i hi hne), f4x_zero]),
    show f4PosList.filter (fun i => decide (i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ))) =
      [41, 43, 44, 45, 46, 47] by decide]
  refine list_prod_sq_eq_one _ (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hi', hj', hl⟩ := hA i hi j hj
    exact f4x_commute_of_lookup hi' hj' hl _ _
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    simp only [sq, f4x, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem f4x_mem_closure_odd_classV {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p ∈ f4CentListV) (c : K) :
    (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈
      closure {x : adjointGroup .F4 K | x * ⟨f4x K 41 1 * f4x K 45 1, mul_mem
        (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ =
          ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)⟩ * x ∧ Odd (orderOf x)} := by
  set v : adjointGroup .F4 K := ⟨f4x K 41 1 * f4x K 45 1, mul_mem
    (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ with hv
  set S := {x : adjointGroup .F4 K | x * v = v * x ∧ Odd (orderOf x)}
  obtain ⟨c₀, hc₀0, hc₀1⟩ : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
    by_contra hcon'
    have hcon : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h => hcon' ⟨x, hx, h⟩
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hK] at hle
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
  have hstep : ∀ m : Fin Tag.F4.rank → ℤ, f4Pairing m (orbitCertRoot .F4 41) = 0 →
      f4Pairing m (orbitCertRoot .F4 45) = 0 → ∀ q ∈ f4CentListV,
      f4Pairing m (orbitCertRoot .F4 q) ∈ [1, -1, 2, -2] → ∀ c : K,
      (⟨f4x K q c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S := by
    intro m hm41 hm45 q hq hmq c
    have hq' := (f4CentListV_lookup q hq).1
    set a : Fin Tag.F4.rank → Kˣ := fun i => w ^ m i
    obtain ⟨ha, -⟩ := (hrest B hB a).2.2
    have hT : (⟨rootDiagUnit .F4 a, ha⟩ : adjointGroup .F4 K) * v =
        v * ⟨rootDiagUnit .F4 a, ha⟩ :=
      Subtype.ext (rootDiagUnit_commute_classV (by rw [rootChar_zpow, hm41, zpow_zero])
        (by rw [rootChar_zpow, hm45, zpow_zero]))
    have hodd : Odd (orderOf (⟨rootDiagUnit .F4 a, ha⟩ : adjointGroup .F4 K)) := by
      rw [← Subgroup.orderOf_coe]
      exact odd_orderOf_rootDiagUnit (by omega) hK a
    have hl : ((rootChar a (orbitCertRoot .F4 q) : Kˣ) : K) ≠ 1 := by
      rw [Ne, Units.val_eq_one, rootChar_zpow]
      refine zpow_ne_one_of_charTwo hw ?_
      simpa using hmq
    exact pinnedX_mem_closure_of_conj hT hodd hl
      (fun d => rootDiagUnit_conj_pinnedX a (f4_isRoot_pos hq').1 d)
      (fun d => Subtype.ext (f4x_commute_classV hq d)) c
  have g : ∀ q ∈ f4CentListV, q ≠ 41 → q ≠ 45 → ∀ c : K,
      (⟨f4x K q c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S := by
    intro q hq h41 h45 c
    have hq' := (f4CentListV_lookup q hq).1
    have hqg : q ∈ f4GenericListV := by
      simp only [f4GenericListV, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨⟨h1, h2, h3, h4⟩, hall⟩ := f4_torus_check_classV
    rcases hall q hqg with h | h
    · exact hstep _ h1 h2 q hq h c
    · exact hstep _ h3 h4 q hq h c
  have hcl : ∀ {i j : ℕ} (s t' : K),
      (⟨f4x K i s, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S →
      (⟨f4x K j t', pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S →
      ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) = ⁅f4x K i s, f4x K j t'⁆ → x ∈ closure S := by
    intro i j s t' hi hj x hx
    have e : x = ⁅(⟨f4x K i s, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K),
        ⟨f4x K j t', pinnedX_mem_adjointGroup _ _⟩⁆ := by
      refine Subtype.ext ?_
      rw [hx, commutatorElement_def, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hi hj) (inv_mem hi)) (inv_mem hj)
  by_cases h41 : p = 41
  ·
    subst h41
    have h := f4x_commutator_eq (K := K) (i := 29) (j := 35) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) 1 c
    have hl : (f4OddCommutatorFactors.lookup (29, 35)).getD [] = [(1, 1, 41)] := by
      decide +kernel
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    exact hcl (i := 29) (j := 35) 1 c (g 29 (by decide) (by decide) (by decide) 1)
      (g 35 (by decide) (by decide) (by decide) c) _ h.symm
  by_cases h45 : p = 45
  ·
    subst h45
    have h := f4x_commutator_eq (K := K) (i := 32) (j := 37) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) 1 c
    have hl : (f4OddCommutatorFactors.lookup (32, 37)).getD [] = [(1, 1, 45)] := by
      decide +kernel
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    exact hcl (i := 32) (j := 37) 1 c (g 32 (by decide) (by decide) (by decide) 1)
      (g 37 (by decide) (by decide) (by decide) c) _ h.symm
  exact g p hp h41 h45 c

theorem mem_of_mem_heightSeries_three_of_forall_f4x {H : Subgroup (adjointGroup .F4 K)}
    (h : ∀ p, 24 ≤ p → p ≤ 47 → 3 ≤ height (orbitCertRoot .F4 p) → ∀ c : K,
      (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ H)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ heightSeries .F4 K 3) : u ∈ H := by
  have hle : heightSeries .F4 K 3 ≤ H.map (adjointGroup .F4 K).subtype := by
    rw [heightSeries, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨β, hβ, d, rfl⟩
    obtain ⟨p, hp, hp', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 β).1 ⟨hβ.1, hβ.2.1⟩
    exact ⟨_, h p hp hp' hβ.2.2 d, rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  rwa [show u = x from Subtype.ext hxu.symm]

theorem innerCentralizerCriterion_F4_v_of_le {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f)
    (hodd : ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ heightSeries .F4 K 3 →
      x ∈ closure {c : adjointGroup .F4 K | c * ⟨f4x K 41 1 * f4x K 45 1, mul_mem
        (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ =
          ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)⟩ * c ∧ Odd (orderOf c)}) :
    InnerCentralizerCriterion
      (⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  refine innerCentralizerCriterion_of_pointwise
    (CFSG.ComponentClassification.UnbalancedCatalog.conj_injective center_adjointGroup_eq_bot)
    (V := (heightSeries .F4 K 3).subgroupOf (adjointGroup .F4 K))
    (fun x hx => hodd x (Subgroup.mem_subgroupOf.1 hx)) fun β hβ => ?_
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g₀, k⟩, hgk₀, -⟩ := hnf β
  set g : adjointGroup .F4 K := g₀
  have hgk : β = MulAut.conj g * (f4Phi (K := K)) ^ (k : ℕ) := hgk₀
  clear_value g
  clear hgk₀
  have hfixp : ∀ p, 24 ≤ p → p ≤ 47 → 3 ≤ height (orbitCertRoot .F4 p) →
      β ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ = ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ :=
    fun p hp hp' h3 => hβ _ (Subgroup.mem_subgroupOf.2
      (pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α ∧ 3 ≤ height α})
        ⟨(f4_isRoot_pos ⟨hp, hp'⟩).1, (f4_isRoot_pos ⟨hp, hp'⟩).2, h3⟩ 1))
  rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    have hA : β ∈ diagonalFieldActors .F4 K := by
      rw [hgk, hj, ← two_mul, f4Phi_pow_two_mul]
      exact mul_mem ((Chevalley_diagonal_field_actor_data.1 .F4 K).2.2 ⟨g, rfl⟩)
        (pow_mem f4Fr_mem_diagonalFieldActors j)
    obtain ⟨u, hu, huC, rfl⟩ := exists_eq_conj_of_mem_actors_of_fix_heightSeries hA
      fun x hx => hβ x (Subgroup.mem_subgroupOf.2 hx)
    refine ⟨⟨u, huC⟩, rfl, fun _ => Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    refine sq_eq_one_of_commute_classV hu fun p hp => ?_
    obtain ⟨⟨hp1, hp2⟩, h3⟩ := f4TestListV_spec p hp
    have h1 := congrArg Subtype.val (hfixp p hp1 hp2 h3)
    rw [MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc u * f4x K p 1 = u * f4x K p 1 * u⁻¹ * u := by group
      _ = f4x K p 1 * u := by rw [h1]
  ·
    exfalso
    have h47 := hfixp 47 (by norm_num) (by norm_num) (by decide)
    rw [hgk, MulAut.mul_apply, hj, f4Phi_pow_odd_f4x_47, MulAut.conj_apply] at h47
    have h47' := congrArg Subtype.val h47
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h47'
    refine conj_f4x_47_ne_f4x_44 (inv_mem g.2) ?_
    rw [← h47']
    group

theorem innerCentralizerCriterion_F4_v {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) := by
  refine innerCentralizerCriterion_F4_v_of_le (by omega) hK fun x hx =>
    mem_of_mem_heightSeries_three_of_forall_f4x (fun p hp hp' h3 c => ?_) hx
  have hpc : p ∈ f4CentListV := by
    interval_cases p <;> first | decide | exact absurd h3 (by decide)
  exact f4x_mem_closure_odd_classV hf hK hpc c

theorem innerInvolutionInput_F4_of_classes_v {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f)
    (hrep : ∀ x : adjointGroup .F4 K, orderOf (MulAut.conj x) = 2 →
      ∃ ψ : MulAut (adjointGroup .F4 K), ∃ s ∈ ({⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩,
        ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩,
        ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩} : Set (adjointGroup .F4 K)), ψ s = x) :
    InnerInvolutionInput (adjointGroup .F4 K) :=
  innerInvolutionInput_F4_of_classes hf hK (innerCentralizerCriterion_F4_v hf hK) hrep

end CFSG.SeitzReduction
