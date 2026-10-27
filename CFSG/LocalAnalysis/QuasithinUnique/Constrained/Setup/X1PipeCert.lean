module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Coset

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

section REnum

variable [Finite Γ] [FaithfulSMul Γ (Fin n)]

omit [Finite Γ] in
theorem benum_data (qs : List (Γ × Γ)) (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹)
    (hE : BaseEnumOK n (List.range n) (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl) :
    (∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst} ↔
      rt n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) x ∈ Ts.toList) ∧
    Nat.card (Subgroup.closure {x | x ∈ qs.map Prod.fst}) = Ts.size ∧
    (∀ i, i < Ts.size → ∃ x ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst},
      rt n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) x = Ts[i]!) := by
  let gens : List Γ := qs.map Prod.fst
  have hG : qs.map (fun p => (tab n p.1).toArray) = genTabs n gens := by
    simp only [genTabs, gens, List.map_map, Function.comp_def]
  have hGi : qs.map (fun p => (tab n p.2).toArray) = genTabsInv n gens := by
    simp only [genTabsInv, gens, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [hqsinv p hp]
  rw [hG, hGi] at hE
  have hB : ∀ b ∈ List.range n, b < n := fun b hb => List.mem_range.mp hb
  have hP : ∀ p ∈ ptsOf (List.range n) (genTabs n gens), p < n := ptsOf_lt hB gens
  have hBP : ∀ b ∈ List.range n, b ∈ ptsOf (List.range n) (genTabs n gens) :=
    fun b hb => List.mem_append_left _ hb
  refine ⟨fun x => ?_, benum_card hB base_of_faithful gens Ts rpar rcl hE,
    benum_reach hB gens Ts rpar rcl hE⟩
  refine ⟨benum_closed hB gens Ts rpar rcl hE x, fun hx => ?_⟩
  obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hx
  have hiT' : i < Ts.size := by simpa using hi
  obtain ⟨y, hy, hyT⟩ := benum_reach hB gens Ts rpar rcl hE i hiT'
  have : rt n (ptsOf (List.range n) (genTabs n gens)) y =
      rt n (ptsOf (List.range n) (genTabs n gens)) x := by
    rw [hyT, getElem!_pos Ts i hiT']
    simpa using hiT
  rwa [← rt_injective hB hBP base_of_faithful this]

omit [Finite Γ] [FaithfulSMul Γ (Fin n)] in
theorem mem_R_of_memR (qs : List (Γ × Γ)) (Ts : Array (List ℕ)) (hn : 0 < n)
    (hmem : ∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst} ↔
      rt n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) x ∈ Ts.toList) (y : Γ)
    (h : memR n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) Ts (keyMap n Ts)
      (tab n y).toArray = true) :
    y ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst} := by
  rw [hmem]
  unfold memR at h
  set cand := (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))).map (img (tab n y).toArray)
    with hcand
  have hrt : rt n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) y = cand := by
    unfold rt
    rw [hcand]
    apply List.map_congr_left
    intro p _
    rw [img_tab]
  rw [hrt]
  cases hk : (keyMap n Ts)[keyNat n n cand]? with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, decide_eq_true_eq] at h
    by_cases hks : k < Ts.size
    · rw [← h]
      have : Ts.getD k [] = Ts[k] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hks]; rfl
      rw [this]
      exact Array.getElem_mem_toList hks
    · exfalso
      have h1 : Ts.getD k [] = [] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
      rw [h1] at h
      have h2 : cand.length ≠ 0 := by
        rw [hcand, List.length_map]
        simp only [ptsOf, List.length_append, List.length_range]
        omega
      rw [← h] at h2
      exact h2 rfl

end REnum

section ActsOnTables

variable {P : Type*} [Group P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem arrImg_compArr (S T : Array ℕ) {i : ℕ} (hi : i < T.size) :
    arrImg (compArr S T) i = arrImg S (arrImg T i) := by
  have e1 : arrImg (compArr S T) i = S[T[i]]! := by
    unfold arrImg compArr
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi]
    rfl
  have e2 : arrImg T i = T[i] := by
    unfold arrImg
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  rw [e1, e2]
  unfold arrImg
  by_cases h : T[i] < S.size
  · rw [getElem!_pos S _ h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rfl
  · rw [getElem!_neg S _ h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

theorem actsOn_comp (C : CosetCert R a b N) {g h : P} {S T : Array ℕ}
    (hg : ActsOn C g (arrImg S)) (hh : ActsOn C h (arrImg T)) (hT : N ≤ T.size) :
    ActsOn C (g * h) (arrImg (compArr S T)) := by
  intro i hi
  have key := actsOn_mul C hg hh i hi
  rw [arrImg_compArr S T (lt_of_lt_of_le hi hT)]
  exact key

theorem arrImg_range {i : ℕ} (hi : i < N) : arrImg (Array.range N) i = i := by
  simp [arrImg, Array.getD_eq_getD_getElem?, hi]

theorem actsOn_range (C : CosetCert R a b N) : ActsOn C 1 (arrImg (Array.range N)) := by
  intro i hi
  rw [arrImg_range hi]
  exact ⟨hi, by simp⟩

end ActsOnTables

section SLPAct

theorem foldl_slpStepA_size (prog : List (ℕ × ℕ)) (T : Array (Array ℕ)) :
    (prog.foldl slpStepA T).size = T.size + prog.length := by
  induction prog generalizing T with
  | nil => simp
  | cons p prog ih =>
    rw [List.foldl_cons, ih]
    simp only [slpStepA, Array.size_push, List.length_cons]
    omega

theorem slpTabsA_size (ta tb : Array ℕ) (prog : List (ℕ × ℕ)) :
    (slpTabsA ta tb prog).size = prog.length + 2 := by
  unfold slpTabsA
  rw [foldl_slpStepA_size]
  simp only [List.size_toArray, List.length_cons, List.length_nil]
  omega

variable {P : Type} [Group P] {R : Subgroup P} {a b : P} {N : ℕ}

theorem slp_actsOn_aux (C : CosetCert R a b N) (prog : List (ℕ × ℕ)) :
    ∀ (E : Array P) (T : Array (Array ℕ)), E.size = T.size →
      (∀ i < T.size, ActsOn C (E.getD i 1) (arrImg T[i]!) ∧ N ≤ T[i]!.size) →
      slpValidAux prog T.size = true →
      ∀ i < (prog.foldl slpStepA T).size,
        ActsOn C ((prog.foldl eltStep E).getD i 1) (arrImg (prog.foldl slpStepA T)[i]!) ∧
          N ≤ (prog.foldl slpStepA T)[i]!.size := by
  induction prog with
  | nil => intro E T _ hT _; exact hT
  | cons p prog ih =>
    intro E T hE hT hv
    simp only [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hp, hv'⟩ := hv
    simp only [List.foldl_cons]
    have hTs : (slpStepA T p).size = T.size + 1 := by simp [slpStepA]
    refine ih (eltStep E p) (slpStepA T p) ?_ ?_ (by rw [hTs]; exact hv')
    · simp [eltStep, slpStepA, hE]
    · intro i hi
      rw [hTs] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · simp only [eltStep, slpStepA]
        rw [getD_push_lt E _ 1 (by omega), getElem!_push_lt' T _ hi]
        exact hT i hi
      · subst hi
        simp only [eltStep, slpStepA]
        have e1 : (E.push (E.getD p.1 1 * E.getD p.2 1)).getD T.size 1 =
            E.getD p.1 1 * E.getD p.2 1 := by
          rw [← hE]; exact getD_push_self E _ 1
        have e2 : (T.push (compArr T[p.1]! T[p.2]!))[T.size]! = compArr T[p.1]! T[p.2]! :=
          getElem!_push_self' T _
        rw [e1, e2]
        exact ⟨actsOn_comp C (hT p.1 hp.1).1 (hT p.2 hp.2).1 (hT p.2 hp.2).2,
          by simpa [compArr] using (hT p.2 hp.2).2⟩

theorem slp_actsOn (C : CosetCert R a b N) {Aa Ab : Array ℕ} (hA : ∀ i, C.Aa i = arrImg Aa i)
    (hB : ∀ i, C.Ab i = arrImg Ab i) (hasz : aszOK N Aa Ab) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) :
    ∀ i < (slpTabsA Aa Ab prog).size,
      ActsOn C ((slpElts a b prog).getD i 1) (arrImg (slpTabsA Aa Ab prog)[i]!) ∧
        N ≤ (slpTabsA Aa Ab prog)[i]!.size := by
  have hAact : ActsOn C a (arrImg Aa) := by
    intro i hi
    have h1 := actsOn_a C i hi
    rw [hA i] at h1
    exact h1
  have hBact : ActsOn C b (arrImg Ab) := by
    intro i hi
    have h1 := actsOn_b C i hi
    rw [hB i] at h1
    exact h1
  exact slp_actsOn_aux C prog #[a, b] #[Aa, Ab] (by simp) (by
    intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · exact ⟨by simpa using hAact, by simpa using hasz.1⟩
    · exact ⟨by simpa using hBact, by simpa using hasz.2⟩) hv

end SLPAct

section ExistsCert

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_compArr (g h : Γ) :
    compArr (tab n g).toArray (tab n h).toArray = (tab n (g * h)).toArray := by
  apply Array.toList_inj.1
  rw [compArr_toList, tab_mul]

theorem getD_eq_getElem!_of_lt (T : Array (Array ℕ)) {i : ℕ} (hi : i < T.size) :
    T.getD i #[] = T[i]! := by
  rw [getElem!_pos T i hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

theorem treeTabs_getD {N : ℕ} {a b : Γ} {ta tb par gen : Array ℕ} (hta : tab n a = ta.toList)
    (htb : tab n b = tb.toList) (hv : treeValid N par gen) (hN : 0 < N) :
    ∀ i < N, (treeTabs n N ta tb par gen).getD i #[] = (tab n (treeR a b par gen i)).toArray := by
  intro i hi
  obtain ⟨hsz, hent⟩ := treeTabs_spec hta htb hv (N - 1) (by omega)
  have hiT : i < (treeTabs n N ta tb par gen).size := by
    show i < ((List.range' 1 (N - 1)).foldl (treeStepT ta tb par gen) #[Array.range n]).size
    rw [hsz]; omega
  rw [getD_eq_getElem!_of_lt _ hiT]
  exact hent i (by omega)

theorem treeInvTabs_getD {N : ℕ} {a b : Γ} {tai tbi par gen : Array ℕ}
    (htai : tab n a⁻¹ = tai.toList) (htbi : tab n b⁻¹ = tbi.toList) (hv : treeValid N par gen)
    (hN : 0 < N) :
    ∀ i < N, (treeInvTabs n N tai tbi par gen).getD i #[] =
      (tab n (treeR a b par gen i)⁻¹).toArray := by
  intro i hi
  obtain ⟨hsz, hent⟩ := treeInvTabs_spec (a := a) (b := b) htai htbi hv (N - 1) (by omega)
  have hiT : i < (treeInvTabs n N tai tbi par gen).size := by
    show i < ((List.range' 1 (N - 1)).foldl (treeStepU tai tbi par gen) #[Array.range n]).size
    rw [hsz]; omega
  rw [getD_eq_getElem!_of_lt _ hiT]
  exact hent i (by omega)

theorem exists_cert (a b : Γ) (R : Subgroup Γ) {N : ℕ} (hN : Nat.card (Γ ⧸ R) = N) (hN0 : 0 < N)
    {par gen Aa Ab : Array ℕ} (htv : treeValid N par gen) (P : List ℕ) (Ts : Array (List ℕ))
    (hmem : ∀ y : Γ, memR n P Ts (keyMap n Ts) (tab n y).toArray = true → y ∈ R)
    (hedge : edgeOK n N P Ts (keyMap n Ts) (tab n a).toArray (tab n b).toArray Aa Ab
      (treeTabs n N (tab n a).toArray (tab n b).toArray par gen)
      (treeInvTabs n N (tab n a⁻¹).toArray (tab n b⁻¹).toArray par gen) = true) :
    ∃ C : CosetCert R a b N, (∀ x, C.r x = treeR a b par gen x) ∧
      (∀ i, C.Aa i = arrImg Aa i) ∧ (∀ i, C.Ab i = arrImg Ab i) := by
  have hta : tab n a = (tab n a).toArray.toList := by simp
  have htb : tab n b = (tab n b).toArray.toList := by simp
  have htai : tab n a⁻¹ = (tab n a⁻¹).toArray.toList := by simp
  have htbi : tab n b⁻¹ = (tab n b⁻¹).toArray.toList := by simp
  have hT := treeTabs_getD (a := a) (b := b) hta htb htv hN0
  have hU := treeInvTabs_getD (a := a) (b := b) htai htbi htv hN0
  unfold edgeOK at hedge
  rw [List.all_eq_true] at hedge
  have key : ∀ i < N, arrImg Aa i < N ∧ arrImg Ab i < N ∧
      (treeR a b par gen (arrImg Aa i))⁻¹ * (a * treeR a b par gen i) ∈ R ∧
      (treeR a b par gen (arrImg Ab i))⁻¹ * (b * treeR a b par gen i) ∈ R := by
    intro i hi
    have h := hedge i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, h2, hmem _ ?_, hmem _ ?_⟩
    · rw [hU _ h1, hT i hi] at h3
      rw [tab_compArr, tab_compArr] at h3
      exact h3
    · rw [hU _ h2, hT i hi] at h4
      rw [tab_compArr, tab_compArr] at h4
      exact h4
  refine ⟨⟨treeR a b par gen, arrImg Aa, arrImg Ab, treeR_zero a b par gen, hN, hN0, ?_, ?_⟩,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · intro i hi
    obtain ⟨h1, _, h3, _⟩ := key i hi
    exact ⟨h1, h3⟩
  · intro i hi
    obtain ⟨_, h2, _, h4⟩ := key i hi
    exact ⟨h2, h4⟩

end ExistsCert

section SLPTabs

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem slp_tabs_spec (a b : Γ) (prog : List (ℕ × ℕ)) (hv : slpValidAux prog 2 = true) :
    ∀ i < (slpTabsA (tab n a).toArray (tab n b).toArray prog).size,
      (tab n ((slpElts a b prog).getD i 1)).toArray =
        (slpTabsA (tab n a).toArray (tab n b).toArray prog)[i]! := by
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  intro i hi
  have hi' : i < (List.foldl slpStepA #[(tab n a).toArray, (tab n b).toArray] prog).size := hi
  have := hinv.2 i hi'
  show (tab n ((List.foldl eltStep #[a, b] prog).getD i 1)).toArray =
    (List.foldl slpStepA #[(tab n a).toArray, (tab n b).toArray] prog)[i]!
  rw [this, Array.toArray_toList]

omit [MulAction Γ (Fin n)] in
theorem slpElts_size (a b : Γ) (prog : List (ℕ × ℕ)) :
    (slpElts a b prog).size = prog.length + 2 := by
  have key : ∀ (E : Array Γ) (prog : List (ℕ × ℕ)),
      (prog.foldl eltStep E).size = E.size + prog.length := by
    intro E prog
    induction prog generalizing E with
    | nil => simp
    | cons p prog ih =>
      rw [List.foldl_cons, ih]
      simp only [eltStep, Array.size_push, List.length_cons]
      omega
  unfold slpElts
  rw [key]
  simp only [List.size_toArray, List.length_cons, List.length_nil]
  omega

end SLPTabs

section Inv

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem eq_inv_of_img (x y : Γ)
    (hxy : ∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) : y = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := n)
  intro b hb
  have hb' : b < n := List.mem_range.mp hb
  rw [act_mul _ _ hb']
  have := hxy b hb'
  simpa only [img_tab] using this

end Inv

end CFSG.QuasithinUnique.Setup.X1
