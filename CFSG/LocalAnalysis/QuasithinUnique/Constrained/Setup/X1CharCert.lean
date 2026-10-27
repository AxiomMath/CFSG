module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeCert

public section

open scoped commutatorElement

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

section Ucs

variable {G : Type*} [Group G]

theorem mem_ucs_succ_iff_gens (S : Set G) (hS : Subgroup.closure S = ⊤) (n : ℕ) (x : G) :
    x ∈ Subgroup.upperCentralSeries G (n + 1) ↔ ∀ s ∈ S, ⁅x, s⁆ ∈ Subgroup.upperCentralSeries G n := by
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  constructor
  · intro h s _; exact h s
  · intro h y
    let P : Subgroup G :=
      { carrier := {y | ⁅x, y⁆ ∈ Subgroup.upperCentralSeries G n}
        one_mem' := by simp
        mul_mem' := by
          intro y z hy hz
          have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
            simp only [commutatorElement_def]; group
          show ⁅x, y * z⁆ ∈ Subgroup.upperCentralSeries G n
          rw [e]
          exact Subgroup.mul_mem _ hy ((Subgroup.upperCentralSeries G n).normal_of_characteristic.conj_mem _
            hz y)
        inv_mem' := by
          intro y hy
          have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
            simp only [commutatorElement_def]; group
          show ⁅x, y⁻¹⁆ ∈ Subgroup.upperCentralSeries G n
          rw [e]
          exact (Subgroup.upperCentralSeries G n).normal_of_characteristic.conj_mem _
            (Subgroup.inv_mem _ hy) y⁻¹ }
    have hP : Subgroup.closure S ≤ P := (Subgroup.closure_le P).2 fun s hs => h s hs
    rw [hS] at hP
    exact hP (Subgroup.mem_top y)

end Ucs

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

@[expose] def tA (n : ℕ) [MulAction Γ (Fin n)] (x : Γ) : Array ℕ := (tab n x).toArray

omit [FaithfulSMul Γ (Fin n)] in
theorem tA_mul (x y : Γ) : compArr (tA n x) (tA n y) = tA n (x * y) := tab_compArr x y

theorem tA_inj {x y : Γ} (h : tA n x = tA n y) : x = y :=
  eq_of_tab_eq (Array.toList_inj.2 h |> fun h' => by simpa [tA] using h')

omit [FaithfulSMul Γ (Fin n)] in
theorem tA_one : tA n (1 : Γ) = Array.range n := by
  apply Array.toList_inj.1
  simp [tA, tab_one]

theorem tA_eq_range_iff {x : Γ} : tA n x = Array.range n ↔ x = 1 := by
  constructor
  · intro h
    exact tA_inj (h.trans tA_one.symm)
  · rintro rfl; exact tA_one

omit [FaithfulSMul Γ (Fin n)] in
theorem tab_eq_range_map (x : Γ) : tab n x = (List.range n).map (act n x) := by
  apply List.ext_getElem
  · simp [tab_length]
  · intro i h1 h2
    have hi : i < n := by simpa [tab_length] using h1
    have : (tab n x)[i] = act n x i := by
      simp [act, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rw [this]
    simp

omit [FaithfulSMul Γ (Fin n)] in
theorem take_rt (qs : List (Γ × Γ)) (x : Γ) :
    (rt n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) x).take n = tab n x := by
  unfold rt ptsOf
  rw [List.map_append, tab_eq_range_map x]
  have : ((List.range n).map (act n x)).length = n := by simp
  rw [List.take_left' this]

end Tables

section RMembership

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

omit [FaithfulSMul Γ (Fin n)] in
theorem tA_eq_of_rt {qs : List (Γ × Γ)} {x : Γ} {T : List ℕ}
    (h : rt n (ptsOf (List.range n) (genTabs n (qs.map Prod.fst))) x = T) :
    (T.take n).toArray = tA n x := by
  rw [← h, take_rt]; rfl

theorem mem_R_iff_tab (qs : List (Γ × Γ)) (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹)
    (hE : BaseEnumOK n (List.range n) (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl) (x : Γ) :
    x ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst} ↔ tA n x ∈ fullTables n Ts := by
  obtain ⟨hmem, _, hreach⟩ := benum_data qs Ts rpar rcl hqsinv hE
  constructor
  · intro hx
    exact List.mem_map.2 ⟨_, (hmem x).1 hx, tA_eq_of_rt rfl⟩
  · intro hx
    obtain ⟨T, hT, hTx⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    have hi' : i < Ts.size := by simpa using hi
    obtain ⟨y, hy, hyT⟩ := hreach i hi'
    have h1 : tA n y = tA n x := by
      rw [← hTx, ← tA_eq_of_rt hyT, getElem!_pos Ts i hi']
      simp
    rw [← tA_inj h1]
    exact hy

theorem exists_of_mem_fullTables (qs : List (Γ × Γ)) (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹)
    (hE : BaseEnumOK n (List.range n) (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl) {T : Array ℕ}
    (hT : T ∈ fullTables n Ts) : ∃ x : Γ, tA n x = T := by
  obtain ⟨_, _, hreach⟩ := benum_data qs Ts rpar rcl hqsinv hE
  obtain ⟨U, hU, hUT⟩ := List.mem_map.1 hT
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hU
  have hi' : i < Ts.size := by simpa using hi
  obtain ⟨y, _, hyT⟩ := hreach i hi'
  refine ⟨y, ?_⟩
  rw [← hUT, ← tA_eq_of_rt hyT, getElem!_pos Ts i hi']
  simp

end RMembership

section Zser

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

@[expose] def ZK (R : Subgroup Γ) (k : ℕ) : Subgroup Γ :=
  (Subgroup.upperCentralSeries ↥R k).map R.subtype

theorem mem_ZK_succ_iff_gens (gensG : List Γ) (k : ℕ) (x : Γ) :
    x ∈ ZK (Subgroup.closure {x | x ∈ gensG}) (k + 1) ↔
      x ∈ Subgroup.closure {x | x ∈ gensG} ∧
        ∀ s ∈ gensG, ⁅x, s⁆ ∈ ZK (Subgroup.closure {x | x ∈ gensG}) k := by
  set R := Subgroup.closure {x | x ∈ gensG} with hR
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r.2, fun s hs => ?_⟩
    have hsR : s ∈ R := Subgroup.subset_closure hs
    have := (Subgroup.mem_upperCentralSeries_succ_iff.1 hr) ⟨s, hsR⟩
    exact ⟨_, this, rfl⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_ucs_succ_iff_gens (((↑) : R → Γ) ⁻¹' {x | x ∈ gensG})
      Subgroup.closure_closure_coe_preimage]
    intro s' hs'
    obtain ⟨w, hw, hwe⟩ := h s'.1 hs'
    have : w = ⁅(⟨x, hx⟩ : R), s'⁆ := Subtype.ext hwe
    rw [← this]
    exact hw

theorem tA_comm_iff {Z : List (Array ℕ)} (hZ : ∀ T ∈ Z, ∃ y : Γ, tA n y = T) (x s : Γ) :
    commIn Z (tA n x) (tA n s) = true ↔ tA n ⁅x, s⁆ ∈ Z := by
  unfold commIn
  rw [List.any_eq_true]
  constructor
  · rintro ⟨z, hz, hzeq⟩
    obtain ⟨y, rfl⟩ := hZ z hz
    simp only [beq_iff_eq] at hzeq
    rw [tA_mul, tA_mul, tA_mul] at hzeq
    have h1 := tA_inj hzeq
    have : ⁅x, s⁆ = y := by
      have e : y = x * s * (s * x)⁻¹ := by rw [h1]; group
      rw [e, commutatorElement_def]; group
    rw [this]; exact hz
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [beq_iff_eq]
    rw [tA_mul, tA_mul, tA_mul]
    congr 1
    rw [commutatorElement_def]; group

omit [FaithfulSMul Γ (Fin n)] in
theorem zSeries_surj (Rl : List (Array ℕ)) (hsurj : ∀ T ∈ Rl, ∃ y : Γ, tA n y = T)
    (gens : List (Array ℕ)) (k : ℕ) :
    ∀ T ∈ zSeries Rl gens (Array.range n) k, ∃ y : Γ, tA n y = T := by
  cases k with
  | zero =>
    intro T hT
    simp only [zSeries, List.mem_singleton] at hT
    exact ⟨1, by rw [hT]; exact tA_one⟩
  | succ k =>
    intro T hT
    simp only [zSeries, zStep, List.mem_filter] at hT
    exact hsurj T hT.1

theorem zSeries_spec (gensG : List Γ) (Rl : List (Array ℕ))
    (hRl : ∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ gensG} ↔ tA n x ∈ Rl)
    (hsurj : ∀ T ∈ Rl, ∃ y : Γ, tA n y = T) (k : ℕ) :
    ∀ x : Γ, x ∈ ZK (Subgroup.closure {x | x ∈ gensG}) k ↔
      tA n x ∈ zSeries Rl (gensG.map (tA n)) (Array.range n) k := by
  induction k with
  | zero =>
    intro x
    simp only [ZK, Subgroup.upperCentralSeries_zero, zSeries, List.mem_singleton]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hr
      subst hr
      exact tA_one
    · intro h
      have : x = 1 := tA_eq_range_iff.1 h
      subst this
      exact ⟨1, Subgroup.one_mem _, rfl⟩
  | succ k ih =>
    intro x
    rw [mem_ZK_succ_iff_gens]
    simp only [zSeries, zStep, List.mem_filter, List.all_eq_true, List.mem_map]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨(hRl x).1 hx, fun S hS => ?_⟩
      obtain ⟨s, hs, rfl⟩ := hS
      exact (tA_comm_iff (zSeries_surj Rl hsurj _ k) x s).2 ((ih _).1 (h s hs))
    · rintro ⟨hx, h⟩
      refine ⟨(hRl x).2 hx, fun s hs => ?_⟩
      exact (ih _).2 ((tA_comm_iff (zSeries_surj Rl hsurj _ k) x s).1 (h _ ⟨s, hs, rfl⟩))

end Zser

section Cen

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem cenList_spec (gensG : List Γ) (Rl : List (Array ℕ))
    (hRl : ∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ gensG} ↔ tA n x ∈ Rl)
    (hsurj : ∀ T ∈ Rl, ∃ y : Γ, tA n y = T) (k : ℕ) (x : Γ) :
    x ∈ (Subgroup.centralizer
        ((Subgroup.upperCentralSeries ↥(Subgroup.closure {x | x ∈ gensG}) k :
          Subgroup ↥(Subgroup.closure {x | x ∈ gensG})) :
          Set ↥(Subgroup.closure {x | x ∈ gensG}))).map
        (Subgroup.closure {x | x ∈ gensG}).subtype ↔
      tA n x ∈ cenList Rl (zSeries Rl (gensG.map (tA n)) (Array.range n) k) := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp only [cenList, List.mem_filter, List.all_eq_true, beq_iff_eq]
    refine ⟨(hRl _).1 r.2, fun Y hY => ?_⟩
    obtain ⟨w, rfl⟩ := zSeries_surj Rl hsurj _ k Y hY
    have hw : w ∈ ZK (Subgroup.closure {x | x ∈ gensG}) k :=
      (zSeries_spec gensG Rl hRl hsurj k w).2 hY
    obtain ⟨u, hu, rfl⟩ := hw
    have h1 := Subgroup.mem_centralizer_iff.1 hr u hu
    have h2 : (r : Γ) * (u : Γ) = (u : Γ) * (r : Γ) := congrArg Subtype.val h1.symm
    show compArr (tA n (r : Γ)) (tA n (u : Γ)) = compArr (tA n (u : Γ)) (tA n (r : Γ))
    rw [tA_mul, tA_mul, h2]
  · intro h
    simp only [cenList, List.mem_filter, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hxl, hcomm⟩ := h
    have hx : x ∈ Subgroup.closure {x | x ∈ gensG} := (hRl x).2 hxl
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : (u : Γ) ∈ ZK (Subgroup.closure {x | x ∈ gensG}) k := ⟨u, hu, rfl⟩
    have hT := (zSeries_spec gensG Rl hRl hsurj k u.1).1 hu'
    have := hcomm _ hT
    rw [tA_mul, tA_mul] at this
    apply Subtype.ext
    exact (tA_inj this).symm

omit [FaithfulSMul Γ (Fin n)] in
theorem tA_conj (g y : Γ) : conjT (tA n g) (tA n g⁻¹) (tA n y) = tA n (g * y * g⁻¹) := by
  unfold conjT
  rw [tA_mul, tA_mul, mul_assoc]

omit [FaithfulSMul Γ (Fin n)] in
theorem tA_conj' (g y : Γ) : conjT (tA n g⁻¹) (tA n g) (tA n y) = tA n (g⁻¹ * y * g) := by
  unfold conjT
  rw [tA_mul, tA_mul, mul_assoc]

omit [FaithfulSMul Γ (Fin n)] in
theorem mem_normalizer_of_normOK {Qx : Subgroup Γ} {L : List (Array ℕ)}
    (hQ : ∀ y : Γ, y ∈ Qx ↔ tA n y ∈ L) (g : Γ)
    (h : normOK L (tA n g) (tA n g⁻¹) = true) : g ∈ Subgroup.normalizer (Qx : Set Γ) := by
  unfold normOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_eq_any_beq, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨c, hc, hce⟩ := h1 _ ((hQ y).1 hy)
    rw [tA_conj] at hce
    exact (hQ _).2 (hce ▸ hc)
  · intro hy
    have hy' := (hQ _).1 hy
    obtain ⟨c, hc, hce⟩ := h2 _ hy'
    rw [tA_conj'] at hce
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this] at hce
    exact (hQ _).2 (hce ▸ hc)

omit [FaithfulSMul Γ (Fin n)] in
theorem not_mem_normalizer_of_notNormOK {Qx : Subgroup Γ} {L : List (Array ℕ)}
    (hQ : ∀ y : Γ, y ∈ Qx ↔ tA n y ∈ L) (hL : ∀ T ∈ L, ∃ y : Γ, tA n y = T) (g : Γ)
    (h : notNormOK L (tA n g) (tA n g⁻¹) = true) : g ∉ Subgroup.normalizer (Qx : Set Γ) := by
  unfold notNormOK at h
  simp only [List.any_eq_true, Bool.not_eq_true', List.contains_eq_any_beq] at h
  obtain ⟨q, hq, hnot⟩ := h
  obtain ⟨y, rfl⟩ := hL q hq
  intro hg
  have := (Subgroup.mem_normalizer_iff.1 hg y).1 ((hQ y).2 hq)
  have h3 := (hQ _).1 this
  rw [← tA_conj] at h3
  simp only [List.any_eq_false, beq_iff_eq] at hnot
  exact hnot _ h3 rfl

end Cen

section Gen

variable {Γ : Type} [Group Γ]

theorem foldl_eltStep_mem (cl : Subgroup Γ) (prog : List (ℕ × ℕ)) :
    ∀ (E : Array Γ), (∀ i < E.size, E.getD i 1 ∈ cl) → slpValidAux prog E.size = true →
      ∀ i < (prog.foldl eltStep E).size, (prog.foldl eltStep E).getD i 1 ∈ cl := by
  induction prog with
  | nil => intro E hE _; exact hE
  | cons p prog ih =>
    intro E hE hv
    simp only [slpValidAux, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hp, hv'⟩ := hv
    simp only [List.foldl_cons]
    have hs : (eltStep E p).size = E.size + 1 := by simp [eltStep]
    refine ih (eltStep E p) ?_ (by rw [hs]; exact hv')
    intro i hi
    rw [hs] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · simp only [eltStep]
      rw [getD_push_lt E _ 1 hi]
      exact hE i hi
    · simp only [eltStep]
      rw [getD_push_self E _ 1]
      exact cl.mul_mem (hE _ hp.1) (hE _ hp.2)

theorem slpElts_mem_closure (g h : Γ) (prog : List (ℕ × ℕ)) (hv : slpValidAux prog 2 = true) :
    ∀ i < (slpElts g h prog).size, (slpElts g h prog).getD i 1 ∈ Subgroup.closure ({g, h} : Set Γ) := by
  refine foldl_eltStep_mem _ prog #[g, h] ?_ hv
  intro i hi
  have hi' : i < 2 := by simpa using hi
  interval_cases i
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

end Gen

section Assembly

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem charPair_of_checks (a b : Γ)
    (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤) {ta tb : Array ℕ}
    (hta : ta = (tab n a).toArray) (htb : tb = (tab n b).toArray)
    {prog qp : List (ℕ × ℕ)} (hslp : slpValidAux prog 2 = true)
    (NT : Array (Array ℕ)) (hNT : NT = slpTabsA ta tb prog) (hqp : qpOK n NT qp)
    (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hE : BaseEnumOK n (List.range n) (qp.map fun p => NT[p.1]!) (qp.map fun p => NT[p.2]!)
      Ts rpar rcl)
    {k m : ℕ} (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m) (hTs : Ts.size = 2 ^ k)
    (Rl : List (Array ℕ)) (hRl : Rl = fullTables n Ts) (gens : List (Array ℕ))
    (hgens : gens = qp.map fun p => NT[p.1]!) (Z1 Qc : List (Array ℕ))
    (hZ1def : Z1 = zSeries Rl gens (Array.range n) 1)
    (hQcdef : Qc = cenList Rl (zSeries Rl gens (Array.range n) 3))
    {gn gin hn' hin : ℕ} (hgn : gn < NT.size) (hgin : gin < NT.size) (hhn : hn' < NT.size)
    (hhin : hin < NT.size)
    (hgg : invPairOK (Array.range n) NT[gn]! NT[gin]! = true)
    (hhh : invPairOK (Array.range n) NT[hn']! NT[hin]! = true)
    (hZ1 : normOK Z1 NT[gn]! NT[gin]! = true) (hQ2 : normOK Qc NT[hn']! NT[hin]! = true)
    (hgQ : notNormOK Qc NT[gn]! NT[gin]! = true) (hhZ : notNormOK Z1 NT[hn']! NT[hin]! = true)
    {wprog : List (ℕ × ℕ)} (hw : slpValidAux wprog 2 = true) (WNT : Array (Array ℕ))
    (hWNT : WNT = slpTabsA NT[gn]! NT[hn']! wprog) {an bn : ℕ} (han : an < WNT.size)
    (hbn : bn < WNT.size) (hwa : WNT[an]! = ta) (hwb : WNT[bn]! = tb) :
    ∃ R : Subgroup Γ, IsPGroup 2 R ∧ ¬ 2 ∣ R.index ∧ CharPair Γ R := by
  subst hta htb hNT
  set E := slpElts a b prog with hEdef
  have hspec := slp_tabs_spec (n := n) a b prog hslp
  let qs : List (Γ × Γ) := qp.map fun p => (E.getD p.1 1, E.getD p.2 1)
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3⟩ := hqp q hq
    refine eq_inv_of_img (n := n) _ _ (fun i hi => ?_)
    have := h3 i hi
    rw [← hspec q.1 h1, ← hspec q.2 h2] at this
    exact this
  have hG1 : qs.map (fun p => (tab n p.1).toArray) =
      qp.map fun p => (slpTabsA (tab n a).toArray (tab n b).toArray prog)[p.1]! := by
    simp only [qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hspec q.1 (hqp q hq).1
  have hG2 : qs.map (fun p => (tab n p.2).toArray) =
      qp.map fun p => (slpTabsA (tab n a).toArray (tab n b).toArray prog)[p.2]! := by
    simp only [qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact hspec q.2 (hqp q hq).2.1
  have hE' : BaseEnumOK n (List.range n) (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl := by
    rw [hG1, hG2]; exact hE
  set gensG : List Γ := qs.map Prod.fst with hgensG
  set R : Subgroup Γ := Subgroup.closure {x | x ∈ gensG} with hR
  have hRl' : ∀ x : Γ, x ∈ R ↔ tA n x ∈ Rl := by
    intro x
    rw [hRl]
    exact mem_R_iff_tab qs Ts rpar rcl hqsinv hE' x
  have hsurj : ∀ T ∈ Rl, ∃ y : Γ, tA n y = T := by
    intro T hT
    rw [hRl] at hT
    exact exists_of_mem_fullTables qs Ts rpar rcl hqsinv hE' hT
  have hgensA : gens = gensG.map (tA n) := by
    rw [hgens]
    simp only [gensG, qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact (hspec q.1 (hqp q hq).1).symm
  have hZ1spec : ∀ y : Γ, y ∈ (Subgroup.upperCentralSeries ↥R 1).map R.subtype ↔ tA n y ∈ Z1 := by
    intro y
    rw [hZ1def, hRl, hgensA, ← hRl]
    exact zSeries_spec gensG Rl hRl' hsurj 1 y
  have hQcspec : ∀ y : Γ, y ∈ (Subgroup.centralizer
      ((Subgroup.upperCentralSeries ↥R 3 : Subgroup ↥R) : Set ↥R)).map R.subtype ↔
      tA n y ∈ Qc := by
    intro y
    rw [hQcdef, hgensA]
    exact cenList_spec gensG Rl hRl' hsurj 3 y
  have hZ1surj : ∀ T ∈ Z1, ∃ y : Γ, tA n y = T := by
    intro T hT
    rw [hZ1def] at hT
    exact zSeries_surj Rl hsurj gens 1 T hT
  have hQcsurj : ∀ T ∈ Qc, ∃ y : Γ, tA n y = T := by
    intro T hT
    rw [hQcdef] at hT
    simp only [cenList, List.mem_filter] at hT
    exact hsurj T hT.1
  have hI : ∀ {i : ℕ}, i < (slpTabsA (tab n a).toArray (tab n b).toArray prog).size →
      tA n (E.getD i 1) = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[i]! :=
    fun {i} hi => hspec i hi
  set g := E.getD gn 1 with hg
  set gi := E.getD gin 1 with hgi
  set h := E.getD hn' 1 with hh
  set hi := E.getD hin 1 with hhi
  have hgiinv : gi = g⁻¹ := by
    have := hgg
    unfold invPairOK at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    rw [← hI hgn, ← hI hgin, tA_mul] at this
    have h1 := tA_inj (this.1.trans tA_one.symm)
    exact (eq_inv_of_mul_eq_one_right h1)
  have hhiinv : hi = h⁻¹ := by
    have := hhh
    unfold invPairOK at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    rw [← hI hhn, ← hI hhin, tA_mul] at this
    have h1 := tA_inj (this.1.trans tA_one.symm)
    exact (eq_inv_of_mul_eq_one_right h1)
  have hgt : tA n g = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[gn]! := hI hgn
  have hgit : tA n g⁻¹ = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[gin]! := by
    rw [← hgiinv]; exact hI hgin
  have hht : tA n h = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[hn']! := hI hhn
  have hhit : tA n h⁻¹ = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[hin]! := by
    rw [← hhiinv]; exact hI hhin
  have hg1 : g ∈ Subgroup.normalizer
      (((Subgroup.upperCentralSeries ↥R 1).map R.subtype : Subgroup Γ) : Set Γ) :=
    mem_normalizer_of_normOK hZ1spec g (by rw [hgt, hgit]; exact hZ1)
  have hh2 : h ∈ Subgroup.normalizer
      (((Subgroup.centralizer ((Subgroup.upperCentralSeries ↥R 3 : Subgroup ↥R) :
        Set ↥R)).map R.subtype : Subgroup Γ) : Set Γ) :=
    mem_normalizer_of_normOK hQcspec h (by rw [hht, hhit]; exact hQ2)
  have hg2 : g ∉ Subgroup.normalizer
      (((Subgroup.centralizer ((Subgroup.upperCentralSeries ↥R 3 : Subgroup ↥R) :
        Set ↥R)).map R.subtype : Subgroup Γ) : Set Γ) :=
    not_mem_normalizer_of_notNormOK hQcspec hQcsurj g (by rw [hgt, hgit]; exact hgQ)
  have hh1 : h ∉ Subgroup.normalizer
      (((Subgroup.upperCentralSeries ↥R 1).map R.subtype : Subgroup Γ) : Set Γ) :=
    not_mem_normalizer_of_notNormOK hZ1spec hZ1surj h (by rw [hht, hhit]; exact hhZ)
  have hclosure : Subgroup.closure ({g, h} : Set Γ) = ⊤ := by
    have hspec2 := slp_tabs_spec (n := n) g h wprog hw
    have hWNT' : slpTabsA (tab n g).toArray (tab n h).toArray wprog = WNT := by
      rw [hWNT, ← hgt, ← hht]; rfl
    have hmem : ∀ i, i < WNT.size → ∀ c : Γ, tA n c = WNT[i]! →
        c = (slpElts g h wprog).getD i 1 := by
      intro i hi c hc
      have := hspec2 i (by rw [hWNT']; exact hi)
      rw [hWNT'] at this
      exact tA_inj (hc.trans this.symm)
    have ha : a ∈ Subgroup.closure ({g, h} : Set Γ) := by
      rw [hmem an han a (by rw [hwa]; rfl)]
      exact slpElts_mem_closure g h wprog hw an (by rw [slpElts_size, ← slpTabsA_size
        (tab n g).toArray (tab n h).toArray wprog, hWNT']; exact han)
    have hb : b ∈ Subgroup.closure ({g, h} : Set Γ) := by
      rw [hmem bn hbn b (by rw [hwb]; rfl)]
      exact slpElts_mem_closure g h wprog hw bn (by rw [slpElts_size, ← slpTabsA_size
        (tab n g).toArray (tab n h).toArray wprog, hWNT']; exact hbn)
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hb
  obtain ⟨_, hcardR, _⟩ := benum_data qs Ts rpar rcl hqsinv hE'
  have hcardR' : Nat.card R = 2 ^ k := by rw [hcardR, hTs]
  have hindex : R.index = m := by
    have h1 := R.card_mul_index
    rw [hcardR', hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  refine ⟨R, IsPGroup.of_card hcardR', ?_, ?_⟩
  · rw [hindex]
    exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)
  · exact ⟨_, _, g, h, inferInstance, inferInstance, hg1, hh2, hg2, hh1, hclosure⟩

end Assembly

end CFSG.QuasithinUnique.Setup.X1
