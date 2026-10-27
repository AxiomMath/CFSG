module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowNative

public section

open scoped commutatorElement

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

section Row

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem benum_dataB {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (qs : List (Γ × Γ))
    (Ts : Array (List ℕ)) (rpar rcl : Array ℕ) (hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹)
    (hE : BaseEnumOK n B (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl) :
    (∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst} ↔
      rt n (ptsOf B (genTabs n (qs.map Prod.fst))) x ∈ Ts.toList) ∧
    Nat.card (Subgroup.closure {x | x ∈ qs.map Prod.fst}) = Ts.size := by
  let gens : List Γ := qs.map Prod.fst
  have hG : qs.map (fun p => (tab n p.1).toArray) = genTabs n gens := by
    simp only [genTabs, gens, List.map_map, Function.comp_def]
  have hGi : qs.map (fun p => (tab n p.2).toArray) = genTabsInv n gens := by
    simp only [genTabsInv, gens, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [hqsinv p hp]
  rw [hG, hGi] at hE
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  refine ⟨fun x => ?_, benum_card hB hbase gens Ts rpar rcl hE⟩
  refine ⟨benum_closed hB gens Ts rpar rcl hE x, fun hx => ?_⟩
  obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hx
  have hiT' : i < Ts.size := by simpa using hi
  obtain ⟨y, hy, hyT⟩ := benum_reach hB gens Ts rpar rcl hE i hiT'
  have : rt n (ptsOf B (genTabs n gens)) y = rt n (ptsOf B (genTabs n gens)) x := by
    rw [hyT, getElem!_pos Ts i hiT']
    simpa using hiT
  rwa [← rt_injective hB hBP hbase this]

theorem eq_of_act_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {g h : Γ}
    (H : ∀ b ∈ B, act n g b = act n h b) : g = h := by
  have : g⁻¹ * h = 1 := by
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb), ← H b hb, ← act_mul _ _ (hB b hb), inv_mul_cancel,
      act_one (hB b hb)]
  exact inv_mul_eq_one.mp this

theorem rt_getD_gen {B : List ℕ} (gens : List Γ) (x : Γ) {t k : ℕ}
    (ht : t < gens.length) (hk : k < B.length) :
    (rt n (ptsOf B (genTabs n gens)) x).getD (B.length * (1 + t) + k) 0 =
      act n x (act n (gens.getD t 1) (B.getD k 0)) := by
  have ht' : t < (genTabs n gens).length := by simpa [genTabs] using ht
  have hgt : (genTabs n gens).getD t #[] = (tab n (gens.getD t 1)).toArray := by
    simp only [genTabs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht]
    simp
  have hgen := ptsOf_getElem?_ext (B := B) (G := genTabs n gens) ht' hk
  rw [hgt] at hgen
  have hrt : (rt n (ptsOf B (genTabs n gens)) x)[B.length * (1 + t) + k]? =
      some (act n x (act n (gens.getD t 1) (B.getD k 0))) := by
    rw [rt_getElem?, hgen]
    simp [img_tab]
  exact getD_of_getElem? hrt

theorem rt_getD_base {B : List ℕ} (gens : List Γ) (x : Γ) {k : ℕ} (hk : k < B.length) :
    (rt n (ptsOf B (genTabs n gens)) x).getD k 0 = act n x (B.getD k 0) := by
  have hbase := ptsOf_getElem?_base (B := B) (G := genTabs n gens) hk
  have hrt : (rt n (ptsOf B (genTabs n gens)) x)[k]? = some (act n x (B.getD k 0)) := by
    rw [rt_getElem?, hbase]
    simp
  exact getD_of_getElem? hrt

theorem commInR_iff {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (gensG : List Γ)
    {Z : List (Array ℕ)} (hZ : ∀ Y ∈ Z, ∃ y : Γ, tA n y = Y) (x : Γ) {j : ℕ}
    (hj : j < gensG.length) :
    commInR B.length Z (rt n (ptsOf B (genTabs n gensG)) x) j (tA n (gensG.getD j 1)) = true ↔
      tA n ⁅x, gensG.getD j 1⁆ ∈ Z := by
  set s := gensG.getD j 1 with hs
  have himg : ∀ (y : Γ) (p : ℕ), img (tA n y) p = act n y p := fun y p => img_tab y p
  have hrow : ∀ k < B.length, (rt n (ptsOf B (genTabs n gensG)) x).getD
      (B.length * (1 + j) + k) 0 = act n x (act n s (B.getD k 0)) :=
    fun k hk => rt_getD_gen gensG x hj hk
  have hbs : ∀ k < B.length, (rt n (ptsOf B (genTabs n gensG)) x).getD k 0 =
      act n x (B.getD k 0) := fun k hk => rt_getD_base gensG x hk
  have hBk : ∀ k < B.length, B.getD k 0 ∈ B := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact List.getElem_mem hk
  unfold commInR
  simp only [List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨Y, hY, hall⟩
    obtain ⟨z, rfl⟩ := hZ Y hY
    have key : x * s = z * (s * x) := by
      apply eq_of_act_eq hB hbase
      intro b hb
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
      have hb' : B[k] = B.getD k 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
      rw [hb']
      have h1 := hall k hk
      rw [hrow k hk, hbs k hk, himg, himg] at h1
      have hlt := hB _ (hBk k hk)
      rw [act_mul x s hlt, act_mul z (s * x) hlt, act_mul s x hlt]
      exact h1
    have : ⁅x, s⁆ = z := by
      calc ⁅x, s⁆ = x * s * (s * x)⁻¹ := by rw [commutatorElement_def]; group
        _ = z * (s * x) * (s * x)⁻¹ := by rw [key]
        _ = z := by group
    rw [this]
    exact hY
  · intro h
    refine ⟨tA n ⁅x, s⁆, h, fun k hk => ?_⟩
    rw [hrow k hk, hbs k hk, himg, himg]
    have hlt := hB _ (hBk k hk)
    have key : x * s = ⁅x, s⁆ * (s * x) := by rw [commutatorElement_def]; group
    have := congrArg (fun g => act n g (B.getD k 0)) key
    rw [act_mul x s hlt, act_mul ⁅x, s⁆ (s * x) hlt, act_mul s x hlt] at this
    exact this

end Row

section RowZ

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

omit [FaithfulSMul Γ (Fin n)] in
theorem zClaim_spec {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (gensG : List Γ) (Ts : Array (List ℕ))
    (hR : ∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ gensG} ↔
      rt n (ptsOf B (genTabs n gensG)) x ∈ Ts.toList)
    (k : ℕ) {Z L : List (Array ℕ)}
    (hZ : ∀ y : Γ, y ∈ ZK (Subgroup.closure {x | x ∈ gensG}) k ↔ tA n y ∈ Z)
    (hZs : ∀ Y ∈ Z, ∃ y : Γ, tA n y = Y) (hLs : ∀ Y ∈ L, ∃ y : Γ, tA n y = Y)
    (hclaim : zClaimOK B.length (gensG.map (tA n)) (ptsOf B (genTabs n gensG)) Ts Z L = true) :
    ∀ y : Γ, y ∈ ZK (Subgroup.closure {x | x ∈ gensG}) (k + 1) ↔ tA n y ∈ L := by
  intro y
  unfold zClaimOK at hclaim
  simp only [Bool.and_eq_true, List.all_eq_true] at hclaim
  obtain ⟨hc1, hc2⟩ := hclaim
  set P := ptsOf B (genTabs n gensG) with hP
  have hBP : ∀ b ∈ B, b ∈ P := fun b hb => List.mem_append_left _ hb
  have hrowOf : ∀ z : Γ, rowOf P (tA n z) = rt n P z := by
    intro z
    unfold rowOf rt
    apply List.map_congr_left
    intro p _
    exact img_tab z p
  have hpass : ∀ x : Γ, passAll B.length (gensG.map (tA n)) Z (rt n P x) = true ↔
      ∀ s ∈ gensG, tA n ⁅x, s⁆ ∈ Z := by
    intro x
    unfold passAll
    simp only [List.all_eq_true, List.mem_range, List.length_map]
    have e : ∀ j (hj : j < gensG.length), (gensG.map (tA n)).getD j #[] =
        tA n (gensG.getD j 1) := by
      intro j hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have e2 : ∀ j (hj : j < gensG.length), gensG.getD j 1 = gensG[j] := by
      intro j hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    constructor
    · intro h s hs
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      have := h j hj
      rw [e j hj] at this
      have hj' := (commInR_iff hB hbase gensG hZs x hj).1 this
      rwa [e2 j hj] at hj'
    · intro h j hj
      rw [e j hj]
      apply (commInR_iff hB hbase gensG hZs x hj).2
      rw [e2 j hj]
      exact h _ (List.getElem_mem hj)
  rw [mem_ZK_succ_iff_gens]
  constructor
  · rintro ⟨hy, hs⟩
    have hyT := (hR y).1 hy
    have hp : passAll B.length (gensG.map (tA n)) Z (rt n P y) = true :=
      (hpass y).2 (fun s hs' => (hZ _).1 (hs s hs'))
    have h1 := hc1 _ hyT
    rw [hp] at h1
    have hcont : (L.map (rowOf P)).contains (rt n P y) = true := by
      simpa using h1.symm
    simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq, List.mem_map] at hcont
    obtain ⟨_, ⟨Y, hYL, rfl⟩, hYr⟩ := hcont
    obtain ⟨y', rfl⟩ := hLs Y hYL
    rw [hrowOf] at hYr
    have : y = y' := rt_injective hB hBP hbase hYr
    subst this
    exact hYL
  · intro hyL
    have hYin := hc2 _ hyL
    rw [hrowOf] at hYin
    have hyT : rt n P y ∈ Ts.toList := by simpa using hYin
    have hy : y ∈ Subgroup.closure {x | x ∈ gensG} := (hR y).2 hyT
    have hcont : (L.map (rowOf P)).contains (rt n P y) = true := by
      simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq, List.mem_map]
      exact ⟨_, ⟨tA n y, hyL, rfl⟩, (hrowOf y).symm⟩
    have h1 := hc1 _ hyT
    rw [hcont] at h1
    have hp : passAll B.length (gensG.map (tA n)) Z (rt n P y) = true := by simpa using h1
    exact ⟨hy, fun s hs => (hZ _).2 ((hpass y).1 hp s hs)⟩

end RowZ

section RowAssembly

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem charPair_of_rowChecks {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ)
    (hgen : Subgroup.closure ({a, b} : Set Γ) = ⊤) {ta tb : Array ℕ}
    (hta : ta = (tab n a).toArray) (htb : tb = (tab n b).toArray)
    {prog qp : List (ℕ × ℕ)} (hslp : slpValidAux prog 2 = true)
    (NT : Array (Array ℕ)) (hNT : NT = slpTabsA ta tb prog) (hqp : qpOK n NT qp)
    (Ts : Array (List ℕ)) (rpar rcl : Array ℕ)
    (hE : BaseEnumOK n B (qp.map fun p => NT[p.1]!) (qp.map fun p => NT[p.2]!) Ts rpar rcl)
    {k m : ℕ} (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m) (hTs : Ts.size = 2 ^ k)
    (gens : List (Array ℕ)) (hgens : gens = qp.map fun p => NT[p.1]!) (P : List ℕ)
    (hP : P = ptsOf B gens) (nodes1 nodes2 nodes3 : List ℕ)
    (hn1 : nodesLt NT.size nodes1 = true) (hn2 : nodesLt NT.size nodes2 = true)
    (hn3 : nodesLt NT.size nodes3 = true) (L1 L2 L3 : List (Array ℕ))
    (hL1 : L1 = nodes1.map fun i => NT[i]!) (hL2 : L2 = nodes2.map fun i => NT[i]!)
    (hL3 : L3 = nodes3.map fun i => NT[i]!)
    (hc1 : zClaimOK B.length gens P Ts [Array.range n] L1 = true)
    (hc2 : zClaimOK B.length gens P Ts L1 L2 = true)
    (hc3 : zClaimOK B.length gens P Ts L2 L3 = true)
    {gn gin hn' hin : ℕ} (hgn : gn < NT.size) (hgin : gin < NT.size) (hhn : hn' < NT.size)
    (hhin : hin < NT.size)
    (hgg : invPairOK (Array.range n) NT[gn]! NT[gin]! = true)
    (hhh : invPairOK (Array.range n) NT[hn']! NT[hin]! = true)
    (hZ1 : normOK L1 NT[gn]! NT[gin]! = true) (hQ2 : normOK L3 NT[hn']! NT[hin]! = true)
    (hgQ : notNormOK L3 NT[gn]! NT[gin]! = true) (hhZ : notNormOK L1 NT[hn']! NT[hin]! = true)
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
  have hE' : BaseEnumOK n B (qs.map fun p => (tab n p.1).toArray)
      (qs.map fun p => (tab n p.2).toArray) Ts rpar rcl := by
    rw [hG1, hG2]; exact hE
  obtain ⟨hRrow, hcardR⟩ := benum_dataB hB hbase qs Ts rpar rcl hqsinv hE'
  set gensG : List Γ := qs.map Prod.fst with hgensG
  set R : Subgroup Γ := Subgroup.closure {x | x ∈ gensG} with hR
  have hgensA : gens = gensG.map (tA n) := by
    rw [hgens]
    simp only [gensG, qs, List.map_map]
    apply List.map_congr_left
    intro q hq
    exact (hspec q.1 (hqp q hq).1).symm
  have hP' : P = ptsOf B (genTabs n gensG) := by rw [hP, hgensA]; rfl
  have hI : ∀ {i : ℕ}, i < (slpTabsA (tab n a).toArray (tab n b).toArray prog).size →
      tA n (E.getD i 1) = (slpTabsA (tab n a).toArray (tab n b).toArray prog)[i]! :=
    fun {i} hi => hspec i hi
  have hLs : ∀ (nodes : List ℕ) (L : List (Array ℕ)),
      nodesLt (slpTabsA (tab n a).toArray (tab n b).toArray prog).size nodes = true →
      L = nodes.map (fun i => (slpTabsA (tab n a).toArray (tab n b).toArray prog)[i]!) →
      ∀ Y ∈ L, ∃ y : Γ, tA n y = Y := by
    intro nodes L hn hL Y hY
    rw [hL] at hY
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hY
    unfold nodesLt at hn
    simp only [List.all_eq_true, decide_eq_true_eq] at hn
    exact ⟨E.getD i 1, hI (hn i hi)⟩
  have hL1s := hLs nodes1 L1 hn1 hL1
  have hL2s := hLs nodes2 L2 hn2 hL2
  have hL3s := hLs nodes3 L3 hn3 hL3
  have hZ0 : ∀ y : Γ, y ∈ ZK R 0 ↔ tA n y ∈ [Array.range n] := by
    intro y
    simp only [ZK, Subgroup.upperCentralSeries_zero, List.mem_singleton]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hr
      subst hr
      exact tA_one
    · intro h
      have : y = 1 := tA_eq_range_iff.1 h
      subst this
      exact ⟨1, Subgroup.one_mem _, rfl⟩
  have hZ0s : ∀ Y ∈ [Array.range n], ∃ y : Γ, tA n y = Y := by
    intro Y hY
    rw [List.mem_singleton] at hY
    exact ⟨1, by rw [hY]; exact tA_one⟩
  have hgensTab : gens = gensG.map (tA n) := hgensA
  have hc1' : zClaimOK B.length (gensG.map (tA n)) (ptsOf B (genTabs n gensG)) Ts
      [Array.range n] L1 = true := by rw [← hgensTab, ← hP']; exact hc1
  have hc2' : zClaimOK B.length (gensG.map (tA n)) (ptsOf B (genTabs n gensG)) Ts L1 L2 = true := by
    rw [← hgensTab, ← hP']; exact hc2
  have hc3' : zClaimOK B.length (gensG.map (tA n)) (ptsOf B (genTabs n gensG)) Ts L2 L3 = true := by
    rw [← hgensTab, ← hP']; exact hc3
  have hz1 := zClaim_spec hB hbase gensG Ts hRrow 0 hZ0 hZ0s hL1s hc1'
  have hz2 := zClaim_spec hB hbase gensG Ts hRrow 1 hz1 hL1s hL2s hc2'
  have hz3 := zClaim_spec hB hbase gensG Ts hRrow 2 hz2 hL2s hL3s hc3'
  have hZ1spec : ∀ y : Γ, y ∈ (Subgroup.upperCentralSeries ↥R 1).map R.subtype ↔ tA n y ∈ L1 :=
    hz1
  have hZ3spec : ∀ y : Γ, y ∈ (Subgroup.upperCentralSeries ↥R 3).map R.subtype ↔ tA n y ∈ L3 :=
    hz3
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
      (((Subgroup.upperCentralSeries ↥R 3).map R.subtype : Subgroup Γ) : Set Γ) :=
    mem_normalizer_of_normOK hZ3spec h (by rw [hht, hhit]; exact hQ2)
  have hg2 : g ∉ Subgroup.normalizer
      (((Subgroup.upperCentralSeries ↥R 3).map R.subtype : Subgroup Γ) : Set Γ) :=
    not_mem_normalizer_of_notNormOK hZ3spec hL3s g (by rw [hgt, hgit]; exact hgQ)
  have hh1 : h ∉ Subgroup.normalizer
      (((Subgroup.upperCentralSeries ↥R 1).map R.subtype : Subgroup Γ) : Set Γ) :=
    not_mem_normalizer_of_notNormOK hZ1spec hL1s h (by rw [hht, hhit]; exact hhZ)
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
  have hcardR' : Nat.card R = 2 ^ k := by rw [hcardR, hTs]
  have hindex : R.index = m := by
    have h1 := R.card_mul_index
    rw [hcardR', hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  refine ⟨R, IsPGroup.of_card hcardR', ?_, ?_⟩
  · rw [hindex]
    exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)
  · exact ⟨_, _, g, h, inferInstance, inferInstance, hg1, hh2, hg2, hh1, hclosure⟩

end RowAssembly

end CFSG.QuasithinUnique.Setup.X1
