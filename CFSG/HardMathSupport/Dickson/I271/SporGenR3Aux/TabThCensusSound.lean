module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalSound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)
open CFSG.Assembly (IsElemAbelian)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
open CFSG.HardMathSupport.Dickson.I271.TabThNative
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative (wordRowsL)

theorem rp_wordRowsL {gs : Array Mat} {R : ℕ → GL (Fin 248) (ZMod 2)} {w : List ℕ}
    (h : ∀ r ∈ w, Rp gs[r]! (R r)) : Rp (wordRowsL gs w) (w.map R).prod := by
  suffices H : ∀ (w : List ℕ), (∀ r ∈ w, Rp gs[r]! (R r)) →
      ∀ (acc : Mat) (g : GL (Fin 248) (ZMod 2)), Rp acc g →
        Rp (w.foldl (fun acc r => mulRows acc gs[r]!) acc) (g * (w.map R).prod) by
    have := H w h idRows 1 (by unfold Rp; rw [CFSG.Sporadic.Th.rowsMatrix_idRows, Units.val_one])
    simpa [wordRowsL] using this
  intro w
  induction w with
  | nil => intro _ acc g hg; simpa using hg
  | cons r w ih =>
    intro hw acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ _ (hg.mul (hw r List.mem_cons_self))

section Main


open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent in
theorem thCensus_sound
    {E : ThE81Data} {X : ThLocalData} {data : List (ℕ × ℕ × String)} {A B Z S U : Mat}
    {gs P : Array Mat} {c : ArrCert}
    (hA : Rp A CFSG.Sporadic.Th.gA) (hB : Rp B CFSG.Sporadic.Th.gB)
    (hZ : Rp Z ((zJ : CFSG.Sporadic.Th.J) : GL (Fin 248) (ZMod 2)))
    (hgs : gs = #[evalWord #[A, B] E.w61, evalWord #[A, B] E.w62])
    (hP : P = E.pW.map (evalWord gs))
    (h : thLocalChecks E X A B Z gs P c = true)
    (hf : censusFusOK X data A B Z S U (matOf P c.par c.lab qN) = true) :
    ∀ {sJ uJ : CFSG.Sporadic.Th.J}, Rp S (sJ : GL (Fin 248) (ZMod 2)) →
      Rp U (uJ : GL (Fin 248) (ZMod 2)) →
    ∃ Q : Subgroup CFSG.Sporadic.Th.J, Nat.card Q = 3 ^ 10 ∧ ∀ s ∈ Q, orderOf s = 3 →
      IsConj s zJ ∨ IsConj s (zJ ^ 2) ∨ IsConj s sJ ∨ IsConj s (sJ ^ 2) ∨ IsConj s uJ ∨
        IsConj s (uJ ^ 2) := by
  set JG := CFSG.Sporadic.Th.J with hJG
  have : Finite JG := Nat.finite_of_card_ne_zero
    (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have hJ := factorization_J
  unfold thLocalChecks at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hl1, hl2, hl3, hpc, horb, hloc, hfus, hrc, hinvl, hip1, hip2, hU2, hUne, hUz, hMz⟩ := h
  unfold localTableChecks at hloc
  simp only [Bool.and_eq_true, and_assoc] at hloc
  obtain ⟨he09, hz2, hz3, hzc, hreps, hct, hcov, htg⟩ := hloc
  set gA := CFSG.Sporadic.Th.gA with hgA
  set gB := CFSG.Sporadic.Th.gB with hgB
  have ha : gA ∈ JG := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : gB ∈ JG := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let cd0 : ℕ → GL (Fin 248) (ZMod 2) := fun l => if l = 0 then gA else gB
  have hcd0J : ∀ l, cd0 l ∈ JG := fun l => by
    by_cases hl : l = 0
    · simp only [cd0, hl, ite_true]; exact ha
    · simp only [cd0, hl, ite_false]; exact hb
  have hAB : ∀ l < 2, Rp (#[A, B] : Array Mat)[l]! (cd0 l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hA
    · exact hB
  have hletters1 : ∀ x ∈ E.w61, x.1 < 2 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 hl1 x hx)
  have hletters2 : ∀ x ∈ E.w62, x.1 < 2 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 hl2 x hx)
  have hx61 : Rp (evalWord #[A, B] E.w61) (wordG cd0 E.w61) :=
    rowsMatrix_evalWord_eq fun x hx => hAB x.1 (hletters1 x hx)
  have hx62 : Rp (evalWord #[A, B] E.w62) (wordG cd0 E.w62) :=
    rowsMatrix_evalWord_eq fun x hx => hAB x.1 (hletters2 x hx)
  have hx61J : wordG cd0 E.w61 ∈ JG := wordG_mem fun x _ => hcd0J x.1
  have hx62J : wordG cd0 E.w62 ∈ JG := wordG_mem fun x _ => hcd0J x.1
  let cd1 : ℕ → GL (Fin 248) (ZMod 2) := fun l =>
    if l = 0 then wordG cd0 E.w61 else wordG cd0 E.w62
  have hcd1J : ∀ l, cd1 l ∈ JG := fun l => by
    by_cases hl : l = 0
    · simp only [cd1, hl, ite_true]; exact hx61J
    · simp only [cd1, hl, ite_false]; exact hx62J
  have hgs1 : ∀ l < 2, Rp gs[l]! (cd1 l) := by
    intro l hl
    rw [hgs]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hx61
    · exact hx62
  have hsize : P.size = 10 := pcCheck_size hpc
  have hpWsize : E.pW.size = 10 := by rw [hP, Array.size_map] at hsize; exact hsize
  have hletters : ∀ k < 10, ∀ x ∈ E.pW[k]!, x.1 < 2 := by
    intro k hk x hx
    have := List.all_eq_true.1 hl3 (E.pW[k]!) (by
      rw [getElem!_pos E.pW k (by omega)]
      exact Array.getElem_mem_toList (by omega))
    exact of_decide_eq_true (List.all_eq_true.1 this x hx)
  let g : ℕ → GL (Fin 248) (ZMod 2) := fun k => wordG cd1 (E.pW[k]!)
  have hg : ∀ l < 10, Rp P[l]! (g l) := by
    intro l hl
    have hPl : P[l]! = evalWord gs E.pW[l]! := by
      rw [hP, getElem!_map_of_lt E.pW (evalWord gs) (by omega)]
    rw [hPl]
    exact rowsMatrix_evalWord_eq fun x hx => hgs1 x.1 (hletters l hl x hx)
  have hgJ : ∀ k, g k ∈ JG := fun k => wordG_mem fun x _ => hcd1J x.1
  obtain ⟨hcube, hconj⟩ := pc_sound hg hpc
  have hQp : IsPGroup 3 (tailGroup g 10 0) := isPGroup_tailGroup g 10 hcube hconj 0
  have hQeq : tailGroup g 10 0 = Subgroup.closure (g '' {k | k < 10}) := by
    have hs : ({l | 0 ≤ l ∧ l < 10} : Set ℕ) = {k | k < 10} := by
      ext l
      simp
    unfold tailGroup
    rw [hs]
  rw [hQeq] at hQp
  set Q := Subgroup.closure (g '' {k | k < 10}) with hQdef
  have hQJ : Q ≤ JG := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact hgJ k
  have hle : Nat.card Q ≤ 59049 := by
    have := card_le_of_isPGroup hQJ hQp
    rw [hJ] at this
    simpa using this
  obtain ⟨⟨gi, hT⟩, hQN⟩ := orbit_table hsize hg hle horb
  have hgiQ : ∀ i < qN, gi i ∈ Q := g_mem hT
  have hgiJ : ∀ i < qN, gi i ∈ JG := fun i hi => hQJ (hgiQ i hi)
  obtain ⟨mul, hmul⟩ : ∃ m, m = mulIdxN c.edges c.par c.lab qN := ⟨_, rfl⟩
  rw [← hmul] at hz2 hz3 hzc hct hcov htg
  have hmulS : ∀ {i j : ℕ}, i < qN → j < qN → mul i j < qN ∧ gi (mul i j) = gi i * gi j := by
    intro i j hi hj
    rw [hmul]
    exact mul_spec hT hi hj
  have hpowS : ∀ {i : ℕ}, i < qN → ∀ e, powIdx mul i e < qN ∧ gi (powIdx mul i e) = gi i ^ e := by
    intro i hi e
    rw [hmul]
    exact powIdx_spec hT hi e
  have hM : ∀ i < qN, Rp (matOf P c.par c.lab qN i) (gi i) := fun i hi =>
    matOf_spec hg hT qN i hi.le hi
  have hz10 : gi 10 = g 9 := by
    obtain ⟨-, h2⟩ := hT.edge 0 hT.pos 9 (by norm_num)
    rw [beq_iff_eq.1 he09, hT.g0, mul_one] at h2
    exact h2
  have hzJ : gi 10 = (zJ : GL (Fin 248) (ZMod 2)) := by
    have h1 : Rp Z (gi 10) := by
      rw [← beq_iff_eq.1 hMz]
      exact hM 10 (by norm_num)
    exact h1.eq_of_eq hZ rfl
  have hz94 : gi 94 = gi 10 * gi 10 := by
    obtain ⟨-, h2⟩ := hmulS (i := 10) (j := 10) (by norm_num) (by norm_num)
    rw [← beq_iff_eq.1 hz2]
    exact h2
  have hzcomm : ∀ q ∈ Q, q * gi 10 = gi 10 * q := by
    have hle' : Q ≤ Subgroup.centralizer {gi 10} := by
      rw [hQdef, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨h1, h2⟩ := hT.edge 10 (by norm_num) k hk
      obtain ⟨h3, h4⟩ := hT.edge 0 hT.pos k hk
      obtain ⟨h5, h6⟩ := hmulS (i := 10) (by norm_num) h3
      have e1 : gi ((c.edges[10]!)[k]!) = gi (mul 10 ((c.edges[0]!)[k]!)) := by
        rw [beq_iff_eq.1 (List.all_eq_true.1 hzc k (List.mem_range.2 hk))]
      rw [h2, h6, h4, hT.g0, mul_one] at e1
      exact e1
    intro q hq
    have hq' := hle' hq
    rw [Subgroup.mem_centralizer_singleton_iff] at hq'
    exact hq'
  have hQJcard : Nat.card (Q.subgroupOf JG) = 3 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, hQN]
    norm_num
  have hzQJ : zJ ∈ Q.subgroupOf JG := by
    rw [Subgroup.mem_subgroupOf, ← hzJ]
    exact hgiQ 10 (by norm_num)
  let cd4 : ℕ → GL (Fin 248) (ZMod 2) := fun l =>
    if l = 0 then gA else if l = 1 then gB else if l = 2 then wordG cd0 E.w61
    else wordG cd0 E.w62
  have hcd4J : ∀ l, cd4 l ∈ JG := fun l => by
    simp only [cd4]
    split_ifs
    · exact ha
    · exact hb
    · exact hx61J
    · exact hx62J
  have hgs4 : ∀ l < 4, Rp (#[A, B, gs[0]!, gs[1]!] : Array Mat)[l]!
      (cd4 l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · exact hA
    · exact hB
    · have e : cd4 2 = cd1 0 := by
        simp only [cd4, cd1, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, if_true]
      rw [e]
      exact hgs1 0 (by norm_num)
    · have e : cd4 3 = cd1 1 := by
        simp only [cd4, cd1, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_ne_zero, if_false]
        rfl
      rw [e]
      exact hgs1 1 (by norm_num)
  have hword4 : ∀ w : List (ℕ × ℕ), (∀ x ∈ w, x.1 < 4) →
      Rp (evalWord #[A, B, gs[0]!, gs[1]!] w) (wordG cd4 w) ∧
        wordG cd4 w ∈ JG := fun w hw =>
    ⟨rowsMatrix_evalWord_eq fun x hx => hgs4 x.1 (hw x hx), wordG_mem fun x _ => hcd4J x.1⟩
  have hfusG : ∀ f ∈ X.fus, f.2.1 < qN ∧ (∃ y ∈ X.tgts, y.1 = f.2.1) ∧ ∃ w ∈ JG,
      gi f.2.1 = w * gi f.1 * w⁻¹ := by
    intro f hf
    have hff := List.all_eq_true.1 hfus f hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true,
      beq_iff_eq] at hff
    obtain ⟨⟨⟨⟨hr, ht⟩, hwl⟩, ⟨y, hy, hyt⟩⟩, hWM⟩ := hff
    have hrq : f.1 < qN := of_decide_eq_true (List.all_eq_true.1 hreps f.1 hr)
    obtain ⟨hW, hWJ⟩ := hword4 f.2.2 fun x hx => of_decide_eq_true (List.all_eq_true.1 hwl x hx)
    refine ⟨ht, ⟨y, hy, hyt⟩, wordG cd4 f.2.2, hWJ, ?_⟩
    have e := (hW.mul (hM f.1 hrq)).eq_of_eq ((hM f.2.1 ht).mul hW) hWM
    rw [e]
    group
  have hinv := classTable_inv hT X (by rw [← hmul]; exact hct)
  rw [← hmul] at hinv
  intro sJ uJ hS hU
  have hcensus := hf
  unfold censusFusOK at hcensus
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hcensus
  obtain ⟨hcov', hdata⟩ := hcensus
  let cdR : ℕ → GL (Fin 248) (ZMod 2) := fun l =>
    if l = 0 then gA else if l = 1 then gB else gB * gB
  have hgsR : ∀ l < 3, Rp (#[A, B, mulRows B B] : Array Mat)[l]! (cdR l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hB.mul hB
  have hcdRJ : ∀ l, cdR l ∈ JG := by
    intro l
    simp only [cdR]
    split_ifs
    · exact ha
    · exact hb
    · exact JG.mul_mem hb hb
  have hword3 : ∀ str : String, Rp (abcRows A B str) ((abcWord str).map cdR).prod ∧
      ((abcWord str).map cdR).prod ∈ JG := by
    intro str
    have hlt : ∀ r ∈ abcWord str, r < 3 := by
      intro r hr
      simp only [abcWord, List.mem_map] at hr
      obtain ⟨ch, -, rfl⟩ := hr
      split_ifs <;> omega
    refine ⟨rp_wordRowsL fun r hr => hgsR r (hlt r hr), ?_⟩
    exact JG.list_prod_mem fun x hx => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      exact hcdRJ l
  let clsG : ℕ → GL (Fin 248) (ZMod 2) := fun k =>
    if k = 0 then (zJ : GL (Fin 248) (ZMod 2))
    else if k = 1 then (zJ : GL (Fin 248) (ZMod 2)) * zJ
    else if k = 2 then (sJ : GL (Fin 248) (ZMod 2))
    else if k = 3 then (sJ : GL (Fin 248) (ZMod 2)) * sJ
    else if k = 4 then (uJ : GL (Fin 248) (ZMod 2)) else (uJ : GL (Fin 248) (ZMod 2)) * uJ
  have hclsRp : ∀ k, Rp (clsRows Z S U k) (clsG k) := by
    intro k
    simp only [clsRows, clsG]
    split_ifs
    · exact hZ
    · exact hZ.mul hZ
    · exact hS
    · exact hS.mul hS
    · exact hU
    · exact hU.mul hU
  have hpow2 : ∀ x : CFSG.Sporadic.Th.J, ((x ^ 2 : CFSG.Sporadic.Th.J) : GL (Fin 248) (ZMod 2)) =
      (x : GL (Fin 248) (ZMod 2)) * (x : GL (Fin 248) (ZMod 2)) := by
    intro x
    rw [pow_two]
    rfl
  refine ⟨Q.subgroupOf JG, hQJcard, ?_⟩
  intro s hs hs3
  rw [Subgroup.mem_subgroupOf] at hs
  obtain ⟨i, hi, hgis⟩ := hT.surj _ hs
  have hs1 : (s : GL (Fin 248) (ZMod 2)) ≠ 1 := by
    intro h1
    have : s = 1 := Subtype.ext (by rw [h1, Subgroup.coe_one])
    rw [this, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have hs3' : (s : GL (Fin 248) (ZMod 2)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs3] at this
    have h' := congrArg Subtype.val this
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [hT.g0] at hgis
    exact hs1 hgis.symm
  have hpow : powIdx mul i 3 = 0 := by
    obtain ⟨h1, h2⟩ := hpowS hi 3
    rw [hgis, hs3', ← hT.g0] at h2
    exact hT.inj _ h1 _ hT.pos h2
  have hcr : (classTable c.edges mul X).2[i]! < qN := by
    have := List.all_eq_true.1 hcov i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    rcases this with (h0 | h0) | h0
    · exact absurd h0 hi0
    · exact absurd hpow h0
    · exact h0
  obtain ⟨hrep, q, hq, hqs⟩ := hinv.2 i hi hcr
  set r := (classTable c.edges mul X).2[i]! with hr
  obtain ⟨y, hy, t, hyt, w, hwJ, htw⟩ : ∃ y ∈ X.tgts, ∃ t, y.1 = t ∧ ∃ w ∈ JG,
      gi t = w * gi r * w⁻¹ := by
    have := List.all_eq_true.1 hrc r hrep
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at this
    rcases this with ⟨f, hf, hfr⟩ | ⟨y, hy, hyr⟩
    · obtain ⟨-, ⟨y, hy, hyt⟩, w, hwJ, hw⟩ := hfusG f hf
      exact ⟨y, hy, f.2.1, hyt, w, hwJ, by rw [hw, hfr]⟩
    · exact ⟨y, hy, r, hyr, 1, JG.one_mem, by group⟩
  obtain ⟨d, hd, hdy⟩ := hcov' y hy
  obtain ⟨⟨⟨hdN, hdcl⟩, -⟩, hWM⟩ := hdata d hd
  have hdt : d.1 = t := by rw [← hyt]; exact hdy
  obtain ⟨hW, hWJ⟩ := hword3 d.2.2
  have hMt : Rp (matOf P c.par c.lab qN d.1) (gi d.1) := hM d.1 hdN
  have hrel : ((abcWord d.2.2).map cdR).prod * gi d.1 =
      clsG d.2.1 * ((abcWord d.2.2).map cdR).prod :=
    (hW.mul hMt).eq_of_eq ((hclsRp d.2.1).mul hW) hWM
  have hgt : gi t = (((abcWord d.2.2).map cdR).prod)⁻¹ * clsG d.2.1 *
      ((abcWord d.2.2).map cdR).prod := by
    rw [← hdt]
    calc gi d.1 = (((abcWord d.2.2).map cdR).prod)⁻¹ *
          (((abcWord d.2.2).map cdR).prod * gi d.1) := by group
      _ = (((abcWord d.2.2).map cdR).prod)⁻¹ * (clsG d.2.1 * ((abcWord d.2.2).map cdR).prod) := by
          rw [hrel]
      _ = _ := by group
  have hκJ : q * w⁻¹ * (((abcWord d.2.2).map cdR).prod)⁻¹ ∈ JG :=
    JG.mul_mem (JG.mul_mem (hQJ hq) (JG.inv_mem hwJ)) (JG.inv_mem hWJ)
  have hsκ : (s : GL (Fin 248) (ZMod 2)) = (q * w⁻¹ * (((abcWord d.2.2).map cdR).prod)⁻¹) *
      clsG d.2.1 * (q * w⁻¹ * (((abcWord d.2.2).map cdR).prod)⁻¹)⁻¹ := by
    have hgr : gi r = w⁻¹ * gi t * w := by rw [htw]; group
    rw [← hgis, hqs, hgr, hgt]
    group
  have key : ∀ x : CFSG.Sporadic.Th.J, clsG d.2.1 = (x : GL (Fin 248) (ZMod 2)) → IsConj s x :=
    fun x hx => isConj_J (c := ⟨_, hκJ⟩) (by rw [← hx]; exact hsκ)
  have hcase : d.2.1 = 0 ∨ d.2.1 = 1 ∨ d.2.1 = 2 ∨ d.2.1 = 3 ∨ d.2.1 = 4 ∨ d.2.1 = 5 := by omega
  rcases hcase with h0 | h1 | h2 | h3 | h4 | h5
  · exact Or.inl (key _ (by simp [clsG, h0]))
  · exact Or.inr (Or.inl (key _ (by rw [hpow2]; simp [clsG, h1])))
  · exact Or.inr (Or.inr (Or.inl (key _ (by simp [clsG, h2]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ (by rw [hpow2]; simp [clsG, h3])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ (by simp [clsG, h4]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ (by rw [hpow2]; simp [clsG, h5]))))))

end Main

end CFSG.HardMathSupport.Dickson.I271
