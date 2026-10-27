module

public import Certificates.Data.Kernel.Misc.Sp8N0
public import Certificates.Data.RudvalisFF81Sp8Norm
public import CFSG.Certificates.Kernel.Misc.Sp8CzSound
public import CFSG.Certificates.Kernel.Misc.HashFoldSound

public section

namespace CFSG.KC.Sp8N0

open CFSG.KD.Sp8N0 CFSG.KD.BfsK CFSG.KC.BfsK CFSG.KC.Mat8P CFSG.KC.Sp8Syl3
  CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sm8)
open scoped Matrix

theorem trS_fold (A : List ℕ) (j : ℕ) : ∀ n,
    (List.range n).foldl (fun acc i => if (A.getD i 0).testBit j then acc + 2 ^ i else acc) 0 <
        2 ^ n ∧
      ∀ i < n, ((List.range n).foldl
        (fun acc i => if (A.getD i 0).testBit j then acc + 2 ^ i else acc) 0).testBit i =
          (A.getD i 0).testBit j
  | 0 => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1 => by
    obtain ⟨hlt, hbit⟩ := trS_fold A j n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl
      (fun acc i => if (A.getD i 0).testBit j then acc + 2 ^ i else acc) 0 = F at hlt hbit ⊢
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    by_cases hb : (A.getD n 0).testBit j = true
    · rw [if_pos hb]
      refine ⟨by omega, fun i hi => ?_⟩
      rw [Nat.add_comm]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Nat.testBit_two_pow_add_gt hi, hbit i hi]
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hlt, hb]
        rfl
    · rw [if_neg hb]
      refine ⟨by omega, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hbit i hi
      · rw [Nat.testBit_eq_false_of_lt hlt]
        simpa using hb

theorem dec8_trS (A : List ℕ) : dec8 (trS A) = (dec8 A)ᵀ := by
  ext i j
  simp only [dec8, Matrix.of_apply, Matrix.transpose_apply, vec8]
  have hj : (trS A).getD j 0 = (List.range 8).foldl
      (fun acc i => if (A.getD i 0).testBit j then acc + 2 ^ i else acc) 0 := by
    rw [List.getD_eq_getElem _ _ (by simp [trS])]
    simp [trS]
  rw [hj, (trS_fold A j 8).2 i i.2]

theorem decS_trS (A : List ℕ) : decS (trS A) = (decS A)ᵀ := by
  rw [decS, decS, dec8_trS, sm8, sm8, Matrix.transpose_submatrix]

theorem valid8_invS (c : List ℕ) : Valid8 (invS c) :=
  valid8_mulS (valid8_mulS (valid8_of_validS (by decide)) _) _

theorem codeS_inv (g : H8) : codeS g⁻¹ = invS (codeS g) := by
  refine codeS_eq_of_decS (valid8_invS _) ?_
  have hj : decS jS = jM := by decide
  rw [invS, decS_mulS, decS_mulS, decS_trS, decS_codeS, hj]
  have h := symp_matS g
  have e : jM * (matS g)ᵀ * jM * matS g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (matS g)ᵀ, h, jM_mul_jM]
  calc jM * (matS g)ᵀ * jM = jM * (matS g)ᵀ * jM * (matS g * matS g⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
    _ = matS g⁻¹ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem conj_iff {y a x : List ℕ} (hy : spS y = true) (ha : spS a = true) (hx : spS x = true) :
    mulS (mulS y a) (invS y) = x ↔ mulS y a = mulS x y := by
  have e1 : mulS (mulS y a) (invS y) = codeS (mkS y hy * mkS a ha * (mkS y hy)⁻¹) := by
    rw [codeS_mul, codeS_mul, codeS_inv, codeS_mkS, codeS_mkS]
  have e2 : mulS y a = codeS (mkS y hy * mkS a ha) := by rw [codeS_mul, codeS_mkS, codeS_mkS]
  have e3 : mulS x y = codeS (mkS x hx * mkS y hy) := by rw [codeS_mul, codeS_mkS, codeS_mkS]
  have e4 : x = codeS (mkS x hx) := (codeS_mkS x hx).symm
  constructor
  · intro h
    rw [e1, e4] at h
    have h' := codeS_injective h
    rw [e2, e3]
    refine congrArg codeS ?_
    rw [← h']
    group
  · intro h
    rw [e2, e3] at h
    have h' := codeS_injective h
    rw [e1, e4]
    refine congrArg codeS ?_
    rw [h']
    group

theorem spS_build {gens : List (List ℕ)} (hg : gens.all spS = true) (par : List (ℕ × ℕ)) :
    ∀ x ∈ build one8 mulS gens par, spS x = true := by
  refine build_mem one8 mulS gens (by decide +kernel) (fun x hx s => ?_) par
  refine CFSG.KC.Sp8Cz.spS_mulS hx ?_
  by_cases hs : s < gens.length
  · rw [List.getD_eq_getElem _ _ hs]
    exact List.all_eq_true.1 hg _ (List.getElem_mem hs)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide +kernel

theorem spS_tab {gens : List (List ℕ)} (hg : gens.all spS = true) {n t : ℕ}
    (ht : t < (tabS gens n).size) : spS ((tabS gens n).getD t []) = true :=
  spS_build hg _ _ (CFSG.KC.Sp8Cz.getD_mem ht)

theorem getD_map_inv {T : Array (List ℕ)} {t : ℕ} (ht : t < T.size) :
    (T.map invS).getD t [] = invS (T.getD t []) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem ht,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  rfl

theorem cfoundS_of {T : Array (List ℕ)} (hT : ∀ t < T.size, spS (T.getD t []) = true)
    {a x : List ℕ} (ha : spS a = true) (hx : spS x = true) {t : ℕ} (ht : t < T.size)
    (h : mulS (T.getD t []) a = mulS x (T.getD t [])) :
    cfoundS T (cmapS T (T.map invS) a) a x = true := by
  rw [CFSG.KC.HashFold.cfoundS_cmapS_iff]
  · exact ⟨t, ht, by rw [getD_map_inv ht]; exact (conj_iff (hT t ht) ha hx).2 h⟩
  · intro s hs e
    rw [getD_map_inv hs] at e
    exact (conj_iff (hT s hs) ha hx).1 e

variable {R : ℕ → ℕ}

structure Header (R : ℕ → ℕ) : Prop where
  gens : ∀ s < 4, EncS (n0Gens.getD s []) (R s)
  zs : ∀ i < 4, EncS (e0Gens.getD i []) (R (Nat.add 4 i))
  zz : EncS zzS (R 8)
  z012 : EncS z012S (R 9)
  z0123 : EncS z0123S (R 10)
  e2 : EncS (mulS z3S z3S) (R 11)
  invs : ∀ s < 4, EncS (invS (n0Gens.getD s [])) (R (Nat.add 35362 s))

theorem n0gen_enc (hz : ∀ s < 4, EncS (n0Gens.getD s []) (R s)) {s : ℕ} (hs : s < 4)
    (d : List ℕ) : EncS (n0Gens.getD s d) (R s) := by
  have hl : n0Gens.length = 4 := rfl
  rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hl]; exact hs) d []]
  exact hz s hs

theorem n0Tab_facts (hz : ∀ s < 4, EncS (n0Gens.getD s []) (R s)) (h : n0TabK R 31104 = true) :
    (tabS n0Gens 31104).size = 31104 ∧ closedCheck mulS n0Gens (tabS n0Gens 31104) = true ∧
      distinctCheck (tabS n0Gens 31104) = true ∧
      ∀ t < 31104, EncS ((tabS n0Gens 31104).getD t []) (recX R 16 t) := by
  unfold n0TabK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨-, hsz, hcl, hdi, hrec⟩ := tableKk_ok (ok := validS) (num := code64) code_inj
    (start := one8) (mul := mulS) (gens := n0Gens) (fuel := 31104) (k := 4) rfl (by norm_num)
    (by norm_num) le_rfl (fun x N hx s hs d => mulE hx (n0gen_enc hz hs d))
    (by rw [h0]; exact one_enc) h (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hsz, hcl, hdi, hrec⟩

theorem n0_spS : n0Gens.all spS = true := by decide +kernel

theorem spS_T {t : ℕ} (ht : t < (tabS n0Gens 31104).size) :
    spS ((tabS n0Gens 31104).getD t []) = true :=
  spS_tab n0_spS ht

theorem e0_spS' : e0Gens.all spS = true := by decide +kernel

theorem e0_spS'' : spS z0S = true ∧ spS z1S = true ∧ spS z2S = true ∧ spS z3S = true := by
  decide +kernel

theorem spS_E {t : ℕ} (ht : t < (tabS e0Gens 81).size) :
    spS ((tabS e0Gens 81).getD t []) = true :=
  spS_tab e0_spS' ht

theorem n0Chk_of {Q : ℕ → ℕ} (hH : Header R) (hQ : ∀ s < 5, EncS (pGens.getD s []) (Q s))
    (hE : CFSG.KD.Sp8Syl3.tabEK Q 81 = true) (hT : n0TabK R 31104 = true)
    (hM : n0MemK R = true) (hC : n0ConjK R Q = true) : n0Chk899104 = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := n0Tab_facts hH.gens hT
  have hMa := CFSG.KC.G2Three.allBelow_g2 hM (by norm_num)
  have hCa := CFSG.KC.G2Three.allBelow_g2 hC (by norm_num)
  unfold n0Chk899104 tabOK
  dsimp only
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, n0_spS⟩, ?_⟩, ?_⟩
  · rw [hsz] at ht
    exact (hrec t ht).1
  · refine CFSG.KC.G2Three.all_of_getD [] fun s hs => CFSG.KC.G2Three.all_of_getD [] fun i hi => ?_
    have hs4 : s < 4 := hs
    have hi4 : i < 4 := hi
    have e := hCa (4 * s + i) (by omega)
    have d1 : Nat.div (4 * s + i) 4 = s := by
      change (4 * s + i) / 4 = s
      omega
    have d2 : Nat.mod (4 * s + i) 4 = i := by
      change (4 * s + i) % 4 = i
      omega
    rw [d1, d2, Bool.and_eq_true] at e
    have hg := hH.gens s hs4
    have hzi := hH.zs i hi4
    have hgi := hH.invs s hs4
    have hc : EncS (conjS (n0Gens.getD s []) (e0Gens.getD i [])) _ := mulE (mulE hg hzi) hgi
    rw [Bool.and_eq_true]
    refine ⟨found_of hQ hE hc e.1, ?_⟩
    rw [beqE (mulE hg hzi) (mulE hc hg)]
    exact e.2
  · refine CFSG.KC.G2Three.all_of_getD [] fun i hi => ?_
    have hi4 : i < 4 := hi
    have e := hMa i hi4
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
    rw [CFSG.KC.G2Three.found_indexMap]
    have hp := hrec _ e.1
    exact ⟨_, by rw [hsz]; exact e.1,
      code_inj _ _ hp.1 (hH.zs i hi4).1 (by rw [hp.2, e.2, (hH.zs i hi4).2])⟩

theorem l1_enc (hH : Header R) : ∀ j < 8, EncS (l1S.getD j []) (l1At R j) := by
  intro j hj
  have h0 := hH.zs 0 (by norm_num)
  have h1 := hH.zs 1 (by norm_num)
  have h2 := hH.zs 2 (by norm_num)
  have h3 := hH.zs 3 (by norm_num)
  interval_cases j
  · exact h0
  · exact mulE h0 h0
  · exact h1
  · exact mulE h1 h1
  · exact h2
  · exact mulE h2 h2
  · exact h3
  · exact mulE h3 h3

theorem l1_spS : ∀ j < 8, spS (l1S.getD j []) = true := by decide +kernel

theorem l1_mem {j : ℕ} (hj : j < 8) : l1S.contains (l1S.getD j []) = true := by
  have hl : l1S.length = 8 := rfl
  rw [List.contains_iff_mem, List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
  exact List.getElem_mem _

theorem conjAtN_spec (hH : Header R) (hT : n0TabK R 31104 = true) {t A X : ℕ} {a x : List ℕ}
    (ha : EncS a A) (hx : EncS x X) (h : conjAtN R t A X = true) :
    t < (tabS n0Gens 31104).size ∧
      mulS ((tabS n0Gens 31104).getD t []) a = mulS x ((tabS n0Gens 31104).getD t []) := by
  obtain ⟨hsz, -, -, hrec⟩ := n0Tab_facts hH.gens hT
  unfold conjAtN at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  have hy := hrec t h.1
  refine ⟨by rw [hsz]; exact h.1, ?_⟩
  rw [← beq_iff_eq, beqE (mulE hy ha) (mulE hx hy)]
  exact h.2

theorem fix_reps : fixS z3S = 64 ∧ fixS (mulS z3S z3S) = 64 ∧ fixS zzS = 16 ∧ fixS z012S = 4 ∧
    fixS z0123S = 1 := by decide +kernel

theorem fixS_conj {y a x : List ℕ} (hy : spS y = true) (ha : spS a = true) (hx : spS x = true)
    (h : mulS y a = mulS x y) : fixS x = fixS a := by
  have e := (conj_iff hy ha hx).2 h
  have e' : codeS (mkS y hy * mkS a ha * (mkS y hy)⁻¹) = x := by
    rw [codeS_mul, codeS_mul, codeS_inv, codeS_mkS, codeS_mkS, e]
  rw [← e', ← fixCount_eq_fixS, fixCount_conj, fixCount_eq_fixS, codeS_mkS]

theorem T_spS : ∀ t < (tabS n0Gens 31104).size, spS ((tabS n0Gens 31104).getD t []) = true :=
  fun _ ht => spS_T ht

theorem conj_case (hH : Header R) (hT : n0TabK R 31104 = true) {t A X : ℕ} {a x : List ℕ}
    (ha : EncS a A) (has : spS a = true) (hx : EncS x X) (hxs : spS x = true)
    (h : conjAtN R t A X = true) :
    fixS x = fixS a ∧ cfoundS (tabS n0Gens 31104)
      (cmapS (tabS n0Gens 31104) ((tabS n0Gens 31104).map invS) a) a x = true := by
  obtain ⟨ht, hm⟩ := conjAtN_spec hH hT ha hx h
  exact ⟨fixS_conj (spS_T ht) has hxs hm, cfoundS_of T_spS has hxs ht hm⟩

theorem clsChk_of {Q : ℕ → ℕ} (hH : Header R) (hQ : ∀ s < 5, EncS (pGens.getD s []) (Q s))
    (hE : CFSG.KD.Sp8Syl3.tabEK Q 81 = true) (hT : n0TabK R 31104 = true)
    (h : clsK R Q = true) : clsChk899104 = true := by
  obtain ⟨hEsz, -, -, hErec⟩ := tabE_facts hQ hE
  have hall := CFSG.KC.G2Three.allBelow_g2 h (by norm_num)
  obtain ⟨f1, f2, f3, f4, f5⟩ := fix_reps
  unfold clsChk899104
  dsimp only
  refine CFSG.KC.G2Three.allCheck_of fun e he => ?_
  have he' : e < 81 := by rw [hEsz] at he; exact he
  have hx := hErec e he'
  have hxs := spS_E he
  have r := hall e he'
  unfold clsAt at r
  generalize (tabS e0Gens 81).getD e [] = x at hx hxs ⊢
  generalize R (Nat.add 31121 e) = w at r
  generalize Nat.land w 7 = c at r
  generalize Nat.land (Nat.shiftRight w 3) 7 = j at r
  generalize Nat.shiftRight w 6 = t at r
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at r
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  rcases r with ⟨-, hx1⟩ | ⟨⟨⟨hc1, hc5⟩, hcj⟩, hl⟩
  · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
    rw [beqE hx one_enc, hx1]
    rfl
  · have hl1 : c ≤ 2 → x = l1S.getD j [] ∧ j < 8 := by
      intro hc2
      rcases hl with hl | ⟨hj, hX⟩
      · omega
      · exact ⟨code_inj _ _ hx.1 (l1_enc hH j hj).1 (by rw [hx.2, hX, (l1_enc hH j hj).2]), hj⟩
    interval_cases c
    · obtain ⟨hf, hcf⟩ := conj_case hH hT (hH.zs 3 (by norm_num)) (by decide +kernel) hx hxs hcj
      obtain ⟨rfl, hj⟩ := hl1 (by norm_num)
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨hf.trans f1, l1_mem hj⟩, Or.inl hcf⟩
    · obtain ⟨hf, hcf⟩ := conj_case hH hT hH.e2 (by decide +kernel) hx hxs hcj
      obtain ⟨rfl, hj⟩ := hl1 (by norm_num)
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨hf.trans f2, l1_mem hj⟩, Or.inr hcf⟩
    · obtain ⟨hf, hcf⟩ := conj_case hH hT hH.zz (by decide +kernel) hx hxs hcj
      refine Or.inl (Or.inl (Or.inr ?_))
      rw [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hf.trans f3, hcf⟩
    · obtain ⟨hf, hcf⟩ := conj_case hH hT hH.z012 (by decide +kernel) hx hxs hcj
      refine Or.inl (Or.inr ?_)
      rw [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hf.trans f4, hcf⟩
    · obtain ⟨hf, hcf⟩ := conj_case hH hT hH.z0123 (by decide +kernel) hx hxs hcj
      refine Or.inr ?_
      rw [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hf.trans f5, hcf⟩

theorem prodChk_of (hH : Header R) (hT : n0TabK R 31104 = true) (h : prodK R = true) :
    prodChk899104 = true := by
  have hall := CFSG.KC.G2Three.allBelow_g2 h (by norm_num)
  unfold prodChk899104
  dsimp only
  refine CFSG.KC.G2Three.all_of_getD 0 fun a ha => CFSG.KC.G2Three.all_of_getD 0 fun b hb => ?_
  rw [List.length_range] at ha hb
  rw [List.getD_eq_getElem _ _ (by simp; exact ha), List.getElem_range,
    List.getD_eq_getElem _ _ (by simp; exact hb), List.getElem_range]
  have e := hall (8 * a + b) (by omega)
  have d1 : Nat.div (8 * a + b) 8 = a := by
    change (8 * a + b) / 8 = a
    omega
  have d2 : Nat.mod (8 * a + b) 8 = b := by
    change (8 * a + b) % 8 = b
    omega
  rw [d1, d2, Bool.or_eq_true, Nat.beq_eq] at e
  rw [Bool.or_eq_true, beq_iff_eq]
  rcases e with e | e
  · exact Or.inl e
  · refine Or.inr (conj_case hH hT hH.zz (by decide +kernel)
      (mulE (l1_enc hH a ha) (l1_enc hH b hb))
      (CFSG.KC.Sp8Cz.spS_mulS (l1_spS a ha) (l1_spS b hb)) e).2

theorem normChk_of (hH : Header R) (hT : n0TabK R 31104 = true) (h : normK R = true) :
    normChk899104 = true := by
  have hall := CFSG.KC.G2Three.allBelow_g2 h (by norm_num)
  have hz : ∀ i < 4, spS (e0Gens.getD i []) = true := by decide +kernel
  unfold normChk899104
  dsimp only
  refine CFSG.KC.G2Three.all_of_getD 0 fun a ha => CFSG.KC.G2Three.all_of_getD 0 fun b hb =>
    CFSG.KC.G2Three.all_of_getD 0 fun c hc => CFSG.KC.G2Three.all_of_getD 0 fun d hd => ?_
  rw [List.length_range] at ha hb hc hd
  have r8 : ∀ x < 8, (List.range 8).getD x 0 = x := fun x hx => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_range]
  rw [r8 a ha, r8 b hb, r8 c hc, r8 d hd]
  have e := hall (512 * a + 64 * b + 8 * c + d) (by omega)
  have d1 : Nat.div (512 * a + 64 * b + 8 * c + d) 512 = a := by
    change (512 * a + 64 * b + 8 * c + d) / 512 = a
    omega
  have d2 : Nat.mod (Nat.div (512 * a + 64 * b + 8 * c + d) 64) 8 = b := by
    change (512 * a + 64 * b + 8 * c + d) / 64 % 8 = b
    omega
  have d3 : Nat.mod (Nat.div (512 * a + 64 * b + 8 * c + d) 8) 8 = c := by
    change (512 * a + 64 * b + 8 * c + d) / 8 % 8 = c
    omega
  have d4 : Nat.mod (512 * a + 64 * b + 8 * c + d) 8 = d := by
    change (512 * a + 64 * b + 8 * c + d) % 8 = d
    omega
  rw [d1, d2, d3, d4] at e
  have q : ∀ x : ℕ, Nat.div x 2 = x / 2 := fun _ => rfl
  rw [q a, q b, q c, q d, Bool.or_eq_true] at e
  rw [Bool.or_eq_true]
  rcases e with e | e
  · exact Or.inl e
  · refine Or.inr ?_
    unfold normAt at e
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩ := e
    have h0 := conjAtN_spec hH hT (hH.zs 0 (by norm_num)) (l1_enc hH a ha) e0
    have h1 := conjAtN_spec hH hT (hH.zs 1 (by norm_num)) (l1_enc hH b hb) e1
    have h2 := conjAtN_spec hH hT (hH.zs 2 (by norm_num)) (l1_enc hH c hc) e2
    have h3 := conjAtN_spec hH hT (hH.zs 3 (by norm_num)) (l1_enc hH d hd) e3
    generalize R (Nat.add 31266 (512 * a + 64 * b + 8 * c + d)) = t at h0 h1 h2 h3
    set T := tabS n0Gens 31104 with hTdef
    have hK : ∀ s < T.size,
        (e0Gens.map fun z => mulS (mulS (T.getD s []) z) ((T.map invS).getD s [])) =
          [l1S.getD a [], l1S.getD b [], l1S.getD c [], l1S.getD d []] ↔
        (mulS (T.getD s []) z0S = mulS (l1S.getD a []) (T.getD s []) ∧
          mulS (T.getD s []) z1S = mulS (l1S.getD b []) (T.getD s []) ∧
          mulS (T.getD s []) z2S = mulS (l1S.getD c []) (T.getD s []) ∧
          mulS (T.getD s []) z3S = mulS (l1S.getD d []) (T.getD s [])) := by
      intro s hs
      rw [getD_map_inv hs]
      have hy := T_spS s hs
      obtain ⟨s0, s1, s2, s3⟩ := e0_spS''
      simp only [e0Gens, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [conj_iff hy s0 (l1_spS a ha), conj_iff hy s1 (l1_spS b hb), conj_iff hy s2 (l1_spS c hc),
        conj_iff hy s3 (l1_spS d hd)]
    have hsome := (CFSG.KC.HashFold.isSome_get?_range_foldl (K := fun s =>
      e0Gens.map fun z => mulS (mulS (T.getD s []) z) ((T.map invS).getD s []))
      (n := T.size) (k := [l1S.getD a [], l1S.getD b [], l1S.getD c [], l1S.getD d []])).2
      ⟨t, h0.1, (hK t h0.1).2 ⟨h0.2, h1.2, h2.2, h3.2⟩⟩
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hsome
    beta_reduce at ht'
    rw [ht']
    obtain ⟨hlt, hk⟩ := CFSG.KC.HashFold.get?_range_foldl ht'
    obtain ⟨k0, k1, k2, k3⟩ := (hK t' hlt).1 hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨hlt, k0⟩, k1⟩, k2⟩, k3⟩

end CFSG.KC.Sp8N0

end
