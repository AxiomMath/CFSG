module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSLayer

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.UnbalancedGS

section SLP

variable {n : ℕ}

@[expose] def RegIn (H : Subgroup (Equiv.Perm (Fin n))) (r : HeGSReg) : Prop :=
  ∃ g ∈ H, Rep n r.1 g ∧ Rep n r.2 g⁻¹

theorem rep_idTab : Rep n (idTab n) 1 := TabRep.idTab.2

theorem regIn_letter {H : Subgroup (Equiv.Perm (Fin n))} {R : Array HeGSReg}
    (hR : ∀ k < R.size, RegIn H R[k]!) {l : ℤ} (hl0 : l ≠ 0) (hl : l.natAbs ≤ R.size) :
    RegIn H (heGSLetter R l) := by
  unfold heGSLetter
  split_ifs with hpos
  · exact hR _ (by omega)
  · obtain ⟨g, hg, h1, h2⟩ := hR ((-l).toNat - 1) (by omega)
    exact ⟨g⁻¹, H.inv_mem hg, h2, by rw [inv_inv]; exact h1⟩

theorem regIn_word {H : Subgroup (Equiv.Perm (Fin n))} {R : Array HeGSReg}
    (hR : ∀ k < R.size, RegIn H R[k]!) :
    ∀ w : List ℤ, Native.lettersOK R.size w = true → RegIn H (heGSWord n R w)
  | [], _ => ⟨1, H.one_mem, rep_idTab, by rw [inv_one]; exact rep_idTab⟩
  | l :: w, hw => by
    simp only [Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlk⟩, hw⟩ := hw
    obtain ⟨a, ha, ha1, ha2⟩ := regIn_letter hR hl0 hlk
    obtain ⟨b, hb, hb1, hb2⟩ := regIn_word hR w (by simpa [Native.lettersOK] using hw)
    refine ⟨a * b, H.mul_mem ha hb, rep_comp ha1 hb1, ?_⟩
    rw [mul_inv_rev]
    exact rep_comp hb2 ha2

theorem getElem!_push_of_lt {R : Array HeGSReg} {r : HeGSReg} {k : ℕ} (hk : k < R.size) :
    (R.push r)[k]! = R[k]! := by
  rw [getElem!_pos (R.push r) k (by simp; omega), getElem!_pos R k hk, Array.getElem_push_lt]

theorem getElem!_push_size {R : Array HeGSReg} {r : HeGSReg} : (R.push r)[R.size]! = r := by
  rw [getElem!_pos (R.push r) R.size (by simp), Array.getElem_push_eq]

theorem regIn_run {H : Subgroup (Equiv.Perm (Fin n))} :
    ∀ (prog : List (List ℤ)) (R : Array HeGSReg), heGSOK R.size prog = true →
      (∀ k < R.size, RegIn H R[k]!) →
      ∀ k < (heGSRun n R prog).size, RegIn H (heGSRun n R prog)[k]!
  | [], R, _, hR => by simpa [heGSRun] using hR
  | w :: prog, R, hok, hR => by
    simp only [heGSOK, Bool.and_eq_true] at hok
    have hR' : ∀ k < (R.push (heGSWord n R w)).size,
        RegIn H (R.push (heGSWord n R w))[k]! := by
      intro k hk
      rw [Array.size_push] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [getElem!_push_of_lt hk]
        exact hR k hk
      · rw [getElem!_push_size]
        exact regIn_word hR w hok.1
    exact regIn_run prog (R.push (heGSWord n R w)) (by rw [Array.size_push]; exact hok.2) hR'

theorem size_heGSRun (R : Array HeGSReg) (prog : List (List ℤ)) :
    (heGSRun n R prog).size = R.size + prog.length := by
  induction prog generalizing R with
  | nil => simp [heGSRun]
  | cons w prog ih =>
    rw [show heGSRun n R (w :: prog) = heGSRun n (R.push (heGSWord n R w)) prog from rfl, ih,
      Array.size_push, List.length_cons]
    omega

end SLP

theorem heK0_eq : heK0 = (pLayer ↥(centralizerIn heP (heGenPerm 0)) 2).map
    (centralizerIn heP (heGenPerm 0)).subtype := rfl

theorem heK0_le : heK0 ≤ heP := (gsFixedLayer_le_inf heP _).trans inf_le_left

theorem heP_le_of_mem {H : Subgroup (Equiv.Perm (Fin 8330))} (h0 : heGenPerm 0 ∈ H)
    (h1 : heGenPerm 1 ∈ H) : heP ≤ H := by
  rw [heP, closure_le]
  rintro _ (rfl | rfl)
  · exact h0
  · exact h1

section Gen


@[expose] def heGSG : Equiv.Perm (Fin 8330) :=
  ((heGenPerm 1)⁻¹ * heGenPerm 0 * heGenPerm 1 * (heGSV : Equiv.Perm (Fin 8330))) ^ 2 *
    (heGenPerm 1)⁻¹

theorem heGSG_mem : heGSG ∈ heP := by
  have h0 := heGenPerm_mem (k := 0) (by norm_num)
  have h1 := heGenPerm_mem (k := 1) (by norm_num)
  have hv : (heGSV : Equiv.Perm (Fin 8330)) ∈ heP := (mem_centralizerIn.mp heGSV.2).1
  exact mul_mem (pow_mem (mul_mem (mul_mem (mul_mem (inv_mem h1) h0) h1) hv) 2) (inv_mem h1)

theorem rep_heGSG : Rep 8330 heGSGTab heGSG := by
  have ha1i := rep_heGen_inv (k := 1) (by norm_num)
  have hz := rep_comp (rep_comp (rep_comp ha1i (rep_heGen (k := 0) (by norm_num)))
    (rep_heGen (k := 1) (by norm_num))) tabRep_heGSVTab.2
  rw [heGSGTab, heGSG, sq]
  exact rep_comp (rep_comp hz hz) ha1i


theorem rep_heGSG_inv : Rep 8330 (CFSG.Monster.B.Co2.Native.invCand 8330 heGSGTab) heGSG⁻¹ := by
  have h := permChk_spec heGS_gen_check.2.1
  rw [h.1.unique rep_heGSG] at h
  exact h.2

theorem heGSG_conj : heGSG * heGenPerm 0 * heGSG⁻¹ = (heGSV : Equiv.Perm (Fin 8330)) := by
  have h1 := rep_comp rep_heGSG (rep_heGen (k := 0) (by norm_num))
  have h2 := rep_comp tabRep_heGSVTab.2 rep_heGSG
  rw [heGS_gen_check.2.2.1] at h1
  rw [h1.unique h2, mul_inv_cancel_right]

theorem gsFixedLayer_v : gsFixedLayer heP (heGSV : Equiv.Perm (Fin 8330)) =
    heK0.map (MulAut.conj heGSG).toMonoidHom := by
  rw [← heGSG_conj]
  exact HeLay.gsFixedLayer_conj heGSG_mem _


theorem heGSInit_get_lt {k : ℕ} (hk : k < 5) :
    heGSInit[k]! = (heGSKTab (heDWords.getD (k % 5) []),
      heGSKTab (heDWords.getD (k % 5) []).reverse) := by
  rw [heGSInit, getElem!_pos _ k (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [hk, ↓reduceIte]

theorem heGSInit_get_ge {k : ℕ} (hk : k < 10) (h5 : ¬ k < 5) :
    heGSInit[k]! =
      (comp 8330 (comp 8330 heGSGTab (heGSKTab (heDWords.getD (k % 5) [])))
          (CFSG.Monster.B.Co2.Native.invCand 8330 heGSGTab),
        comp 8330 (comp 8330 heGSGTab (heGSKTab (heDWords.getD (k % 5) []).reverse))
          (CFSG.Monster.B.Co2.Native.invCand 8330 heGSGTab)) := by
  rw [heGSInit, getElem!_pos _ k (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [h5, ↓reduceIte]

theorem regIn_heGSInit : ∀ k < heGSInit.size,
    RegIn (heK0 ⊔ gsFixedLayer heP (heGSV : Equiv.Perm (Fin 8330))) heGSInit[k]! := by
  intro k hk
  have hk10 : k < 10 := by rw [heGSInit, Array.size_ofFn] at hk; exact hk
  have hw := heDWords_lt (k % 5)
  have hE := tabRep_heGSKTab hw
  have hEi : TabRep (heGSKTab (heDWords.getD (k % 5) []).reverse)
      (heGSKW (heDWords.getD (k % 5) []))⁻¹ := by
    rw [← heGSKW_reverse hw]
    exact tabRep_heGSKTab fun j hj => hw j (List.mem_reverse.mp hj)
  have hEK : heGSKW (heDWords.getD (k % 5) []) ∈ heK0 :=
    mem_heK0_of_rho0_mem (x := heGSE (k % 5)) (by
      rw [rho0_heGSE]; exact heDPerm_mem_D (Nat.mod_lt _ (by norm_num)))
  by_cases h5 : k < 5
  · rw [heGSInit_get_lt h5]
    refine ⟨heGSKW (heDWords.getD (k % 5) []), mem_sup_left hEK, ?_, ?_⟩
    · dsimp only
      exact hE.2
    · dsimp only
      exact hEi.2
  · rw [heGSInit_get_ge hk10 h5]
    have hc1 := rep_comp (rep_comp rep_heGSG hE.2) rep_heGSG_inv
    have hc2 := rep_comp (rep_comp rep_heGSG hEi.2) rep_heGSG_inv
    have hinv : heGSG * (heGSKW (heDWords.getD (k % 5) []))⁻¹ * heGSG⁻¹ =
        (heGSG * heGSKW (heDWords.getD (k % 5) []) * heGSG⁻¹)⁻¹ := by group
    rw [hinv] at hc2
    refine ⟨heGSG * heGSKW (heDWords.getD (k % 5) []) * heGSG⁻¹, mem_sup_right ?_, ?_, ?_⟩
    · rw [gsFixedLayer_v]
      exact ⟨_, hEK, rfl⟩
    · dsimp only
      exact hc1
    · dsimp only
      exact hc2

theorem sup_gsFixedLayer_v : heK0 ⊔ gsFixedLayer heP (heGSV : Equiv.Perm (Fin 8330)) = heP := by
  obtain ⟨hok, -, -, h0, h1⟩ := heGS_gen_check
  have hrun := regIn_run (H := heK0 ⊔ gsFixedLayer heP (heGSV : Equiv.Perm (Fin 8330)))
    heGSProg heGSInit (by rw [heGSInit, Array.size_ofFn]; exact hok) regIn_heGSInit
  have hsize : (heGSRun 8330 heGSInit heGSProg).size = 135 := by
    rw [size_heGSRun, heGSInit, Array.size_ofFn]
    simp [heGSProg]
  have hmem : ∀ i < 2, heGenPerm i ∈ heK0 ⊔ gsFixedLayer heP (heGSV : Equiv.Perm (Fin 8330)) := by
    intro i hi
    obtain ⟨p, hp, hp1, -⟩ := hrun (133 + i) (by omega)
    have hrep : Rep 8330 (heGSRun 8330 heGSInit heGSProg)[133 + i]!.1 (heGenPerm i) := by
      interval_cases i
      · rw [h0]; exact rep_heGen (by norm_num)
      · rw [h1]; exact rep_heGen (by norm_num)
    rwa [hrep.unique hp1]
  exact le_antisymm (sup_le heK0_le ((gsFixedLayer_le_inf heP _).trans inf_le_left))
    (heP_le_of_mem (hmem 0 (by norm_num)) (hmem 1 (by norm_num)))

end Gen

theorem exists_conj_d1
    {d : Equiv.Perm (Fin 105)} (hd : d ∈ genGroup 105 heDGens heDPerm)
    (h1 : d ≠ 1) (h2 : d * d = 1) :
    ∃ c ∈ genGroup 105 heDGens heDPerm, c * heDPerm 1 * c⁻¹ = d := by
  obtain ⟨l, hl⟩ := classFunS_surjective tabRep_heDGens heD_cert (ConjClasses.mk ⟨d, hd⟩)
  rw [classFunS, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hl
  obtain ⟨⟨c, hcD⟩, hc⟩ := hl
  have hc' : c * classRepPerm heDPerm heDClassWords l * c⁻¹ = d := by
    have h := congrArg Subtype.val hc
    simpa only [coe_mul, coe_inv] using h
  have hrep2 : classRepPerm heDPerm heDClassWords l * classRepPerm heDPerm heDClassWords l = 1 := by
    have e : c * (classRepPerm heDPerm heDClassWords l * classRepPerm heDPerm heDClassWords l) *
        c⁻¹ = d * d := by
      rw [← hc']; group
    rw [h2] at e
    calc _ = c⁻¹ * (c * (classRepPerm heDPerm heDClassWords l *
          classRepPerm heDPerm heDClassWords l) * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group
  have hT := tabRep_classRep tabRep_heDGens heD_cert l.2
  obtain ⟨l, hl10⟩ := l
  have hcases : l = 0 ∨ l = 1 ∨ l ∈ [2, 3, 4, 5, 6, 7, 8, 9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases hcases with rfl | rfl | hl
  · exfalso
    apply h1
    rw [← hc']
    show c * (([] : List ℕ).map heDPerm).prod * c⁻¹ = 1
    simp
  · refine ⟨c, hcD, ?_⟩
    rw [← hc']
    show c * heDPerm 1 * c⁻¹ = c * (([1] : List ℕ).map heDPerm).prod * c⁻¹
    simp
  · exfalso
    exact heGS_layer_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2 l hl
      (((hT.comp hT).eq_iff TabRep.idTab).2 hrep2)

section Classes


theorem mem_heZ0_of_mem_ker {k : ↥(centralizerIn heP (heGenPerm 0))}
    (hk : k ∈ HeLay.rho0.ker) : (k : Equiv.Perm (Fin 8330)) ∈ heZ0 := by
  rw [heZ0, LocalAnalysis.ComponentInitial.mem_map_center_iff]
  refine ⟨mem_map_of_mem _ (ker_le_layer hk), fun e he => ?_⟩
  obtain ⟨e', he', rfl⟩ := he
  exact congrArg Subtype.val (layer_comm_ker he' hk)

theorem exists_conj_v {w : Equiv.Perm (Fin 8330)} (hwK : w ∈ heK0)
    (hwc : w ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0)) (hwZ : w ∉ heZ0) :
    ∃ s ∈ heK0, w = s * (heGSV : Equiv.Perm (Fin 8330)) * s⁻¹ := by
  rw [heK0_eq] at hwK
  obtain ⟨n₀, hn₀, rfl⟩ := hwK
  have hn₀D : HeLay.rho0 n₀ ∈ genGroup 105 heDGens heDPerm := by
    rw [← layer_facts.2.2]
    exact mem_map_of_mem _ hn₀
  have hn₀1 : HeLay.rho0 n₀ ≠ 1 := fun h => hwZ (mem_heZ0_of_mem_ker h)
  have hw2 : n₀ * n₀ = 1 := by
    apply Subtype.ext
    have h := HeFM.orderOf_of_mem_conjClass hwc
    rw [coe_mul, ← sq, ← h, coe_one]
    exact pow_orderOf_eq_one _
  have hn₀2 : HeLay.rho0 n₀ * HeLay.rho0 n₀ = 1 := by rw [← map_mul, hw2, map_one]
  obtain ⟨c, hc, hcd⟩ := exists_conj_d1 hn₀D hn₀1 hn₀2
  rw [← layer_facts.2.2] at hc
  obtain ⟨s, hs, rfl⟩ := hc
  set w' := s⁻¹ * n₀ * s with hw'
  have hw'ρ : HeLay.rho0 w' = HeLay.rho0 (heGSE 1) := by
    rw [hw', map_mul, map_mul, map_inv, ← hcd, rho0_heGSE]
    group
  have hk : w' * (heGSE 1)⁻¹ ∈ HeLay.rho0.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hw'ρ, mul_inv_cancel]
  have hw'e : w' = (w' * (heGSE 1)⁻¹) * heGSE 1 := by group
  have hfix : fixCard (w' : Equiv.Perm (Fin 8330)) = 346 := by
    obtain ⟨c', -, hc'⟩ := hwc
    have hc'' : (n₀ : Equiv.Perm (Fin 8330)) = c' * heGenPerm 0 * c'⁻¹ := hc'
    have e : (w' : Equiv.Perm (Fin 8330)) = ((s : Equiv.Perm (Fin 8330))⁻¹ * c') *
        heGenPerm 0 * ((s : Equiv.Perm (Fin 8330))⁻¹ * c')⁻¹ := by
      rw [hw', coe_mul, coe_mul, coe_inv, hc'']
      group
    rw [e, fixCard_conj, fixCard_heA0]
  obtain ⟨-, -, -, -, -, -, -, -, -, hf1, hf2, hf3, -⟩ := heGS_layer_check
  have hU := coe_heGSU
  have he1 : ((heGSE 1 : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330)) =
      heGSKW (heDWords.getD 1 []) := rfl
  have hfixW : ∀ w : List ℕ, (∀ j ∈ w, j < 9) → heGSFix (heGSKTab w) ≠ 346 →
      fixCard (heGSKW w) ≠ 346 := by
    intro w hw hf
    rw [fixCard_eq_countP (tabRep_heGSKTab hw).2]
    exact hf
  have hlt1 := heDWords_lt 1
  have hltU := heGSComm2_lt heGSUComm
  have hw'v : w' = heGSV := by
    rcases mem_ker_rho0 hk with h | h | h | h <;> rw [h] at hw'e
    · exfalso
      apply hfixW _ hlt1 hf1
      rw [← he1, ← hfix, hw'e, one_mul]
    · rw [hw'e]
      rfl
    · exfalso
      apply hfixW _ (fun j hj => (List.mem_append.mp hj).elim (hltU j) (hlt1 j)) hf2
      rw [← hfix, hw'e, coe_mul, hU, he1, heGSKW_append]
    · exfalso
      apply hfixW (0 :: (heGSComm2 heGSUComm ++ heDWords.getD 1 []))
        (fun j hj => by
          rcases List.mem_cons.mp hj with rfl | hj
          · norm_num
          · exact (List.mem_append.mp hj).elim (hltU j) (hlt1 j)) hf3
      have hperm : ((heGST0 * heGSU * heGSE 1 : ↥(centralizerIn heP (heGenPerm 0))) :
          Equiv.Perm (Fin 8330)) = heGSKW (0 :: (heGSComm2 heGSUComm ++ heDWords.getD 1 [])) := by
        rw [coe_mul, coe_mul, hU, he1]
        show heGenPerm 0 * heGSKW (heGSComm2 heGSUComm) * heGSKW (heDWords.getD 1 []) =
          heInnerCP0 0 * heGSKW (heGSComm2 heGSUComm ++ heDWords.getD 1 [])
        rw [heInnerCP0_zero, heGSKW_append, mul_assoc]
      rw [← hfix, hw'e, hperm]
  refine ⟨s, by rw [heK0_eq]; exact mem_map_of_mem _ hs, ?_⟩
  have e : n₀ = s * w' * s⁻¹ := by rw [hw']; group
  show (n₀ : Equiv.Perm (Fin 8330)) = _
  rw [e, hw'v, coe_mul, coe_mul, coe_inv]

end Classes

theorem heldTwoAGenerationModel :
    HeldTwoAGenerationModel := by
  intro w hwK hwc hwZ _
  obtain ⟨s, hsK, rfl⟩ := exists_conj_v hwK hwc hwZ
  have hsP : s ∈ heP := heK0_le hsK
  have hK : heK0.map (MulAut.conj s).toMonoidHom = heK0 :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hsK)
  have hP : heP.map (MulAut.conj s).toMonoidHom = heP :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hsP)
  rw [HeLay.gsFixedLayer_conj hsP, ← hK, ← Subgroup.map_sup, sup_gsFixedLayer_v, hP]

end CFSG.ComponentClassification.GrSLit.HeGS
