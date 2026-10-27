module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Slp
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import Certificates.Certificate129080

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

@[expose] def d1gs : List (Equiv.Perm (Fin 2300)) := aSeeds ++ [locZ, locT] ++ cTuple ++ dTuple

theorem repTuple_pair {x y : Array ℕ} {a b : Equiv.Perm (Fin 2300)} (hx : Rep 2300 x a)
    (hy : Rep 2300 y b) : RepTuple 2300 #[x, y] [a, b] := by
  refine ⟨rfl, fun h hh => ?_⟩
  have hh' : h < 2 := hh
  interval_cases h
  · exact hx
  · exact hy

theorem d1_base_rep : RepTuple 2300 (d1Base ()) d1gs :=
  (((repTuple_a.append (repTuple_pair rep_z rep_t)).append repTuple_c).append repTuple_d)

theorem d1gs_mem : ∀ g ∈ d1gs, g ∈ co2P := by
  intro g hg
  simp only [d1gs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · exact aSeeds_mem g hg
  · rcases hg with rfl | rfl
    · exact locZ_mem
    · exact locT_mem
  · exact cTuple_mem g hg
  · exact dTuple_mem g hg

@[expose] def d1Vals : List (Equiv.Perm (Fin 2300)) := extendTuple d1gs d1SlpA

theorem getD_one_mem' {H : Subgroup (Equiv.Perm (Fin 2300))} {l : List (Equiv.Perm (Fin 2300))}
    (hl : ∀ g ∈ l, g ∈ H) (i : ℕ) : l.getD i 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact H.one_mem
  | some g => exact hl g (List.mem_of_getElem? h)

theorem d1Vals_mem (i : ℕ) : d1Vals.getD i 1 ∈ co2P :=
  getD_one_mem' (extendTuple_mem co2P d1gs d1SlpA d1gs_mem) i

theorem d1_checks : d1Check () = true := Certificates.certificate129080

theorem d1_stageA :
    (∀ e ∈ d1EqsA, wordValue d1Vals e.1 = wordValue d1Vals e.2) ∧
      (∀ e ∈ d1NesA, wordValue d1Vals e.1 ≠ wordValue d1Vals e.2) := by
  have h := d1_checks
  simp only [d1Check, Bool.and_eq_true] at h
  exact slpOK_sound d1_base_rep h.1

theorem extendTuple_getD_lt : ∀ (ds : List (List ℤ)) (gs : List (Equiv.Perm (Fin 2300))) (i : ℕ),
    i < gs.length → (extendTuple gs ds).getD i 1 = gs.getD i 1
  | [], gs, i, _ => rfl
  | w :: ds, gs, i, h => by
    rw [extendTuple_cons, extendTuple_getD_lt ds _ i (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem d1gs_length : d1gs.length = 8 := by
  have h1 : cTuple.length = 2 := cTuple_length
  have h2 : dTuple.length = 2 := dTuple_length
  simp [d1gs, aSeeds, h1, h2]

theorem d1Vals_length : d1Vals.length = 8 + d1SlpA.length := by
  rw [d1Vals, extendTuple_length, d1gs_length]

theorem d1Vals_base {i : ℕ} (hi : i < 8) : d1Vals.getD i 1 = d1gs.getD i 1 :=
  extendTuple_getD_lt _ _ _ (by rw [d1gs_length]; exact hi)

theorem d1_z : d1Vals.getD 2 1 = locZ := by
  rw [d1Vals_base (by norm_num)]
  simp [d1gs, aSeeds, List.getD_eq_getElem?_getD]

theorem d1_t : d1Vals.getD 3 1 = locT := by
  rw [d1Vals_base (by norm_num)]
  simp [d1gs, aSeeds, List.getD_eq_getElem?_getD]

theorem d1_c (j : ℕ) (hj : j < 2) : d1Vals.getD (4 + j) 1 = cTuple.getD j 1 := by
  rw [d1Vals_base (by omega)]
  have h1 : cTuple.length = 2 := cTuple_length
  have hz : (aSeeds ++ [locZ, locT]).length = 4 := by
    rw [List.length_append, aSeeds_length, List.length_cons, List.length_cons, List.length_nil]
  have e : d1gs = (aSeeds ++ [locZ, locT]) ++ (cTuple ++ dTuple) := by
    rw [d1gs, List.append_assoc, List.append_assoc]
  rw [e, List.getD_append_right _ _ _ _ (by omega), hz, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by omega)]

theorem d1_d (j : ℕ) (hj : j < 2) : d1Vals.getD (6 + j) 1 = dTuple.getD j 1 := by
  rw [d1Vals_base (by omega)]
  have h1 : cTuple.length = 2 := cTuple_length
  interval_cases j <;> simp [d1gs, aSeeds, List.getD_eq_getElem?_getD, List.getElem?_append_right, h1]

theorem cTuple_getD_mem (j : ℕ) : cTuple.getD j 1 ∈ locC :=
  getD_one_mem' (fun _ hg => Subgroup.subset_closure hg) j

theorem dTuple_getD_mem (j : ℕ) : dTuple.getD j 1 ∈ locD :=
  getD_one_mem' (fun _ hg => Subgroup.subset_closure hg) j

theorem cTuple_getD_comm (j : ℕ) : cTuple.getD j 1 * locZ = locZ * cTuple.getD j 1 := by
  have h := cTuple_getD_mem j
  rw [locC_eq_centralizer] at h
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h).2

theorem d1_repA : RepTuple 2300 (slpFinal (d1Base ()) d1SlpA) d1Vals := by
  have h := d1_checks
  simp only [d1Check, Bool.and_eq_true, slpOK] at h
  exact slp_repTuple d1_base_rep h.1.1 h.1.2.1.1

theorem d1_stages :
    d1StageOK (slpFinal (d1Base ()) d1SlpA) d1Stage1 = true ∧
      d1StageOK (slpFinal (d1Base ()) d1SlpA) d1Stage2 = true ∧
      d1StageOK (slpFinal (d1Base ()) d1SlpA) d1Stage3 = true := by
  have h := d1_checks
  simp only [d1Check, Bool.and_eq_true] at h
  exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

theorem co2P_le_of_stage {st : D1Stage}
    (hst : d1StageOK (slpFinal (d1Base ()) d1SlpA) st = true)
    (hidx : ∀ i ∈ st.gens, 1 ≤ i ∧ i ≤ d1Vals.length)
    {H : Subgroup (Equiv.Perm (Fin 2300))} (hH : ∀ i ∈ st.gens, d1Vals.getD (i - 1) 1 ∈ H) :
    co2P ≤ H := by
  have hsel := RepTuple_select d1_repA hidx
  have key := slpTargets_sound hsel hst
  have hmem : ∀ g ∈ st.gens.map (fun i => d1Vals.getD (i - 1) 1), g ∈ H := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    exact hH i hi
  have hall := extendTuple_mem H _ st.slp hmem
  have hl0 : 0 < aSeeds.length := by rw [aSeeds_length]; exact Nat.two_pos
  have hl1 : 1 < aSeeds.length := by rw [aSeeds_length]; exact Nat.one_lt_two
  have h0 := key (st.w0, aArrs[0]!) (List.mem_cons.2 (Or.inl rfl)) (aSeeds.getD 0 1)
    (repTuple_a.rep hl0)
  have h1 := key (st.w1, aArrs[1]!) (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
    (aSeeds.getD 1 1) (repTuple_a.rep hl1)
  have e0 : aSeeds.getD 0 1 = co2Gen 0 := List.getD_cons_zero
  have e1 : aSeeds.getD 1 1 = co2Gen 1 := List.getD_cons_succ.trans List.getD_cons_zero
  rw [co2P, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · have := wordValue_mem _ H hall st.w0
    rw [h0, e0] at this
    exact this
  · have := wordValue_mem _ H hall st.w1
    rw [h1, e1] at this
    exact this

theorem conj_cent_mem {h c x : Equiv.Perm (Fin 2300)} (hh : h ∈ co2P) (hc : c ∈ co2P)
    (hcx : c * x = x * c) : h * c * h⁻¹ ∈ co2P ⊓ Subgroup.centralizer {h * x * h⁻¹} := by
  refine Subgroup.mem_inf.2 ⟨co2P.mul_mem (co2P.mul_mem hh hc) (co2P.inv_mem hh),
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc h * c * h⁻¹ * (h * x * h⁻¹) = h * (c * x) * h⁻¹ := by group
    _ = h * (x * c) * h⁻¹ := by rw [hcx]
    _ = h * x * h⁻¹ * (h * c * h⁻¹) := by group

@[expose] def NN (zp fp : Equiv.Perm (Fin 2300)) : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {y | ∃ c ∈ co2P ⊓ Subgroup.centralizer {locT}, y = c * zp * c⁻¹ ∨ y = c * fp * c⁻¹}

theorem d1_eqs :
    d1Vals.getD 9 1 * d1Vals.getD 9 1 = 1 ∧ d1Vals.getD 10 1 * d1Vals.getD 10 1 = 1 ∧
    d1Vals.getD 9 1 * d1Vals.getD 10 1 = d1Vals.getD 10 1 * d1Vals.getD 9 1 ∧
    d1Vals.getD 15 1 * locZ * (d1Vals.getD 15 1)⁻¹ = d1Vals.getD 9 1 ∧
    d1Vals.getD 20 1 * locZ * (d1Vals.getD 20 1)⁻¹ = d1Vals.getD 10 1 ∧
    d1Vals.getD 10 1 = d1Vals.getD 9 1 * locT ∧
    d1Vals.getD 21 1 = d1Vals.getD 15 1 * cTuple.getD 0 1 * (d1Vals.getD 15 1)⁻¹ ∧
    d1Vals.getD 22 1 = d1Vals.getD 15 1 * cTuple.getD 1 1 * (d1Vals.getD 15 1)⁻¹ ∧
    d1Vals.getD 23 1 = d1Vals.getD 20 1 * cTuple.getD 0 1 * (d1Vals.getD 20 1)⁻¹ ∧
    d1Vals.getD 24 1 = d1Vals.getD 20 1 * cTuple.getD 1 1 * (d1Vals.getD 20 1)⁻¹ ∧
    d1Vals.getD 25 1 = dTuple.getD 0 1 * d1Vals.getD 9 1 * (dTuple.getD 0 1)⁻¹ ∧
    d1Vals.getD 26 1 = dTuple.getD 1 1 * d1Vals.getD 9 1 * (dTuple.getD 1 1)⁻¹ ∧
    d1Vals.getD 27 1 = dTuple.getD 0 1 * d1Vals.getD 10 1 * (dTuple.getD 0 1)⁻¹ ∧
    d1Vals.getD 28 1 = dTuple.getD 1 1 * d1Vals.getD 10 1 * (dTuple.getD 1 1)⁻¹ := by
  have E := d1_stageA.1
  have hz := d1_z
  have ht := d1_t
  have hc0 := d1_c 0 (by norm_num)
  have hc1 := d1_c 1 (by norm_num)
  have hd0 := d1_d 0 (by norm_num)
  have hd1 := d1_d 1 (by norm_num)
  simp only [Nat.add_zero] at hc0 hd0
  have e1 := E ([10, 10], []) (by simp [d1EqsA])
  have e2 := E ([11, 11], []) (by simp [d1EqsA])
  have e3 := E ([10, 11], [11, 10]) (by simp [d1EqsA])
  have e4 := E ([16, 3, -16], [10]) (by simp [d1EqsA])
  have e5 := E ([21, 3, -21], [11]) (by simp [d1EqsA])
  have e6 := E ([11], [10, 4]) (by simp [d1EqsA])
  have e7 := E ([22], [16, 5, -16]) (by simp [d1EqsA])
  have e8 := E ([23], [16, 6, -16]) (by simp [d1EqsA])
  have e9 := E ([24], [21, 5, -21]) (by simp [d1EqsA])
  have e10 := E ([25], [21, 6, -21]) (by simp [d1EqsA])
  have e11 := E ([26], [7, 10, -7]) (by simp [d1EqsA])
  have e12 := E ([27], [8, 10, -8]) (by simp [d1EqsA])
  have e13 := E ([28], [7, 11, -7]) (by simp [d1EqsA])
  have e14 := E ([29], [8, 11, -8]) (by simp [d1EqsA])
  simp [wordValue, letterValue] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  simp only [List.getD_eq_getElem?_getD, Nat.reduceAdd] at hz ht hc0 hc1 hd0 hd1
  rw [hz] at e4 e5
  rw [ht] at e6
  rw [hc0] at e7 e9
  rw [hc1] at e8 e10
  rw [hd0] at e11 e13
  rw [hd1] at e12 e14
  simp only [List.getD_eq_getElem?_getD, mul_assoc]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩

theorem d1_ne : d1Vals.getD 9 1 ≠ d1Vals.getD 10 1 := by
  have := d1_stageA.2 ([10], [11]) (by simp [d1NesA])
  simpa [wordValue, letterValue, List.getD_eq_getElem?_getD] using this

theorem cTuple_getD_mem_P (j : ℕ) : cTuple.getD j 1 ∈ co2P := locC_le_P (cTuple_getD_mem j)

theorem dTuple_getD_mem_cent (j : ℕ) : dTuple.getD j 1 ∈ co2P ⊓ Subgroup.centralizer {locT} := by
  have h := dTuple_getD_mem j
  rwa [locD_eq_centralizer] at h

theorem NN_mem_left (zp fp : Equiv.Perm (Fin 2300)) : zp ∈ NN zp fp :=
  Subgroup.subset_closure ⟨1, Subgroup.one_mem _, Or.inl (by simp)⟩

theorem NN_mem_right (zp fp : Equiv.Perm (Fin 2300)) : fp ∈ NN zp fp :=
  Subgroup.subset_closure ⟨1, Subgroup.one_mem _, Or.inr (by simp)⟩

theorem NN_mem_conj_left (zp fp : Equiv.Perm (Fin 2300)) {c : Equiv.Perm (Fin 2300)}
    (hc : c ∈ co2P ⊓ Subgroup.centralizer {locT}) : c * zp * c⁻¹ ∈ NN zp fp :=
  Subgroup.subset_closure ⟨c, hc, Or.inl rfl⟩

theorem NN_mem_conj_right (zp fp : Equiv.Perm (Fin 2300)) {c : Equiv.Perm (Fin 2300)}
    (hc : c ∈ co2P ⊓ Subgroup.centralizer {locT}) : c * fp * c⁻¹ ∈ NN zp fp :=
  Subgroup.subset_closure ⟨c, hc, Or.inr rfl⟩

theorem d1_len : d1Vals.length = 29 := by
  rw [d1Vals_length]
  rfl

theorem d1Stage1_gens : d1Stage1.gens = [22, 23, 24, 25] := rfl

theorem d1Stage2_gens : d1Stage2.gens = [22, 23, 10, 11, 26, 27, 28, 29] := rfl

theorem d1Stage3_gens : d1Stage3.gens = [24, 25, 10, 11, 26, 27, 28, 29] := rfl

theorem d1_ambient :
    ∃ zp fp : Equiv.Perm (Fin 2300), zp ∈ co2P ∧ fp ∈ co2P ∧ zp * zp = 1 ∧ fp * fp = 1 ∧
      zp * fp = fp * zp ∧ zp ≠ fp ∧ zp * fp = locT ∧
      (∃ g ∈ co2P, g * locZ * g⁻¹ = zp) ∧ (∃ g ∈ co2P, g * locZ * g⁻¹ = fp) ∧
      co2P ≤ (co2P ⊓ Subgroup.centralizer {zp}) ⊔ (co2P ⊓ Subgroup.centralizer {fp}) ∧
      co2P ≤ (co2P ⊓ Subgroup.centralizer {zp}) ⊔ NN zp fp ∧
      co2P ≤ (co2P ⊓ Subgroup.centralizer {fp}) ⊔ NN zp fp := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := d1_eqs
  obtain ⟨hs1, hs2, hs3⟩ := d1_stages
  have hcz0 : d1Vals.getD 21 1 ∈ co2P ⊓ Subgroup.centralizer {d1Vals.getD 9 1} := by
    have := conj_cent_mem (d1Vals_mem 15) (cTuple_getD_mem_P 0) (cTuple_getD_comm 0)
    rw [e4] at this
    rwa [e7]
  have hcz1 : d1Vals.getD 22 1 ∈ co2P ⊓ Subgroup.centralizer {d1Vals.getD 9 1} := by
    have := conj_cent_mem (d1Vals_mem 15) (cTuple_getD_mem_P 1) (cTuple_getD_comm 1)
    rw [e4] at this
    rwa [e8]
  have hcf0 : d1Vals.getD 23 1 ∈ co2P ⊓ Subgroup.centralizer {d1Vals.getD 10 1} := by
    have := conj_cent_mem (d1Vals_mem 20) (cTuple_getD_mem_P 0) (cTuple_getD_comm 0)
    rw [e5] at this
    rwa [e9]
  have hcf1 : d1Vals.getD 24 1 ∈ co2P ⊓ Subgroup.centralizer {d1Vals.getD 10 1} := by
    have := conj_cent_mem (d1Vals_mem 20) (cTuple_getD_mem_P 1) (cTuple_getD_comm 1)
    rw [e5] at this
    rwa [e10]
  have hn0 : d1Vals.getD 25 1 ∈ NN (d1Vals.getD 9 1) (d1Vals.getD 10 1) := by
    rw [e11]; exact NN_mem_conj_left _ _ (dTuple_getD_mem_cent 0)
  have hn1 : d1Vals.getD 26 1 ∈ NN (d1Vals.getD 9 1) (d1Vals.getD 10 1) := by
    rw [e12]; exact NN_mem_conj_left _ _ (dTuple_getD_mem_cent 1)
  have hn2 : d1Vals.getD 27 1 ∈ NN (d1Vals.getD 9 1) (d1Vals.getD 10 1) := by
    rw [e13]; exact NN_mem_conj_right _ _ (dTuple_getD_mem_cent 0)
  have hn3 : d1Vals.getD 28 1 ∈ NN (d1Vals.getD 9 1) (d1Vals.getD 10 1) := by
    rw [e14]; exact NN_mem_conj_right _ _ (dTuple_getD_mem_cent 1)
  refine ⟨d1Vals.getD 9 1, d1Vals.getD 10 1, d1Vals_mem 9, d1Vals_mem 10, e1, e2, e3, d1_ne, ?_,
    ⟨_, d1Vals_mem 15, e4⟩, ⟨_, d1Vals_mem 20, e5⟩, ?_, ?_, ?_⟩
  · rw [e6, ← mul_assoc, e1, one_mul]
  · refine co2P_le_of_stage hs1 (fun i hi => ?_) (fun i hi => ?_)
    · rw [d1Stage1_gens] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [d1_len]
    · rw [d1Stage1_gens] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact Subgroup.mem_sup_left hcz0
      · exact Subgroup.mem_sup_left hcz1
      · exact Subgroup.mem_sup_right hcf0
      · exact Subgroup.mem_sup_right hcf1
  · refine co2P_le_of_stage hs2 (fun i hi => ?_) (fun i hi => ?_)
    · rw [d1Stage2_gens] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [d1_len]
    · rw [d1Stage2_gens] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Subgroup.mem_sup_left hcz0
      · exact Subgroup.mem_sup_left hcz1
      · exact Subgroup.mem_sup_right (NN_mem_left _ _)
      · exact Subgroup.mem_sup_right (NN_mem_right _ _)
      · exact Subgroup.mem_sup_right hn0
      · exact Subgroup.mem_sup_right hn1
      · exact Subgroup.mem_sup_right hn2
      · exact Subgroup.mem_sup_right hn3
  · refine co2P_le_of_stage hs3 (fun i hi => ?_) (fun i hi => ?_)
    · rw [d1Stage3_gens] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [d1_len]
    · rw [d1Stage3_gens] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Subgroup.mem_sup_left hcf0
      · exact Subgroup.mem_sup_left hcf1
      · exact Subgroup.mem_sup_right (NN_mem_left _ _)
      · exact Subgroup.mem_sup_right (NN_mem_right _ _)
      · exact Subgroup.mem_sup_right hn0
      · exact Subgroup.mem_sup_right hn1
      · exact Subgroup.mem_sup_right hn2
      · exact Subgroup.mem_sup_right hn3

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
