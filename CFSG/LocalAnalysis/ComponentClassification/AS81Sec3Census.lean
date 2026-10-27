
module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusBase
import all CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusBase

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusCert
import all CFSG.Fischer.F4

public section

namespace CFSG.ComponentClassification.AS81.Census

open CFSG.Fischer CFSG.PSL3Four.Native QuadraticMap CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

section Facts

theorem check_parts :
    matsOK = true ∧ lOK = true ∧ formsOK = true ∧ m1OK = true ∧ goodOK = true ∧
      badOK = true := by
  have h := census_check
  simp only [censusCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem mats_parts :
    ((isomOK x0M = true ∧ f2Mat x0M = true) ∧ (isomOK tauM = true ∧ f2Mat tauM = true) ∧
      (isomOK cM = true ∧ f2Mat cM = true) ∧ (isomOK b3M = true ∧ f2Mat b3M = true) ∧
      (isomOK b5M = true ∧ f2Mat b5M = true) ∧ (isomOK g1M = true ∧ f2Mat g1M = true) ∧
      (isomOK g2M = true ∧ f2Mat g2M = true) ∧ (isomOK g1iM = true ∧ f2Mat g1iM = true) ∧
      (isomOK g2iM = true ∧ f2Mat g2iM = true)) ∧
    matMul g1M g1iM = idMat ∧ matMul g2M g2iM = idMat ∧ matMul cM x0M = matMul x0M cM ∧
    matMul tauM tauM = idMat ∧ rootsM.size = 20 ∧ (rootsM[0]!).1 = idMat ∧
    ∀ j < 20, isomOK (rootsM[j]!).1 = true ∧ isomOK (rootsM[j]!).2 = true ∧
      matMul (rootsM[j]!).1 (rootsM[j]!).2 = idMat := by
  have h := check_parts.1
  simp only [matsOK, Bool.and_eq_true, List.all_cons, List.all_nil, beq_iff_eq,
    allBelow_eq_true, Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩, hH⟩ := h
  exact ⟨hA, hB, hC, hD, hE, hF, hG, fun j hj => ⟨(hH j hj).1.1, (hH j hj).1.2, (hH j hj).2⟩⟩

theorem isom_x0 : isomOK x0M = true := mats_parts.1.1.1
theorem f2_x0 : f2Mat x0M = true := mats_parts.1.1.2
theorem isom_tau : isomOK tauM = true := mats_parts.1.2.1.1
theorem f2_tau : f2Mat tauM = true := mats_parts.1.2.1.2
theorem isom_c : isomOK cM = true := mats_parts.1.2.2.1.1
theorem f2_c : f2Mat cM = true := mats_parts.1.2.2.1.2
theorem isom_b3 : isomOK b3M = true := mats_parts.1.2.2.2.1.1
theorem f2_b3 : f2Mat b3M = true := mats_parts.1.2.2.2.1.2
theorem isom_b5 : isomOK b5M = true := mats_parts.1.2.2.2.2.1.1
theorem f2_b5 : f2Mat b5M = true := mats_parts.1.2.2.2.2.1.2
theorem isom_g1 : isomOK g1M = true := mats_parts.1.2.2.2.2.2.1.1
theorem f2_g1 : f2Mat g1M = true := mats_parts.1.2.2.2.2.2.1.2
theorem isom_g2 : isomOK g2M = true := mats_parts.1.2.2.2.2.2.2.1.1
theorem f2_g2 : f2Mat g2M = true := mats_parts.1.2.2.2.2.2.2.1.2

theorem isom_root {j : ℕ} (hj : j < 20) : isomOK (rootsM[j]!).1 = true :=
  (mats_parts.2.2.2.2.2.2.2 j hj).1

@[expose] noncomputable def X0 : OV := ofArr x0M isom_x0

@[expose] noncomputable def Tau : OV := ofArr tauM isom_tau

@[expose] noncomputable def Cc : OV := ofArr cM isom_c

@[expose] noncomputable def B3 : OV := ofArr b3M isom_b3

@[expose] noncomputable def B5 : OV := ofArr b5M isom_b5

@[expose] noncomputable def G1 : OV := ofArr g1M isom_g1

@[expose] noncomputable def G2 : OV := ofArr g2M isom_g2

@[expose] noncomputable def Root (j : ℕ) (hj : j < 20) : OV :=
  ofArr (rootsM[j]!).1 (isom_root hj)

@[expose] noncomputable def Lc : Subgroup OV := Subgroup.closure {G1, G2}

theorem G1_mem_stab : G1 ∈ MulAction.stabilizer OV N0 := mem_stab_of_f2 isom_g1 f2_g1
theorem G2_mem_stab : G2 ∈ MulAction.stabilizer OV N0 := mem_stab_of_f2 isom_g2 f2_g2
theorem Tau_mem_stab : Tau ∈ MulAction.stabilizer OV N0 := mem_stab_of_f2 isom_tau f2_tau
theorem Cc_mem_stab : Cc ∈ MulAction.stabilizer OV N0 := mem_stab_of_f2 isom_c f2_c

theorem Lc_le_stab : Lc ≤ MulAction.stabilizer OV N0 := by
  rw [Lc, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact G1_mem_stab
  · exact G2_mem_stab

@[expose] noncomputable def Ls : Subgroup (MulAction.stabilizer OV N0) :=
  Subgroup.closure {⟨G1, G1_mem_stab⟩, ⟨G2, G2_mem_stab⟩}

theorem map_Ls : Ls.map (MulAction.stabilizer OV N0).subtype = Lc := by
  rw [Ls, MonoidHom.map_closure, Lc]
  congr 1
  ext g
  simp

theorem enumerates_L :
    Enumerates (Ls.map sigma) lEnum.tabs.toList := by
  have hl := check_parts.2.1
  simp only [lOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hl
  rw [Ls, MonoidHom.map_closure]
  refine enumerates_closure (gens := #[f2perm g1M, f2perm g2M]) ?_ ?_ hl.1.1.1
  · rintro _ ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨0, by decide, tabRep_f2perm isom_g1 f2_g1⟩
    · exact ⟨1, by decide, tabRep_f2perm isom_g2 f2_g2⟩
  · intro j hj
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨_, ⟨_, Or.inl rfl, rfl⟩, tabRep_f2perm isom_g1 f2_g1⟩
    · exact ⟨_, ⟨_, Or.inr rfl, rfl⟩, tabRep_f2perm isom_g2 f2_g2⟩

theorem card_L_map : Nat.card (Ls.map sigma) = 20160 := by
  rw [enumerates_L.card, Array.length_toList]
  have hl := check_parts.2.1
  simp only [lOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hl
  exact hl.1.1.2

theorem card_Lc : 20160 ≤ Nat.card Lc := by
  rw [← card_L_map, ← map_Ls,
    Subgroup.card_map_of_injective (MulAction.stabilizer OV N0).subtype_injective]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd Ls sigma)

theorem l_parts :
    lEnum.tabs.contains (f2perm tauM) = false ∧ lEnum.tabs.contains (f2perm cM) = false := by
  have hl := check_parts.2.1
  simp only [lOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hl
  exact ⟨hl.1.2, hl.2⟩

theorem not_mem_Lc {M : Array ℕ} (h : isomOK M = true) (hM : f2Mat M = true)
    (hn : lEnum.tabs.contains (f2perm M) = false) : ofArr M h ∉ Lc := by
  intro hL
  rw [← map_Ls] at hL
  obtain ⟨g, hg, hge⟩ := hL
  have hg' : g = ⟨ofArr M h, mem_stab_of_f2 h hM⟩ := Subtype.ext hge
  subst hg'
  obtain ⟨t, ht, hrep⟩ := enumerates_L.complete _ ⟨_, hg, rfl⟩
  have he := hrep.tab_eq (tabRep_f2perm h hM)
  subst he
  have hmem : (f2perm M) ∈ lEnum.tabs := Array.mem_toList_iff.mp ht
  have := Array.contains_iff_mem.mpr hmem
  rw [hn] at this
  exact Bool.false_ne_true this

theorem Tau_not_mem : Tau ∉ Lc := not_mem_Lc isom_tau f2_tau l_parts.1

theorem Cc_not_mem : Cc ∉ Lc := not_mem_Lc isom_c f2_c l_parts.2

theorem forms_parts : orbits.size = 20 ∧
    (∀ j < 20, treeOK orbitStep 2 (rootForm j) orbits[j]! = true) ∧
    (List.range 20).foldl (fun s j => s + (orbits[j]!).tabs.size) 0 = 48960 ∧
    ∀ j < 20, ∀ i < (orbits[j]!).tabs.size, formIndex.get? (orbits[j]!).tabs[i]! = some j := by
  have hf := check_parts.2.2.1
  simp only [formsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Array.all_eq_true] at hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hf
  refine ⟨h1, h2, h3, fun j hj i hi => ?_⟩
  rw [getElem!_pos (orbits[j]!).tabs i hi]
  exact h4 j hj i hi

theorem rep_root {j : ℕ} (hj : j < 20) : Rep (rootForm j) (Root j hj • N0) :=
  rep_smul rep_n0 (isom_root hj)

theorem orbitStep_rep (k : ℕ) {t : Tab} {φ : Set V₀} (ht : Rep t φ) :
    Rep (orbitStep k t) ((if k = 0 then G1 else G2) • φ) := by
  unfold Census.orbitStep
  split_ifs
  · rw [g1T, formStepT_actTab ht]
    exact rep_smul ht isom_g1
  · rw [g2T, formStepT_actTab ht]
    exact rep_smul ht isom_g2

theorem rep_orbit {j : ℕ} (hj : j < 20) {i : ℕ} (hi : i < (orbits[j]!).tabs.size) :
    ∃ l ∈ Lc, Rep (orbits[j]!).tabs[i]! ((l * Root j hj) • N0) := by
  obtain ⟨φ, ⟨l, hl, rfl⟩, hrep⟩ := tree_rep (forms_parts.2.1 j hj)
    (f := fun k φ => (if k = 0 then G1 else G2) • φ) (fun k _ t φ ht => orbitStep_rep k ht)
    (rep_root hj) (fun φ => ∃ l ∈ Lc, φ = (l * Root j hj) • N0) ⟨1, one_mem _, by rw [one_mul]⟩
    (fun k _ φ ⟨l, hl, hφ⟩ => ⟨(if k = 0 then G1 else G2) * l, mul_mem (by
        split_ifs
        · exact Subgroup.subset_closure (Or.inl rfl)
        · exact Subgroup.subset_closure (Or.inr rfl)) hl,
      by rw [hφ, ← mul_smul, mul_assoc]⟩) i hi
  exact ⟨l, hl, hrep⟩

theorem tabs_inj {j j' : ℕ} (hj : j < 20) (hj' : j' < 20) {i i' : ℕ}
    (hi : i < (orbits[j]!).tabs.size) (hi' : i' < (orbits[j']!).tabs.size)
    (h : (orbits[j]!).tabs[i]! = (orbits[j']!).tabs[i']!) : j = j' ∧ i = i' := by
  have h1 := forms_parts.2.2.2 j hj i hi
  have h2 := forms_parts.2.2.2 j' hj' i' hi'
  rw [h, h2] at h1
  have hjj : j = j' := (Option.some_injective _ h1).symm
  subst hjj
  refine ⟨rfl, ?_⟩
  obtain ⟨-, -, hnd, -, -⟩ := treeOK_spec (forms_parts.2.1 j hj)
  rw [List.nodup_iff_injective_getElem] at hnd
  rw [getElem!_pos (orbits[j]!).tabs i hi, getElem!_pos (orbits[j]!).tabs i' hi'] at h
  have := @hnd ⟨i, by simpa using hi⟩ ⟨i', by simpa using hi'⟩ (by simpa using h)
  simpa using this

theorem card_Pos : Nat.card Pos = 48960 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← forms_parts.2.2.1, foldl_range_sum, Finset.sum_range]

@[expose] noncomputable def formAt (p : Pos) : MulAction.orbit OV N0 :=
  ⟨((rep_orbit p.1.isLt p.2.isLt).choose * Root p.1 p.1.isLt) • N0, ⟨_, rfl⟩⟩

theorem rep_formAt (p : Pos) : Rep (orbits[p.1.val]!).tabs[p.2.val]! (formAt p : Set V₀) :=
  (rep_orbit p.1.isLt p.2.isLt).choose_spec.2

theorem formAt_injective : Function.Injective formAt := by
  intro p q hpq
  have hp := rep_formAt p
  have hq := rep_formAt q
  rw [hpq] at hp
  have he := hp.tab_eq hq
  obtain ⟨h1, h2⟩ := tabs_inj p.1.isLt q.1.isLt p.2.isLt q.2.isLt he
  obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := p
  obtain ⟨⟨j', hj'⟩, ⟨i', hi'⟩⟩ := q
  simp only at h1 h2
  subst h1
  subst h2
  rfl

@[expose] noncomputable def lPair : Lc ⊕ Lc → MulAction.stabilizer OV N0 :=
  Sum.elim (fun l => ⟨l, Lc_le_stab l.2⟩)
    (fun l => ⟨l * Tau, mul_mem (Lc_le_stab l.2) Tau_mem_stab⟩)

theorem lPair_injective : Function.Injective lPair := by
  rintro (a | a) (b | b) h
  · have h' : (a : OV) = b := congrArg (fun x : MulAction.stabilizer OV N0 => (x : OV)) h
    exact congrArg Sum.inl (Subtype.ext h')
  · exfalso
    have h' : (a : OV) = b * Tau := congrArg Subtype.val h
    apply Tau_not_mem
    have e : Tau = (b : OV)⁻¹ * a := by rw [h']; group
    rw [e]
    exact mul_mem (inv_mem b.2) a.2
  · exfalso
    have h' : (a : OV) * Tau = b := congrArg Subtype.val h
    apply Tau_not_mem
    have e : Tau = (a : OV)⁻¹ * b := by rw [← h']; group
    rw [e]
    exact mul_mem (inv_mem a.2) b.2
  · have h' : (a : OV) * Tau = b * Tau := congrArg Subtype.val h
    exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h'))

theorem card_orbit_stab : Nat.card (MulAction.orbit OV N0) = 48960 ∧
    Nat.card (MulAction.stabilizer OV N0) = 40320 := by
  have h1 : 48960 ≤ Nat.card (MulAction.orbit OV N0) :=
    card_Pos ▸ Nat.card_le_card_of_injective formAt formAt_injective
  have h2 : 40320 ≤ Nat.card (MulAction.stabilizer OV N0) := by
    have := Nat.card_le_card_of_injective lPair lPair_injective
    rw [Nat.card_sum] at this
    have := card_Lc
    omega
  have h3 := card_orbit_mul
  constructor <;> nlinarith

theorem exists_rep_of_orbit (g : OV) :
    ∃ p : Pos, Rep (orbits[p.1.val]!).tabs[p.2.val]! (g • N0) := by
  have hbij := formAt_injective.bijective_of_nat_card_le (by rw [card_orbit_stab.1, card_Pos])
  obtain ⟨p, hp⟩ := hbij.2 ⟨g • N0, ⟨g, rfl⟩⟩
  refine ⟨p, ?_⟩
  have h := rep_formAt p
  rw [hp] at h
  exact h

theorem mem_or_of_stab {s : OV} (hs : s ∈ MulAction.stabilizer OV N0) :
    s ∈ Lc ∨ ∃ l ∈ Lc, s = l * Tau := by
  have hbij := lPair_injective.bijective_of_nat_card_le (by
    rw [card_orbit_stab.2, Nat.card_sum]
    have h2 : Nat.card (Lc ⊕ Lc) ≤ Nat.card (MulAction.stabilizer OV N0) :=
      Nat.card_le_card_of_injective lPair lPair_injective
    rw [Nat.card_sum, card_orbit_stab.2] at h2
    have := card_Lc
    omega)
  obtain ⟨x, hx⟩ := hbij.2 ⟨s, hs⟩
  rcases x with l | l
  · left
    have : (l : OV) = s := congrArg Subtype.val hx
    rw [← this]
    exact l.2
  · right
    have : (l : OV) * Tau = s := congrArg Subtype.val hx
    exact ⟨l, l.2, this.symm⟩

theorem Tau_mul_Tau : Tau * Tau = 1 := ofArr_mul_eq_one isom_tau isom_tau mats_parts.2.2.2.2.1

theorem Tau_inv : Tau⁻¹ = Tau := inv_eq_of_mul_eq_one_right Tau_mul_Tau

theorem Cc_comm : Cc * X0 = X0 * Cc := ofArr_comm isom_c isom_x0 mats_parts.2.2.2.1

theorem root_zero : Root 0 (by norm_num) = 1 := ofArr_eq_one _ mats_parts.2.2.2.2.2.2.1

theorem conj_Tau_mem {l : OV} (hl : l ∈ Lc) : Tau⁻¹ * l * Tau ∈ Lc := by
  have hs : Tau⁻¹ * l * Tau ∈ MulAction.stabilizer OV N0 :=
    mul_mem (mul_mem (inv_mem Tau_mem_stab) (Lc_le_stab hl)) Tau_mem_stab
  rcases mem_or_of_stab hs with h | ⟨l', hl', h⟩
  · exact h
  · exfalso
    apply Tau_not_mem
    have h2 : l = Tau * l' := by
      calc l = Tau * (Tau⁻¹ * l * Tau) * Tau⁻¹ := by group
        _ = Tau * (l' * Tau) * Tau⁻¹ := by rw [h]
        _ = Tau * l' := by group
    have e : Tau = l * l'⁻¹ := by rw [h2]; group
    rw [e]
    exact mul_mem hl (inv_mem hl')

theorem exists_Lc_conj {m : OV} (hm : m ∈ MulAction.stabilizer OV N0) :
    ∃ m' ∈ Lc, m'⁻¹ * X0 * m' = m⁻¹ * X0 * m := by
  rcases mem_or_of_stab hm with h | ⟨l', hl', h⟩
  · exact ⟨m, h, rfl⟩
  · obtain ⟨l₀, hl₀, hc⟩ := (mem_or_of_stab Cc_mem_stab).resolve_left Cc_not_mem
    refine ⟨Cc * m, ?_, ?_⟩
    · rw [hc, h]
      have e : l₀ * Tau * (l' * Tau) = l₀ * (Tau⁻¹ * l' * Tau) := by
        rw [Tau_inv]
        group
      rw [e]
      exact mul_mem hl₀ (conj_Tau_mem hl')
    · have hcx : Cc⁻¹ * X0 * Cc = X0 := by rw [mul_assoc, ← Cc_comm]; group
      calc (Cc * m)⁻¹ * X0 * (Cc * m) = m⁻¹ * (Cc⁻¹ * X0 * Cc) * m := by group
        _ = m⁻¹ * X0 * m := by rw [hcx]

theorem good_parts {j : ℕ} (hgood : j ∈ goodOrbits) :
    ∃ y l : Array ℕ, j < 20 ∧ formStep x0M (rootForm j) = rootForm j ∧ isomOK y = true ∧
      isomOK l = true ∧ f2Mat l = true ∧ matMul x0M l = matMul l y ∧
      matMul (rootsM[j]!).1 y = matMul x0M (rootsM[j]!).1 := by
  have hg := check_parts.2.2.2.2.1
  simp only [goodOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hg
  obtain ⟨hmap, hall⟩ := hg
  rw [← hmap, List.mem_map] at hgood
  obtain ⟨⟨j', y, l⟩, hmem, rfl⟩ := hgood
  have h := hall _ hmem
  simp only [decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hj, hfix⟩, hy⟩, -⟩, hl⟩, hlf⟩, hxl⟩, hry⟩ := h
  exact ⟨y, l, hj, hfix, hy, hl, hlf, hxl, hry⟩

theorem root_mem_tabs {j : ℕ} (hj : j < 20) :
    0 < (orbits[j]!).tabs.size ∧ (orbits[j]!).tabs[0]! = rootForm j := by
  obtain ⟨hpos, h0, -, -, -⟩ := treeOK_spec (forms_parts.2.1 j hj)
  exact ⟨hpos, h0⟩

theorem root_ne {j : ℕ} (hj : j < 20) (hj0 : j ≠ 0) : Root j hj • N0 ≠ N0 := by
  intro h
  have h1 := rep_root hj
  rw [h] at h1
  have h2 := rep_root (j := 0) (by norm_num)
  rw [root_zero, one_smul] at h2
  have he := h1.tab_eq h2
  obtain ⟨hp, hr⟩ := root_mem_tabs hj
  obtain ⟨hp0, hr0⟩ := root_mem_tabs (j := 0) (by norm_num)
  rw [← hr, ← hr0] at he
  exact hj0 (tabs_inj hj (by norm_num) hp hp0 he).1

theorem good_stab (H : Subgroup OV) (hL : Lc ≤ H) (hx : ∀ h ∈ H, h * X0 = X0 * h → h • N0 = N0)
    {j : ℕ} (hgood : j ∈ goodOrbits) (hj : j < 20) {k : OV} (hk : k ∈ H)
    (hkN : k • N0 = Root j hj • N0) : k • N0 = N0 := by
  obtain ⟨y, l, -, -, hy, hl, hlf, hxl, hry⟩ := good_parts hgood
  set Y := ofArr y hy with hYdef
  set Lj := ofArr l hl with hLjdef
  have hLjS : Lj ∈ MulAction.stabilizer OV N0 := mem_stab_of_f2 hl hlf
  have hXL : X0 * Lj = Lj * Y := ofArr_mul_eq_mul isom_x0 hl hl hy hxl
  have hRY : Root j hj * Y = X0 * Root j hj :=
    ofArr_mul_eq_mul (isom_root hj) hy isom_x0 (isom_root hj) hry
  have hs : (Root j hj)⁻¹ * k ∈ MulAction.stabilizer OV N0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hkN, ← mul_smul, inv_mul_cancel, one_smul]
  set m := Lj * ((Root j hj)⁻¹ * k) with hmdef
  have hm : m ∈ MulAction.stabilizer OV N0 := mul_mem hLjS hs
  obtain ⟨m', hm', hconj⟩ := exists_Lc_conj hm
  have hY : Y = (Root j hj)⁻¹ * X0 * Root j hj := by
    rw [mul_assoc, ← hRY]
    group
  have hY' : Y = Lj⁻¹ * X0 * Lj := by
    rw [mul_assoc, hXL]
    group
  have hk1 : k⁻¹ * X0 * k = m⁻¹ * X0 * m := by
    calc k⁻¹ * X0 * k = ((Root j hj)⁻¹ * k)⁻¹ * ((Root j hj)⁻¹ * X0 * Root j hj) *
          ((Root j hj)⁻¹ * k) := by group
      _ = ((Root j hj)⁻¹ * k)⁻¹ * (Lj⁻¹ * X0 * Lj) * ((Root j hj)⁻¹ * k) := by rw [← hY, hY']
      _ = m⁻¹ * X0 * m := by rw [hmdef]; group
  have hn : k * m'⁻¹ ∈ H := mul_mem hk (inv_mem (hL hm'))
  have hn1 : (k * m'⁻¹)⁻¹ * X0 * (k * m'⁻¹) = X0 := by
    calc (k * m'⁻¹)⁻¹ * X0 * (k * m'⁻¹) = m' * (k⁻¹ * X0 * k) * m'⁻¹ := by group
      _ = m' * (m'⁻¹ * X0 * m') * m'⁻¹ := by rw [hk1, hconj]
      _ = X0 := by group
  have hnx : (k * m'⁻¹) * X0 = X0 * (k * m'⁻¹) := by
    calc (k * m'⁻¹) * X0 = (k * m'⁻¹) * ((k * m'⁻¹)⁻¹ * X0 * (k * m'⁻¹)) := by rw [hn1]
      _ = X0 * (k * m'⁻¹) := by group
  have hnN := hx _ hn hnx
  have hm'N : m' • N0 = N0 := Lc_le_stab hm'
  calc k • N0 = (k * m'⁻¹) • (m' • N0) := by rw [← mul_smul, inv_mul_cancel_right]
    _ = N0 := by rw [hm'N, hnN]

theorem bad_parts {j : ℕ} (hj : j < 20) (hj0 : j ≠ 0) (hgood : j ∉ goodOrbits) {e : ℕ}
    (he : e < 2) : ∃ w : List ℕ, (∀ x ∈ w, x < 4) ∧
      matMul (if e = 0 then (rootsM[j]!).1 else matMul (rootsM[j]!).1 tauM)
        (if e = 0 then (rootsM[j]!).2 else matMul tauM (rootsM[j]!).2) = idMat ∧
      ∃ j' ∈ goodOrbits, formStep (wordMat #[g1M, g2M,
          if e = 0 then (rootsM[j]!).1 else matMul (rootsM[j]!).1 tauM,
          if e = 0 then (rootsM[j]!).2 else matMul tauM (rootsM[j]!).2] w) n0Tab ∈
        (orbits[j']!).tabs := by
  have hb := check_parts.2.2.2.2.2
  simp only [badOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, List.mem_range, decide_eq_true_eq] at hb
  obtain ⟨hcov, hall⟩ := hb
  rcases hcov j hj with (h0 | hg) | hc
  · exact absurd h0 hj0
  · exact absurd (by simpa using hg) hgood
  obtain ⟨⟨j', e', w⟩, hmem, hje⟩ := hc e he
  obtain ⟨rfl, rfl⟩ := hje
  have h := hall _ hmem
  simp only [Array.contains_iff_mem] at h
  obtain ⟨⟨⟨-, -⟩, hw⟩, hinv, j'', hj'', ht⟩ := h
  exact ⟨w, hw, hinv, j'', hj'', ht⟩

theorem census (H : Subgroup OV) (hg1 : G1 ∈ H) (hg2 : G2 ∈ H)
    (hx : ∀ h ∈ H, h * X0 = X0 * h → h • N0 = N0) {h : OV} (hh : h ∈ H) : h • N0 = N0 := by
  have hL : Lc ≤ H := (Subgroup.closure_le H).mpr (by rintro _ (rfl | rfl) <;> assumption)
  have hgoodN : ∀ k ∈ H, ∀ j' (hj' : j' < 20) (i' : ℕ) (hi' : i' < (orbits[j']!).tabs.size),
      j' ∈ goodOrbits → Rep (orbits[j']!).tabs[i']! (k • N0) → k • N0 = N0 := by
    intro k hk j' hj' i' hi' hg hrep
    obtain ⟨l, hl, hrepl⟩ := rep_orbit hj' hi'
    have heq : k • N0 = (l * Root j' hj') • N0 := hrep.set_eq hrepl
    have hk' : (l⁻¹ * k) • N0 = Root j' hj' • N0 := by
      rw [mul_smul, heq, ← mul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 := good_stab H hL hx hg hj' (mul_mem (inv_mem (hL hl)) hk) hk'
    calc k • N0 = l • ((l⁻¹ * k) • N0) := by rw [← mul_smul, mul_inv_cancel_left]
      _ = N0 := by rw [h1]; exact Lc_le_stab hl
  obtain ⟨p, hp⟩ := exists_rep_of_orbit h
  obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := p
  obtain ⟨l, hl, hrep⟩ := rep_orbit hj hi
  have heq : h • N0 = (l * Root j hj) • N0 := hp.set_eq hrep
  have hkH : l⁻¹ * h ∈ H := mul_mem (inv_mem (hL hl)) hh
  have hkN : (l⁻¹ * h) • N0 = Root j hj • N0 := by
    rw [mul_smul, heq, ← mul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
  suffices hk0 : (l⁻¹ * h) • N0 = N0 by
    calc h • N0 = l • ((l⁻¹ * h) • N0) := by rw [← mul_smul, mul_inv_cancel_left]
      _ = N0 := by rw [hk0]; exact Lc_le_stab hl
  by_cases hj0 : j = 0
  · subst hj0
    rw [hkN, root_zero, one_smul]
  by_cases hg : j ∈ goodOrbits
  · obtain ⟨hpos, h0⟩ := root_mem_tabs hj
    refine good_stab H hL hx hg hj hkH hkN
  exfalso
  have hs : (Root j hj)⁻¹ * (l⁻¹ * h) ∈ MulAction.stabilizer OV N0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hkN, ← mul_smul, inv_mul_cancel, one_smul]
  obtain ⟨e, he, E, hEH, hEact⟩ : ∃ e < 2, ∃ E ∈ H, ∀ v, ((E : OV) : V₀ ≃ₗ[F4] V₀) v =
      toLin (if e = 0 then (rootsM[j]!).1 else matMul (rootsM[j]!).1 tauM) v := by
    rcases mem_or_of_stab hs with hsL | ⟨l', hl', hsl⟩
    · refine ⟨0, by norm_num, Root j hj, ?_, fun v => rfl⟩
      have e1 : Root j hj = (l⁻¹ * h) * ((Root j hj)⁻¹ * (l⁻¹ * h))⁻¹ := by group
      rw [e1]
      exact mul_mem hkH (inv_mem (hL hsL))
    · refine ⟨1, by norm_num, Root j hj * Tau, ?_, fun v => ?_⟩
      · have e1 : Root j hj * Tau = (l⁻¹ * h) * (Tau⁻¹ * l'⁻¹ * Tau) := by
          have e2 : Root j hj = (l⁻¹ * h) * ((Root j hj)⁻¹ * (l⁻¹ * h))⁻¹ := by group
          rw [hsl] at e2
          rw [e2]
          group
        rw [e1]
        exact mul_mem hkH (hL (conj_Tau_mem (inv_mem hl')))
      · simp only [one_ne_zero, ↓reduceIte, toLin_matMul, LinearMap.comp_apply]
        rfl
  obtain ⟨w, hw, hinv, j', hj'g, ht⟩ := bad_parts hj hj0 hg he
  set hM := if e = 0 then (rootsM[j]!).1 else matMul (rootsM[j]!).1 tauM with hhM
  set hiM := if e = 0 then (rootsM[j]!).2 else matMul tauM (rootsM[j]!).2 with hhiM
  have hEinv : ∀ v, ((E⁻¹ : OV) : V₀ ≃ₗ[F4] V₀) v = toLin hiM v := by
    intro v
    have h1 : ((E : OV) : V₀ ≃ₗ[F4] V₀) (toLin hiM v) = v := by
      rw [hEact, ← LinearMap.comp_apply, ← toLin_matMul, hinv, toLin_idMat, LinearMap.id_apply]
    have h2 : ((E⁻¹ : OV) : V₀ ≃ₗ[F4] V₀) (((E : OV) : V₀ ≃ₗ[F4] V₀) (toLin hiM v)) =
        toLin hiM v := by
      change ((E⁻¹ * E : OV) : V₀ ≃ₗ[F4] V₀) (toLin hiM v) = toLin hiM v
      rw [inv_mul_cancel]
      rfl
    rw [h1] at h2
    exact h2
  let a : ℕ → OV := fun x => if x = 0 then G1 else if x = 1 then G2 else if x = 2 then E else E⁻¹
  have ha : ∀ x < 4, a x ∈ H := by
    intro x hx4
    simp only [a]
    split_ifs
    · exact hg1
    · exact hg2
    · exact hEH
    · exact inv_mem hEH
  have hact : ∀ x < 4, ∀ v, ((a x : OV) : V₀ ≃ₗ[F4] V₀) v =
      toLin (#[g1M, g2M, hM, hiM] : Array (Array ℕ))[x]! v := by
    intro x hx4 v
    interval_cases x
    · rfl
    · rfl
    · exact hEact v
    · exact hEinv v
  set W := w.foldl (fun r x => r * a x) 1 with hWdef
  have hWH : W ∈ H := foldl_mul_mem a ha w hw 1 (one_mem _)
  have hWact : ∀ v, ((W : OV) : V₀ ≃ₗ[F4] V₀) v = toLin (wordMat #[g1M, g2M, hM, hiM] w) v :=
    foldl_mul_apply a _ hact w hw 1 idMat (fun v => by rw [toLin_idMat]; rfl)
  have hWinj : Function.Injective (toLin (wordMat #[g1M, g2M, hM, hiM] w)) := by
    intro u v huv
    rw [← hWact, ← hWact] at huv
    exact (W : V₀ ≃ₗ[F4] V₀).injective huv
  have hrepW : Rep (formStep (wordMat #[g1M, g2M, hM, hiM] w) n0Tab) (W • N0) := by
    have h1 := rep_formStep rep_n0 hWinj
    rw [smul_N0_eq, show (fun v => ((W : OV) : V₀ ≃ₗ[F4] V₀) v) =
      ⇑(toLin (wordMat #[g1M, g2M, hM, hiM] w)) from funext hWact]
    exact h1
  have hj'20 : j' < 20 := by
    simp only [goodOrbits, List.mem_cons, List.mem_nil_iff, or_false] at hj'g
    omega
  obtain ⟨i', hi', hti⟩ := exists_getElem!_of_mem (Array.mem_toList_iff.mpr ht)
  rw [← hti] at hrepW
  have hWN := hgoodN W hWH j' hj'20 i' hi' hj'g hrepW
  have hj'0 : j' ≠ 0 := by
    simp only [goodOrbits, List.mem_cons, List.mem_nil_iff, or_false] at hj'g
    omega
  obtain ⟨l'', hl'', hrepl⟩ := rep_orbit hj'20 hi'
  have heq' : W • N0 = (l'' * Root j' hj'20) • N0 := hrepW.set_eq hrepl
  apply root_ne hj'20 hj'0
  have h2 : l''⁻¹ • N0 = N0 := Lc_le_stab (inv_mem hl'')
  calc Root j' hj'20 • N0 = l''⁻¹ • ((l'' * Root j' hj'20) • N0) := by
        rw [← mul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = N0 := by rw [← heq', hWN, h2]

theorem eq_of_fixed_b {g : OV} (h3 : B3 • (g • N0) = g • N0) (h5 : B5 • (g • N0) = g • N0) :
    g • N0 = N0 := by
  obtain ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩, hp⟩ := exists_rep_of_orbit g
  have hp' : Rep (orbits[j]!).tabs[i]! (g • N0) := hp
  have h3' : formStepT b3T (orbits[j]!).tabs[i]! = (orbits[j]!).tabs[i]! := by
    rw [b3T, formStepT_actTab hp']
    have h := rep_smul hp' isom_b3
    rw [show ofArr b3M isom_b3 = B3 from rfl, h3] at h
    exact h.tab_eq hp'
  have h5' : formStepT b5T (orbits[j]!).tabs[i]! = (orbits[j]!).tabs[i]! := by
    rw [b5T, formStepT_actTab hp']
    have h := rep_smul hp' isom_b5
    rw [show ofArr b5M isom_b5 = B5 from rfl, h5] at h
    exact h.tab_eq hp'
  have hm := check_parts.2.2.2.1
  simp only [m1OK, allBelow_eq_true, Array.all_eq_true] at hm
  have h := hm j hj i hi
  rw [← getElem!_pos (orbits[j]!).tabs i hi, h3', h5'] at h
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact hp'.set_eq (h ▸ rep_n0)

end Facts

end CFSG.ComponentClassification.AS81.Census
