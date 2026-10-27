module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Fib
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Census
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClassesBase

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8E

open Subgroup CFSG.ComponentClassification.RankTwoClassical.ExcO8
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.EvenSmallLie.OmegaEight.Cover

structure CensusChecks : Prop where
  arr : censusArrCheck = true
  chain : censusChainCheck = true
  cover : censusCoverCheck = true
  fusion : censusFusionCheck = true
  deriv : censusDerivCheck = true

theorem arr_facts (hC : CensusChecks) :
    (∀ i < 8, isInvA 480 eArrs[i]! (invCand 480 eArrs[i]!) = true ∧
      isInvA 480 (invCand 480 eArrs[i]!) eArrs[i]! = true) ∧
    (∀ t ∈ [pairA negArr (idA 240), pairA (idA 240) negArr, pairA negArr negArr],
      isInvA 480 t (invCand 480 t) = true ∧ isInvA 480 (invCand 480 t) t = true) ∧
    evalCodes eGens [1, 5, 1, 5] = z2 ∧ evalCodes eGens [5, 7, 5, 7] = z1 := by
  have h := hC.arr
  simp only [censusArrCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    schreierPermEq_eq_true_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem eArrs_get {i : ℕ} (hi : i < 8) :
    eArrs[i]! =
      pairA (wordArr (omWords.getD (rhoPerm.getD i 0) [])) (wordArr (omWords.getD i [])) := by
  rw [eArrs, getElem!_pos _ i (by simpa using hi)]
  simp

theorem chain_facts (hC : CensusChecks) :
    ValidSchreier seQ ∧ seQ.orderCertificate = 16384 ∧
      ValidSchreier s48Q ∧ s48Q.orderCertificate = 4096 ∧ (∀ g ∈ s48Gens, g * x48 = x48 * g) ∧
      ValidSchreier s16Q ∧ s16Q.orderCertificate = 1024 ∧ ∀ g ∈ s16Gens, g * x16 = x16 * g := by
  have h := hC.chain
  simp only [censusChainCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    schreierPermEq_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

abbrev tT : Subgroup (Equiv.Perm (Fin 480)) := seQ.originalSubgroup

theorem tT_eq : tT = Subgroup.closure {g | g ∈ seGens} := by
  rw [tT, seQ, certificate_originalSubgroup]

theorem card_tT (hC : CensusChecks) : Nat.card tT = 16384 := by
  rw [← seQ.orderCertificate_eq_card (chain_facts hC).1, (chain_facts hC).2.1]

abbrev tSize (r : Equiv.Perm (Fin 480)) : ℕ :=
  (conjClosure 480 (listTables seGens) (listTables (seGens.map (·⁻¹))) (toTable r) 600).1.size

theorem hn480 : (480 : ℕ) < 2 ^ 32 := by norm_num

theorem hord {g : Equiv.Perm (Fin 480)} (hg : ordTest 480 2 (toTable g) = true) : orderOf g = 2 :=
  (ordTest_iff perm_faithful (rep_toTable hn480 g) (by norm_num)).1 hg

theorem cover_of_repsOK {Q : RawSchreierDatum 480} (hQ : ValidSchreier Q)
    {gens : List (Equiv.Perm (Fin 480))}
    (hgens : Q.originalSubgroup = Subgroup.closure {g | g ∈ gens})
    {reps : List (Equiv.Perm (Fin 480))} (hreps : ∀ r ∈ reps, r ∈ Q.originalSubgroup)
    (h1 : repsOK 480 (listTables gens) (listTables (gens.map (·⁻¹))) (cosetOrderTables Q 1 2)
      (reps.map toTable) 600 = true)
    (h2 : ∀ r ∈ reps, ordTest 480 2 (toTable r) = true) :
    (∀ u ∈ Q.originalSubgroup, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ Q.originalSubgroup,
      u = c * r * c⁻¹) ∧
    ∀ r ∈ reps, (conjClosure 480 (listTables gens) (listTables (gens.map (·⁻¹))) (toTable r)
      600).1.size ≤ (conjClass Q.originalSubgroup r).ncard := by
  have hG : ∀ g ∈ gens, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hgens]
    exact Subgroup.subset_closure hg
  exact CFSG.EvenSmallLie.UnitarySix.exists_conj_of_repsOK_normalizing hn480 Q hQ
    Q.originalSubgroup
    (fun c hc h hh => Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem hc hh)
      (Q.originalSubgroup.inv_mem hc))
    (listTables_spec hn480 hG) (by norm_num) reps (fun r hr => ⟨hreps r hr, hord (h2 r hr)⟩)
    600 h1

theorem mem_of_words {S : Subgroup (Equiv.Perm (Fin 480))} {gens : List (Equiv.Perm (Fin 480))}
    (hS : S = Subgroup.closure {g | g ∈ gens}) (w : List ℤ) : evalCodes gens w ∈ S := by
  refine evalCodes_mem S (fun g hg => ?_) w
  rw [hS]
  exact Subgroup.subset_closure hg

abbrev s48 : Subgroup (Equiv.Perm (Fin 480)) := s48Q.originalSubgroup
abbrev s16 : Subgroup (Equiv.Perm (Fin 480)) := s16Q.originalSubgroup

theorem s48_eq :
    s48 = Subgroup.closure {g | g ∈ s48Words.map fun w => tab (evalCodes seGens w)} := by
  rw [s48, s48Q, certificate_originalSubgroup]
  rfl

theorem s16_eq :
    s16 = Subgroup.closure {g | g ∈ s16Words.map fun w => tab (evalCodes seGens w)} := by
  rw [s16, s16Q, certificate_originalSubgroup]
  rfl

theorem cover_facts (hC : CensusChecks) :
    (∀ u ∈ tT, orderOf u = 2 → ∃ r ∈ seReps, ∃ c ∈ tT, u = c * r * c⁻¹) ∧
      (∀ r ∈ seReps, tSize r ≤ (conjClass tT r).ncard) ∧
      (∀ u ∈ s48, orderOf u = 2 → ∃ r ∈ r48Reps, ∃ c ∈ s48, u = c * r * c⁻¹) ∧
      ∀ u ∈ s16, orderOf u = 2 → ∃ r ∈ r16Reps, ∃ c ∈ s16, u = c * r * c⁻¹ := by
  have h := hC.cover
  simp only [censusCoverCheck, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hT := chain_facts hC
  have hreps : ∀ r ∈ seReps, r ∈ tT := fun r hr => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    rw [tab_eq]
    exact mem_of_words tT_eq w
  have hwords : ∀ {S : Subgroup (Equiv.Perm (Fin 480))} {gens : List (Equiv.Perm (Fin 480))}
      {ws : List (List ℤ)}, S = Subgroup.closure {g | g ∈ gens} →
      ∀ r ∈ ws.map (evalCodes gens), r ∈ S := fun hS r hr => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact mem_of_words hS w
  have hs48 : s48Q.originalSubgroup = Subgroup.closure {g | g ∈ s48Gens} := by
    rw [s48Q, certificate_originalSubgroup]
  have hs16 : s16Q.originalSubgroup = Subgroup.closure {g | g ∈ s16Gens} := by
    rw [s16Q, certificate_originalSubgroup]
  have c1 := cover_of_repsOK hT.1 tT_eq hreps h1 h2
  have c2 := cover_of_repsOK hT.2.2.1 hs48 (hwords hs48) h3 h4
  have c3 := cover_of_repsOK hT.2.2.2.2.2.1 hs16 (hwords hs16) h5 h6
  exact ⟨c1.1, c1.2, c2.1, c3.1⟩

theorem deriv_facts (hC : CensusChecks) :
    (∀ r ∈ r48Reps, r ≠ x48 → ∃ st, derivCheck eGens okW zs [] [x48, r] st = true) ∧
      ∀ r ∈ r16Reps, r ≠ x16 → ∃ st, derivCheck eGens okW zs [48] [x16, r] st = true := by
  have h := hC.deriv
  simp only [censusDerivCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨exists_deriv_of_zip h1 h3, exists_deriv_of_zip h2 h4⟩

theorem x_mem {x : Equiv.Perm (Fin 480)} (hx : x ∈ xs) : x ∈ tT := by
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · rw [x48, tab_eq]
    exact mem_of_words tT_eq _
  · rw [x16, tab_eq]
    exact mem_of_words tT_eq _

theorem s_le_T {S : Subgroup (Equiv.Perm (Fin 480))} {ws : List (List ℤ)}
    (hS : S = Subgroup.closure {g | g ∈ ws.map fun w => tab (evalCodes seGens w)}) : S ≤ tT := by
  rw [hS, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [SetLike.mem_coe, tab_eq]
  exact mem_of_words tT_eq w

theorem s_le_centralizer {S : Subgroup (Equiv.Perm (Fin 480))} {gens : List (Equiv.Perm (Fin 480))}
    (hS : S = Subgroup.closure {g | g ∈ gens}) {x : Equiv.Perm (Fin 480)}
    (h : ∀ g ∈ gens, g * x = x * g) : S ≤ Subgroup.centralizer {x} := by
  rw [hS, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact h g hg

section Model

theorem coe_wElt {i : ℕ} (hi : i < 8) : (wElt i : Equiv.Perm (Fin 240)) = omLift i := by
  simp only [wElt, hi, ↓reduceDIte]

theorem eHom_apply (x : eFib) : eHom x = pairHom (((x : wPlus × wPlus).1 : Equiv.Perm (Fin 240)),
    ((x : wPlus × wPlus).2 : Equiv.Perm (Fin 240))) := rfl

theorem eHom_eElt {i : ℕ} (hi : i < 8) :
    eHom (eElt i) = pairHom (omLift (rhoPerm.getD i 0), omLift i) := by
  rw [eHom_apply]
  simp only [eElt, hi, ↓reduceDIte, eEltPair]
  rw [coe_wElt hi, coe_wElt (rhoPerm_lt hi)]

theorem eGens_getD (hC : CensusChecks) {i : ℕ} (hi : i < 8) : eGens.getD i 1 = eHom (eElt i) := by
  rw [eGens, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  refine (rep_permOrId ((arr_facts hC).1 i hi)).unique ?_
  rw [eHom_eElt hi, eArrs_get hi]
  exact rep_pairA (rep_wordArr _ (omWords_lt (rhoPerm_lt hi))) (rep_wordArr _ (omWords_lt hi))

theorem eGens_mem (hC : CensusChecks) : ∀ g ∈ eGens, g ∈ e480 := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi8 : i < 8 := by simpa [eGens] using hi
  rw [← List.getD_eq_getElem _ 1 hi, eGens_getD hC hi8]
  exact ⟨_, rfl⟩

theorem okW_mem (hC : CensusChecks) : ∀ w, okW w = true → evalCodes eGens w ∈ e480 :=
  fun w _ => evalCodes_mem e480 (eGens_mem hC) w

theorem z1_eq (hC : CensusChecks) : z1 = eHom (zElt true false) := by
  refine (rep_permOrId ((arr_facts hC).2.1 _ (by simp))).unique ?_
  have : eHom (zElt true false) = pairHom (zPerm, 1) := rfl
  rw [this]
  exact rep_pairA rep_negArr rep_idA

theorem z2_eq (hC : CensusChecks) : z2 = eHom (zElt false true) := by
  refine (rep_permOrId ((arr_facts hC).2.1 _ (by simp))).unique ?_
  have : eHom (zElt false true) = pairHom (1, zPerm) := rfl
  rw [this]
  exact rep_pairA rep_idA rep_negArr

theorem z3_eq (hC : CensusChecks) : z3 = eHom (zElt true true) := by
  refine (rep_permOrId ((arr_facts hC).2.1 _ (by simp))).unique ?_
  have : eHom (zElt true true) = pairHom (zPerm, zPerm) := rfl
  rw [this]
  exact rep_pairA rep_negArr rep_negArr

theorem mem_zs_iff (hC : CensusChecks) {z : Equiv.Perm (Fin 480)} :
    z ∈ zs ↔ z = eHom (zElt true false) ∨ z = eHom (zElt false true) ∨
      z = eHom (zElt true true) := by
  simp only [zs, List.mem_cons, List.not_mem_nil, or_false, z1_eq hC, z2_eq hC, z3_eq hC]

theorem z_comm (hC : CensusChecks) : ∀ g ∈ e480, ∀ z ∈ zs, g * z = z * g := by
  rintro _ ⟨g, rfl⟩ z hz
  have hc : ∀ a b, eHom g * eHom (zElt a b) = eHom (zElt a b) * eHom g := fun a b => by
    rw [← map_mul, ← map_mul, mem_center_iff.1 (ker_qE_le_center (zElt_mem_ker a b)) g]
  rcases (mem_zs_iff hC).1 hz with rfl | rfl | rfl <;> exact hc _ _

theorem isPerfect_eFib' (hC : CensusChecks) : Group.IsPerfect eFib := by
  obtain ⟨-, -, h04, h46⟩ := arr_facts hC
  have e04 : evalCodes eGens [1, 5, 1, 5] = eHom ((eElt 0 * eElt 4) ^ 2) := by
    simp only [evalCodes, show (0 : ℤ) < 1 by norm_num, show (0 : ℤ) < 5 by norm_num,
      ↓reduceIte, mul_one]
    rw [show (1 : ℤ).toNat - 1 = 0 from rfl, show (5 : ℤ).toNat - 1 = 4 from rfl,
      eGens_getD hC (by norm_num), eGens_getD hC (by norm_num), sq, map_mul, map_mul]
    group
  have e46 : evalCodes eGens [5, 7, 5, 7] = eHom ((eElt 4 * eElt 6) ^ 2) := by
    simp only [evalCodes, show (0 : ℤ) < 5 by norm_num, show (0 : ℤ) < 7 by norm_num,
      ↓reduceIte, mul_one]
    rw [show (5 : ℤ).toNat - 1 = 4 from rfl, show (7 : ℤ).toNat - 1 = 6 from rfl,
      eGens_getD hC (by norm_num), eGens_getD hC (by norm_num), sq, map_mul, map_mul]
    group
  refine isPerfect_eFib (eHom_injective ?_) (eHom_injective ?_)
  · rw [← e04, h04, z2_eq hC]
  · rw [← e46, h46, z1_eq hC]

theorem tT_le (hC : CensusChecks) : tT ≤ e480 := by
  rw [tT_eq, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [SetLike.mem_coe, tab_eq]
  exact okW_mem hC w rfl

theorem exists_conj_le_T (hC : CensusChecks) : ∀ Q : Subgroup (Equiv.Perm (Fin 480)),
    Q ≤ e480 → IsPGroup 2 Q → ∃ g ∈ e480, ∀ q ∈ Q, g * q * g⁻¹ ∈ tT := by
  intro Q hQ hQ2
  have hcard : Nat.card (tT.subgroupOf e480) = 16384 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tT_le hC)).toEquiv, card_tT hC]
  have hT2 : IsPGroup 2 tT := IsPGroup.of_card (n := 14) (by rw [card_tT hC]; norm_num)
  have hidx : ¬ 2 ∣ (tT.subgroupOf e480).index := by
    have h := (tT.subgroupOf e480).card_mul_index
    rw [hcard, card_e480] at h
    have h2 : (tT.subgroupOf e480).index = 42525 := by omega
    rw [h2]
    norm_num
  exact exists_conj_le_of_odd_index hT2 hidx hQ hQ2

theorem fusion_facts (hC : CensusChecks) :
    xs.map fixNum = xsFix ∧ (∀ x ∈ xs, orderOf x = 2 ∧ x ∉ zs) ∧
      (∀ r ∈ seReps, r ∈ zs ∨ ∃ x ∈ xs, ∃ g ∈ e480, g * r * g⁻¹ = x) ∧
      ∀ r ∈ seReps, ∀ q ∈ xsFix.zip xsMin, fixNum r = q.1 → q.2 ≤ tSize r := by
  have h := hC.fusion
  simp only [censusFusionCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hlen, hfix⟩, hxs⟩, hfus⟩, hsz⟩ := h
  refine ⟨hfix, ?_, ?_, ?_⟩
  · intro x hx
    have := List.all_eq_true.1 hxs x hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    refine ⟨hord this.1, fun hz => ?_⟩
    have h2 := this.2
    rw [List.any_eq_false] at h2
    exact h2 x hz ((schreierPermEq_eq_true_iff _ _).2 rfl)
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hi2 : i < fusion.length := by rw [hlen]; exact hi
    have hpair : (seReps[i], fusion[i]) ∈ seReps.zip fusion := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [hlen, hi], by rw [List.getElem_zip]; rfl⟩
    have hmem := List.all_eq_true.1 hfus _ hpair
    generalize seReps[i] = r at hmem ⊢
    generalize fusion[i] = f at hmem
    obtain ⟨k, w⟩ := f
    dsimp only at hmem
    by_cases h0 : k = 0
    · subst h0
      simp only [↓reduceIte, List.any_eq_true, schreierPermEq_eq_true_iff] at hmem
      obtain ⟨z, hz, rfl⟩ := hmem
      exact Or.inl hz
    · simp only [h0, ↓reduceIte, Bool.and_eq_true, schreierPermEq_eq_true_iff,
        decide_eq_true_eq] at hmem
      obtain ⟨hk, hconj⟩ := hmem
      have hk' : k - 1 < xs.length := by omega
      refine Or.inr ⟨xs.getD (k - 1) 1, ?_, _, by rw [tab_eq]; exact okW_mem hC w rfl, hconj⟩
      rw [List.getD_eq_getElem _ _ hk']
      exact List.getElem_mem hk'
  · intro r hr q hq hfr
    have h' := all_zip_repSizes hsz r hr
    have := List.all_eq_true.1 h' q hq
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    exact this.resolve_left (not_not.2 hfr)

theorem conj_classes_e480 (hC : CensusChecks) {y : Equiv.Perm (Fin 480)} (hy : y ∈ e480)
    (ho : orderOf y = 2) (hyz : y ∉ zs) :
    ∃ x ∈ xs, fixNum y = fixNum x ∧ ∃ g ∈ e480, g * y * g⁻¹ = x :=
  conj_classes (z_comm hC) (tT_le hC) (exists_conj_le_T hC) (cover_facts hC).1
    (fusion_facts hC).2.2.1 hy ho hyz

theorem false_of_class (hC : CensusChecks) {x : Equiv.Perm (Fin 480)} (hx : x ∈ xs)
    {S : Subgroup (Equiv.Perm (Fin 480))} (hST : S ≤ tT) (hSx : S ≤ Subgroup.centralizer {x})
    {m e : ℕ} (hcard : Nat.card S = 2 ^ e) (hme : 2 ^ e * m = 16384)
    (hm : ∀ r ∈ seReps, fixNum r = fixNum x → r ∉ zs → m ≤ (conjClass tT r).ncard)
    {reps : List (Equiv.Perm (Fin 480))}
    (hcov : ∀ u ∈ S, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ S, u = c * r * c⁻¹) {forbid : List ℕ}
    (hder : ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck eGens okW zs forbid [x, r] st = true)
    {X : Subgroup (Equiv.Perm (Fin 480))} (hX : Hyp212In e480 {z | z ∈ zs} X) (hxX : x ∈ X)
    (hf : ∀ y ∈ X, y ≠ 1 → fixNum y ∉ forbid) : False := by
  have hxs := (fusion_facts hC).2.1 x hx
  have hxW : x ∈ e480 := tT_le hC (x_mem hx)
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 480)), R ≤ e480 ⊓ Subgroup.centralizer {x} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card S := by
    intro R hR hR2
    have h := card_le_of_commute (z_comm hC) (tT_le hC) (exists_conj_le_T hC) (cover_facts hC).1
      hxW hxs.1 hxs.2 (fun r hr => (hR hr).1)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hR hr).2) hR2 hm
    rw [card_tT hC, ← hme] at h
    rw [hcard]
    exact Nat.le_of_mul_le_mul_right h (by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hme
        exact absurd hme (by norm_num)
      · exact h0)
  exact false_of_pair (z_comm hC) (okW_mem hC) (fun s hs => ⟨tT_le hC (hST hs), hSx hs⟩)
    (IsPGroup.of_card hcard) hmax hcov hder hX hxX hf

theorem hm_of (hC : CensusChecks) {x : Equiv.Perm (Fin 480)} {f m : ℕ} (hfx : fixNum x = f)
    (hq : (f, m) ∈ xsFix.zip xsMin) :
    ∀ r ∈ seReps, fixNum r = fixNum x → r ∉ zs → m ≤ (conjClass tT r).ncard :=
  fun r hr hfr _ => ((fusion_facts hC).2.2.2 r hr _ hq (hfr.trans hfx)).trans
    ((cover_facts hC).2.1 r hr)

theorem fix_xs (hC : CensusChecks) : fixNum x48 = 48 ∧ fixNum x16 = 16 := by
  have h := (fusion_facts hC).1
  simp only [xs, xsFix, List.map_cons, List.map_nil, List.cons.injEq] at h
  exact ⟨h.1, h.2.1⟩

theorem not_hyp212In_e480 (hC : CensusChecks) (X : Subgroup (Equiv.Perm (Fin 480))) :
    ¬ Hyp212In e480 {z | z ∈ zs} X := by
  have hT := chain_facts hC
  obtain ⟨f48, f16⟩ := fix_xs hC
  obtain ⟨-, -, c48, c16⟩ := cover_facts hC
  obtain ⟨d48', d16'⟩ := deriv_facts hC
  refine not_hyp212In_of_classes (z_comm hC) ?_ (fun y hy ho hyz => conj_classes_e480 hC hy ho hyz)
    ?_ X
  · rw [(fusion_facts hC).1]
    decide
  · intro k hk Y hY hxY hf
    simp only [xs, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact false_of_class hC (S := s48) (by simp [xs]) (s_le_T s48_eq)
        (s_le_centralizer (s48_eq.trans rfl) hT.2.2.2.2.1)
        (e := 12) (by rw [s48, ← s48Q.orderCertificate_eq_card hT.2.2.1, hT.2.2.2.1]; norm_num)
        (m := 4) (by norm_num) (hm_of hC f48 (by decide)) c48 d48' hY hxY
        (fun _ _ _ => List.not_mem_nil)
    · exact false_of_class hC (S := s16) (by simp [xs]) (s_le_T s16_eq)
        (s_le_centralizer (s16_eq.trans rfl) hT.2.2.2.2.2.2.2)
        (e := 10) (by rw [s16, ← s16Q.orderCertificate_eq_card hT.2.2.2.2.2.1,
          hT.2.2.2.2.2.2.1]; norm_num)
        (m := 16) (by norm_num) (hm_of hC f16 (by decide)) c16 d16' hY hxY
        (fun y hy hy1 => by simpa [xs, f48] using hf y hy hy1)

end Model

end CFSG.ComponentClassification.RankTwoClassical.ExcO8E
