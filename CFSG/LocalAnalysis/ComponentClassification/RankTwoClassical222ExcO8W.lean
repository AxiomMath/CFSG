module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8WInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Census
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClassesBase

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8W

open Subgroup CFSG.ComponentClassification.RankTwoClassical.ExcO8
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 CFSG.EvenSmallLie.OmegaEight.Weyl

structure CensusChecks : Prop where
  arr : censusArrCheck = true
  chain : censusChainCheck = true
  cover : censusCoverCheck = true
  fusion : censusFusionCheck = true
  deriv : censusDerivCheck = true

theorem arr_facts (hC : CensusChecks) :
    (∀ r < 240, isInvA 240 reflArrs[r]! (invCand 240 reflArrs[r]!) = true ∧
      isInvA 240 (invCand 240 reflArrs[r]!) reflArrs[r]! = true) ∧
    (isInvA 240 negArr (invCand 240 negArr) = true ∧
      isInvA 240 (invCand 240 negArr) negArr = true) := by
  have h := hC.arr
  simp only [censusArrCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem refls_getD (hC : CensusChecks) {r : ℕ} (hr : r < 240) : refls.getD r 1 = refl r := by
  rw [refls, List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map, List.getElem_range,
    permOrId_eq_permOfArr ((arr_facts hC).1 r hr)]
  have h : reflArrs[r]! = reflArr r := by
    rw [reflArrs, getElem!_pos _ r (by simpa using hr)]
    simp
  rw [h]
  rfl

theorem zC_eq (hC : CensusChecks) : zC = zPerm :=
  permOrId_eq_permOfArr (arr_facts hC).2

theorem chain_facts (hC : CensusChecks) :
    ValidSchreier tQ ∧ tQ.orderCertificate = 8192 ∧ (∀ w ∈ tWords, okW w = true) ∧
      ValidSchreier s24Q ∧ s24Q.orderCertificate = 4096 ∧ (∀ g ∈ s24Gens, g * x24 = x24 * g) ∧
      ValidSchreier s60Q ∧ s60Q.orderCertificate = 2048 ∧ (∀ g ∈ s60Gens, g * x60 = x60 * g) ∧
      ValidSchreier s4Q ∧ s4Q.orderCertificate = 2048 ∧ (∀ g ∈ s4Gens, g * x4 = x4 * g) ∧
      ValidSchreier s8Q ∧ s8Q.orderCertificate = 1024 ∧ ∀ g ∈ s8Gens, g * x8 = x8 * g := by
  have h := hC.chain
  simp only [censusChainCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    schreierPermEq_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

abbrev tT : Subgroup (Equiv.Perm (Fin 240)) := tQ.originalSubgroup

theorem tT_eq : tT = Subgroup.closure {g | g ∈ tGens} := by
  rw [tT, tQ, certificate_originalSubgroup]

theorem card_tT (hC : CensusChecks) : Nat.card tT = 8192 := by
  rw [← tQ.orderCertificate_eq_card (chain_facts hC).1, (chain_facts hC).2.1]

abbrev tSize (r : Equiv.Perm (Fin 240)) : ℕ :=
  (conjClosure 240 (listTables tGens) (listTables (tGens.map (·⁻¹))) (toTable r) 600).1.size

theorem hn240 : (240 : ℕ) < 2 ^ 32 := by norm_num

theorem hord {g : Equiv.Perm (Fin 240)} (hg : ordTest 240 2 (toTable g) = true) : orderOf g = 2 :=
  (ordTest_iff perm_faithful (rep_toTable hn240 g) (by norm_num)).1 hg

theorem cover_of_repsOK {Q : RawSchreierDatum 240} (hQ : ValidSchreier Q)
    {gens : List (Equiv.Perm (Fin 240))}
    (hgens : Q.originalSubgroup = Subgroup.closure {g | g ∈ gens})
    {reps : List (Equiv.Perm (Fin 240))} (hreps : ∀ r ∈ reps, r ∈ Q.originalSubgroup)
    (h1 : repsOK 240 (listTables gens) (listTables (gens.map (·⁻¹))) (cosetOrderTables Q 1 2)
      (reps.map toTable) 600 = true)
    (h2 : ∀ r ∈ reps, ordTest 240 2 (toTable r) = true) :
    (∀ u ∈ Q.originalSubgroup, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ Q.originalSubgroup,
      u = c * r * c⁻¹) ∧
    ∀ r ∈ reps, (conjClosure 240 (listTables gens) (listTables (gens.map (·⁻¹))) (toTable r)
      600).1.size ≤ (conjClass Q.originalSubgroup r).ncard := by
  have hG : ∀ g ∈ gens, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hgens]
    exact Subgroup.subset_closure hg
  exact CFSG.EvenSmallLie.UnitarySix.exists_conj_of_repsOK_normalizing hn240 Q hQ
    Q.originalSubgroup
    (fun c hc h hh => Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem hc hh)
      (Q.originalSubgroup.inv_mem hc))
    (listTables_spec hn240 hG) (by norm_num) reps (fun r hr => ⟨hreps r hr, hord (h2 r hr)⟩)
    600 h1

theorem sQ_originalSubgroup {gens : List (Equiv.Perm (Fin 240))} {words : List (List ℤ)} {k : ℕ}
    {base : Vector (Fin 240) k} {hb : base.toList.Nodup} :
    (certificate (by decide) gens words base hb).originalSubgroup =
      Subgroup.closure {g | g ∈ gens} :=
  certificate_originalSubgroup _ _ _ _ _

abbrev s24 : Subgroup (Equiv.Perm (Fin 240)) := s24Q.originalSubgroup
abbrev s60 : Subgroup (Equiv.Perm (Fin 240)) := s60Q.originalSubgroup
abbrev s4 : Subgroup (Equiv.Perm (Fin 240)) := s4Q.originalSubgroup
abbrev s8 : Subgroup (Equiv.Perm (Fin 240)) := s8Q.originalSubgroup

theorem mem_of_words {S : Subgroup (Equiv.Perm (Fin 240))} {gens : List (Equiv.Perm (Fin 240))}
    (hS : S = Subgroup.closure {g | g ∈ gens}) (w : List ℤ) : evalCodes gens w ∈ S := by
  refine evalCodes_mem S (fun g hg => ?_) w
  rw [hS]
  exact Subgroup.subset_closure hg

theorem cover_facts (hC : CensusChecks) :
    (∀ u ∈ tT, orderOf u = 2 → ∃ r ∈ tReps, ∃ c ∈ tT, u = c * r * c⁻¹) ∧
      (∀ r ∈ tReps, tSize r ≤ (conjClass tT r).ncard) ∧
      (∀ u ∈ s24, orderOf u = 2 → ∃ r ∈ r24Reps, ∃ c ∈ s24, u = c * r * c⁻¹) ∧
      (∀ u ∈ s60, orderOf u = 2 → ∃ r ∈ r60Reps, ∃ c ∈ s60, u = c * r * c⁻¹) ∧
      (∀ u ∈ s4, orderOf u = 2 → ∃ r ∈ r4Reps, ∃ c ∈ s4, u = c * r * c⁻¹) ∧
      ∀ u ∈ s8, orderOf u = 2 → ∃ r ∈ r8Reps, ∃ c ∈ s8, u = c * r * c⁻¹ := by
  have h := hC.cover
  simp only [censusCoverCheck, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have hT := chain_facts hC
  have hreps : ∀ r ∈ tReps, r ∈ tT := fun r hr => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    rw [tab_eq]
    exact mem_of_words tT_eq w
  have hwords : ∀ {S : Subgroup (Equiv.Perm (Fin 240))} {gens : List (Equiv.Perm (Fin 240))}
      {ws : List (List ℤ)}, S = Subgroup.closure {g | g ∈ gens} →
      ∀ r ∈ ws.map (evalCodes gens), r ∈ S := fun hS r hr => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact mem_of_words hS w
  have c1 := cover_of_repsOK hT.1 tT_eq hreps h1 h2
  have c2 := cover_of_repsOK hT.2.2.2.1 sQ_originalSubgroup (hwords sQ_originalSubgroup) h3 h4
  have c3 := cover_of_repsOK hT.2.2.2.2.2.2.1 sQ_originalSubgroup (hwords sQ_originalSubgroup)
    h5 h6
  have c4 := cover_of_repsOK hT.2.2.2.2.2.2.2.2.2.1 sQ_originalSubgroup
    (hwords sQ_originalSubgroup) h7 h8
  have c5 := cover_of_repsOK hT.2.2.2.2.2.2.2.2.2.2.2.2.1 sQ_originalSubgroup
    (hwords sQ_originalSubgroup) h9 h10
  exact ⟨c1.1, c1.2, c2.1, c3.1, c4.1, c5.1⟩

theorem deriv_facts (hC : CensusChecks) :
    (∀ r ∈ r24Reps, r ≠ x24 → ∃ st, derivCheck refls okW zs [] [x24, r] st = true) ∧
      (∀ r ∈ r60Reps, r ≠ x60 → ∃ st, derivCheck refls okW zs [24] [x60, r] st = true) ∧
      (∀ r ∈ r4Reps, r ≠ x4 → ∃ st, derivCheck refls okW zs [24, 60] [x4, r] st = true) ∧
      ∀ r ∈ r8Reps, r ≠ x8 → ∃ st, derivCheck refls okW zs [24, 60, 4] [x8, r] st = true := by
  have h := hC.deriv
  simp only [censusDerivCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨exists_deriv_of_zip h1 h5, exists_deriv_of_zip h2 h6, exists_deriv_of_zip h3 h7,
    exists_deriv_of_zip h4 h8⟩

theorem x_mem {x : Equiv.Perm (Fin 240)} (hx : x ∈ xs) : x ∈ tT := by
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [x24, tab_eq]
    exact mem_of_words tT_eq _
  · rw [x60, tab_eq]
    exact mem_of_words tT_eq _
  · rw [x4, tab_eq]
    exact mem_of_words tT_eq _
  · rw [x8, tab_eq]
    exact mem_of_words tT_eq _

theorem s_le_T {S : Subgroup (Equiv.Perm (Fin 240))} {ws : List (List ℤ)}
    (hS : S = Subgroup.closure {g | g ∈ ws.map fun w => tab (evalCodes tGens w)}) : S ≤ tT := by
  rw [hS, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [SetLike.mem_coe, tab_eq]
  exact mem_of_words tT_eq w

theorem s24_eq :
    s24 = Subgroup.closure {g | g ∈ s24Words.map fun w => tab (evalCodes tGens w)} := by
  rw [s24, s24Q, certificate_originalSubgroup]
  rfl

theorem s60_eq :
    s60 = Subgroup.closure {g | g ∈ s60Words.map fun w => tab (evalCodes tGens w)} := by
  rw [s60, s60Q, certificate_originalSubgroup]
  rfl

theorem s4_eq :
    s4 = Subgroup.closure {g | g ∈ s4Words.map fun w => tab (evalCodes tGens w)} := by
  rw [s4, s4Q, certificate_originalSubgroup]
  rfl

theorem s8_eq :
    s8 = Subgroup.closure {g | g ∈ s8Words.map fun w => tab (evalCodes tGens w)} := by
  rw [s8, s8Q, certificate_originalSubgroup]
  rfl

theorem s_le_centralizer {S : Subgroup (Equiv.Perm (Fin 240))} {gens : List (Equiv.Perm (Fin 240))}
    (hS : S = Subgroup.closure {g | g ∈ gens}) {x : Equiv.Perm (Fin 240)}
    (h : ∀ g ∈ gens, g * x = x * g) : S ≤ Subgroup.centralizer {x} := by
  rw [hS, Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact h g hg

section Census

theorem evalCodes_refls (hC : CensusChecks) : ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 240) →
    evalCodes refls w ∈ wE8 ∧ Equiv.Perm.sign (evalCodes refls w) = (-1) ^ w.length
  | [], _ => by simp [evalCodes]
  | z :: w, h => by
    obtain ⟨hz0, hz⟩ := h z List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := evalCodes_refls hC w fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hlt : ∀ k : ℕ, 0 < k → k ≤ 240 → refls.getD (k - 1) 1 = refl (k - 1) ∧ k - 1 < 240 :=
      fun k hk hk2 => ⟨refls_getD hC (by omega), by omega⟩
    rw [evalCodes]
    by_cases hpos : 0 < z
    · simp only [hpos, ↓reduceIte]
      obtain ⟨he, hk⟩ := hlt z.toNat (by omega) (by omega)
      rw [he]
      refine ⟨mul_mem (refl_mem hk) ih1, ?_⟩
      rw [map_mul, sign_refl hk, ih2, List.length_cons, pow_succ, mul_comm]
    · simp only [hpos, ↓reduceIte]
      obtain ⟨he, hk⟩ := hlt (-z).toNat (by omega) (by omega)
      rw [he, refl_inv hk]
      refine ⟨mul_mem (refl_mem hk) ih1, ?_⟩
      rw [map_mul, sign_refl hk, ih2, List.length_cons, pow_succ, mul_comm]

theorem okW_mem (hC : CensusChecks) : ∀ w, okW w = true → evalCodes refls w ∈ wPlus := by
  intro w hw
  simp only [okW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  obtain ⟨hlen, hall⟩ := hw
  obtain ⟨h1, h2⟩ := evalCodes_refls hC w fun z hz => hall z hz
  refine mem_wPlus_iff.2 ⟨h1, ?_⟩
  rw [h2]
  exact Even.neg_one_pow (Nat.even_iff.2 hlen)

theorem z_comm (hC : CensusChecks) : ∀ g ∈ wPlus, ∀ z ∈ zs, g * z = z * g := by
  intro g hg z hz
  simp only [zs, List.mem_cons, List.not_mem_nil, or_false] at hz
  rw [hz, zC_eq hC]
  exact zPerm_comm g (wPlus_le hg)

theorem tGens_mem (hC : CensusChecks) : ∀ g ∈ tGens, g ∈ wPlus := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  rw [tab_eq]
  exact okW_mem hC w ((chain_facts hC).2.2.1 w hw)

theorem tT_le (hC : CensusChecks) : tT ≤ wPlus := by
  rw [tT_eq, Subgroup.closure_le]
  exact fun g hg => tGens_mem hC g hg

theorem exists_conj_le_T (hC : CensusChecks) : ∀ Q : Subgroup (Equiv.Perm (Fin 240)),
    Q ≤ wPlus → IsPGroup 2 Q → ∃ g ∈ wPlus, ∀ q ∈ Q, g * q * g⁻¹ ∈ tT := by
  intro Q hQ hQ2
  have hcard : Nat.card (tT.subgroupOf wPlus) = 8192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tT_le hC)).toEquiv, card_tT hC]
  have hT2 : IsPGroup 2 tT := IsPGroup.of_card (n := 13) (by rw [card_tT hC]; norm_num)
  have hidx : ¬ 2 ∣ (tT.subgroupOf wPlus).index := by
    have h := (tT.subgroupOf wPlus).card_mul_index
    rw [hcard, card_wPlus] at h
    have h2 : (tT.subgroupOf wPlus).index = 42525 := by omega
    rw [h2]
    norm_num
  exact exists_conj_le_of_odd_index hT2 hidx hQ hQ2

theorem fusion_facts (hC : CensusChecks) :
    xs.map fixNum = xsFix ∧ (∀ x ∈ xs, orderOf x = 2 ∧ x ∉ zs) ∧
      (∀ r ∈ tReps, r ∈ zs ∨ ∃ x ∈ xs, ∃ g ∈ wPlus, g * r * g⁻¹ = x) ∧
      ∀ r ∈ tReps, ∀ q ∈ xsFix.zip xsMin, fixNum r = q.1 → q.2 ≤ tSize r := by
  have h := hC.fusion
  simp only [censusFusionCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hlen, hfix⟩, hxs⟩, hfus⟩, hsz⟩ := h
  refine ⟨hfix, ?_, ?_, ?_⟩
  · intro x hx
    have := List.all_eq_true.1 hxs x hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    refine ⟨hord this.1, fun hz => ?_⟩
    simp only [zs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rw [hz, (schreierPermEq_eq_true_iff _ _).2 rfl] at this
    exact Bool.noConfusion this.2
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hi2 : i < fusion.length := by rw [hlen]; exact hi
    have hpair : (tReps[i], fusion[i]) ∈ tReps.zip fusion := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [hlen, hi], by rw [List.getElem_zip]; rfl⟩
    have hmem := List.all_eq_true.1 hfus _ hpair
    generalize tReps[i] = r at hmem ⊢
    generalize fusion[i] = f at hmem
    obtain ⟨k, w⟩ := f
    dsimp only at hmem
    by_cases h0 : k = 0
    · subst h0
      simp only [↓reduceIte, schreierPermEq_eq_true_iff] at hmem
      left
      simp only [zs, List.mem_cons, List.not_mem_nil, or_false]
      exact hmem
    · simp only [h0, ↓reduceIte, Bool.and_eq_true, schreierPermEq_eq_true_iff,
        decide_eq_true_eq] at hmem
      obtain ⟨⟨hw, hk⟩, hconj⟩ := hmem
      have hk' : k - 1 < xs.length := by omega
      refine Or.inr ⟨xs.getD (k - 1) 1, ?_, _, by rw [tab_eq]; exact okW_mem hC w hw, hconj⟩
      rw [List.getD_eq_getElem _ _ hk']
      exact List.getElem_mem hk'
  · intro r hr q hq hfr
    have h' := all_zip_repSizes hsz r hr
    have := List.all_eq_true.1 h' q hq
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    exact this.resolve_left (not_not.2 hfr)

theorem conj_classes_wPlus (hC : CensusChecks) {y : Equiv.Perm (Fin 240)} (hy : y ∈ wPlus)
    (ho : orderOf y = 2) (hyz : y ∉ zs) :
    ∃ x ∈ xs, fixNum y = fixNum x ∧ ∃ g ∈ wPlus, g * y * g⁻¹ = x :=
  conj_classes (z_comm hC) (tT_le hC) (exists_conj_le_T hC) (cover_facts hC).1
    (fusion_facts hC).2.2.1 hy ho hyz

theorem false_of_class (hC : CensusChecks) {x : Equiv.Perm (Fin 240)} (hx : x ∈ xs)
    {S : Subgroup (Equiv.Perm (Fin 240))} (hST : S ≤ tT) (hSx : S ≤ Subgroup.centralizer {x})
    {m e : ℕ} (hcard : Nat.card S = 2 ^ e) (hme : 2 ^ e * m = 8192)
    (hm : ∀ r ∈ tReps, fixNum r = fixNum x → r ∉ zs → m ≤ (conjClass tT r).ncard)
    {reps : List (Equiv.Perm (Fin 240))}
    (hcov : ∀ u ∈ S, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ S, u = c * r * c⁻¹) {forbid : List ℕ}
    (hder : ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck refls okW zs forbid [x, r] st = true)
    {X : Subgroup (Equiv.Perm (Fin 240))} (hX : Hyp212In wPlus {z | z ∈ zs} X) (hxX : x ∈ X)
    (hf : ∀ y ∈ X, y ≠ 1 → fixNum y ∉ forbid) : False := by
  have hxs := (fusion_facts hC).2.1 x hx
  have hxW : x ∈ wPlus := tT_le hC (x_mem hx)
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 240)), R ≤ wPlus ⊓ Subgroup.centralizer {x} →
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

theorem hm_of (hC : CensusChecks) {x : Equiv.Perm (Fin 240)} {f m : ℕ} (hfx : fixNum x = f)
    (hq : (f, m) ∈ xsFix.zip xsMin) :
    ∀ r ∈ tReps, fixNum r = fixNum x → r ∉ zs → m ≤ (conjClass tT r).ncard :=
  fun r hr hfr _ => ((fusion_facts hC).2.2.2 r hr _ hq (hfr.trans hfx)).trans
    ((cover_facts hC).2.1 r hr)

theorem fix_xs (hC : CensusChecks) :
    fixNum x24 = 24 ∧ fixNum x60 = 60 ∧ fixNum x4 = 4 ∧ fixNum x8 = 8 := by
  have h := (fusion_facts hC).1
  simp only [xs, xsFix, List.map_cons, List.map_nil, List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem not_hyp212In_wPlus (hC : CensusChecks) (X : Subgroup (Equiv.Perm (Fin 240))) :
    ¬ Hyp212In wPlus {z | z ∈ zs} X := by
  have hT := chain_facts hC
  obtain ⟨f24, f60, f4, f8⟩ := fix_xs hC
  obtain ⟨-, -, c24, c60, c4, c8⟩ := cover_facts hC
  obtain ⟨d24', d60', d4', d8'⟩ := deriv_facts hC
  refine not_hyp212In_of_classes (z_comm hC) ?_ (fun y hy ho hyz => conj_classes_wPlus hC hy ho hyz)
    ?_ X
  · rw [(fusion_facts hC).1]
    decide
  · intro k hk Y hY hxY hf
    simp only [xs, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact false_of_class hC (S := s24) (by simp [xs]) (s_le_T s24_eq)
        (s_le_centralizer (s24_eq.trans rfl) hT.2.2.2.2.2.1)
        (e := 12) (by rw [s24, ← s24Q.orderCertificate_eq_card hT.2.2.2.1, hT.2.2.2.2.1]; norm_num)
        (m := 2) (by norm_num) (hm_of hC f24 (by decide)) c24 d24' hY hxY
        (fun _ _ _ => List.not_mem_nil)
    · exact false_of_class hC (S := s60) (by simp [xs]) (s_le_T s60_eq)
        (s_le_centralizer (s60_eq.trans rfl) hT.2.2.2.2.2.2.2.2.1)
        (e := 11) (by rw [s60, ← s60Q.orderCertificate_eq_card hT.2.2.2.2.2.2.1,
          hT.2.2.2.2.2.2.2.1]; norm_num)
        (m := 4) (by norm_num) (hm_of hC f60 (by decide)) c60 d60' hY hxY
        (fun y hy hy1 => by simpa [xs, f24] using hf y hy hy1)
    · exact false_of_class hC (S := s4) (by simp [xs]) (s_le_T s4_eq)
        (s_le_centralizer (s4_eq.trans rfl) hT.2.2.2.2.2.2.2.2.2.2.2.1)
        (e := 11) (by rw [s4, ← s4Q.orderCertificate_eq_card hT.2.2.2.2.2.2.2.2.2.1,
          hT.2.2.2.2.2.2.2.2.2.2.1]; norm_num)
        (m := 4) (by norm_num) (hm_of hC f4 (by decide)) c4 d4' hY hxY
        (fun y hy hy1 => by simpa [xs, f24, f60] using hf y hy hy1)
    · exact false_of_class hC (S := s8) (by simp [xs]) (s_le_T s8_eq)
        (s_le_centralizer (s8_eq.trans rfl) hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        (e := 10) (by rw [s8, ← s8Q.orderCertificate_eq_card hT.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hT.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num)
        (m := 8) (by norm_num) (hm_of hC f8 (by decide)) c8 d8' hY hxY
        (fun y hy hy1 => by simpa [xs, f24, f60, f4] using hf y hy hy1)

end Census

end CFSG.ComponentClassification.RankTwoClassical.ExcO8W
