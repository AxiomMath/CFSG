module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Cert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcQuot
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcU6

open Subgroup CFSG.EvenSmallLie.UnitarySix CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.M12Cover CFSG.Fischer

theorem fixCount_eq_ncard (g : Equiv.Perm (Fin 693)) :
    fixCount g = {p : Fin 693 | g p = p}.ncard :=
  (ncard_fixed g).symm

theorem fixCount_conj (c g : Equiv.Perm (Fin 693)) : fixCount (c * g * c⁻¹) = fixCount g := by
  rw [fixCount_eq_ncard, fixCount_eq_ncard, ncard_fixed_conj]

theorem fixCount_one : fixCount 1 = 693 := by
  rw [fixCount_eq_ncard]
  simp [Set.ncard_univ]

theorem ne_one_of_fixCount {g : Equiv.Perm (Fin 693)} (h : fixCount g ≠ 693) : g ≠ 1 :=
  fun h1 => h (h1 ▸ fixCount_one)

theorem point_facts :
    x2 ∈ uA ∧ x3 ∈ uA ∧ fixCount x2 = 53 ∧ fixCount x3 = 21 ∧ fixCount j1 = 181 := by
  have h := census_point_check
  simp only [censusPointCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨(aQ.sift_eq_true_iff_mem_original aQ_valid _).1 h1,
    (aQ.sift_eq_true_iff_mem_original aQ_valid _).1 h2, h3, h4, h5⟩

theorem fixCount_j :
    fixCount j1 = 181 ∧ fixCount j2 = 53 ∧ fixCount j3 = 21 := by
  obtain ⟨-, -, -, -, -, -, -, hf1, hf2, hf3⟩ := orbit_facts
  exact ⟨(fixCount_eq_ncard _).trans hf1, (fixCount_eq_ncard _).trans hf2,
    (fixCount_eq_ncard _).trans hf3⟩

theorem fixCount_of_mem_conjClass
    {r x : Equiv.Perm (Fin 693)} (hr : r ∈ uA) (hr1 : r ≠ 1) (hx : x ∈ conjClass uK r) :
    fixCount x = fixCount r := by
  rw [fixCount_eq_ncard, fixCount_eq_ncard]
  exact (conjClass_facts hr hr1 x hx).2

theorem exists_conj_of_mem_conjClass
    {r x : Equiv.Perm (Fin 693)} (hx : x ∈ conjClass uK r) : ∃ k ∈ T46, k * r * k⁻¹ = x := by
  obtain ⟨k, hk, hkx⟩ := hx
  exact ⟨k, uK_le_T46 hk, hkx.symm⟩

theorem conj_of_mem_uA
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ uA) (hx1 : x ≠ 1) :
    (fixCount x = 181 ∧ ∃ k ∈ T46, k * j1 * k⁻¹ = x) ∨
      (fixCount x = 53 ∧ ∃ k ∈ T46, k * j2 * k⁻¹ = x) ∨
      (fixCount x = 21 ∧ ∃ k ∈ T46, k * j3 * k⁻¹ = x) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -⟩ := orbit_facts
  obtain ⟨f1, f2, f3⟩ := fixCount_j
  obtain ⟨-, -, -, -, ho1, ho2, ho3, -, -, -⟩ := orbit_facts
  have hne : ∀ g : Equiv.Perm (Fin 693), orderOf g = 2 → g ≠ 1 := fun g hg h => by
    rw [h, orderOf_one] at hg
    exact absurd hg (by norm_num)
  rcases korbits.1 x hx hx1 with h | h | h
  · exact Or.inl ⟨(fixCount_of_mem_conjClass j1_mem (hne _ ho1) h).trans f1,
      exists_conj_of_mem_conjClass h⟩
  · exact Or.inr (Or.inl ⟨(fixCount_of_mem_conjClass j2_mem (hne _ ho2) h).trans f2,
      exists_conj_of_mem_conjClass h⟩)
  · exact Or.inr (Or.inr ⟨(fixCount_of_mem_conjClass j3_mem (hne _ ho3) h).trans f3,
      exists_conj_of_mem_conjClass h⟩)

theorem conj_j2_x2 :
    ∃ k ∈ T46, k * j2 * k⁻¹ = x2 := by
  obtain ⟨hx2, -, h53, -, -⟩ := point_facts
  rcases conj_of_mem_uA hx2 (ne_one_of_fixCount (by rw [h53]; norm_num)) with
    ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rw [h53] at h
    exact absurd h (by norm_num)
  · exact h
  · rw [h53] at h
    exact absurd h (by norm_num)

theorem conj_j3_x3 :
    ∃ k ∈ T46, k * j3 * k⁻¹ = x3 := by
  obtain ⟨-, hx3, -, h21, -⟩ := point_facts
  rcases conj_of_mem_uA hx3 (ne_one_of_fixCount (by rw [h21]; norm_num)) with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · rw [h21] at h
    exact absurd h (by norm_num)
  · rw [h21] at h
    exact absurd h (by norm_num)
  · exact h

theorem conj_classes
    {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46)
    (ho : orderOf t = 2) :
    (fixCount t = 181 ∧ ∃ g ∈ T46, g * t * g⁻¹ = j1) ∨
      (fixCount t = 53 ∧ ∃ g ∈ T46, g * t * g⁻¹ = x2) ∨
      (fixCount t = 21 ∧ ∃ g ∈ T46, g * t * g⁻¹ = x3) := by
  obtain ⟨f1, f2, f3⟩ := fixCount_j
  obtain ⟨g, hg, h⟩ := involution_classes ht ho
  have hfc : fixCount t = fixCount (g * t * g⁻¹) := (fixCount_conj g t).symm
  rcases h with h | h | h
  · exact Or.inl ⟨by rw [hfc, h, f1], g, hg, h⟩
  · obtain ⟨k, hk, hkx⟩ := conj_j2_x2
    refine Or.inr (Or.inl ⟨by rw [hfc, h, f2], k * g, T46.mul_mem hk hg, ?_⟩)
    rw [← hkx, ← h]
    group
  · obtain ⟨k, hk, hkx⟩ := conj_j3_x3
    refine Or.inr (Or.inr ⟨by rw [hfc, h, f3], k * g, T46.mul_mem hk hg, ?_⟩)
    rw [← hkx, ← h]
    group

theorem alphabet_mem :
    ∀ g ∈ alphabet, g ∈ T46 := by
  intro g hg
  simp only [alphabet, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg | hg
  · exact u62Letters_mem g hg
  · exact uA_le_T46 (aGens_mem g hg)
  · exact uK_le_T46 (kGens_mem g hg)
  · exact uT_le_T46 (tGens_mem g hg)
  · rw [hg]
    exact u62W_mem _
  · rw [hg]
    exact u62W_mem _

theorem maskProd_mem {X : Subgroup (Equiv.Perm (Fin 693))} :
    ∀ (cur : List (Equiv.Perm (Fin 693))) (m : ℕ), (∀ g ∈ cur, g ∈ X) → maskProd cur m ∈ X
  | [], _, _ => X.one_mem
  | g :: gs, m, h => by
    rw [maskProd]
    refine X.mul_mem ?_ (maskProd_mem gs (m / 2) fun x hx => h x (List.mem_cons_of_mem _ hx))
    split_ifs
    · exact h g List.mem_cons_self
    · exact X.one_mem

theorem badState_eq_false
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : SqClosed T46 X)
    {forbid : List ℕ} (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ∉ forbid)
    {cur : List (Equiv.Perm (Fin 693))} (hcur : ∀ g ∈ cur, g ∈ X) :
    badState forbid cur = false := by
  have h1 : ∀ g ∈ cur, schreierPermEq (g * g) 1 = true := fun g hg => by
    rw [schreierPermEq_eq_true_iff, ← sq]
    exact hX.sq_eq_one g (hcur g hg)
  have h2 : ∀ g ∈ cur, ∀ h ∈ cur, schreierPermEq (g * h) (h * g) = true := fun g hg h hh => by
    rw [schreierPermEq_eq_true_iff]
    exact hX.mul_comm (hcur g hg) (hcur h hh)
  have h3 : ∀ m, (!schreierPermEq (tab (maskProd cur m)) 1 &&
      forbid.contains (fixCount (tab (maskProd cur m)))) = false := fun m => by
    rw [tab_eq]
    by_cases hp1 : maskProd cur m = 1
    · rw [hp1]
      have : schreierPermEq (1 : Equiv.Perm (Fin 693)) 1 = true :=
        (schreierPermEq_eq_true_iff _ _).2 rfl
      rw [this]
      rfl
    · have := hf _ (maskProd_mem cur m hcur) hp1
      simp [this]
  unfold badState
  rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.any_eq_false]
    intro g hg
    simp [h1 g hg]
  · rw [List.any_eq_false]
    intro g hg
    rw [Bool.not_eq_true, List.any_eq_false]
    intro h hh
    simp [h2 g hg h hh]
  · rw [List.any_eq_false]
    intro m _
    rw [h3 m]
    exact Bool.false_ne_true

theorem derivCheck_eq_false
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : SqClosed T46 X) {forbid : List ℕ}
    (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ∉ forbid) :
    ∀ (steps : List (ℕ × List ℤ × ℕ)) (cur : List (Equiv.Perm (Fin 693))),
      (∀ g ∈ cur, g ∈ X) → derivCheck forbid cur steps = false
  | [], cur, hcur => by
    rw [derivCheck]
    exact badState_eq_false hX hf hcur
  | (m, w, i) :: rest, cur, hcur => by
    rw [derivCheck, badState_eq_false hX hf hcur, Bool.false_or]
    dsimp only
    simp only [Bool.and_eq_false_iff]
    by_cases h1 : schreierPermEq (tab (maskProd cur m)) 1 = true
    · exact Or.inl (Or.inl (Or.inl (by simp [h1])))
    by_cases h2 : schreierPermEq (tab (evalCodes alphabet w) * tab (maskProd cur m))
        (tab (maskProd cur m) * tab (evalCodes alphabet w)) = true
    · by_cases h3 : i < cur.length
      · refine Or.inr (derivCheck_eq_false hX hf rest _ fun g hg => ?_)
        rcases List.mem_append.1 hg with hg | hg
        · exact hcur g hg
        · rw [List.mem_singleton] at hg
          rw [hg]
          simp only [tab_eq] at h1 h2 ⊢
          have hp := maskProd_mem cur m hcur
          have hp1 : maskProd cur m ≠ 1 := fun h => h1 (by rw [h, schreierPermEq_eq_true_iff])
          have hc : evalCodes alphabet w ∈ T46 := evalCodes_mem _ alphabet_mem w
          have hcw := (schreierPermEq_eq_true_iff _ _).1 h2
          have hb : cur.getD i 1 ∈ X := by
            rw [List.getD_eq_getElem _ _ h3]
            exact hcur _ (List.getElem_mem h3)
          have := hX.sq_conj_mem _ hp hp1 _ hc hcw _ hb
          rw [← sq]
          exact this
      · exact Or.inl (Or.inr (by simpa using h3))
    · exact Or.inl (Or.inl (Or.inr (by simpa using h2)))

abbrev s2 : Subgroup (Equiv.Perm (Fin 693)) := s2Q.originalSubgroup

abbrev s3 : Subgroup (Equiv.Perm (Fin 693)) := s3Q.originalSubgroup

theorem chain_facts :
    ValidSchreier s2Q ∧ s2Q.orderCertificate = 16384 ∧ ValidSchreier s3Q ∧
      s3Q.orderCertificate = 4096 ∧ (∀ g ∈ s2Gens, g * x2 = x2 * g) ∧
      ∀ g ∈ s3Gens, g * x3 = x3 * g := by
  have h := census_chain_check
  simp only [censusChainCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    schreierPermEq_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem s2_eq : s2 = Subgroup.closure {g | g ∈ s2Gens} := by
  rw [s2, s2Q, certificate_originalSubgroup]

theorem s3_eq : s3 = Subgroup.closure {g | g ∈ s3Gens} := by
  rw [s3, s3Q, certificate_originalSubgroup]

theorem s2Gens_mem : ∀ g ∈ s2Gens, g ∈ s2 := fun g hg => by
  rw [s2_eq]
  exact Subgroup.subset_closure hg

theorem s3Gens_mem : ∀ g ∈ s3Gens, g ∈ s3 := fun g hg => by
  rw [s3_eq]
  exact Subgroup.subset_closure hg

theorem s2_le_uS : s2 ≤ uS := by
  rw [s2_eq]
  refine closure_le_of_mem fun g hg => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [tab_eq]
  exact evalCodes_mem _ sGens_mem w

theorem s3_le_uS : s3 ≤ uS := by
  rw [s3_eq]
  refine closure_le_of_mem fun g hg => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  rw [tab_eq]
  exact evalCodes_mem _ sGens_mem w

theorem s2_le_centralizer :
    s2 ≤ Subgroup.centralizer {x2} := by
  rw [s2_eq]
  refine closure_le_of_mem fun g hg => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact chain_facts.2.2.2.2.1 g hg

theorem s3_le_centralizer :
    s3 ≤ Subgroup.centralizer {x3} := by
  rw [s3_eq]
  refine closure_le_of_mem fun g hg => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact chain_facts.2.2.2.2.2 g hg

theorem card_s2 :
    Nat.card s2 = 16384 := by
  rw [← s2Q.orderCertificate_eq_card chain_facts.1, chain_facts.2.1]

theorem card_s3 :
    Nat.card s3 = 4096 := by
  rw [← s3Q.orderCertificate_eq_card chain_facts.2.2.1, chain_facts.2.2.2.1]

abbrev sSize (r : Equiv.Perm (Fin 693)) : ℕ :=
  (conjClosure 693 (listTables sGens) (listTables (sGens.map (·⁻¹))) (toTable r) 100).1.size

theorem sylow_cover :
    (∀ u ∈ uS, orderOf u = 2 → ∃ r ∈ sReps, ∃ c ∈ uS, u = c * r * c⁻¹) ∧
      ∀ r ∈ sReps, (fixCount r = 53 → 2 ≤ (conjClass uS r).ncard) ∧
        (fixCount r = 21 → 8 ≤ (conjClass uS r).ncard) := by
  obtain ⟨h1, -, -, -, -, h6⟩ := sylow_facts
  refine ⟨h1, fun r hr => ?_⟩
  rw [fixCount_eq_ncard]
  exact h6 r hr

theorem zip_map_self {α β : Type*} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

theorem size_facts :
    ∀ r ∈ sReps, (fixCount r = 53 → 2 ≤ sSize r) ∧ (fixCount r = 21 → 8 ≤ sSize r) := by
  have h := census_size_check
  have e : sReps.zip (repSizes 693 (listTables sGens) (listTables (sGens.map (·⁻¹)))
      (sReps.map toTable) 100) = sReps.map fun r => (r, sSize r) := by
    rw [repSizes, List.map_map, zip_map_self]
    rfl
  rw [censusSizeCheck, e, List.all_map, List.all_eq_true] at h
  intro r hr
  have := h r hr
  simp only [Function.comp, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at this
  exact ⟨fun h53 => this.1.resolve_left (not_not.2 h53),
    fun h21 => this.2.resolve_left (not_not.2 h21)⟩

theorem reps_facts :
    (∀ u ∈ s2, orderOf u = 2 → ∃ r ∈ r2Reps, ∃ c ∈ s2, u = c * r * c⁻¹) ∧
      ∀ u ∈ s3, orderOf u = 2 → ∃ r ∈ r3Reps, ∃ c ∈ s3, u = c * r * c⁻¹ := by
  have h := census_cover_check
  simp only [censusCoverCheck, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hord : ∀ g : Equiv.Perm (Fin 693), ordTest 693 2 (toTable g) = true → orderOf g = 2 :=
    fun g hg => (ordTest_iff perm_faithful (rep_toTable hn693 g) (by norm_num)).1 hg
  refine ⟨(exists_conj_of_repsOK_normalizing hn693 s2Q chain_facts.1 s2
    (fun c hc h hh => s2.mul_mem (s2.mul_mem hc hh) (s2.inv_mem hc))
    (listTables_spec hn693 s2Gens_mem) (by norm_num) r2Reps (fun r hr => ⟨?_, hord r (h2 r hr)⟩)
    600 h1).1, (exists_conj_of_repsOK_normalizing hn693 s3Q chain_facts.2.2.1 s3
    (fun c hc h hh => s3.mul_mem (s3.mul_mem hc hh) (s3.inv_mem hc))
    (listTables_spec hn693 s3Gens_mem) (by norm_num) r3Reps (fun r hr => ⟨?_, hord r (h4 r hr)⟩)
    600 h3).1⟩
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem _ s2Gens_mem w
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem _ s3Gens_mem w

theorem exists_deriv_of_zip {reps : List (Equiv.Perm (Fin 693))}
    {ds : List (List (ℕ × List ℤ × ℕ))} {x : Equiv.Perm (Fin 693)} {forbid : List ℕ}
    (hlen : ds.length = reps.length)
    (hall : (reps.zip ds).all (fun p => schreierPermEq p.1 x || derivCheck forbid [x, p.1] p.2) =
      true) :
    ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck forbid [x, r] st = true := by
  intro r hr hrx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < (reps.zip ds).length := by simp [hlen, hi]
  have hmem : (reps.zip ds)[i] ∈ reps.zip ds := List.getElem_mem hi'
  have h := List.all_eq_true.1 hall _ hmem
  rw [List.getElem_zip] at h
  have hne : schreierPermEq reps[i] x = false := by
    rw [Bool.eq_false_iff, ne_eq, schreierPermEq_eq_true_iff]
    exact hrx
  rw [hne, Bool.false_or] at h
  exact ⟨_, h⟩

theorem deriv_facts :
    (∀ r ∈ sReps, r ≠ j1 → ∃ st, derivCheck [] [j1, r] st = true) ∧
      (∀ r ∈ r2Reps, r ≠ x2 → ∃ st, derivCheck [181] [x2, r] st = true) ∧
      ∀ r ∈ r3Reps, r ≠ x3 → ∃ st, derivCheck [181, 53] [x3, r] st = true := by
  have h := census_deriv_check
  simp only [censusDerivCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨exists_deriv_of_zip h1 h4, exists_deriv_of_zip h2 h5, exists_deriv_of_zip h3 h6⟩

theorem isPGroup_of_sq {X : Subgroup (Equiv.Perm (Fin 693))} (h : ∀ p ∈ X, p ^ 2 = 1) :
    IsPGroup 2 X := by
  refine IsPGroup.of_exponent_dvd_pow (n := 1) (Monoid.exponent_dvd_of_forall_pow_eq_one ?_)
  intro g
  rw [pow_one]
  exact Subtype.ext (h g g.2)

theorem exists_conj_le_of_card_le {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hmax : ∀ R : Subgroup G, IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    {X : Subgroup G} (hX : IsPGroup 2 X) : ∃ c : G, ∀ x ∈ X, c * x * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hXR⟩ := hX.exists_le_sylow
  obtain ⟨R₂, hSR⟩ := hS.exists_le_sylow
  have hR₂ : (R₂ : Subgroup G) = S :=
    (Subgroup.eq_of_le_of_card_ge hSR (hmax R₂ R₂.isPGroup')).symm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G R R₂
  refine ⟨c, fun x hx => ?_⟩
  have h2 : c * x * c⁻¹ ∈ ((c • R : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨x, hXR hx, rfl⟩
  rw [hc, hR₂] at h2
  exact h2

theorem exists_conj_le_of_card_le' {K S X : Subgroup (Equiv.Perm (Fin 693))} (hSK : S ≤ K)
    (hS : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ K → IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    (hXK : X ≤ K) (hX : IsPGroup 2 X) : ∃ c ∈ K, ∀ x ∈ X, c * x * c⁻¹ ∈ S := by
  have hS' : IsPGroup 2 (S.subgroupOf K) := hS.comap_of_injective K.subtype K.subtype_injective
  have hX' : IsPGroup 2 (X.subgroupOf K) := hX.comap_of_injective K.subtype K.subtype_injective
  have hcardS : Nat.card (S.subgroupOf K) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have hmax' : ∀ R : Subgroup K, IsPGroup 2 R → Nat.card R ≤ Nat.card (S.subgroupOf K) := by
    intro R hR
    rw [hcardS, ← Subgroup.card_map_of_injective K.subtype_injective]
    exact hmax _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) (hR.map K.subtype)
  obtain ⟨c, hc⟩ := exists_conj_le_of_card_le hS' hmax' hX'
  refine ⟨c, c.2, fun x hx => ?_⟩
  have := hc ⟨x, hXK hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem exists_conj_le_uS
    {Q : Subgroup (Equiv.Perm (Fin 693))} (hQT : Q ≤ T46) (hQ : IsPGroup 2 Q) :
    ∃ g ∈ T46, ∀ q ∈ Q, g * q * g⁻¹ ∈ uS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 T46 := uS_isPGroup.toSylow not_two_dvd_index_uS
  have hQ' : IsPGroup 2 (Q.subgroupOf T46) :=
    hQ.comap_of_injective T46.subtype T46.subtype_injective
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T46 R S'
  refine ⟨g, g.2, fun q hq => ?_⟩
  have h2 : g * ⟨q, hQT hq⟩ * g⁻¹ ∈ ((g • R : Sylow 2 T46) : Subgroup T46) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hR (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  rw [hg] at h2
  have h3 : g * ⟨q, hQT hq⟩ * g⁻¹ ∈ uS.subgroupOf T46 := by simpa [S'] using h2
  rw [Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem card_le_of_commute
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ T46) (hxo : orderOf x = 2)
    {R : Subgroup (Equiv.Perm (Fin 693))} (hRT : R ≤ T46) (hRx : ∀ r ∈ R, r * x = x * r)
    (hR : IsPGroup 2 R) {m : ℕ}
    (hm : ∀ r ∈ sReps, fixCount r = fixCount x → m ≤ (conjClass uS r).ncard) :
    Nat.card R * m ≤ 32768 := by
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hcomm : ∀ r ∈ R, ∀ k : ℤ, r * x ^ k * r⁻¹ = x ^ k := fun r hr k => by
    have hc : Commute r x := hRx r hr
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  have hnorm : R ≤ Subgroup.normalizer (Subgroup.zpowers x : Set (Equiv.Perm (Fin 693))) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact Subgroup.mem_zpowers_iff.2 ⟨k, (hcomm r hr k).symm⟩
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      calc x ^ k = r⁻¹ * (r * x ^ k * r⁻¹) * r := by group
        _ = r⁻¹ * x ^ k * r := by rw [hcomm r hr k]
        _ = r⁻¹ * (r * y * r⁻¹) * r := by rw [hk]
        _ = y := by group
  have hQ := IsPGroup.to_sup_of_normal_right' hR hz hnorm
  have hQT : R ⊔ Subgroup.zpowers x ≤ T46 := sup_le hRT ((Subgroup.zpowers_le).2 hx)
  obtain ⟨g, hg, hgQ⟩ := exists_conj_le_uS hQT hQ
  set y := g * x * g⁻¹ with hy
  have hyS : y ∈ uS := hgQ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hyo : orderOf y = 2 := (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hxo
  obtain ⟨r, hr, c, hc, hyr⟩ := sylow_cover.1 y hyS hyo
  have hfr : fixCount r = fixCount x := by
    rw [← fixCount_conj c r, ← hyr, hy, fixCount_conj]
  have hmr := hm r hr hfr
  have hcls : conjClass uS y = conjClass uS r := by
    rw [hyr]
    exact conjClass_conj uS hc r
  have hcard := ncard_conjClass_mul_card uS y
  rw [card_uS, hcls] at hcard
  have hle : Nat.card R ≤ Nat.card (centralizerIn uS y) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨hgQ q (Subgroup.mem_sup_left hq), ?_⟩
    change g * q * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * q * g⁻¹)
    have := hRx q hq
    calc g * q * g⁻¹ * (g * x * g⁻¹) = g * (q * x) * g⁻¹ := by group
      _ = g * (x * q) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * q * g⁻¹) := by group
  calc Nat.card R * m ≤ Nat.card (centralizerIn uS y) * (conjClass uS r).ncard :=
        Nat.mul_le_mul hle hmr
    _ = 32768 := by rw [mul_comm]; exact hcard

theorem false_of_pair
    {x : Equiv.Perm (Fin 693)} {S : Subgroup (Equiv.Perm (Fin 693))}
    {reps : List (Equiv.Perm (Fin 693))} {forbid : List ℕ}
    (hS : S ≤ T46 ⊓ Subgroup.centralizer {x}) (hS2 : IsPGroup 2 S)
    (hmax : ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ T46 ⊓ Subgroup.centralizer {x} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card S)
    (hcov : ∀ u ∈ S, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ S, u = c * r * c⁻¹)
    (hder : ∀ r ∈ reps, r ≠ x → ∃ st, derivCheck forbid [x, r] st = true)
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : SqClosed T46 X) (hx : x ∈ X)
    (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ∉ forbid) : False := by
  have hXC : X ≤ T46 ⊓ Subgroup.centralizer {x} := fun y hy =>
    ⟨hX.le hy, Subgroup.mem_centralizer_singleton_iff.2 (hX.mul_comm hy hx)⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_card_le' hS hS2 hmax hXC (isPGroup_of_sq hX.sq_eq_one)
  have hcx : c * x * c⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hcC.2, mul_inv_cancel_right]
  have hX₂ : SqClosed T46 (X.map (MulAut.conj c).toMonoidHom) := hX.conj hcC.1
  have hx₂ : x ∈ X.map (MulAut.conj c).toMonoidHom := ⟨x, hx, hcx⟩
  have hX₂S : X.map (MulAut.conj c).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  have hf₂ : ∀ y ∈ X.map (MulAut.conj c).toMonoidHom, y ≠ 1 → fixCount y ∉ forbid := by
    rintro _ ⟨y, hy, rfl⟩ hy1
    change fixCount (c * y * c⁻¹) ∉ forbid
    rw [fixCount_conj]
    exact hf y hy fun h => hy1 (by rw [h, map_one])
  obtain ⟨y, hy, hy1, hyx⟩ : ∃ y ∈ X.map (MulAut.conj c).toMonoidHom, y ≠ 1 ∧ y ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : ((X.map (MulAut.conj c).toMonoidHom : Subgroup (Equiv.Perm (Fin 693))) :
        Set (Equiv.Perm (Fin 693))) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have h4 := hX₂.four_le
    have h2 : ({1, x} : Set (Equiv.Perm (Fin 693))).ncard ≤ 2 := by
      calc ({1, x} : Set (Equiv.Perm (Fin 693))).ncard
          ≤ ({x} : Set (Equiv.Perm (Fin 693))).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq] at h3
    change Nat.card (X.map (MulAut.conj c).toMonoidHom) ≤ _ at h3
    omega
  have hyo : orderOf y = 2 := orderOf_eq_prime (hX₂.sq_eq_one y hy) hy1
  obtain ⟨r, hr, s, hs, hysr⟩ := hcov y (hX₂S hy) hyo
  have hsx : s⁻¹ * x * s⁻¹⁻¹ = x := by
    have e := Subgroup.mem_centralizer_singleton_iff.1 (hS hs).2
    calc s⁻¹ * x * s⁻¹⁻¹ = s⁻¹ * (x * s) := by group
      _ = s⁻¹ * (s * x) := by rw [e]
      _ = x := by group
  have hX₃ := hX₂.conj (T46.inv_mem (hS hs).1)
  have hx₃ : x ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
    ⟨x, hx₂, hsx⟩
  have hr₃ : r ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by
    refine ⟨y, hy, ?_⟩
    change s⁻¹ * y * s⁻¹⁻¹ = r
    rw [hysr]
    group
  have hf₃ : ∀ z ∈ (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom,
      z ≠ 1 → fixCount z ∉ forbid := by
    rintro _ ⟨z, hz, rfl⟩ hz1
    change fixCount (s⁻¹ * z * s⁻¹⁻¹) ∉ forbid
    rw [fixCount_conj]
    exact hf₂ z hz fun h => hz1 (by rw [h, map_one])
  have hsx' : s * x * s⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (hS hs).2, mul_inv_cancel_right]
  have hrx : r ≠ x := fun h => hyx (by rw [hysr, h, hsx'])
  obtain ⟨st, hst⟩ := hder r hr hrx
  have hfalse := derivCheck_eq_false hX₃ hf₃ st [x, r] (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hx₃
    · exact hr₃)
  rw [hst] at hfalse
  exact Bool.noConfusion hfalse

theorem false_of_j1
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : SqClosed T46 X)
    (hx : j1 ∈ X) : False := by
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ T46 ⊓ Subgroup.centralizer {j1} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card uS := by
    intro R hR hR2
    obtain ⟨g, -, hg⟩ := exists_conj_le_uS (fun r hr => (hR hr).1) hR2
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨q, hq, rfl⟩
    exact hg q hq
  exact false_of_pair (forbid := [])
    (fun s hs => ⟨uS_le_T46 hs,
      Subgroup.mem_centralizer_singleton_iff.2 (j1_comm_uS s hs).symm⟩)
    (IsPGroup.of_card (n := 15) (by rw [card_uS]; norm_num)) hmax sylow_cover.1 deriv_facts.1
    hX hx fun _ _ _ => List.not_mem_nil

theorem x2_facts :
    x2 ∈ T46 ∧ orderOf x2 = 2 ∧ x3 ∈ T46 ∧ orderOf x3 = 2 := by
  obtain ⟨h2, h3, f2, f3, -⟩ := point_facts
  exact ⟨uA_le_T46 h2, orderOf_eq_prime (uA_sq x2 h2) (ne_one_of_fixCount (by rw [f2]; norm_num)),
    uA_le_T46 h3, orderOf_eq_prime (uA_sq x3 h3) (ne_one_of_fixCount (by rw [f3]; norm_num))⟩

theorem false_of_x2
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : SqClosed T46 X)
    (hx : x2 ∈ X) (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ≠ 181) : False := by
  obtain ⟨hxT, hxo, -, -⟩ := x2_facts
  obtain ⟨-, -, f2, -, -⟩ := point_facts
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ T46 ⊓ Subgroup.centralizer {x2} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card s2 := by
    intro R hR hR2
    have h := card_le_of_commute (m := 2) hxT hxo (fun r hr => (hR hr).1)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hR hr).2) hR2
      (fun r hr hfr => (sylow_cover.2 r hr).1 (hfr.trans f2))
    rw [card_s2]
    omega
  exact false_of_pair (forbid := [181])
    (fun s hs => ⟨uS_le_T46 (s2_le_uS hs), s2_le_centralizer hs⟩)
    (IsPGroup.of_card (n := 14) (by rw [card_s2]; norm_num)) hmax reps_facts.1
    deriv_facts.2.1 hX hx fun y hy hy1 => by simpa using hf y hy hy1

theorem false_of_x3
    {X : Subgroup (Equiv.Perm (Fin 693))} (hX : SqClosed T46 X)
    (hx : x3 ∈ X) (hf : ∀ y ∈ X, y ≠ 1 → fixCount y ≠ 181 ∧ fixCount y ≠ 53) : False := by
  obtain ⟨-, -, hxT, hxo⟩ := x2_facts
  obtain ⟨-, -, -, f3, -⟩ := point_facts
  have hmax : ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ T46 ⊓ Subgroup.centralizer {x3} →
      IsPGroup 2 R → Nat.card R ≤ Nat.card s3 := by
    intro R hR hR2
    have h := card_le_of_commute (m := 8) hxT hxo (fun r hr => (hR hr).1)
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hR hr).2) hR2
      (fun r hr hfr => (sylow_cover.2 r hr).2 (hfr.trans f3))
    rw [card_s3]
    omega
  exact false_of_pair (forbid := [181, 53])
    (fun s hs => ⟨uS_le_T46 (s3_le_uS hs), s3_le_centralizer hs⟩)
    (IsPGroup.of_card (n := 12) (by rw [card_s3]; norm_num)) hmax reps_facts.2
    deriv_facts.2.2 hX hx fun y hy hy1 => by simpa using hf y hy hy1

theorem not_sqClosed_T46
    (X : Subgroup (Equiv.Perm (Fin 693))) :
    ¬ SqClosed T46 X := by
  intro hX
  have hinv : ∀ y ∈ X, y ≠ 1 → y ∈ T46 ∧ orderOf y = 2 := fun y hy hy1 =>
    ⟨hX.le hy, orderOf_eq_prime (hX.sq_eq_one y hy) hy1⟩
  have hconj_ne : ∀ {g z : Equiv.Perm (Fin 693)}, g * z * g⁻¹ ≠ 1 → z ≠ 1 := fun h hz =>
    h (by rw [hz, mul_one, mul_inv_cancel])
  by_cases h1 : ∃ y ∈ X, y ≠ 1 ∧ fixCount y = 181
  · obtain ⟨y, hy, hy1, hfy⟩ := h1
    obtain ⟨hyT, hyo⟩ := hinv y hy hy1
    rcases conj_classes hyT hyo with ⟨-, g, hg, hgy⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact false_of_j1 (hX.conj hg) ⟨y, hy, hgy⟩
    · rw [hfy] at h
      exact absurd h (by norm_num)
    · rw [hfy] at h
      exact absurd h (by norm_num)
  push Not at h1
  by_cases h2 : ∃ y ∈ X, y ≠ 1 ∧ fixCount y = 53
  · obtain ⟨y, hy, hy1, hfy⟩ := h2
    obtain ⟨hyT, hyo⟩ := hinv y hy hy1
    rcases conj_classes hyT hyo with ⟨h, -⟩ | ⟨-, g, hg, hgy⟩ | ⟨h, -⟩
    · rw [hfy] at h
      exact absurd h (by norm_num)
    · refine false_of_x2 (hX.conj hg) ⟨y, hy, hgy⟩ ?_
      rintro _ ⟨z, hz, rfl⟩ hz1
      change fixCount (g * z * g⁻¹) ≠ 181
      rw [fixCount_conj]
      exact h1 z hz (hconj_ne hz1)
    · rw [hfy] at h
      exact absurd h (by norm_num)
  push Not at h2
  have hne : X ≠ ⊥ := by
    intro h
    have h4 := hX.four_le
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨hyT, hyo⟩ := hinv y hy hy1'
  rcases conj_classes hyT hyo with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, g, hg, hgy⟩
  · exact h1 y hy hy1' h
  · exact h2 y hy hy1' h
  · refine false_of_x3 (hX.conj hg) ⟨y, hy, hgy⟩ ?_
    rintro _ ⟨z, hz, rfl⟩ hz1
    change fixCount (g * z * g⁻¹) ≠ 181 ∧ fixCount (g * z * g⁻¹) ≠ 53
    rw [fixCount_conj]
    exact ⟨h1 z hz (hconj_ne hz1), h2 z hz (hconj_ne hz1)⟩

end CFSG.ComponentClassification.RankTwoClassical.ExcU6

namespace CFSG.ComponentClassification.RankTwoClassical

theorem exc213_PSU_six :
    Exc213 .PSU 6 := by
  intro H _ _ _ _ hL P hP
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hL
  exact ExcU6.not_sqClosed_T46 _ (hP.sqClosed_map.map_mulEquiv e)

