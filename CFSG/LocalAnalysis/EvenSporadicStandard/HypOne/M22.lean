module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TMu
public import Certificates.Certificate24274

public section

namespace CFSG.EvenSporadicStandard.HypOne.M22

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates CFSG.QuasithinUnique.Setup.X1

theorem involution_cover :
    (∀ u, 1⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      ∃ r ∈ [m22Rep1], ∃ c ∈ NativeSporadic.M22, u = c * r * c⁻¹) ∧
    ∀ r ∈ [m22Rep1], (conjClosure 22 (pairTables m22gA m22gB)
      (pairTables m22gA⁻¹ m22gB⁻¹) (toTable r) 2000).1.size ≤
        (conjClass NativeSporadic.M22 r).ncard := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  rw [m22InvReps_eq] at hok
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have h := exists_conj_of_repsOK hn m22Certificate m22Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m22Rep1] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok
  rw [m22Certificate_originalSubgroup] at h
  exact h

theorem centralizerIn_rep1 :
    centralizerIn NativeSporadic.M22 m22Rep1 = m22CentQ1.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m22_rep_data1
  obtain ⟨-, hsz, -⟩ := m22_oddcore_cover
  rw [m22InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m22Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (involution_cover.2 _ (by simp)) ?_
  rw [hsz, hKc, m22_card]

theorem outer_cover :
    (∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      ∃ r ∈ [m22OutRep1, m22OutRep2], ∃ c ∈ NativeSporadic.M22, u = c * r * c⁻¹) ∧
    ∀ r ∈ [m22OutRep1, m22OutRep2], (conjClosure 22 (pairTables m22gA m22gB)
      (pairTables m22gA⁻¹ m22gB⁻¹) (toTable r) 2000).1.size ≤
        (conjClass NativeSporadic.M22 r).ncard := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m22_outer_cover
  rw [m22OutReps_eq] at hok
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  have h := exists_conj_of_repsOK hn m22Certificate m22Certificate_check
    (pairTables_spec hn hA hB) m22Delta hg₀ (by norm_num) [m22OutRep1, m22OutRep2]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 2000 hok
  rw [m22Certificate_originalSubgroup] at h
  exact h

theorem centralizerIn_o1 :
    centralizerIn NativeSporadic.M22 m22OutRep1 = m22OutCentQ1.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m22_out_rep_data1
  obtain ⟨-, hsz, -⟩ := m22_outer_cover
  rw [m22OutReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m22Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (outer_cover.2 _ (by simp)) ?_
  rw [hsz.1, hKc, m22_card]

theorem centralizerIn_o2 :
    centralizerIn NativeSporadic.M22 m22OutRep2 = m22OutCentQ2.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m22_out_rep_data2
  obtain ⟨-, hsz, -⟩ := m22_outer_cover
  rw [m22OutReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m22Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (outer_cover.2 _ (by simp)) ?_
  rw [hsz.2, hKc, m22_card]

theorem fourClassesLarge_centralizerIn_M :
    ∀ v ∈ NativeSporadic.M22, orderOf v = 2 →
      FourClassesLarge (centralizerIn NativeSporadic.M22 v) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  refine fourClassesLarge_centralizerIn_of_reps _ [m22Rep1] ?_ ?_
  · intro v hv h2
    exact involution_cover.1 v (by rwa [inv_one, one_mul]) h2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨hc, -, -, -⟩ := m22_oddcore_cent1
    rw [centralizerIn_rep1]
    exact fourClassesLarge_of_fourCheck hn m22CentQ1 hc centGens1 (fun g hg => by
      rw [m22CentQ1, certificate_originalSubgroup]
      exact Subgroup.subset_closure hg) innerFourWords 4000 Certificates.certificate24274.1

theorem A_index
    {x y : Equiv.Perm (Fin 22)} (hx : x ∈ m22A) (hxM : x ∉ NativeSporadic.M22) (hy : y ∈ m22A)
    (hyM : y ∉ NativeSporadic.M22) : x⁻¹ * y ∈ NativeSporadic.M22 := by
  have hx' := (mem_m22A.1 hx).resolve_left hxM
  have hy' := (mem_m22A.1 hy).resolve_left hyM
  have : x⁻¹ * y = (m22Delta⁻¹ * x)⁻¹ * (m22Delta⁻¹ * y) := by group
  rw [this]
  exact mul_mem (inv_mem hx') hy'

theorem outRep_mem
    {r : Equiv.Perm (Fin 22)} (hr : m22Delta⁻¹ * r ∈ m22Certificate.originalSubgroup) :
    r ∈ m22A ∧ r ∉ NativeSporadic.M22 := by
  rw [m22Certificate_originalSubgroup] at hr
  refine ⟨mem_m22A.2 (Or.inr hr), fun hrM => ?_⟩
  apply delta_not_mem
  have : m22Delta = r * (m22Delta⁻¹ * r)⁻¹ := by group
  rw [this]
  exact mul_mem hrM (inv_mem hr)

theorem autData_parts :
    ValidSchreier kChainA ∧ ValidSchreier kChainO1 ∧ ValidSchreier kChainO2 ∧
      commT 22 (toTable (evalCodes gensA zWordA)) (toTable m22gA) = true ∧
      m22Certificate.sift (evalCodes gensA zWordA) 0 = false ∧
      fourCheck 22 kChainA kGensA kFourWordsA 4000 = true ∧
      fourCheck 22 kChainO1 kGensO1 kFourWordsO1 4000 = true ∧
      fourCheck 22 kChainO2 kGensO2 kFourWordsO2 4000 = true := by
  have h := Certificates.certificate24274.2.1
  simp only [autData, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem zA_mem : evalCodes gensA zWordA ∈ m22A :=
  evalCodes_mem _ (fun g hg => Subgroup.subset_closure (by
    simp only [gensA, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp)) _

theorem zA_not_mem :
    evalCodes gensA zWordA ∉ NativeSporadic.M22 := by
  rw [← m22Certificate_originalSubgroup,
    ← (m22Certificate.schreier_chain_order m22Certificate_check).2.2.2.1,
    (autData_parts).2.2.2.2.1]
  exact Bool.false_ne_true

theorem zA_comm :
    evalCodes gensA zWordA * m22Rep1 = m22Rep1 * evalCodes gensA zWordA := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have h := (commT_iff (rep_toTable hn (evalCodes gensA zWordA)) (rep_toTable hn m22gA)).1
    (autData_parts).2.2.2.1
  have e : m22Rep1 = m22gA := by simp [m22Rep1, m22InvReps, m22InvRepWords, evalCodes]
  rw [e]
  exact h

theorem centralizerIn_A_rep1 :
    centralizerIn m22A m22Rep1 = kChainA.originalSubgroup := by
  have hD : centralizerIn NativeSporadic.M22 m22Rep1 =
      Subgroup.closure {g | g ∈ centGens1} := by
    rw [centralizerIn_rep1, m22CentQ1, certificate_originalSubgroup]
    rfl
  have hz : evalCodes gensA zWordA ∈ centralizerIn m22A m22Rep1 :=
    mem_centralizerIn.2 ⟨zA_mem, zA_comm⟩
  rw [centralizerIn_eq_closure m22A NativeSporadic.M22 m22_le_A (fun x hx hxM y hy hyM =>
    A_index hx hxM hy hyM) m22Rep1 _ centGens1 hD hz zA_not_mem, kChainA,
    certificate_originalSubgroup]
  rfl

theorem centralizerIn_A_o1 :
    centralizerIn m22A m22OutRep1 = kChainO1.originalSubgroup := by
  obtain ⟨hr, -, -, -, -⟩ := m22_out_rep_data1
  obtain ⟨hmem, hnot⟩ := outRep_mem hr
  have hD : centralizerIn NativeSporadic.M22 m22OutRep1 =
      Subgroup.closure {g | g ∈ m22OutCentWords1.map (evalCodes gensM)} := by
    rw [centralizerIn_o1, m22OutCentQ1, certificate_originalSubgroup]
    rfl
  have hz : m22OutRep1 ∈ centralizerIn m22A m22OutRep1 := mem_centralizerIn.2 ⟨hmem, rfl⟩
  rw [centralizerIn_eq_closure m22A NativeSporadic.M22 m22_le_A (fun x hx hxM y hy hyM =>
    A_index hx hxM hy hyM) m22OutRep1 m22OutRep1 _ hD hz hnot, kChainO1,
    certificate_originalSubgroup]
  rfl

theorem centralizerIn_A_o2 :
    centralizerIn m22A m22OutRep2 = kChainO2.originalSubgroup := by
  obtain ⟨hr, -, -, -, -⟩ := m22_out_rep_data2
  obtain ⟨hmem, hnot⟩ := outRep_mem hr
  have hD : centralizerIn NativeSporadic.M22 m22OutRep2 =
      Subgroup.closure {g | g ∈ m22OutCentWords2.map (evalCodes gensM)} := by
    rw [centralizerIn_o2, m22OutCentQ2, certificate_originalSubgroup]
    rfl
  have hz : m22OutRep2 ∈ centralizerIn m22A m22OutRep2 := mem_centralizerIn.2 ⟨hmem, rfl⟩
  rw [centralizerIn_eq_closure m22A NativeSporadic.M22 m22_le_A (fun x hx hxM y hy hyM =>
    A_index hx hxM hy hyM) m22OutRep2 m22OutRep2 _ hD hz hnot, kChainO2,
    certificate_originalSubgroup]
  rfl

theorem fourClassesLarge_A_reps :
    FourClassesLarge (centralizerIn m22A m22Rep1) ∧
      FourClassesLarge (centralizerIn m22A m22OutRep1) ∧
      FourClassesLarge (centralizerIn m22A m22OutRep2) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8⟩ := autData_parts
  rw [centralizerIn_A_rep1, centralizerIn_A_o1, centralizerIn_A_o2]
  refine ⟨fourClassesLarge_of_fourCheck hn kChainA h1 kGensA (fun g hg => ?_) kFourWordsA 4000 h6,
    fourClassesLarge_of_fourCheck hn kChainO1 h2 kGensO1 (fun g hg => ?_) kFourWordsO1 4000 h7,
    fourClassesLarge_of_fourCheck hn kChainO2 h3 kGensO2 (fun g hg => ?_) kFourWordsO2 4000 h8⟩
  · rw [kChainA, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  · rw [kChainO1, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  · rw [kChainO2, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg

theorem A_cover :
    ∀ x ∈ m22A, orderOf x = 2 →
      ∃ r ∈ [m22Rep1, m22OutRep1, m22OutRep2], ∃ c ∈ m22A, x = c * r * c⁻¹ := by
  intro x hx h2
  by_cases hxM : x ∈ NativeSporadic.M22
  · obtain ⟨r, hr, c, hc, e⟩ := involution_cover.1 x (by rwa [inv_one, one_mul]) h2
    refine ⟨r, ?_, c, m22_le_A hc, e⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact Or.inl hr
  · have hmem := (mem_m22A.1 hx).resolve_left hxM
    obtain ⟨r, hr, c, hc, e⟩ := outer_cover.1 x hmem h2
    refine ⟨r, ?_, c, m22_le_A hc, e⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact Or.inr hr

theorem fourClassesLarge_A_centralizerIn :
    ∀ v ∈ m22A, orderOf v = 2 → FourClassesLarge (centralizerIn m22A v) := by
  refine fourClassesLarge_centralizerIn_of_reps _ [m22Rep1, m22OutRep1, m22OutRep2] A_cover ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fourClassesLarge_A_reps.1
  · exact fourClassesLarge_A_reps.2.1
  · exact fourClassesLarge_A_reps.2.2

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.M22 := by
  have hc : Subgroup.center NativeSporadic.M22 = ⊥ := m22_center_eq_bot'
  have hinj := conj_injective_of_center_eq_bot hc
  have hfin : Finite NativeSporadic.M22 := Nat.finite_of_card_ne_zero (by rw [m22_card]; norm_num)
  refine hypothesisOne_of_aut hc (index_dvd_two_of_card_le hinj m22_mulAut_card)
    (fun t ht => m22_inner_oddCore t ht) (fun α h2 hα => m22_outer_oddCore α h2 hα) ?_ ?_
  · intro y hy
    exact FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv NativeSporadic.M22 y)
      (fourClassesLarge_centralizerIn_M y y.2 (by rw [Subgroup.orderOf_coe]; exact hy))
  · intro x hx
    let e : ↥m22A ≃* MulAut S22 := MulEquiv.ofBijective muA muA_bijective
    obtain ⟨a, rfl⟩ := e.surjective x
    have ha : orderOf a = 2 := by rw [← MulEquiv.orderOf_eq e]; exact hx
    refine FourClassesLarge.of_mulEquiv (centralizerEquiv e a).symm ?_
    refine FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv m22A a) ?_
    exact fourClassesLarge_A_centralizerIn a a.2 (by rw [Subgroup.orderOf_coe]; exact ha)

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.M22 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hmem : ∀ w : List ℤ, evalCodes gensM w ∈ NativeSporadic.M22 := fun w =>
    evalCodes_mem _ (by
      intro g hg
      simp only [gensM, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact m22a.2
      · exact m22b.2) w
  have h1 : e1 ∈ NativeSporadic.M22 := hmem wordE1
  have h2 : e2 ∈ NativeSporadic.M22 := hmem wordE2
  have h3 : e3 ∈ NativeSporadic.M22 := hmem wordE3
  exact hasElemAbelianEight_of_e8Check (a := e1) (b := e2) (c := e3) hn
    Certificates.certificate24274.2.2.1 h1 h2 h3

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.M22 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hc : Subgroup.center NativeSporadic.M22 = ⊥ := m22_center_eq_bot'
  let e : ↥m22A ≃* MulAut S22 := MulEquiv.ofBijective muA muA_bijective
  have hdata := Certificates.certificate24274.2.2.2
  simp only [foursData, Bool.and_eq_true] at hdata
  obtain ⟨hf1, hf2⟩ := hdata
  obtain ⟨hr1, -, -, -, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, -, -, -, -⟩ := m22_out_rep_data2
  let ρ1 : ↥m22A := ⟨m22OutRep1, (outRep_mem hr1).1⟩
  let ρ2 : ↥m22A := ⟨m22OutRep2, (outRep_mem hr2).1⟩
  have hl : ∀ w : List ℤ, evalCodes gensM w ∈ NativeSporadic.M22 := fun w =>
    evalCodes_mem _ (by
      intro g hg
      simp only [gensM, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact m22a.2
      · exact m22b.2) w
  refine foursGroupCondition_of_reps [e ρ1, e ρ2] ?_ ?_
  · intro φ hφ hout
    obtain ⟨a, rfl⟩ := e.surjective φ
    have haa : a * a = 1 := e.injective (by rw [map_mul, hφ, map_one])
    have haM : (a : Equiv.Perm (Fin 22)) ∉ NativeSporadic.M22 := by
      intro ham
      exact hout ⟨a, ham⟩ (muA_of_mem ⟨(a : Equiv.Perm (Fin 22)), ham⟩)
    have ha2 : orderOf (a : Equiv.Perm (Fin 22)) = 2 := by
      refine orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, haa, Subgroup.coe_one]) ?_
      intro h1
      exact haM (h1 ▸ NativeSporadic.M22.one_mem)
    obtain ⟨r, hr, c, hc', hcr⟩ := outer_cover.1 a ((mem_m22A.1 a.2).resolve_left haM) ha2
    have hcA : muA ⟨c, m22_le_A hc'⟩ = MulAut.conj (⟨c, hc'⟩ : S22) := muA_of_mem ⟨c, hc'⟩
    have hrA : (a : Equiv.Perm (Fin 22)) = c * r * c⁻¹ := hcr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨e ρ1, by simp, MulAut.conj (⟨c, hc'⟩ : S22), ?_⟩
      have : a = ⟨c, m22_le_A hc'⟩ * ρ1 * ⟨c, m22_le_A hc'⟩⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hrA)
      rw [this, map_mul, map_mul, map_inv]
      show muA _ * _ * (muA _)⁻¹ = _
      rw [hcA]
    · refine ⟨e ρ2, by simp, MulAut.conj (⟨c, hc'⟩ : S22), ?_⟩
      have : a = ⟨c, m22_le_A hc'⟩ * ρ2 * ⟨c, m22_le_A hc'⟩⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact hrA)
      rw [this, map_mul, map_mul, map_inv]
      show muA _ * _ * (muA _)⁻¹ = _
      rw [hcA]
  · intro ρ hρ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    have key : ∀ (r : Equiv.Perm (Fin 22)) (hrA : r ∈ m22A) (l0 : Equiv.Perm (Fin 22))
        (hl0 : l0 ∈ NativeSporadic.M22)
        (h2 : orderOf (l0 * r * l0⁻¹ * r⁻¹) = 2),
        ∃ l : S22, (l * (e ⟨r, hrA⟩ l)⁻¹) ^ 2 = 1 ∧ l * (e ⟨r, hrA⟩ l)⁻¹ ∉ Subgroup.center S22 := by
      intro r hrA l0 hl0 h2
      refine ⟨⟨l0, hl0⟩, ?_, ?_⟩
      all_goals
        have hv : (((⟨l0, hl0⟩ : S22) * (e ⟨r, hrA⟩ ⟨l0, hl0⟩)⁻¹ : S22) : Equiv.Perm (Fin 22)) =
            l0 * r * l0⁻¹ * r⁻¹ := by
          show l0 * (r * l0 * r⁻¹)⁻¹ = _
          group
      · apply Subtype.ext
        rw [SubgroupClass.coe_pow, hv, OneMemClass.coe_one]
        rw [← h2]
        exact pow_orderOf_eq_one _
      · rw [hc, Subgroup.mem_bot]
        intro h1
        have := congrArg Subtype.val h1
        rw [hv] at this
        rw [OneMemClass.coe_one] at this
        rw [this, orderOf_one] at h2
        omega
    rcases hρ with rfl | rfl
    · refine key m22OutRep1 (outRep_mem hr1).1 l1 (hl _) ?_
      exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hf1
    · refine key m22OutRep2 (outRep_mem hr2).1 l2 (hl _) ?_
      exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hf2

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M22) :
    Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne Y :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native
  exact rowData_of_hasElemAbelianEight hI
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y]
    (h : IsSporadic Y .M22) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .M22) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.M22
