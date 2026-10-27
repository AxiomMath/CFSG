module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuCheck

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem originalSubgroup_le_closure_listTables {n : ℕ} (Q : RawSchreierDatum n)
    {L : List (Equiv.Perm (Fin n))} (hQ : Q.originalSubgroup = closure {g | g ∈ L}) :
    Q.originalSubgroup ≤ closure {g | ∃ l < (listTables L).size, g = L.getD l 1} :=
  hQ.le.trans (closure_listTables L)

theorem m23K_comps : CompsSatisfy m23CentQ1.originalSubgroup fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hH : m23CentQ1.originalSubgroup = closure {g | g ∈ m23KGens} := by
    rw [m23CentQ1, certificate_originalSubgroup]
    rfl
  have hL : ∀ g ∈ m23KGens, g ∈ m23CentQ1.originalSubgroup :=
    fun g hg => hH ▸ subset_closure hg
  have hcard : Nat.card m23CentQ1.originalSubgroup = 2688 := m23_rep_data1.2.2.2.1
  exact compsSatisfy_of_threeWitnessOK hn _ (listTables_spec hn hL)
    (originalSubgroup_le_closure_listTables _ hH) (evalCodes_mem _ hL _) (evalCodes_mem _ hL _)
    m23_three_witness_check (by rw [hcard]; norm_num)

theorem m24K1_comps : CompsSatisfy m24CentQ1.originalSubgroup fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hH : m24CentQ1.originalSubgroup = closure {g | g ∈ m24K1Gens} := by
    rw [m24CentQ1, certificate_originalSubgroup]
    rfl
  have hL : ∀ g ∈ m24K1Gens, g ∈ m24CentQ1.originalSubgroup :=
    fun g hg => hH ▸ subset_closure hg
  have hcard : Nat.card m24CentQ1.originalSubgroup = 7680 := m24_rep_data1.2.2.2.1
  exact compsSatisfy_of_threeWitnessOK hn _ (listTables_spec hn hL)
    (originalSubgroup_le_closure_listTables _ hH) (evalCodes_mem _ hL _) (evalCodes_mem _ hL _)
    m24_three_witness_check1 (by rw [hcard]; norm_num)

theorem m24K2_comps : CompsSatisfy m24CentQ2.originalSubgroup fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hH : m24CentQ2.originalSubgroup = closure {g | g ∈ m24K2Gens} := by
    rw [m24CentQ2, certificate_originalSubgroup]
    rfl
  have hL : ∀ g ∈ m24K2Gens, g ∈ m24CentQ2.originalSubgroup :=
    fun g hg => hH ▸ subset_closure hg
  have hcard : Nat.card m24CentQ2.originalSubgroup = 21504 := m24_rep_data2.2.2.2.1
  exact compsSatisfy_of_threeWitnessOK hn _ (listTables_spec hn hL)
    (originalSubgroup_le_closure_listTables _ hH) (evalCodes_mem _ hL _) (evalCodes_mem _ hL _)
    m24_three_witness_check2 (by rw [hcard]; norm_num)

theorem m22OK_comps :
    CompsSatisfy m22OutCentQ2.originalSubgroup fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hH : m22OutCentQ2.originalSubgroup = closure {g | g ∈ m22OKGens} := by
    rw [m22OutCentQ2, certificate_originalSubgroup]
    rfl
  have hL : ∀ g ∈ m22OKGens, g ∈ m22OutCentQ2.originalSubgroup :=
    fun g hg => hH ▸ subset_closure hg
  have hcard : Nat.card m22OutCentQ2.originalSubgroup = 1344 := m22_out_rep_data2.2.2.2.1
  exact compsSatisfy_of_threeWitnessOK hn _ (listTables_spec hn hL)
    (originalSubgroup_le_closure_listTables _ hH) (evalCodes_mem _ hL _) (evalCodes_mem _ hL _)
    m22_three_witness_check (by rw [hcard]; norm_num)

theorem m11_centralizerIn_comps : ∀ u ∈ NativeSporadic.M11, orderOf u = 2 →
    CompsSatisfy (centralizerIn NativeSporadic.M11 u) fun Y _ => Nat.card Y ∣ 48 := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, hsz, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  simp only [repSizes, m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hsz
  rw [← m11Certificate_originalSubgroup]
  intro u hu ho
  refine compsSatisfy_centralizerIn_of_reps hn m11Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (isoInvariant_card_dvd 48)
    [(evalCodes [m11gA, m11gB] [1], m11CentQ1.originalSubgroup)] (by simpa using ⟨hr, hro⟩)
    400 hok ?_ u (by simpa using hu) ho
  simp only [List.mem_singleton, forall_eq]
  refine ⟨hK, ?_, ?_⟩
  · rw [hsz, hKc, m11Certificate_originalSubgroup, m11_card]
  · rw [← hKc]
    exact compsSatisfy_card_dvd

theorem m22_centralizerIn_comps : ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
    CompsSatisfy (centralizerIn NativeSporadic.M22 u) fun Y _ => Nat.card Y ∣ 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  refine compsSatisfy_centralizerIn_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (isoInvariant_card_dvd 384)
    [(m22Rep1, m22CentQ1.originalSubgroup)] ?_ 2000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hK1, ?_, ?_⟩
    · rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]
    · rw [← hKc1]
      exact compsSatisfy_card_dvd

theorem m23_centralizerIn_comps : ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
    CompsSatisfy (centralizerIn NativeSporadic.M23 u) fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  refine compsSatisfy_centralizerIn_of_reps hn m23Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) isoInvariant_not_three_dvd
    [(m23Rep1, m23CentQ1.originalSubgroup)] ?_ 4000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨hK1, by rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card], m23K_comps⟩

theorem m24_centralizerIn_comps : ∀ u ∈ NativeSporadic.M24, orderOf u = 2 →
    CompsSatisfy (centralizerIn NativeSporadic.M24 u) fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m24Certificate_originalSubgroup]
  intro u hu ho
  refine compsSatisfy_centralizerIn_of_reps hn m24Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) isoInvariant_not_three_dvd
    [(m24Rep1, m24CentQ1.originalSubgroup), (m24Rep2, m24CentQ2.originalSubgroup)]
    ?_ 40000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hK1, by rw [hsz.1, hKc1, m24Certificate_originalSubgroup, m24_card], m24K1_comps⟩
    · exact ⟨hK2, by rw [hsz.2, hKc2, m24Certificate_originalSubgroup, m24_card], m24K2_comps⟩

theorem m22_outer_centralizerIn_comps : ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 →
    orderOf u = 2 →
    CompsSatisfy (centralizerIn NativeSporadic.M22 u) fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  refine compsSatisfy_centralizerIn_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB)
    m22Delta hg₀ isoInvariant_not_three_dvd
    [(m22OutRep1, m22OutCentQ1.originalSubgroup), (m22OutRep2, m22OutCentQ2.originalSubgroup)]
    ?_ 2000 hok ?_ u hu ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨hK1, by rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card], ?_⟩
      exact compsSatisfy_not_three_of_card (by rw [hKc1]; norm_num)
    · exact ⟨hK2, by rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card], m22OK_comps⟩

theorem m22_outer_comps (α : MulAut NativeSporadic.M22) (hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M22) :
    CompsSatisfy (fixSub α) fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hδ' := inv_conj_mem NativeSporadic.M22 m22_delta_normalizes m22_delta_sq
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer NativeSporadic.M22 m22Delta
    m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hα
  set u := g * m22Delta
  have hu : m22Delta⁻¹ * u ∈ NativeSporadic.M22 := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ NativeSporadic.M22 := by
    have : u * u = g * (m22Delta * g * m22Delta⁻¹) * (m22Delta * m22Delta) := by
      simp only [u]; group
    rw [this]
    exact NativeSporadic.M22.mul_mem
      (NativeSporadic.M22.mul_mem hg (m22_delta_normalizes g hg)) m22_delta_sq
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : NativeSporadic.M22) ∈ Subgroup.center NativeSporadic.M22 := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut NativeSporadic.M22 => (φ z : Equiv.Perm (Fin 22))) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : Equiv.Perm (Fin 22)) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by
            rw [hz]
        _ = u * u * z := by group
    rw [m22_center_eq_bot', Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hfix := map_fixSub_conjOn NativeSporadic.M22 α u hαg
  exact CompsSatisfy.of_mulEquiv isoInvariant_not_three_dvd
    (((fixSub α).equivMapOfInjective NativeSporadic.M22.subtype
      NativeSporadic.M22.subtype_injective).trans (MulEquiv.subgroupCongr hfix))
    (m22_outer_centralizerIn_comps u hu ho)

end CFSG.ComponentClassification.RestrictedStd.Spor
