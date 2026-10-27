module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSocleQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu

public section

namespace CFSG.QuasithinUnique.Id2519.MathNoLayer

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.ComponentClassification.OuterAutomorphisms

theorem noK_of_check {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (E : List Table) (h : noLayerOK n E (allTables Q) = true) : NoK Q.originalSubgroup := by
  obtain ⟨F, hFK, hnorm, hp, hc⟩ := exists_normal_selfcentralizing hn Q hQ E h
  rintro ⟨B, hB, -⟩
  exact noComponent_of_normal_selfcentralizing hFK hnorm hp hc B hB

theorem noK_of_card {M : Type*} [Group M] {K : Subgroup M} [Finite K] {N : ℕ}
    (hN : Nat.card K ∣ N) (hN7680 : N ≤ 7680) (h168 : ¬ 168 ∣ N) (h360 : ¬ 360 ∣ N)
    (hsmall : ∀ p : ℕ, 17 ≤ p → p ≤ 25 → ¬ p * (p * p - 1) ∣ 2 * N) (hN0 : 0 < N) : NoK K :=
  not_hasKComponent_of_dvd hN h168 h360 (big_p_not_dvd hN7680 hN0 hsmall)

theorem m23_cent1_noK :
    NoK m23CentQ1.originalSubgroup := by
  obtain ⟨hc, -, -, -⟩ := m23_oddcore_cent1
  exact noK_of_check (by norm_num) m23CentQ1 hc _ m23_noLayer_check

theorem m23_involution_centralizer_noK
    : ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
    NoK (centralizerIn NativeSporadic.M23 u) := by
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
  refine centralizer_noK_of_reps hn m23Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
    [(m23Rep1, m23CentQ1.originalSubgroup)]
    ?_ 4000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hK1, ?_, m23_cent1_noK⟩
    rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]

theorem m24_cent1_noK : NoK m24CentQ1.originalSubgroup := by
  obtain ⟨-, -, -, hKc1, -⟩ := m24_rep_data1
  refine noK_of_card (N := 7680) (by rw [hKc1]) le_rfl (by decide) (by decide) ?_ (by norm_num)
  intro p hp1 hp2
  interval_cases p <;> decide

theorem m24_cent2_noK :
    NoK m24CentQ2.originalSubgroup := by
  obtain ⟨hc, -, -, -⟩ := m24_oddcore_cent2
  exact noK_of_check (by norm_num) m24CentQ2 hc _ m24_noLayer_check

theorem m24_involution_centralizer_noK
    : ∀ u ∈ NativeSporadic.M24, orderOf u = 2 →
    NoK (centralizerIn NativeSporadic.M24 u) := by
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
  refine centralizer_noK_of_reps hn m24Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
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
    · refine ⟨hK1, ?_, m24_cent1_noK⟩
      rw [hsz.1, hKc1, m24Certificate_originalSubgroup, m24_card]
    · refine ⟨hK2, ?_, m24_cent2_noK⟩
      rw [hsz.2, hKc2, m24Certificate_originalSubgroup, m24_card]

theorem m22_cent1_noK : NoK m22CentQ1.originalSubgroup := by
  obtain ⟨-, -, -, hKc1, -⟩ := m22_rep_data1
  refine noK_of_card (N := 384) (by rw [hKc1]) (by norm_num) (by decide) (by decide) ?_
    (by norm_num)
  intro p hp1 hp2
  interval_cases p <;> decide

theorem m22_involution_centralizer_noK
    : ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
    NoK (centralizerIn NativeSporadic.M22 u) := by
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
  refine centralizer_noK_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
    [(m22Rep1, m22CentQ1.originalSubgroup)]
    ?_ 2000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hK1, ?_, m22_cent1_noK⟩
    rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]

theorem m22_outCent1_noK
    : NoK m22OutCentQ1.originalSubgroup := by
  obtain ⟨-, -, -, hKc1, -⟩ := m22_out_rep_data1
  refine noK_of_card (N := 320) (by rw [hKc1]) (by norm_num) (by decide) (by decide) ?_
    (by norm_num)
  intro p hp1 hp2
  interval_cases p <;> decide

theorem m22_outCent2_noK :
    NoK m22OutCentQ2.originalSubgroup := by
  obtain ⟨hc, -, -, -⟩ := m22_outer_cent2
  exact noK_of_check (by norm_num) m22OutCentQ2 hc _ m22o_noLayer_check

theorem m22_outer_centralizer_noK
    : ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
    NoK (centralizerIn NativeSporadic.M22 u) := by
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
  refine centralizer_noK_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB) m22Delta hg₀
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
    · refine ⟨hK1, ?_, m22_outCent1_noK⟩
      rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card]
    · refine ⟨hK2, ?_, m22_outCent2_noK⟩
      rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card]

section Rows

theorem fixSubgroup_eq_fixSub {H : Type*} [Group H] (α : MulAut H) : fixSubgroup α = fixSub α :=
  Subgroup.ext fun _ => Iff.rfl

theorem tabIdentFor_of_fix
    {s : TauCeti.SporadicName}
    (hsimple : IsSimpleGroup (NativeSporadic.Carrier s))
    (hnc : ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a)
    (hfix : ∀ α : MulAut (NativeSporadic.Carrier s), α * α = 1 → α ≠ 1 →
      ¬ HasKComponent ↥(fixSubgroup α)) :
    TabIdentFor (@Ident.FamSporadic s) := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨e⟩ := hX
  have hs' : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := e.isSimpleGroup
  have hnc' : ∃ a b : ↥X ⧸ CFSG.pCore 2 ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hpc := pCore_eq_center_of_simple_quotient hs.quasi hs' hnc'
  have e' : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier s :=
    (QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e
  have hπ := Tab.quotProj_surjective e'
  have hker := Tab.quotProj_ker e'
  exact hfix _ (Tab.quotAct_mul_self (Tab.quotProj e') hπ hker hs.tN hs.sq)
    (Tab.quotAct_ne_one (Tab.quotProj e') hπ hker hs.tN hs.quasi hs.comm)
    (hs.hasKComponent_fix_quot hs.ktype (Tab.quotProj e') hπ hker)

theorem fix_of_inner {M : Type*} [Group M] (H : Subgroup M) (hZ : Subgroup.center H = ⊥)
    (α : MulAut H) (hα : α ∈ inner H) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ y : H, orderOf (y : M) = 2 ∧ Nonempty (↥(fixSubgroup α) ≃* ↥(centralizerIn H (y : M))) := by
  obtain ⟨y, rfl⟩ := hα
  have hinj := conj_injective_of_center_bot hZ
  have hy2 : y * y = 1 := by
    apply hinj
    rw [map_mul, map_one]
    exact hα2
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  refine ⟨y, by rw [Subgroup.orderOf_coe]; exact hord, ?_⟩
  have hmap := map_fixSub_conjOn H (MulAut.conj y) (y : M) (fun h => rfl)
  exact ⟨(Subgroup.equivMapOfInjective (fixSub (MulAut.conj y)) H.subtype
    H.subtype_injective).trans (MulEquiv.subgroupCongr hmap)⟩

theorem m23_fix_noK
    (α : MulAut NativeSporadic.M23) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ¬ HasKComponent ↥(fixSubgroup α) := by
  obtain ⟨y, hy, ⟨e⟩⟩ := fix_of_inner NativeSporadic.M23 m23_center_eq_bot' α
    (CFSG.QuasithinUnique.Ch1.m23_all_inner α) hα2 hα1
  exact fun hk => m23_involution_centralizer_noK _ y.2 hy (hk.of_mulEquiv e)

theorem tabIdentFor_m23
    : TabIdentFor (@Ident.FamSporadic .M23) :=
  tabIdentFor_of_fix fam_m23_simplicity.2.2 ⟨m23GenA, m23GenB, m23_gens_not_comm⟩ m23_fix_noK

theorem m24_fix_noK
    (α : MulAut NativeSporadic.M24) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ¬ HasKComponent ↥(fixSubgroup α) := by
  obtain ⟨y, hy, ⟨e⟩⟩ :=
    fix_of_inner NativeSporadic.M24 m24_center_eq_bot' α (CFSG.QuasithinUnique.Ch1.m24_all_inner α)
      hα2 hα1
  exact fun hk => m24_involution_centralizer_noK _ y.2 hy (hk.of_mulEquiv e)

theorem tabIdentFor_m24
    : TabIdentFor (@Ident.FamSporadic .M24) :=
  tabIdentFor_of_fix fam_m24_simplicity.2.2 ⟨m24a, m24b, m24_gens_not_comm⟩ m24_fix_noK

theorem m22_fix_noK
    (α : MulAut NativeSporadic.M22) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ¬ HasKComponent ↥(fixSubgroup α) := by
  by_cases hin : α ∈ inner NativeSporadic.M22
  · obtain ⟨y, hy, ⟨e⟩⟩ := fix_of_inner NativeSporadic.M22 m22_center_eq_bot' α hin hα2 hα1
    exact fun hk => m22_involution_centralizer_noK _ y.2 hy (hk.of_mulEquiv e)
  · rw [fixSubgroup_eq_fixSub]
    exact outer_noK_of_witness NativeSporadic.M22 m22Delta m22_delta_normalizes m22_delta_sq
      m22_center_eq_bot' m22_delta_outer m22_mulAut_card m22_outer_centralizer_noK α hα2 hin

theorem tabIdentFor_m22
    : TabIdentFor (@Ident.FamSporadic .M22) :=
  tabIdentFor_of_fix fam_m22_simplicity.2.2 ⟨m22a, m22b, m22_gens_not_comm⟩ m22_fix_noK

end Rows

end CFSG.QuasithinUnique.Id2519.MathNoLayer
