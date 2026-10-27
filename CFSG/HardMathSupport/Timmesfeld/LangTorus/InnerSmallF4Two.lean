module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false




section Basic

variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

private theorem conj_mem_commutator_self {G : Type*} [Group G] (H : Subgroup G) {g x : G}
    (hg : g ∈ H)
    (hx : x ∈ ⁅H, H⁆) : g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨g * a * g⁻¹, H.mul_mem (H.mul_mem hg ha) (H.inv_mem hg),
      g * b * g⁻¹, H.mul_mem (H.mul_mem hg hb) (H.inv_mem hg), ?_⟩
    simp only [commutatorElement_def]; group
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]; exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hx

theorem good_reflect (i : KernelComponent χ) {ε γ : Fin τ.rank → ℤ}
    (hε : ε ∈ componentRoots χ i) (hγ : γ ∈ componentRoots χ i)
    (h : ∀ c : K, pinnedX τ K γ c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :
    ∀ c : K, pinnedX τ K (rootReflection ε • γ) c ∈
      ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hεr : IsRoot τ ε := hΨ.isRoot ε hε
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  obtain ⟨hsup, hmon, hmaps⟩ := rootWeylOne_spec (K := K) hεr
  have hnC : rootWeylOne τ K ε ∈ componentRootSpan K χ i :=
    sup_le (rootSubgroup_le_rootSpan hε) (rootSubgroup_le_rootSpan (hΨ.neg_mem ε hε)) hsup
  have hπ : weylQuotientHom τ K ⟨rootWeylOne τ K ε, hmon⟩ = rootReflection ε :=
    weylQuotientHom_eq hmaps
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hmon hγr
  rw [hπ] at hμ
  intro c
  have e : pinnedX τ K (rootReflection ε • γ) c =
      rootWeylOne τ K ε * pinnedX τ K γ (μ⁻¹ * c) * (rootWeylOne τ K ε)⁻¹ := by
    rw [hμ, ← mul_assoc, Units.mul_inv, one_mul]
  rw [e]
  exact conj_mem_commutator_self _ hnC (h _)

theorem good_neg (i : KernelComponent χ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i)
    (h : ∀ c : K, pinnedX τ K γ c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :
    ∀ c : K, pinnedX τ K (-γ) c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have := good_reflect i hγ hγ h
  rwa [rootReflection_smul_self (hΨ.isRoot γ hγ)] at this

end Basic

section TwoField

variable {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}

theorem iform_nsmul_right_eq {τ : Tag} (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform x (n • y) = n * iform x y := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n y, iform_smul_right]

theorem iform_nsmul_left_eq {τ : Tag} (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform (n • x) y = n * iform x y := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, iform_smul_left]

theorem good_of_sameLength (i : KernelComponent χ) {α δ : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ componentRoots χ i) (hδ : δ ∈ componentRoots χ i) (hne1 : δ ≠ α) (hne2 : δ ≠ -α)
    (hlen : iform α α = iform δ δ) (hnz : iform α δ ≠ 0) (t : K) :
    pinnedX .F4 K α t ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hαr : IsRoot .F4 α := hΨ.isRoot α hα
  obtain ⟨δ', hδ'Ψ, hne1', hne2', hneg, hlen'⟩ : ∃ δ' ∈ componentRoots χ i, δ' ≠ α ∧ δ' ≠ -α ∧
      iform α δ' < 0 ∧ iform α α = iform δ' δ' := by
    rcases lt_or_gt_of_ne hnz with h | h
    · exact ⟨δ, hδ, hne1, hne2, h, hlen⟩
    · refine ⟨-δ, hΨ.neg_mem δ hδ, fun e => hne2 (by rw [← neg_neg δ, e]),
        fun e => hne1 (by rw [← neg_neg δ, e, neg_neg]), ?_, ?_⟩
      · rw [iform_neg_right_eq]; omega
      · rw [iform_neg_left_eq, iform_neg_right_eq, neg_neg]; exact hlen
  have hδ'r : IsRoot .F4 δ' := hΨ.isRoot δ' hδ'Ψ
  have hne2'' : α ≠ -δ' := fun e => hne2' (by rw [e, neg_neg])
  have hsq := iform_sq_lt hαr hδ'r hne1'.symm hne2''
  have hdv1 := iform_dvd_of_isRoot hαr δ'
  have hae := iform_self_cases noG2_F4 hαr
  have he : 2 * iform α δ' = - iform α α := by
    generalize iform α δ' = e at hsq hdv1 hneg ⊢
    rcases hae with h | h <;> rw [h] at hsq hdv1 ⊢ <;> rw [← hlen', h] at hsq <;>
      (have hlow : -4 < e := by nlinarith) <;> interval_cases e <;> omega
  have hsumr : IsRoot .F4 (α + δ') := isRoot_add_of_iform_neg hαr hδ'r hne2'' hneg
  have hβΨ : α + δ' ∈ componentRoots χ i := hΨ.add_mem α hα δ' hδ'Ψ hsumr
  have hγΨ : -δ' ∈ componentRoots χ i := hΨ.neg_mem δ' hδ'Ψ
  have hγr : IsRoot .F4 (-δ') := IsRoot.neg hδ'r
  have hb : iform (α + δ') (α + δ') = iform α α + 2 * iform α δ' + iform δ' δ' := by
    simp only [iform_add_left, iform_add_right]
    rw [iform_comm δ' α]; ring
  have hneg_eq : iform (-δ') (-δ') = iform δ' δ' := by
    rw [iform_neg_left_eq, iform_neg_right_eq, neg_neg]
  have hne : α + δ' ≠ -δ' := by
    intro e
    have e3 := congrArg (fun x => iform x δ') e
    simp only [iform_add_left, iform_neg_left_eq] at e3
    have hpos := iform_self_pos hαr.ne_zero
    omega
  have hne' : α + δ' ≠ -(-δ') := by
    intro e
    rw [neg_neg] at e
    exact hαr.ne_zero (by simpa using e)
  have hsum : α + δ' + -δ' = α := by abel
  obtain ⟨C, hCc, hCr, hform⟩ := f4_commutator_single hsumr hγr hne hne'
    (by rw [hb, hneg_eq]; omega) (by rw [hsum]; exact hαr)
  have hpos := iform_self_pos hαr.ne_zero
  have hnr : ¬ IsRoot .F4 (-δ' - (α + δ')) := by
    intro hr
    have := iform_self_cases noG2_F4 hr
    simp only [iform_sub_left, iform_sub_right, iform_add_left, iform_add_right,
      iform_neg_left_eq, iform_neg_right_eq, neg_neg] at this
    rw [iform_comm δ' α] at this
    omega
  have hC1 : C = 1 ∨ C = -1 := by
    rcases hCr with h | h
    · exact absurd h hnr
    · exact h
  have hCK : (C : K) ≠ 0 := by rcases hC1 with h | h <;> simp [h]
  have := pinnedX_mem_commutator_of_formula i hβΨ hγΨ hCK (fun c d => hform K c d) t
  rwa [hsum] at this

theorem neg_one_eq_one_of_two (hK2 : ∀ x : K, x = 0 ∨ x = 1) : (-1 : K) = 1 := by
  rcases hK2 (1 + 1) with h | h
  · exact neg_eq_of_add_eq_zero_right h
  · exfalso
    have : (1 : K) = 0 := by simpa using h
    exact one_ne_zero this

theorem good_iff_one (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    {γ : Fin Tag.F4.rank → ℤ} :
    (∀ c : K, pinnedX .F4 K γ c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) ↔
      pinnedX .F4 K γ 1 ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  refine ⟨fun h => h 1, fun h c => ?_⟩
  rcases hK2 c with rfl | rfl
  · rw [pinnedX_zero]; exact one_mem _
  · exact h

theorem good_mixed (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    {s l : Fin Tag.F4.rank → ℤ} (hs : s ∈ componentRoots χ i) (hl : l ∈ componentRoots χ i)
    (hss : iform s s = 2) (hll : iform l l = 4) (hsl : iform s l = -2) :
    pinnedX .F4 K (s + l) 1 ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ ↔
      pinnedX .F4 K (2 • s + l) 1 ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨-, -, C₁, C₂, hC₁, hC₂, hform⟩ :=
    f4_commutator_mixed (hΨ.isRoot s hs) (hΨ.isRoot l hl) hss hll hsl
  have hcomm : ⁅pinnedX .F4 K s 1, pinnedX .F4 K l 1⁆ ∈
      ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :=
    Subgroup.commutator_mem_commutator (pinnedX_mem_rootSpan hs _) (pinnedX_mem_rootSpan hl _)
  rw [hform K 1 1] at hcomm
  have h1 : (C₁ : K) = 1 := by rcases hC₁ with h | h <;> simp [h, neg_one_eq_one_of_two hK2]
  have h2 : (C₂ : K) = 1 := by rcases hC₂ with h | h <;> simp [h, neg_one_eq_one_of_two hK2]
  simp only [h1, h2, one_mul, mul_one, one_pow] at hcomm
  constructor
  · intro hx
    have := mul_mem (inv_mem hx) hcomm
    simpa using this
  · intro hy
    have := mul_mem hcomm (inv_mem hy)
    simpa using this

theorem iform_short_long_eq {a b : Fin Tag.F4.rank → ℤ} (ha : IsRoot .F4 a) (hb : IsRoot .F4 b)
    (h2 : iform a a = 2) (h4 : iform b b = 4) (hneg : iform a b < 0) : iform a b = -2 := by
  have hne : a ≠ b := fun e => by rw [e] at h2; omega
  have hne' : a ≠ -b := fun e => by
    have := congrArg (fun x => iform x x) e
    simp only [iform_neg_left_eq, iform_neg_right_eq, neg_neg] at this
    omega
  have hsq := iform_sq_lt ha hb hne hne'
  have hdv := iform_dvd_of_isRoot hb a
  rw [iform_comm b a, h4] at hdv
  rw [h2, h4] at hsq
  generalize iform a b = e at hsq hdv hneg ⊢
  have hlow : -4 < e := by nlinarith
  interval_cases e <;> omega

theorem exists_neg_sign {a b : Fin Tag.F4.rank → ℤ} {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hb : b ∈ Ψ) (hnz : iform a b ≠ 0) :
    ∃ b', (b' = b ∨ b' = -b) ∧ b' ∈ Ψ ∧ iform a b' < 0 ∧ iform b' b' = iform b b := by
  rcases lt_or_gt_of_ne hnz with h | h
  · exact ⟨b, Or.inl rfl, hb, h, rfl⟩
  · refine ⟨-b, Or.inr rfl, hΨ.neg_mem b hb, ?_, ?_⟩
    · rw [iform_neg_right_eq]; omega
    · rw [iform_neg_left_eq, iform_neg_right_eq, neg_neg]

section Refl

variable {s l : Fin Tag.F4.rank → ℤ} (hs : IsRoot .F4 s) (hl : IsRoot .F4 l)
  (hss : iform s s = 2) (hll : iform l l = 4) (hsl : iform s l = -2)

include hl hll hsl in
theorem refl_l_s : rootReflection l • s = s + l := by
  have hls : iform l s = -2 := by rw [iform_comm]; exact hsl
  have hc : corootPair l s = -1 := by simp [corootPair, hls, hll]
  rw [rootReflection_smul hl, hc]
  simp

include hs hss hsl in
theorem refl_s_l : rootReflection s • l = 2 • s + l := by
  have hc : corootPair s l = -2 := by simp [corootPair, hss, hsl]
  rw [rootReflection_smul hs, hc, neg_smul, sub_neg_eq_add, two_smul, two_smul]
  abel

include hs hss hsl in
theorem refl_s_2sl : rootReflection s • (2 • s + l) = l := by
  have h1 : iform s (2 • s + l) = 2 := by
    rw [iform_add_right, iform_nsmul_right_eq, hss, hsl]; norm_num
  have hc : corootPair s (2 • s + l) = 2 := by
    unfold corootPair; rw [h1, hss]; norm_num
  rw [rootReflection_smul hs, hc, two_smul, two_smul]
  abel

include hl hll hsl hss in
theorem refl_l_sl : rootReflection l • (s + l) = s := by
  have h1 : iform l (s + l) = 2 := by
    rw [iform_add_right, iform_comm l s, hsl, hll]; norm_num
  have hc : corootPair l (s + l) = 1 := by
    unfold corootPair; rw [h1, hll]; norm_num
  rw [rootReflection_smul hl, hc]
  simp

end Refl

theorem good_short_to_long (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    {s l : Fin Tag.F4.rank → ℤ} (hs : s ∈ componentRoots χ i) (hl : l ∈ componentRoots χ i)
    (hss : iform s s = 2) (hll : iform l l = 4) (hsl : iform s l = -2)
    (hGs : ∀ c : K, pinnedX .F4 K s c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :
    ∀ c : K, pinnedX .F4 K l c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hsr := hΨ.isRoot s hs
  have hlr := hΨ.isRoot l hl
  obtain ⟨hr1, hr2, -⟩ := f4_commutator_mixed hsr hlr hss hll hsl
  have hm1 : s + l ∈ componentRoots χ i := hΨ.add_mem s hs l hl hr1
  have hm2 : 2 • s + l ∈ componentRoots χ i := by
    have : 2 • s + l = s + (s + l) := by rw [two_smul]; abel
    rw [this]; exact hΨ.add_mem s hs _ hm1 (this ▸ hr2)
  have h1 := good_reflect i hl hs hGs
  rw [refl_l_s hlr hll hsl] at h1
  have h2 := (good_iff_one hK2 i).2 ((good_mixed hK2 i hs hl hss hll hsl).1 (h1 1))
  have h3 := good_reflect i hs hm2 h2
  rwa [refl_s_2sl hsr hss hsl] at h3

theorem good_long_to_short (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    {s l : Fin Tag.F4.rank → ℤ} (hs : s ∈ componentRoots χ i) (hl : l ∈ componentRoots χ i)
    (hss : iform s s = 2) (hll : iform l l = 4) (hsl : iform s l = -2)
    (hGl : ∀ c : K, pinnedX .F4 K l c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :
    ∀ c : K, pinnedX .F4 K s c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hsr := hΨ.isRoot s hs
  have hlr := hΨ.isRoot l hl
  obtain ⟨hr1, hr2, -⟩ := f4_commutator_mixed hsr hlr hss hll hsl
  have hm1 : s + l ∈ componentRoots χ i := hΨ.add_mem s hs l hl hr1
  have h1 := good_reflect i hs hl hGl
  rw [refl_s_l hsr hss hsl] at h1
  have h2 := (good_iff_one hK2 i).2 ((good_mixed hK2 i hs hl hss hll hsl).2 (h1 1))
  have h3 := good_reflect i hl hm1 h2
  rwa [refl_l_sl hlr hss hll hsl] at h3

theorem good_closure (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    {a b : Fin Tag.F4.rank → ℤ} (ha : a ∈ componentRoots χ i) (hb : b ∈ componentRoots χ i)
    (hGa : ∀ c : K, pinnedX .F4 K a c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆)
    (hab : iform a b ≠ 0) :
    ∀ c : K, pinnedX .F4 K b c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  by_cases h1 : b = a
  · subst h1; exact hGa
  by_cases h2 : b = -a
  · subst h2; exact good_neg i ha hGa
  have har := hΨ.isRoot a ha
  have hbr := hΨ.isRoot b hb
  have hae := iform_self_cases noG2_F4 har
  have hbe := iform_self_cases noG2_F4 hbr
  by_cases hlen : iform a a = iform b b
  · exact fun t => good_of_sameLength i hb ha (Ne.symm h1) (fun e => h2 (by rw [e, neg_neg]))
      hlen.symm (by rw [iform_comm]; exact hab) t
  rcases hae with ha2 | ha4 <;> rcases hbe with hb2 | hb4
  · exact absurd (ha2.trans hb2.symm) hlen
  ·
    obtain ⟨l, hl_eq, hlΨ, hnegl, hlenl⟩ := exists_neg_sign hΨ hb hab
    have hlr := hΨ.isRoot l hlΨ
    have hsl := iform_short_long_eq har hlr ha2 (by rw [hlenl, hb4]) hnegl
    have hGl := good_short_to_long hK2 i ha hlΨ ha2 (by rw [hlenl, hb4]) hsl hGa
    rcases hl_eq with rfl | rfl
    · exact hGl
    · have := good_neg i hlΨ hGl
      rwa [neg_neg] at this
  ·
    obtain ⟨s, hs_eq, hsΨ, hnegs, hlens⟩ := exists_neg_sign hΨ hb hab
    have hsr := hΨ.isRoot s hsΨ
    have hss : iform s s = 2 := by rw [hlens, hb2]
    have hsl : iform s a = -2 := by
      have := iform_short_long_eq hsr har hss ha4 (by rw [iform_comm]; exact hnegs)
      exact this
    have hGs := good_long_to_short hK2 i hsΨ ha hss ha4 hsl hGa
    rcases hs_eq with rfl | rfl
    · exact hGs
    · have := good_neg i hsΨ hGs
      rwa [neg_neg] at this
  · exact absurd (ha4.trans hb4.symm) hlen

theorem good_of_hasA2 (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    (hA2 : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
      iform α α = iform δ δ ∧ iform α δ ≠ 0) :
    ∀ γ ∈ componentRoots χ i, ∀ c : K,
      pinnedX .F4 K γ c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨α, hα, δ, hδ, hne1, hne2, hlen, hnz⟩ := hA2
  set S : Set (Fin Tag.F4.rank → ℤ) := {γ | γ ∈ componentRoots χ i ∧ ∀ c : K,
    pinnedX .F4 K γ c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆} with hS
  have hSsub : S ⊆ componentRoots χ i := fun γ hγ => hγ.1
  have horth : ∀ a ∈ S, ∀ b ∈ componentRoots χ i, b ∉ S → iform a b = 0 := by
    intro a ha b hb hbS
    by_contra hne
    exact hbS ⟨hb, good_closure hK2 i ha.1 hb ha.2 hne⟩
  have hαS : α ∈ S := ⟨hα, fun c => good_of_sameLength i hα hδ hne1 hne2 hlen hnz c⟩
  rcases hΨ.irreducible S hSsub horth with h | h
  · rw [h] at hαS; exact absurd hαS (Set.notMem_empty α)
  · intro γ hγ
    rw [← h] at hγ
    exact hγ.2

theorem isPerfect_componentRootSpan_F4_two (hK2 : ∀ x : K, x = 0 ∨ x = 1) (i : KernelComponent χ)
    (hA2 : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
      iform α α = iform δ δ ∧ iform α δ ≠ 0) :
    Group.IsPerfect (componentRootSpan K χ i) :=
  isPerfect_componentRootSpan_of_forall i fun γ hγ t => good_of_hasA2 hK2 i hA2 γ hγ t

theorem eq_b2Block_of_noA2 (i : KernelComponent χ)
    (hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α)
    (hnoA2 : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ ≠ α → δ ≠ -α →
      iform α α = iform δ δ → iform α δ = 0) :
    ∃ s l : Fin Tag.F4.rank → ℤ, iform s s = 2 ∧ iform l l = 4 ∧ iform s l = -2 ∧
      componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)} := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨α0, hα0, -⟩ := id hbig
  obtain ⟨δ0, hδ0, hne1, hne2, hnz⟩ := exists_nonorth_partner hΨ hbig hα0
  have hα0r := hΨ.isRoot α0 hα0
  have hδ0r := hΨ.isRoot δ0 hδ0
  have hlen : iform α0 α0 ≠ iform δ0 δ0 := fun h => hnz (hnoA2 α0 hα0 δ0 hδ0 hne1 hne2 h)
  obtain ⟨s, l, hs, hl, hss, hll, hsl⟩ : ∃ s l, s ∈ componentRoots χ i ∧ l ∈ componentRoots χ i ∧
      iform s s = 2 ∧ iform l l = 4 ∧ iform s l = -2 := by
    rcases iform_self_cases noG2_F4 hα0r with h1 | h1 <;> rcases iform_self_cases noG2_F4 hδ0r with h2 | h2
    · exact absurd (h1.trans h2.symm) hlen
    · obtain ⟨l, -, hlΨ, hneg, hlen'⟩ := exists_neg_sign hΨ hδ0 hnz
      exact ⟨α0, l, hα0, hlΨ, h1, by rw [hlen', h2],
        iform_short_long_eq hα0r (hΨ.isRoot l hlΨ) h1 (by rw [hlen', h2]) hneg⟩
    · obtain ⟨s, -, hsΨ, hneg, hlen'⟩ := exists_neg_sign (a := α0) hΨ hδ0 hnz
      have hsr := hΨ.isRoot s hsΨ
      refine ⟨s, α0, hsΨ, hα0, by rw [hlen', h2], h1, ?_⟩
      have := iform_short_long_eq hsr hα0r (by rw [hlen', h2]) h1 (by rw [iform_comm]; exact hneg)
      exact this
    · exact absurd (h1.trans h2.symm) hlen
  have hsr := hΨ.isRoot s hs
  have hlr := hΨ.isRoot l hl
  obtain ⟨hr1, hr2, -⟩ := f4_commutator_mixed hsr hlr hss hll hsl
  have hm1 : s + l ∈ componentRoots χ i := hΨ.add_mem s hs l hl hr1
  have hm2 : 2 • s + l ∈ componentRoots χ i := by
    have : 2 • s + l = s + (s + l) := by rw [two_smul]; abel
    rw [this]; exact hΨ.add_mem s hs _ hm1 (this ▸ hr2)
  set B : Set (Fin Tag.F4.rank → ℤ) := {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)}
    with hB
  have hBsub : B ⊆ componentRoots χ i := by
    intro x hx
    simp only [hB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs
    · exact hΨ.neg_mem _ hs
    · exact hl
    · exact hΨ.neg_mem _ hl
    · exact hm1
    · exact hΨ.neg_mem _ hm1
    · exact hm2
    · exact hΨ.neg_mem _ hm2
  have hBneg : ∀ x ∈ B, -x ∈ B := by
    intro x hx
    simp only [hB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [neg_neg, true_or, or_true]
  have hss1 : iform (s + l) (s + l) = 2 := by
    simp only [iform_add_left, iform_add_right]; rw [iform_comm l s]; omega
  have hss2 : iform (2 • s + l) (2 • s + l) = 4 := by
    simp only [iform_add_left, iform_add_right, iform_nsmul_right_eq, iform_nsmul_left_eq]
    rw [iform_comm l s]; push_cast; omega
  have horth : ∀ a ∈ B, ∀ b ∈ componentRoots χ i, b ∉ B → iform a b = 0 := by
    intro a ha b hb hbB
    by_contra hne
    have hbr := hΨ.isRoot b hb
    have hsB : s ∈ B := by simp [hB]
    have hlB : l ∈ B := by simp [hB]
    have hslB : s + l ∈ B := by simp [hB]
    have hs2B : 2 • s + l ∈ B := by simp [hB]
    have hnb : ∀ x ∈ B, x ≠ b ∧ x ≠ -b := fun x hx =>
      ⟨fun e => hbB (e ▸ hx), fun e => hbB (by
        have : b = -x := by rw [e, neg_neg]
        rw [this]; exact hBneg x hx)⟩
    have hf : iform b s ≠ 0 ∨ iform b l ≠ 0 ∨ iform b (s + l) ≠ 0 ∨ iform b (2 • s + l) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2, h3, h4⟩ := hcon
      apply hne
      rw [iform_comm]
      simp only [hB, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | assumption | (rw [iform_neg_right_eq, neg_eq_zero]; assumption)
    have hrel1 : 2 * iform b s = iform b (2 • s + l) - iform b l := by
      rw [iform_add_right, iform_nsmul_right_eq]; push_cast; ring
    have hrel2 : 2 * iform b (s + l) = iform b (2 • s + l) + iform b l := by
      rw [iform_add_right, iform_add_right, iform_nsmul_right_eq]; push_cast; ring
    have hrel3 : iform b l = iform b (s + l) - iform b s := by
      rw [iform_add_right]; ring
    have hrel4 : iform b (2 • s + l) = iform b s + iform b (s + l) := by
      rw [iform_add_right, iform_add_right, iform_nsmul_right_eq]; push_cast; ring
    rcases iform_self_cases noG2_F4 hbr with hb2 | hb4
    ·
      have : iform b s ≠ 0 ∨ iform b (s + l) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        omega
      rcases this with h | h
      · have := hnoA2 b hb s hs (hnb s hsB).1
          (hnb s hsB).2 (by rw [hb2, hss]) 
        exact h this
      · have := hnoA2 b hb (s + l) hm1 (hnb _ hslB).1
          (hnb _ hslB).2 (by rw [hb2, hss1])
        exact h this
    · have : iform b l ≠ 0 ∨ iform b (2 • s + l) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        omega
      rcases this with h | h
      · have := hnoA2 b hb l hl (hnb _ hlB).1
          (hnb _ hlB).2 (by rw [hb4, hll])
        exact h this
      · have := hnoA2 b hb (2 • s + l) hm2 (hnb _ hs2B).1
          (hnb _ hs2B).2 (by rw [hb4, hss2])
        exact h this
  refine ⟨s, l, hss, hll, hsl, ?_⟩
  rcases hΨ.irreducible B hBsub horth with h | h
  · exact absurd h (Set.nonempty_iff_ne_empty.1 ⟨s, by simp [hB]⟩)
  · exact h.symm

end TwoField

end CFSG.HardMathSupport.Timmesfeld.LangTorus
