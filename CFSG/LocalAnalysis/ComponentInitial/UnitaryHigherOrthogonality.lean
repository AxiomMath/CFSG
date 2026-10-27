module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPointNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairOrbits

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

universe u

variable {p f : ℕ} {K : Type} [Field K]

section Abstract

variable (h : UnitaryFieldData p f K) {V : Type u} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
include h in
theorem card_lines_le_of_finrank_two (W : Submodule K V) (hW : Module.finrank K W = 2) :
    Nat.card {M : Submodule K V // Module.finrank K M = 1 ∧ M ≤ W} = (p ^ f) ^ 2 + 1 := by
  have := h.finite
  have e : {M : Submodule K V // Module.finrank K M = 1 ∧ M ≤ W} ≃
      {N : Submodule K W // Module.finrank K N = 1} :=
    { toFun := fun M => ⟨M.1.comap W.subtype, by
        rw [finrank_comap_subtype, inf_eq_left.mpr M.2.2, M.2.1]⟩
      invFun := fun N => ⟨N.1.map W.subtype, by
        rw [← (Submodule.equivMapOfInjective W.subtype W.injective_subtype N.1).finrank_eq, N.2],
        Submodule.map_subtype_le W N.1⟩
      left_inv := fun M => Subtype.ext (by
        change (M.1.comap W.subtype).map W.subtype = M.1
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr M.2.2])
      right_inv := fun N =>
        Subtype.ext (Submodule.comap_map_eq_of_injective W.injective_subtype N.1) }
  rw [Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule (K := K) (V := W)),
    Projectivization.card_of_finrank_two K W hW, h.card]
  ring

variable {B : V →ₛₗ[h.bar] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem subOrtho_span_left_iff {a : V} {M : Submodule K V} :
    SubOrtho B (K ∙ a) M ↔ ∀ y ∈ M, B a y = 0 := by
  refine ⟨fun hM y hy => hM a (Submodule.mem_span_singleton_self a) y hy, fun hM x hx y hy => ?_⟩
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp [hM y hy]

omit [FiniteDimensional K V] in
theorem finrank_span_sup_eq_two [FiniteDimensional K V] {a : V} (ha0 : a ≠ 0)
    {M : Submodule K V} (hM : Module.finrank K M = 1) (hne : M ≠ K ∙ a) :
    Module.finrank K ↥(K ∙ a ⊔ M) = 2 := by
  have hLa : Module.finrank K (K ∙ a) = 1 := finrank_span_singleton ha0
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) M
  have h2 : Module.finrank K ↥(K ∙ a ⊓ M) = 0 := by
    by_contra h0
    have hle : Module.finrank K ↥(K ∙ a ⊓ M) ≤ 1 := hLa ▸ Submodule.finrank_mono inf_le_left
    have h3 : K ∙ a ⊓ M = K ∙ a := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have h4 : K ∙ a ⊓ M = M := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
    exact hne (h4.symm.trans h3)
  rw [h2, hLa, hM] at h1
  omega

theorem card_orth_lines (hB : B.IsSymm) {a : V} (ha0 : a ≠ 0) (haa : B a a = 0) :
    Nat.card {M : TotIsoSubspaces B 1 // M.1 ≠ K ∙ a ∧ ∀ y ∈ M.1, B a y = 0} =
      (p ^ f) ^ 2 * Nat.card {W : TotIsoSubspaces B 2 // a ∈ W.1} := by
  classical
  have := h.finite
  have : Finite V := Module.finite_of_finite K
  have hLa : Module.finrank K (K ∙ a) = 1 := finrank_span_singleton ha0
  have hplane : ∀ M : {M : TotIsoSubspaces B 1 // M.1 ≠ K ∙ a ∧ ∀ y ∈ M.1, B a y = 0},
      Module.finrank K ↥(K ∙ a ⊔ M.1.1) = 2 ∧
        ∀ x ∈ K ∙ a ⊔ M.1.1, ∀ y ∈ K ∙ a ⊔ M.1.1, B x y = 0 := fun M =>
    ⟨finrank_span_sup_eq_two ha0 M.1.2.1 M.2.1, sup_isotropic haa M.1.2.2 M.2.2 fun x hx => by
      rw [← hB.eq a x, M.2.2 x hx, map_zero]⟩
  let F : {M : TotIsoSubspaces B 1 // M.1 ≠ K ∙ a ∧ ∀ y ∈ M.1, B a y = 0} →
      {W : TotIsoSubspaces B 2 // a ∈ W.1} := fun M =>
    ⟨⟨K ∙ a ⊔ M.1.1, hplane M⟩, Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)⟩
  have hfib : ∀ W : {W : TotIsoSubspaces B 2 // a ∈ W.1},
      Nat.card {M // F M = W} = (p ^ f) ^ 2 := by
    intro W
    have haW : K ∙ a ≤ W.1.1 := (Submodule.span_singleton_le_iff_mem _ _).mpr W.2
    let t₀ : {M : Submodule K V // Module.finrank K M = 1 ∧ M ≤ W.1.1} := ⟨K ∙ a, hLa, haW⟩
    have e : {M // F M = W} ≃
        {t : {M : Submodule K V // Module.finrank K M = 1 ∧ M ≤ W.1.1} // t ≠ t₀} :=
      { toFun := fun M => ⟨⟨M.1.1.1, M.1.1.2.1, le_sup_right.trans
            (congrArg (fun W' : {W : TotIsoSubspaces B 2 // a ∈ W.1} => W'.1.1) M.2).le⟩,
          fun ht => M.1.2.1 (congrArg Subtype.val ht)⟩
        invFun := fun t => ⟨⟨⟨t.1.1, t.1.2.1, fun x hx y hy =>
            W.1.2.2 x (t.1.2.2 hx) y (t.1.2.2 hy)⟩, fun he => t.2 (Subtype.ext he),
            fun y hy => W.1.2.2 a W.2 y (t.1.2.2 hy)⟩,
          Subtype.ext (Subtype.ext (Submodule.eq_of_le_of_finrank_eq (sup_le haW t.1.2.2)
            (by rw [finrank_span_sup_eq_two ha0 t.1.2.1 fun he => t.2 (Subtype.ext he),
              W.1.2.1])))⟩
        left_inv := fun M => Subtype.ext (Subtype.ext (Subtype.ext rfl))
        right_inv := fun t => Subtype.ext (Subtype.ext rfl) }
    have hT := card_lines_le_of_finrank_two h W.1.1 W.1.2.1
    rw [← Nat.card_congr (Equiv.optionSubtypeNe t₀), Finite.card_option] at hT
    rw [Nat.card_congr e]
    omega
  have : Fintype {W : TotIsoSubspaces B 2 // a ∈ W.1} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  ring

theorem card_isoLines_mul (hB : B.IsSymm) (hBl : B.SeparatingLeft) {m : ℕ}
    (hm : Module.finrank K V = m) (hm2 : 2 ≤ m) :
    (Nat.card (TotIsoSubspaces B 1) : ℤ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) =
      (((p ^ f : ℕ) : ℤ) ^ m - (-1) ^ m) * (((p ^ f : ℕ) : ℤ) ^ (m - 1) - (-1) ^ (m - 1)) := by
  have := (isotropic_subspace_count h hB hBl hm 1).2.1 (by omega)
  rw [Finset.Icc_self, Finset.prod_singleton, Finset.prod_range_one, mul_zero, Nat.sub_zero,
    mul_one] at this
  exact this

end Abstract

theorem card_subtype_eq_card_ne_add_one {α : Type*} [Finite α] {P : α → Prop} {a : α}
    (ha : P a) : Nat.card {x // P x} = Nat.card {x // x ≠ a ∧ P x} + 1 := by
  classical
  rw [← Nat.card_congr (Equiv.optionSubtypeNe (⟨a, ha⟩ : {x // P x})), Finite.card_option]
  congr 1
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1.1, fun he => x.2 (Subtype.ext he), x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, fun he => x.2.1 (congrArg Subtype.val he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

abbrev LineOrth (h : UnitaryFieldData p f K) {r ε : ℕ} (L M : hypIsotropicLines h r ε) : Prop :=
  SubOrtho (hypForm h r ε) (L : Submodule K (HypIndex r ε → K)) M

variable {r ε : ℕ} (h : UnitaryFieldData p f K)

theorem lineOrth_self (L : hypIsotropicLines h r ε) : LineOrth h L L :=
  isTotIso_of_mem_isoLines (B := hypForm h r ε) L.2

theorem exists_eq_span_of_mem_hypIsotropicLines {L : Submodule K (HypIndex r ε → K)}
    (hL : L ∈ hypIsotropicLines h r ε) :
    ∃ a, a ≠ 0 ∧ hypForm h r ε a a = 0 ∧ L = K ∙ a := by
  obtain ⟨hL1, hL2⟩ := mem_hypIsotropicLines.mp hL
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L) fun h0 => by
    rw [h0, finrank_bot] at hL1
    exact zero_ne_one hL1
  exact ⟨a, ha0, hL2 a ha, eq_span_singleton_of_mem_of_finrank_eq_one hL1 ha ha0⟩

theorem subOrtho_smul_iff (g : hypSU h r ε) (L M : Submodule K (HypIndex r ε → K)) :
    SubOrtho (hypForm h r ε) (g • L) (g • M) ↔ SubOrtho (hypForm h r ε) L M := by
  constructor
  · intro hgLM x hx y hy
    rw [← hypForm_smul_smul h g]
    exact hgLM _ (Submodule.smul_mem_pointwise_smul x g L hx) _
      (Submodule.smul_mem_pointwise_smul y g M hy)
  · intro hLM x hx y hy
    obtain ⟨x', hx', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g L).mp hx
    obtain ⟨y', hy', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y g M).mp hy
    rw [hypForm_smul_smul]
    exact hLM x' hx' y' hy'

theorem hyp_pair_orbits {L M L' M' : hypIsotropicLines h r ε} (hne : L ≠ M) (hne' : L' ≠ M') :
    (∃ g : hypSU h r ε, g • L = L' ∧ g • M = M') ↔ (LineOrth h L M ↔ LineOrth h L' M') := by
  have hB := hypForm_isSymm h (r := r) (ε := ε)
  have hBl := hypForm_separatingLeft h (r := r) (ε := ε)
  have hsymm : ∀ x y, hypForm h r ε x y = 0 → hypForm h r ε y x = 0 := fun x y hxy => by
    rw [← hB.eq x y, hxy, map_zero]
  have hhyp : ∀ L M : hypIsotropicLines h r ε, ¬ LineOrth h L M →
      ∃ a b, hypForm h r ε a a = 0 ∧ hypForm h r ε b b = 0 ∧ hypForm h r ε a b = 1 ∧
        (L : Submodule K (HypIndex r ε → K)) = K ∙ a ∧
        (M : Submodule K (HypIndex r ε → K)) = K ∙ b := by
    intro L M hLM
    obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
    obtain ⟨c, hc0, hc, hMc⟩ := exists_eq_span_of_mem_hypIsotropicLines h M.2
    have hac : hypForm h r ε a c ≠ 0 := fun h0 => hLM (by
      change SubOrtho _ _ _
      rw [hLa, hMc]
      exact (orth_span_iff (B := hypForm h r ε) a c).mpr h0)
    refine ⟨a, (hypForm h r ε a c)⁻¹ • c, ha, by simp [hc], by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hac], hLa, ?_⟩
    rw [hMc, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hac))]
  have horth : ∀ L M : hypIsotropicLines h r ε, L ≠ M → LineOrth h L M →
      ∃ a₁ a₂, LinearIndependent K ![a₁, a₂] ∧ hypForm h r ε a₁ a₁ = 0 ∧
        hypForm h r ε a₁ a₂ = 0 ∧ hypForm h r ε a₂ a₁ = 0 ∧ hypForm h r ε a₂ a₂ = 0 ∧
        (L : Submodule K (HypIndex r ε → K)) = K ∙ a₁ ∧
        (M : Submodule K (HypIndex r ε → K)) = K ∙ a₂ := by
    intro L M hne hLM
    obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
    obtain ⟨c, hc0, hc, hMc⟩ := exists_eq_span_of_mem_hypIsotropicLines h M.2
    have hac : hypForm h r ε a c = 0 := by
      have hLM' : SubOrtho (hypForm h r ε) (K ∙ a) (K ∙ c) := by
        rw [← hLa, ← hMc]
        exact hLM
      exact (orth_span_iff (B := hypForm h r ε) a c).mp hLM'
    have hne' : K ∙ a ≠ K ∙ c := fun heq => hne (Subtype.ext (by rw [hLa, hMc, heq]))
    exact ⟨a, c, linearIndependent_pair_of_span_ne ha0 hc0 hne', ha, hac, hsymm a c hac, hc,
      hLa, hMc⟩
  have hext : ∀ L M L' M' : hypIsotropicLines h r ε,
      ∀ g' ∈ sesqSpecialUnitaryGroup (hypForm h r ε),
      (L : Submodule K (HypIndex r ε → K)).map
          (g' : (HypIndex r ε → K) →ₗ[K] HypIndex r ε → K) = L' →
      (M : Submodule K (HypIndex r ε → K)).map
          (g' : (HypIndex r ε → K) →ₗ[K] HypIndex r ε → K) = M' →
      ∃ g : hypSU h r ε, g • L = L' ∧ g • M = M' := by
    intro L M L' M' g' hg' hL hM
    obtain ⟨g, hg⟩ := exists_hypSU_of_mem h hg'
    exact ⟨g, Subtype.ext (by rw [← hL, ← hg]; rfl), Subtype.ext (by rw [← hM, ← hg]; rfl)⟩
  constructor
  · rintro ⟨g, hgL, hgM⟩
    rw [← hgL, ← hgM]
    exact (subOrtho_smul_iff h g L M).symm
  · intro hiff
    by_cases hLM : LineOrth h L M
    · obtain ⟨a₁, a₂, hli, h11, h12, h21, h22, hL, hM⟩ := horth L M hne hLM
      obtain ⟨a₁', a₂', hli', h11', h12', h21', h22', hL', hM'⟩ :=
        horth L' M' hne' (hiff.mp hLM)
      obtain ⟨g', hg', hg1, hg2⟩ := exists_sesqSpecialUnitary_of_orthogonal h hB hBl hli h11 h12
        h21 h22 hli' h11' h12' h21' h22'
      exact hext L M L' M' g' hg' (by rw [hL, hg1, hL']) (by rw [hM, hg2, hM'])
    · obtain ⟨a, b, ha, hb, hab, hL, hM⟩ := hhyp L M hLM
      obtain ⟨a', b', ha', hb', hab', hL', hM'⟩ := hhyp L' M' (fun h' => hLM (hiff.mpr h'))
      obtain ⟨g', hg', hg1, hg2⟩ :=
        exists_sesqSpecialUnitary_of_hyperbolic h hB hBl ha hb hab ha' hb' hab'
      exact hext L M L' M' g' hg' (by rw [hL, hg1, hL']) (by rw [hM, hg2, hM'])

theorem hypProjLineAction_hypProj_apply (g : hypSU h r ε) (L : hypIsotropicLines h r ε) :
    hypProjLineAction h r ε (hypProj h r ε g) L = g • L :=
  rfl

theorem suborbit_iff {L M : hypIsotropicLines h r ε} (hML : M ≠ L)
    (M' : hypIsotropicLines h r ε) :
    (∃ x : hypPSU h r ε, hypProjLineAction h r ε x L = L ∧ hypProjLineAction h r ε x M = M') ↔
      M' ≠ L ∧ (LineOrth h L M ↔ LineOrth h L M') := by
  constructor
  · rintro ⟨x, hxL, hxM⟩
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
    have hne : M' ≠ L := fun he => hML ((hypProjLineAction h r ε (hypProj h r ε g)).injective
      (by rw [hxM, hxL, he]))
    rw [hypProjLineAction_hypProj_apply] at hxL hxM
    exact ⟨hne, (hyp_pair_orbits h (Ne.symm hML) (Ne.symm hne)).mp ⟨g, hxL, hxM⟩⟩
  · rintro ⟨hne, hiff⟩
    obtain ⟨g, hgL, hgM⟩ := (hyp_pair_orbits h (Ne.symm hML) (Ne.symm hne)).mpr hiff
    exact ⟨hypProj h r ε g, hgL, hgM⟩

theorem card_suborbit_of_orth {L M : hypIsotropicLines h r ε} (hML : M ≠ L)
    (hLM : LineOrth h L M) :
    Nat.card {M' : hypIsotropicLines h r ε // ∃ x : hypPSU h r ε,
      hypProjLineAction h r ε x L = L ∧ hypProjLineAction h r ε x M = M'} =
    Nat.card {M' : hypIsotropicLines h r ε // M' ≠ L ∧ LineOrth h L M'} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun M' => (suborbit_iff h hML M').trans
    (and_congr_right fun _ => iff_true_left hLM))

theorem card_suborbit_of_not_orth {L M : hypIsotropicLines h r ε} (hLM : ¬ LineOrth h L M) :
    Nat.card {M' : hypIsotropicLines h r ε // ∃ x : hypPSU h r ε,
      hypProjLineAction h r ε x L = L ∧ hypProjLineAction h r ε x M = M'} =
    Nat.card {M' : hypIsotropicLines h r ε // ¬ LineOrth h L M'} := by
  have hML : M ≠ L := fun he => hLM (he ▸ lineOrth_self h L)
  refine Nat.card_congr (Equiv.subtypeEquivRight fun M' => (suborbit_iff h hML M').trans ?_)
  rw [iff_false_left hLM]
  exact ⟨fun hM' => hM'.2, fun hM' => ⟨fun he => hM' (he ▸ lineOrth_self h L), hM'⟩⟩

theorem exists_conj_eq_of_mem_lineNormalizer {φ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hφ : φ ∈ lineNormalizer h r ε) (x : hypPSU h r ε) :
    ∃ y, hypProjLineAction h r ε y = φ * hypProjLineAction h r ε x * φ⁻¹ :=
  (Subgroup.mem_normalizer_iff.mp hφ (hypProjLineAction h r ε x)).mp ⟨x, rfl⟩

theorem suborbit_smul_of_mem_lineNormalizer {φ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hφ : φ ∈ lineNormalizer h r ε) {L M M' : hypIsotropicLines h r ε}
    (hx : ∃ x : hypPSU h r ε, hypProjLineAction h r ε x L = L ∧
      hypProjLineAction h r ε x M = M') :
    ∃ y : hypPSU h r ε, hypProjLineAction h r ε y (φ L) = φ L ∧
      hypProjLineAction h r ε y (φ M) = φ M' := by
  obtain ⟨x, hxL, hxM⟩ := hx
  obtain ⟨y, hy⟩ := exists_conj_eq_of_mem_lineNormalizer h hφ x
  refine ⟨y, ?_, ?_⟩
  · rw [hy, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply, hxL]
  · rw [hy, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
      Equiv.symm_apply_apply, hxM]

theorem card_suborbit_lineNormalizer {φ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hφ : φ ∈ lineNormalizer h r ε) (L M : hypIsotropicLines h r ε) :
    Nat.card {M' : hypIsotropicLines h r ε // ∃ x : hypPSU h r ε,
      hypProjLineAction h r ε x (φ L) = φ L ∧ hypProjLineAction h r ε x (φ M) = M'} =
    Nat.card {M' : hypIsotropicLines h r ε // ∃ x : hypPSU h r ε,
      hypProjLineAction h r ε x L = L ∧ hypProjLineAction h r ε x M = M'} := by
  have hφ' : φ⁻¹ ∈ lineNormalizer h r ε := inv_mem hφ
  have hinv : ∀ M'' : {M' : hypIsotropicLines h r ε // ∃ x : hypPSU h r ε,
      hypProjLineAction h r ε x (φ L) = φ L ∧ hypProjLineAction h r ε x (φ M) = M'},
      ∃ x : hypPSU h r ε, hypProjLineAction h r ε x L = L ∧
        hypProjLineAction h r ε x M = φ⁻¹ M''.1 := fun M'' => by
    have := suborbit_smul_of_mem_lineNormalizer h hφ' M''.2
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using this
  refine (Nat.card_congr
    { toFun := fun M' => ⟨φ M'.1, suborbit_smul_of_mem_lineNormalizer h hφ M'.2⟩
      invFun := fun M'' => ⟨φ⁻¹ M''.1, hinv M''⟩
      left_inv := fun M' => Subtype.ext (by
        change φ⁻¹ (φ M'.1) = M'.1
        simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply])
      right_inv := fun M'' => Subtype.ext (by
        change φ (φ⁻¹ M''.1) = M''.1
        simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]) }).symm

@[expose] def hypLinesEquiv :
    hypIsotropicLines h r ε ≃ TotIsoSubspaces (hypForm h r ε) 1 where
  toFun L := ⟨L.1, L.2.1, isTotIso_of_mem_isoLines (B := hypForm h r ε) L.2⟩
  invFun W := ⟨W.1, W.2.1, fun a ha => W.2.2 a ha a ha⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit h in
theorem finrank_hypIndex_fun : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := by
  rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]

theorem two_le_q (h : UnitaryFieldData p f K) : 2 ≤ p ^ f :=
  h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)

theorem card_orth_hypLines (hr : 2 ≤ r) (L : hypIsotropicLines h r ε) :
    (Nat.card {M : hypIsotropicLines h r ε // M ≠ L ∧ LineOrth h L M} : ℤ) *
        (((p ^ f : ℕ) : ℤ) ^ 2 - 1) =
      ((p ^ f : ℕ) : ℤ) ^ 2 * ((((p ^ f : ℕ) : ℤ) ^ (2 * r + ε - 2) - (-1) ^ (2 * r + ε - 2)) *
        (((p ^ f : ℕ) : ℤ) ^ (2 * r + ε - 2 - 1) - (-1) ^ (2 * r + ε - 2 - 1))) := by
  have hB := hypForm_isSymm h (r := r) (ε := ε)
  have hBl := hypForm_separatingLeft h (r := r) (ε := ε)
  obtain ⟨a, ha0, haa, hLa⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 haa
  obtain ⟨-, -, -, hUsep, hUdim⟩ := hsplit b hab hbb
  have hba : hypForm h r ε b a = 1 := by rw [← hB.eq a b, hab, map_one]
  have hUa : ∀ x ∈ pairOrth (hypForm h r ε) a b, hypForm h r ε x a = 0 := fun x hx => by
    rw [← hB.eq a x,
      (Submodule.mem_orthogonalBilin.mp hx) a (Submodule.subset_span (by simp)), map_zero]
  have e1 : {M : hypIsotropicLines h r ε // M ≠ L ∧ LineOrth h L M} ≃
      {M : TotIsoSubspaces (hypForm h r ε) 1 //
        M.1 ≠ K ∙ a ∧ ∀ y ∈ M.1, hypForm h r ε a y = 0} :=
    (hypLinesEquiv h).subtypeEquiv fun M => by
      refine and_congr ⟨fun hne he => hne (Subtype.ext (he.trans hLa.symm)), fun hne he =>
        hne (by rw [← hLa, ← he]; rfl)⟩ ?_
      change SubOrtho _ _ _ ↔ _
      rw [hLa]
      exact subOrtho_span_left_iff h
  rw [Nat.card_congr e1, card_orth_lines h hB ha0 haa,
    Nat.card_congr (isoFiberEquiv ha0 haa hba hUa 1 :
      {W : TotIsoSubspaces (hypForm h r ε) 2 // a ∈ W.1} ≃ _),
    Nat.cast_mul, Nat.cast_pow (p ^ f) 2, mul_assoc,
    card_isoLines_mul h (hB.domRestrict _) hUsep (m := 2 * r + ε - 2)
      (by rw [hUdim, finrank_hypIndex_fun]) (by omega)]

theorem card_hypLines (hr : 1 ≤ r) :
    (Nat.card (hypIsotropicLines h r ε) : ℤ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) =
      (((p ^ f : ℕ) : ℤ) ^ (2 * r + ε) - (-1) ^ (2 * r + ε)) *
        (((p ^ f : ℕ) : ℤ) ^ (2 * r + ε - 1) - (-1) ^ (2 * r + ε - 1)) := by
  rw [Nat.card_congr (hypLinesEquiv h)]
  exact card_isoLines_mul h (hypForm_isSymm h) (hypForm_separatingLeft h) finrank_hypIndex_fun
    (by omega)

theorem card_hypLines_eq (L : hypIsotropicLines h r ε) :
    Nat.card (hypIsotropicLines h r ε) =
      Nat.card {M : hypIsotropicLines h r ε // M ≠ L ∧ LineOrth h L M} + 1 +
        Nat.card {M : hypIsotropicLines h r ε // ¬ LineOrth h L M} := by
  classical
  have := h.finite
  have : Finite (HypIndex r ε → K) := inferInstance
  rw [← Nat.card_congr (Equiv.sumCompl fun M : hypIsotropicLines h r ε => LineOrth h L M),
    Nat.card_sum, card_subtype_eq_card_ne_add_one (lineOrth_self h L)]

theorem card_not_orth_hypLines (hr : 2 ≤ r) (L : hypIsotropicLines h r ε) :
    Nat.card {M : hypIsotropicLines h r ε // ¬ LineOrth h L M} =
      (p ^ f) ^ (2 * (2 * r + ε) - 3) := by
  have h1 := card_orth_hypLines h hr L
  have h2 := card_hypLines h (r := r) (ε := ε) (by omega)
  have h3 : (Nat.card (hypIsotropicLines h r ε) : ℤ) =
      Nat.card {M : hypIsotropicLines h r ε // M ≠ L ∧ LineOrth h L M} + 1 +
        Nat.card {M : hypIsotropicLines h r ε // ¬ LineOrth h L M} := by
    exact_mod_cast card_hypLines_eq h L
  obtain ⟨j, hj⟩ : ∃ j, 2 * r + ε = j + 4 := ⟨2 * r + ε - 4, by omega⟩
  rw [hj, show j + 4 - 2 = j + 2 by omega, show j + 2 - 1 = j + 1 by omega] at h1
  rw [hj, show j + 4 - 1 = j + 3 by omega] at h2
  rw [hj, show 2 * (j + 4) - 3 = 2 * j + 5 by omega]
  have hq : (2 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast two_le_q h
  have hq1 : ((p ^ f : ℕ) : ℤ) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) ^ 2 := by nlinarith
    intro h0
    linarith
  have hs : ((-1 : ℤ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have key : (Nat.card {M : hypIsotropicLines h r ε // ¬ LineOrth h L M} : ℤ) *
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) =
      ((p ^ f : ℕ) : ℤ) ^ (2 * j + 5) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
    linear_combination h2 - h1 - (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * h3 +
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * hs
  exact_mod_cast mul_right_cancel₀ hq1 key

theorem card_orth_hypLines_eq (hr : 2 ≤ r) {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hV : Module.finrank K V = 2 * r + ε - 2)
    (L : hypIsotropicLines h r ε) :
    Nat.card {M : hypIsotropicLines h r ε // M ≠ L ∧ LineOrth h L M} =
      (p ^ f) ^ 2 * Nat.card (TotIsoSubspaces B 1) := by
  have h1 := card_orth_hypLines h hr L
  have h2 := card_isoLines_mul h hB hBl hV (by omega)
  have hq : (2 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast two_le_q h
  have hq1 : ((p ^ f : ℕ) : ℤ) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) ^ 2 := by nlinarith
    intro h0
    linarith
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, Nat.cast_pow (p ^ f) 2]
  refine mul_right_cancel₀ hq1 ?_
  rw [h1, mul_assoc, h2]

theorem pow_two_mul_card_ne (hr : 2 ≤ r) {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hV : Module.finrank K V = 2 * r + ε - 2) :
    (p ^ f) ^ 2 * Nat.card (TotIsoSubspaces B 1) ≠ (p ^ f) ^ (2 * (2 * r + ε) - 3) := by
  intro heq
  have hI := card_isoLines_mul h hB hBl hV (by omega)
  obtain ⟨j, hj⟩ : ∃ j, 2 * r + ε = j + 4 := ⟨2 * r + ε - 4, by omega⟩
  rw [hj, show j + 4 - 2 = j + 2 by omega, show j + 2 - 1 = j + 1 by omega] at hI
  rw [hj, show 2 * (j + 4) - 3 = 2 * j + 5 by omega] at heq
  have hq : (2 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast two_le_q h
  have hq0 : ((p ^ f : ℕ) : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (by positivity)
  have hcast := congrArg (Nat.cast : ℕ → ℤ) heq
  rw [Nat.cast_mul, Nat.cast_pow (p ^ f) 2, Nat.cast_pow (p ^ f) (2 * j + 5)] at hcast
  have hI' : (Nat.card (TotIsoSubspaces B 1) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (2 * j + 3) := by
    refine mul_left_cancel₀ hq0 ?_
    rw [hcast]
    ring
  have hs : ((-1 : ℤ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hdvd : ((p ^ f : ℕ) : ℤ) ∣ 1 := ⟨2 * ((p ^ f : ℕ) : ℤ) ^ (2 * j + 2) -
      ((p ^ f : ℕ) : ℤ) ^ (2 * j + 4) + (-1) ^ j * ((p ^ f : ℕ) : ℤ) ^ (j + 1) -
      (-1) ^ j * ((p ^ f : ℕ) : ℤ) ^ j, by
    linear_combination hI - (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * hI' - hs⟩
  have := Int.eq_one_of_dvd_one (by positivity) hdvd
  linarith

theorem unitary_normalizer_preserves_orthogonality (hr : 2 ≤ r) :
    (∀ φ ∈ lineNormalizer h r ε, ∀ L M : hypIsotropicLines h r ε,
      LineOrth h L M ↔ LineOrth h (φ L) (φ M)) ∧
    (∀ L M M' : hypIsotropicLines h r ε, M ≠ L →
      ((∃ x : hypPSU h r ε, hypProjLineAction h r ε x L = L ∧
          hypProjLineAction h r ε x M = M') ↔
        M' ≠ L ∧ (LineOrth h L M ↔ LineOrth h L M'))) ∧
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      {B : V →ₛₗ[h.bar] V →ₗ[K] K}, B.IsSymm → B.SeparatingLeft →
      Module.finrank K V = 2 * r + ε - 2 → ∀ L : hypIsotropicLines h r ε,
      Nat.card {M : hypIsotropicLines h r ε // M ≠ L ∧ LineOrth h L M} =
          (p ^ f) ^ 2 * Nat.card (TotIsoSubspaces B 1) ∧
        Nat.card {M : hypIsotropicLines h r ε // ¬ LineOrth h L M} =
          (p ^ f) ^ (2 * (2 * r + ε) - 3) ∧
        (p ^ f) ^ 2 * Nat.card (TotIsoSubspaces B 1) ≠ (p ^ f) ^ (2 * (2 * r + ε) - 3) := by
  refine ⟨fun φ hφ L M => ?_, fun L M M' hML => suborbit_iff h hML M',
    fun hB hBl hV L => ⟨card_orth_hypLines_eq h hr hB hBl hV L, card_not_orth_hypLines h hr L,
      pow_two_mul_card_ne h hr hB hBl hV⟩⟩
  have hV₀ : Module.finrank K (HypIndex (r - 1) ε → K) = 2 * r + ε - 2 := by
    rw [finrank_hypIndex_fun]
    omega
  have hc₁ := card_orth_hypLines_eq h hr (hypForm_isSymm h) (hypForm_separatingLeft h) hV₀
  have hne₀ := pow_two_mul_card_ne h hr (hypForm_isSymm h) (hypForm_separatingLeft h) hV₀
  by_cases hML : M = L
  · rw [hML]
    exact iff_of_true (lineOrth_self h L) (lineOrth_self h (φ L))
  have hφML : φ M ≠ φ L := fun he => hML (φ.injective he)
  have hA := card_suborbit_lineNormalizer h hφ L M
  constructor
  · intro h1
    by_contra h2
    rw [card_suborbit_of_not_orth h h2, card_suborbit_of_orth h hML h1,
      card_not_orth_hypLines h hr, hc₁] at hA
    exact hne₀ hA.symm
  · intro h2
    by_contra h1
    rw [card_suborbit_of_orth h hφML h2, card_suborbit_of_not_orth h h1, hc₁,
      card_not_orth_hypLines h hr] at hA
    exact hne₀ hA

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
