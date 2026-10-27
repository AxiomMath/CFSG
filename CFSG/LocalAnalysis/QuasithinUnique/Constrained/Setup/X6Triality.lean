module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section Index

variable {t : TwistTag} {K : Type} [Field K] [Finite K]

theorem relIndex_graphFixedParabolic_singleton
    (σ : K ≃+* K) (a : Fin t.foldedTag.rank) :
    (graphFixedRootBorel t K σ.toRingHom).relIndex
        (graphFixedParabolic t K σ.toRingHom {a}) =
      1 + Nat.card (orbitField t K σ.toRingHom a) := by
  classical
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have : Finite (ModGL t.tag K) := finite_modGL
  set B := graphFixedRootBorel t K σ.toRingHom with hB
  set P := graphFixedParabolic t K σ.toRingHom {a} with hP
  have hBP : B ≤ P := graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom {a}
  have hcell : ∀ w : WeylGroup t.tag, w ∈ relWeylTwist t →
      Nat.card (graphFixedRootBruhatCell t K σ.toRingHom w) =
        Nat.card B * Nat.card (graphFixedInversionUnipotent t K σ.toRingHom w) := by
    intro w hw
    rw [← Nat.card_congr (bijOn_graphFixedRootBruhatCell hσ hw).equiv,
      Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    rfl
  have hD1 : graphFixedRootBruhatCell t K σ.toRingHom 1 = (B : Set (ModGL t.tag K)) := by
    ext x
    rw [mem_graphFixedRootBruhatCell]
    constructor
    · rintro ⟨b, hb, b', hb', rfl⟩
      rw [canonicalRep_one, mul_one]
      exact mul_mem hb hb'
    · intro hx
      exact ⟨x, hx, 1, one_mem _, by rw [canonicalRep_one]; simp⟩
  have hPset : (P : Set (ModGL t.tag K)) =
      graphFixedRootBruhatCell t K σ.toRingHom 1 ∪
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) := by
    rw [hP, graphFixedParabolic_eq_cells hσ]
    ext x
    simp only [mem_graphFixedParabolicCells, Set.mem_union]
    constructor
    · rintro ⟨w, hw, hx⟩
      rcases mem_foldedParabolicWeylGroup_singleton hw with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨1, one_mem _, hx⟩
      · exact ⟨t.orbitReflection a,
          orbitReflection_mem_foldedParabolicWeylGroup_iff.2 (Set.mem_singleton a), hx⟩
  have hdisj : Disjoint (graphFixedRootBruhatCell t K σ.toRingHom 1)
      (graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a)) :=
    disjoint_graphFixedRootBruhatCell (t.orbitReflection_ne_one a).symm
  have hU : graphFixedInversionUnipotent t K σ.toRingHom (t.orbitReflection a) =
      orbitXSubgroup t K σ.toRingHom a := by
    rw [orbitXSubgroup, closure_range_orbitX, graphFixedInversionUnipotent,
      inversionSet_orbitReflection]
  have hnc : ∀ s : Set (ModGL t.tag K), Nat.card s = s.ncard := fun s => Nat.card_coe_set_eq s
  have hcardP : Nat.card P = Nat.card B + Nat.card B * Nat.card (orbitField t K σ.toRingHom a) := by
    have e1 : Nat.card P = (P : Set (ModGL t.tag K)).ncard := hnc (P : Set (ModGL t.tag K))
    rw [e1, hPset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ← hnc, ← hnc, hD1,
      hcell _ (t.orbitReflection_mem a), hU, natCard_orbitXSubgroup]
    rfl
  have hmul : B.relIndex P * Nat.card B = Nat.card P := by
    have h := Subgroup.relIndex_mul_card B P
    rwa [inf_eq_left.2 hBP] at h
  have hpos : 0 < Nat.card B := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hmul, hcardP]
  ring

end Index

section Triality

variable {f : ℕ} {K : Type} [Field K] [Finite K]

theorem foldedRank_D4_cases (a : Fin TwistTag.D4.foldedTag.rank) :
    a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ := by
  revert a
  decide

theorem card_orbit_D4 :
    (TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 3 ∧
      (TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 1 := by
  decide

theorem triality_hasUnequalCovers
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∃ U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧
        HasUnequalCovers (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) U
          ((2 ^ f) ^ 3 + 1) (2 ^ f + 1) := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨σ', hσ', -, hcard', -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  subst hσσ'
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ C :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      C := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hBnorm := (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
  obtain ⟨hcov, hinj, -⟩ := exceptional_fixed_minimal_Borel_intersections TwistTag.D4 K σ
  have hcov' : ∀ A : Subgroup (ModGL TwistTag.D4.tag K), A ≤ C →
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖ A ↔
        A = graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨0, by decide⟩} ∨
          A = graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩}) := by
    intro A hA
    rw [(hcov A hA)]
    constructor
    · rintro ⟨a, rfl⟩
      rcases foldedRank_D4_cases a with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
  set P₀ := graphFixedParabolic TwistTag.D4 K σ.toRingHom {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}
    with hP₀
  set P₁ := graphFixedParabolic TwistTag.D4 K σ.toRingHom {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}
    with hP₁
  have hP₀C : P₀ ≤ C := graphFixedParabolic_le _ _ _ _
  have hP₁C : P₁ ≤ C := graphFixedParabolic_le _ _ _ _
  have hne : P₀ ≠ P₁ := fun h => by
    have := @hinj ⟨0, by decide⟩ ⟨1, by decide⟩ h
    exact absurd (congrArg Fin.val this) (by decide)
  have hcov₀ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖ P₀ :=
    (hcov' P₀ hP₀C).2 (Or.inl rfl)
  have hcov₁ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖ P₁ :=
    (hcov' P₁ hP₁C).2 (Or.inr rfl)
  have hP₀ne : P₀ ≠ C := fun h =>
    hcov₀.2 hcov₁.lt (lt_of_le_of_ne (hP₁C.trans_eq h.symm) hne.symm)
  have hP₁ne : P₁ ≠ C := fun h => hcov₁.2 hcov₀.lt (lt_of_le_of_ne (hP₀C.trans_eq h.symm) hne)
  have hgen : P₀ ⊔ P₁ = C := by
    refine le_antisymm (sup_le hP₀C hP₁C) ?_
    rw [hC, graphFixedRootGroup_eq_sup_closure hσs]
    refine sup_le (le_sup_of_le_left (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _))
      ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨a, rfl⟩
    rcases foldedRank_D4_cases a with rfl | rfl
    · exact Subgroup.mem_sup_left
        (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, Set.mem_singleton _, rfl⟩))
    · exact Subgroup.mem_sup_right
        (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, Set.mem_singleton _, rfl⟩))
  have hi₀ : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex P₀ = (2 ^ f) ^ 3 + 1 := by
    have h := relIndex_graphFixedParabolic_singleton σ
      (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
    rw [hcard', card_orbit_D4.1] at h
    rw [add_comm]
    exact h
  have hi₁ : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex P₁ = 2 ^ f + 1 := by
    have h := relIndex_graphFixedParabolic_singleton σ
      (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
    rw [hcard', card_orbit_D4.2, pow_one] at h
    rw [add_comm]
    exact h
  exact ⟨(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C,
    isSylowTwoOf_subgroupOf_top hUsyl,
    hasUnequalCovers_of_ambient hUsyl hBnorm hcov' hP₀C hP₁C hP₀ne hP₁ne hgen hi₀ hi₁⟩

theorem exists_mulEquiv_triality_model
    {X : Type} [Group X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) :
    1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧
        Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hf : 1 ≤ f := hX.1.2.1
  obtain ⟨K, hF, hFin, hK, σ₀, hσ₀, ⟨e⟩⟩ := hX.2
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK'
  have h0 : σ₀ = σ.toRingHom := RingHom.ext fun c => (hσ₀ c).trans (hσ c).symm
  subst h0
  obtain ⟨-, -, -, -, -, -, -, ⟨e'⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK' σ hσ
  exact ⟨hf, K, hF, hFin, σ, hK', hσ, ⟨e.trans e'⟩⟩

theorem even_triality_model_two_extensions
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) :
    Subgroup.center X = ⊥ ∧
    TwoGeneratingSylowOvergroups X ∧
    (∀ D : Subgroup (MulAut X), inner X ≤ D →
      IsPGroup 2 (D ⧸ (inner X).subgroupOf D) → ∀ R : Subgroup (MulAut X),
        CFSG.QuasithinUnique.IsSylowTwoOf R D →
          ∃ M₁ M₂ : Subgroup (MulAut X), M₁ ≠ M₂ ∧ M₁ ⋖ D ∧ M₂ ⋖ D ∧ R ≤ M₁ ∧ R ≤ M₂) ∧
    ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ →
      HasUnequalCovers X U (2 ^ (3 * f) + 1) (2 ^ f + 1) := by
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨U₀, hU₀, hcov⟩ := triality_hasUnequalCovers hf hK σ hσ
  have hZC : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial _ _ σ
  have hpow : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  have hne : (2 ^ f) ^ 3 + 1 ≠ 2 ^ f + 1 := by
    intro h
    have h1 : (2 ^ f) ^ 3 = 2 ^ f := Nat.add_right_cancel h
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      have hq : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hgen : TwoGeneratingSylowOvergroups (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    hcov.twoGenerating hZC hU₀ hne
  have hgenX : TwoGeneratingSylowOvergroups X := hgen.of_mulEquiv e.symm
  refine ⟨?_, hgenX, fun D hD _ R hR => (hgenX D hD R hR).exists_two_maximal, fun U hU => ?_⟩
  · have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [hZC] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  · have h := hcov.of_isSylow e hU₀ hU
    rwa [hpow] at h

end Triality

end CFSG.QuasithinUnique.Setup.X6
