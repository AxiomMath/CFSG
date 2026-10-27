module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4

public section

namespace CFSG.QuasithinUnique.B113Lie.D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem overgroup_le_parabolic
    (σ : K ≃+* K) (A : Subgroup (ModGL TwistTag.D4.tag K))
    (hUA : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ A)
    (hAC : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hAne : A ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    A ≤ P0 σ ∨ A ≤ P1 σ := by
  obtain ⟨J, hJ, hAJ, -⟩ :=
    (fixed_positive_root_overgroup_parabolic_containment TwistTag.D4 K σ hAC hUA).2.2 hAne
  obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
    by_contra h
    exact hJ (Set.eq_univ_of_forall fun a => not_not.1 fun ha => h ⟨a, ha⟩)
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  rcases foldedRank_D4_cases a with rfl | rfl
  · right
    refine hAJ.trans ((graphFixedParabolic_le_iff hσs).2 fun j hj => ?_)
    rcases foldedRank_D4_cases j with rfl | rfl
    · exact absurd hj ha
    · exact Set.mem_singleton _
  · left
    refine hAJ.trans ((graphFixedParabolic_le_iff hσs).2 fun j hj => ?_)
    rcases foldedRank_D4_cases j with rfl | rfl
    · exact Set.mem_singleton _
    · exact absurd hj ha

theorem parabolicData
    {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ParabolicData ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      {(P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ f) ^ 3) = c := by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
    ring
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK3]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hU, hcov, h₀, h₁, hgen, hi₀, hi₁⟩ := triality_named_covers hf σ hK hσ
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hne : (2 ^ f) ^ 3 + 1 ≠ 2 ^ f + 1 := by
    intro h
    have h1 : (2 ^ f) ^ 3 = 2 ^ f := Nat.add_right_cancel h
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hinv := invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; exact hne)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hP₀C : P0 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hP₁C : P1 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hQ₀C : Q0 σ ≤ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have hQ₁C : Q1 σ ≤ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ C :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUP : ∀ P : Subgroup ↥C, P = (P0 σ).subgroupOf C ∨ P = (P1 σ).subgroupOf C →
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C ≤ P := by
    intro P hP
    exact (Subgroup.le_normalizer).trans ((hcov P).2 hP).le
  refine ParabolicData.of_pair hU (hUP _ (Or.inl rfl)) (hUP _ (Or.inr rfl)) h₀ h₁ hgen
    (cover_subgroupOf hUC (fun A hUA hAC hAne => overgroup_le_parabolic σ A hUA hAC hAne))
    ?_ ?_ hinv
  · refine (ParabolicFacts.of_map (Q := (Q0 σ).subgroupOf C) C.subtype C.subtype_injective
      ?_).charTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀C, Subgroup.map_subgroupOf_eq_of_le hQ₀C]
    exact parabolicFacts_a0 σ hσ3 hK4
  · refine (ParabolicFacts.of_map (Q := (Q1 σ).subgroupOf C) C.subtype C.subtype_injective
      ?_).charTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact parabolicFacts_a1 σ hσ3

end CFSG.QuasithinUnique.B113Lie.D4

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X6

theorem d4_sylowFacts
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) :
    SylowFacts S T := by
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model h
  have : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.TwistTag.D4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  exact SylowFacts.of_mulEquiv_isSylow e (D4.parabolicData hf σ hK hσ).sylowFacts hT

end CFSG.QuasithinUnique.B113Lie
