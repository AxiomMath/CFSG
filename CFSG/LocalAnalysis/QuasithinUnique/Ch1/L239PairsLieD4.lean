module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section Invariance

variable {X : Type*} [Group X]

theorem invariant_of_unequal_covers {U P₁ P₂ : Subgroup X}
    (hcov : ∀ A : Subgroup X, Subgroup.normalizer (U : Set X) ⋖ A ↔ A = P₁ ∨ A = P₂)
    (hidx : (Subgroup.normalizer (U : Set X)).relIndex P₁ ≠
      (Subgroup.normalizer (U : Set X)).relIndex P₂) :
    ∀ α : MulAut X, U.map α.toMonoidHom = U →
      P₁.map α.toMonoidHom = P₁ ∧ P₂.map α.toMonoidHom = P₂ := by
  intro α hα
  set B := Subgroup.normalizer (U : Set X) with hB
  have hB1 : B ⋖ P₁ := (hcov P₁).2 (Or.inl rfl)
  have hB2 : B ⋖ P₂ := (hcov P₂).2 (Or.inr rfl)
  have hBα : B.map α.toMonoidHom = B := by
    rw [hB, Subgroup.map_equiv_normalizer_eq, hα]
  have hcovα : ∀ P : Subgroup X, B ⋖ P →
      P.map α.toMonoidHom = P₁ ∨ P.map α.toMonoidHom = P₂ := by
    intro P hP
    have h := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α)).2 hP
    change B.map α.toMonoidHom ⋖ P.map α.toMonoidHom at h
    rw [hBα] at h
    exact (hcov _).1 h
  have hrel : ∀ P : Subgroup X, B.relIndex (P.map α.toMonoidHom) = B.relIndex P := by
    intro P
    have := Subgroup.relIndex_map_map_of_injective (f := α.toMonoidHom) B P α.injective
    rwa [hBα] at this
  refine ⟨?_, ?_⟩
  · rcases hcovα P₁ hB1 with h | h
    · exact h
    · exact absurd ((hrel P₁).symm.trans (by rw [h])) hidx
  · rcases hcovα P₂ hB2 with h | h
    · exact absurd ((hrel P₂).symm.trans (by rw [h])).symm hidx
    · exact h

end Invariance

section Covers

variable {K : Type} [Field K] [Finite K]

theorem triality_named_covers
    {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    CFSG.QuasithinUnique.IsSylowTwoOf
        ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ⊤ ∧
      (∀ A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) : Set _) ⋖ A ↔
          A = (P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∨
            A = (P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      (P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ ⊤ ∧
      (P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ ⊤ ∧
      (P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊔
          (P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊤ ∧
      (Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) : Set _)).relIndex
          ((P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        (2 ^ f) ^ 3 + 1 ∧
      (Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) : Set _)).relIndex
          ((P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = 2 ^ f + 1 := by
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
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) C := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hBnorm := (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
  obtain ⟨hcov, hinj, -⟩ := exceptional_fixed_minimal_Borel_intersections TwistTag.D4 K σ
  have hcov' : ∀ A : Subgroup (ModGL TwistTag.D4.tag K), A ≤ C →
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖ A ↔
        A = P0 σ ∨ A = P1 σ) := by
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
  have hP₀C : P0 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hP₁C : P1 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hne : P0 σ ≠ P1 σ := fun h => by
    have := @hinj ⟨0, by decide⟩ ⟨1, by decide⟩ h
    exact absurd (congrArg Fin.val this) (by decide)
  have hcov₀ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖ P0 σ :=
    (hcov' (P0 σ) hP₀C).2 (Or.inl rfl)
  have hcov₁ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ⋖ P1 σ :=
    (hcov' (P1 σ) hP₁C).2 (Or.inr rfl)
  have hP₀ne : P0 σ ≠ C := fun h =>
    hcov₀.2 hcov₁.lt (lt_of_le_of_ne (hP₁C.trans_eq h.symm) hne.symm)
  have hP₁ne : P1 σ ≠ C := fun h =>
    hcov₁.2 hcov₀.lt (lt_of_le_of_ne (hP₀C.trans_eq h.symm) hne)
  have hgen : P0 σ ⊔ P1 σ = C := by
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
  have hi₀ : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex (P0 σ) =
      (2 ^ f) ^ 3 + 1 := by
    have h := relIndex_graphFixedParabolic_singleton σ
      (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
    rw [hcard', card_orbit_D4.1] at h
    rw [add_comm]
    exact h
  have hi₁ : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex (P1 σ) = 2 ^ f + 1 := by
    have h := relIndex_graphFixedParabolic_singleton σ
      (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)
    rw [hcard', card_orbit_D4.2, pow_one] at h
    rw [add_comm]
    exact h
  obtain ⟨hc, hn₁, hn₂, hg, hnorm⟩ := ambient_covers_data hUsyl.1 hBnorm hcov' hP₀C hP₁C hP₀ne hP₁ne hgen
  refine ⟨isSylowTwoOf_subgroupOf_top hUsyl, hc, hn₁, hn₂, hg, ?_, ?_⟩
  · rw [hnorm, Subgroup.relIndex_subgroupOf hP₀C]; exact hi₀
  · rw [hnorm, Subgroup.relIndex_subgroupOf hP₁C]; exact hi₁

end Covers

section Pair

variable {K : Type} [Field K] [Finite K]

theorem hasParabolicPair
    {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    HasParabolicPair ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
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
  obtain ⟨-, hcov, h₀, h₁, hgen, hi₀, hi₁⟩ := triality_named_covers hf σ hK hσ
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
  have hP₀C : P0 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  have hP₁C : P1 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  have hQ₀C : Q0 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have hQ₁C : Q1 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  refine ⟨(P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), h₀, h₁, hgen, hinv,
    ⟨(Q0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ?_⟩,
    ⟨(Q1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ?_⟩⟩
  · refine ParabolicFacts.of_map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀C, Subgroup.map_subgroupOf_eq_of_le hQ₀C]
    exact parabolicFacts_a0 σ hσ3 hK4
  · refine ParabolicFacts.of_map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact parabolicFacts_a1 σ hσ3

end Pair

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6

theorem pairsFor_3D4
    : PairsFor Type3D4 := by
  intro G _ _ L R _ hty _ hRN hS
  obtain ⟨f, hf, hmod⟩ := hty
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hmod
  exact pairConclusion_of_hasParabolicPair e (D4.triality_named_covers hf σ hK hσ).1
    (D4.hasParabolicPair hf σ hK hσ) hRN hS

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
