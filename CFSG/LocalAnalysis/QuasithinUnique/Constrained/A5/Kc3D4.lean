module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Odd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LieType.BorelTits.AllModels
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
public import Certificates.Certificate3950
public import Certificates.Certificate17030
public import Certificates.Certificate3951
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.A5.Kc3G2
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

theorem isoInv_d4ev (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3D4Ev X) :
    Kc3D4Ev Y :=
  let ⟨f, hf, hev, hm⟩ := h
  ⟨f, hf, hev, chevalleyExceptionalModel_of_mulEquiv e hm⟩

theorem d4_fin_two_cases : ∀ i : Fin TwistTag.D4.foldedTag.rank, i = D4.fa0 ∨ i = D4.fa1 := by
  intro i
  have h2 : TwistTag.D4.foldedTag.rank = 2 := by decide
  rcases i with ⟨i, hi⟩
  rw [h2] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem d4_rt2
    (G : Type) [Group G] [Finite G] (K : Subgroup G) (h : Kc3D4Ev ↥K) :
    BT2 K ∧ Lat2 K := by
  obtain ⟨f, hf, -, hmodel⟩ := h
  refine ⟨bt2_of_holds K (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hmodel),
    lat2_of_lattice K ?_⟩
  intro U' hU'
  obtain ⟨K0, hF, hFin, σ, φ, hK, hσ, -, hres, -⟩ := even_rank_two_residual_triality hmodel hU'
  have hK3 : Nat.card K0 = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K0 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K0) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ f) ^ 3) = c := by
      have : Fintype K0 := Fintype.ofFinite K0
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
    ring
  have hK4 : 4 ≤ Nat.card K0 := by
    rw [hK3]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun j => ((graphFixedParabolic TwistTag.D4 K0 σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom)).map φ.symm.toMonoidHom,
    fun j => ((graphFixedParabolicRadical TwistTag.D4 K0 σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom)).map φ.symm.toMonoidHom, hres, fun j => ?_⟩
  have hPC : ∀ i : Fin TwistTag.D4.foldedTag.rank,
      graphFixedParabolic TwistTag.D4 K0 σ.toRingHom {i} ≤
        graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom := fun i =>
    graphFixedParabolic_le _ _ _ _
  have hQC : ∀ i : Fin TwistTag.D4.foldedTag.rank,
      graphFixedParabolicRadical TwistTag.D4 K0 σ.toRingHom {i} ≤
        graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom := fun i =>
    graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have key : ∀ i : Fin TwistTag.D4.foldedTag.rank,
      ParabolicFacts (graphFixedParabolic TwistTag.D4 K0 σ.toRingHom {i})
        (graphFixedParabolicRadical TwistTag.D4 K0 σ.toRingHom {i}) →
      ParabolicFacts (((graphFixedParabolic TwistTag.D4 K0 σ.toRingHom {i}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom)).map φ.symm.toMonoidHom)
        (((graphFixedParabolicRadical TwistTag.D4 K0 σ.toRingHom {i}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom)).map φ.symm.toMonoidHom) := by
    intro i hi
    refine ParabolicFacts.map ?_ φ.symm.toMonoidHom φ.symm.injective
    refine ParabolicFacts.of_map (graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K0 σ.toRingHom).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le (hPC i), Subgroup.map_subgroupOf_eq_of_le (hQC i)]
    exact hi
  refine key (d4Index j) ?_
  rcases d4_fin_two_cases (d4Index j) with h | h
  · rw [h]
    exact D4.parabolicFacts_a0 σ hσ3 hK4
  · rw [h]
    exact D4.parabolicFacts_a1 σ hσ3

theorem kc3ForS'_d4_even
    : Kc3ForS' Kc3D4Ev :=
  kc3ForS'_of_rt2 fun G _ _ K h => d4_rt2 G K h

theorem kc3For_d4_even
    : Kc3For Kc3D4Ev :=
  kc3For_of_simple' isoInv_d4ev kc3ForS'_d4_even

end CFSG.QuasithinUnique.A5
