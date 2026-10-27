module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearData

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

@[expose] noncomputable def sylowBar (hz : IsCentralInvolution (S : Subgroup G) z) :
    (S : Subgroup G) →* EscapingQuotient z :=
  (escapingMk z).comp (Subgroup.inclusion hz.le_centralizer)

omit [Finite G] in
theorem sylowBar_apply (hz : IsCentralInvolution (S : Subgroup G) z) (s : (S : Subgroup G)) :
    sylowBar hz s = escapingMk z ⟨s, hz.le_centralizer s.2⟩ := rfl

omit [Finite G] in
theorem sylowBar_self (hz : IsCentralInvolution (S : Subgroup G) z) :
    sylowBar hz ⟨z, hz.1⟩ = escapingBar z := rfl

theorem sylowBar_injective (hz : IsCentralInvolution (S : Subgroup G) z) :
    Function.Injective (sylowBar hz) := by
  intro a b h
  have := escapingMk_injOn_twoGroup S.isPGroup' (a := ⟨a, hz.le_centralizer a.2⟩)
    (b := ⟨b, hz.le_centralizer b.2⟩) a.2 b.2 h
  exact Subtype.ext (congrArg (fun m : Subgroup.centralizer ({z} : Set G) => (m : G)) this)

omit [Finite G] in
theorem sylowBar_range (hz : IsCentralInvolution (S : Subgroup G) z) :
    (sylowBar hz).range = escapingSylowImage S z := by
  rw [sylowBar, MonoidHom.range_comp, Subgroup.inclusion_range]

noncomputable def sylowBarSylow (hz : IsCentralInvolution (S : Subgroup G) z) :
    Sylow 2 (EscapingQuotient z) :=
  (S.subtype hz.le_centralizer).mapSurjective (QuotientGroup.mk'_surjective _)

theorem coe_sylowBarSylow (hz : IsCentralInvolution (S : Subgroup G) z) :
    (sylowBarSylow hz : Subgroup (EscapingQuotient z)) = (sylowBar hz).range := by
  rw [sylowBar_range, sylowBarSylow, Sylow.coe_mapSurjective, Sylow.coe_subtype]

theorem mul_self_eq_one_of_sylowBar (hz : IsCentralInvolution (S : Subgroup G) z)
    {s : (S : Subgroup G)} (hs : sylowBar hz s * sylowBar hz s = 1) : (s : G) * s = 1 := by
  have h : sylowBar hz (s * s) = sylowBar hz 1 := by rw [map_mul, hs, map_one]
  exact congrArg Subtype.val (sylowBar_injective hz h)

theorem commute_of_sylowBar (hz : IsCentralInvolution (S : Subgroup G) z)
    {s t : (S : Subgroup G)} (h : sylowBar hz s * sylowBar hz t = sylowBar hz t * sylowBar hz s) :
    (s : G) * t = t * s := by
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (sylowBar_injective hz h)

section Component

variable {H : Subgroup G} (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
include hset hz hesc hJ hzJ

omit hJ hzJ in
theorem caseOne_quotientData : EscapingQuotientData H z :=
  escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc

theorem caseOne_component_normal : J.Normal :=
  (caseOne_quotientData hset hz hesc).component_normal hJ hzJ

theorem exists_linearSylowData {n : ℕ} (hn : 2 ≤ n) (e : J ≃* CFSG.Theory.Comparator.PSL2Model n) :
    ∃ D : Subgroup (EscapingQuotient z),
      LinearSylowData J ((sylowBar hz).range ⊓ J) D (2 ^ n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := caseOne_component_normal hset hz hesc hJ hzJ
  set T := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal (sylowBarSylow hz) J
  have hT := CFSG.ProperTwoGeneratedCore.normal_sylow_intersection_eq (sylowBarSylow hz) J
  rw [coe_sylowBarSylow] at hT
  rw [← hT]
  exact linearSylowData_of_mulEquiv hn e T

end Component

end CFSG.ProperTwoGeneratedCore.Lemma37
