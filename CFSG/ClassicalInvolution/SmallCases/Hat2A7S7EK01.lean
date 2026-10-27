module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM00
public import CFSG.ClassicalInvolution.Q3.Q3T7FUK1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem _root_.CFSG.ClassicalInvolution.Hat2A7E.HM.toU {G : Type} [Group G] {Ω : Set (Subgroup G)} (hΩ : CFSG.ClassicalInvolution.Hat2A7E.HM Ω) :
    CFSG.ClassicalInvolution.T7FU.HM .twoA7 Ω :=
  { toMod := hΩ, toGen := CFSG.ClassicalInvolution.Hat2A7E.HM.toGen hΩ }

end CFSG.ClassicalInvolution.Hat2A7E
namespace CFSG.ClassicalInvolution.Hat2A7E

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace CentQ

theorem omega4_quot (hΩ : HM Ω) (h62 : L6_2On Ω) (X : Subgroup G) [X.Normal]
    (hXc : X ≤ Subgroup.center G) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) = 1 →
        ⁅K.map (QuotientGroup.mk' X), J.map (QuotientGroup.mk' X)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' X)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' X))) :=
  CFSG.ClassicalInvolution.T7FU.CentQ.omega4_quot (CFSG.ClassicalInvolution.Hat2A7E.HM.toU hΩ) h62
    X hXc hXK hK hJ hKJ

theorem classical_quot (hΩ : HM Ω) (h62 : L6_2On Ω) (X : Subgroup G) [X.Normal]
    (hXc : X ≤ Subgroup.center G) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    ∀ L ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω,
      ∃ z : G ⧸ X, IsClassicalMemberU .twoA7 L z := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K hK) hz
  obtain ⟨zc, hzc⟩ := hΩ.classical K hK
  obtain ⟨e'⟩ := AscQuot.nonempty_quotOddCoreEquiv (hXK K hK)
  refine ⟨QuotientGroup.mk' X z, ?_⟩
  refine
    { admissible := trivial
      orderOf_eq_two := orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one
      mem := hz'.mem
      perfect := fun hns => by
        have hKp : Group.IsPerfect ↥K := hzc.perfect hns
        rw [Subgroup.isPerfect_iff] at hKp ⊢
        rw [← Subgroup.map_commutator, hKp]
      subnormal := ?_
      witness := Uniform.MemberType.Witness.of_quotientEquiv e' hzc.witness }
  refine AscQuot.isSubnormal_centralizer ?_ ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hz.commute_of_mem hk]
  · intro c hc hne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective X c
    rw [← AscQuot.map_conjSub] at hne ⊢
    have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    have hKJ : K ≠ conjSub g K := fun h => hne (by rw [← h])
    obtain ⟨h4, h4'⟩ := omega4_quot hΩ h62 X hXc hXK hK hJ hKJ
    have hzJ : QuotientGroup.mk' X z ∈ (conjSub g K).map (QuotientGroup.mk' X) := by
      have h1 : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hz.mem
      refine ⟨g * z * g⁻¹, h1, ?_⟩
      rw [map_mul, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
    have hdvd : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓
        (conjSub g K).map (QuotientGroup.mk' X)) := by
      have := Subgroup.orderOf_dvd_natCard
        (K.map (QuotientGroup.mk' X) ⊓ (conjSub g K).map (QuotientGroup.mk' X))
        (x := QuotientGroup.mk' X z) ⟨hz'.mem, hzJ⟩
      rwa [orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one] at this
    have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
    exact (h4' (le_antisymm h4 h1)).trans inf_le_left

theorem commutes_of_quot (hΩ : HM Ω) (h67 : L6_7On Ω) (h62 : L6_2On Ω) (h69 : L6_9On Ω)
    (h611 : L6_11On Ω) (X : Subgroup G) [X.Normal] (hXc : X ≤ Subgroup.center G)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {v : G} (hvJ : v ∈ J)
    (hvnc : ¬ ∀ w ∈ J, v * w = w * v) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (hvz : QuotientGroup.mk' X v * QuotientGroup.mk' X z =
      QuotientGroup.mk' X z * QuotientGroup.mk' X v) :
    v * z = z * v :=
  CFSG.ClassicalInvolution.T7FU.CentQ.commutes_of_quot (CFSG.ClassicalInvolution.Hat2A7E.HM.toU hΩ)
    h67 h62 h69 h611 X hXc hK hJ hKJ hz hvJ hvnc hv2 hvz

theorem omega5_quot (hΩ : HM Ω) (h67 : L6_7On Ω) (h62 : L6_2On Ω) (h69 : L6_9On Ω)
    (h611 : L6_11On Ω) (X : Subgroup G) [X.Normal] (hXc : X ≤ Subgroup.center G)
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    ∀ L ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω,
      ∀ L' ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω, L ≠ L' →
        ∀ z : G ⧸ X, IsUniqueInvolution L z → ∀ v ∈ L',
          (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
            v ∈ Subgroup.normalizer (L : Set (G ⧸ X)) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne z' hz' _ ⟨v₀, hv₀J, rfl⟩ hvnc hv2 hcomm
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have hz'eq : z' = QuotientGroup.mk' X z :=
    hz'.eq (isUniqueInvolution_map_mk_of_odd (hXK K hK) hz)
  have hv2a : IsPGroup 2 (Subgroup.zpowers
      (⟨QuotientGroup.mk' X v₀, Subgroup.mem_map_of_mem _ hv₀J⟩ :
        ↥(J.map (QuotientGroup.mk' X)))) := by
    obtain ⟨n, hn⟩ := hv2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
    exact hn
  obtain ⟨v, hvb, hv2b⟩ := exists_isPGroup_zpowers_lift (AscQuot.quotRestrict J X)
    (AscQuot.quotRestrict_surjective J X) hv2a
  have hvc : QuotientGroup.mk' X (v : G) = QuotientGroup.mk' X v₀ := congrArg Subtype.val hvb
  have hv2c : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    obtain ⟨n, hn⟩ := hv2b.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Nat.card_zpowers]
    exact hn
  have hvnc' : ¬ ∀ w ∈ J, (v : G) * w = w * v := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hvc, ← map_mul, ← map_mul, h w hw])
  have hvz : QuotientGroup.mk' X (v : G) * QuotientGroup.mk' X z =
      QuotientGroup.mk' X z * QuotientGroup.mk' X (v : G) := by
    rw [hvc]
    exact hz'eq ▸ hcomm
  have hvz' : (v : G) * z = z * v :=
    commutes_of_quot hΩ h67 h62 h69 h611 X hXc hK hJ hKJ hz v.2 hvnc' hv2c hvz
  have hvK : (v : G) ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK J hJ hKJ z hz v v.2 hvnc' hv2c hvz'
  rw [← hvc, mem_normalizer_iff_conjSub_eq, ← AscQuot.map_conjSub,
    mem_normalizer_iff_conjSub_eq.mp hvK]

theorem quotient_hyp (hΩ : HM Ω) (X : Subgroup G) [X.Normal] (hXc : X ≤ Subgroup.center G)
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    HM (Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω) := by
  have h62 : L6_2On Ω := Sec6Gen.l6_2Gen G Ω hΩ.toGen
  have h67 : L6_7On Ω := Q3.Q3CP.l67Gen G Ω hΩ.toGen
  have h69 : L6_9On Ω := Hat2A7E.Asc77.l6_9_proved G Ω hΩ.toGen
  have h611 : L6_11On Ω := Sec6Gen.l6_11Gen G Ω hΩ.toGen
  refine
    { conjInvariant := AscQuot.conjInvariant_quot hΩ.conjInvariant X
      classical := classical_quot hΩ h62 X hXc hXK
      omega4 := ?_
      omega5 := omega5_quot hΩ h67 h62 h69 h611 X hXc hXK }
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
  exact omega4_quot hΩ h62 X hXc hXK hK hJ (fun h => hne (by rw [h]))

end CentQ
end CFSG.ClassicalInvolution.Hat2A7E
