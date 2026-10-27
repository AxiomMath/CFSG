module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem gz9_card_P_le {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hF3 : Vert Fusion3Facts a z) {a₁ : G} (ha₁z : a₁ ∈ Gx z) (ha₁Q : a₁ ∉ Qz z)
    (ha₁ : IsConj a a₁) :
    Nat.card {q : ↥(Gx z) // q ∈ CFSG.pCore 2 ↥(Gx z) ∧
        ⁅q, (⟨a₁, ha₁z⟩ : ↥(Gx z))⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z))} ≤
      Nat.card ↥(CFSG.pCore 2 ↥(Gx z) ⊓
        Subgroup.centralizer ({(⟨a₁, ha₁z⟩ : ↥(Gx z))} : Set ↥(Gx z))) := by
  let t : ↥(Gx z) := ⟨a₁, ha₁z⟩
  have hQext : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hcenter : centerOf (CFSG.pCore 2 ↥(Gx z)) = Subgroup.zpowers (GxSelf z) :=
    centerOf_eq_zpowers h.orderOf_z hQext
  have hz2val : (GxSelf z : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change z ^ 2 = 1
    rw [← h.orderOf_z]
    exact pow_orderOf_eq_one z
  have hcomm : ∀ q : ↥(Gx z), q ∈ CFSG.pCore 2 ↥(Gx z) →
      ⁅q, t⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z)) →
        q ∈ Subgroup.centralizer ({t} : Set ↥(Gx z)) := by
    intro q _ hqZ
    rw [hcenter] at hqZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqZ
    have hkeq : ⁅q, t⁆ = (GxSelf z) ^ (k % (2 : ℤ)) :=
      hk.symm.trans (zpow_eq_zpow_emod' k hz2val)
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · have h1 : ⁅q, t⁆ = 1 := by
        rw [hkeq, hk0]
        exact zpow_zero (GxSelf z)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exfalso
      have hgt : ⁅q, t⁆ = GxSelf z := by
        have h' := hkeq
        rw [hk1] at h'
        simpa using h'
      have hG : (q : G) * a₁ * (q : G)⁻¹ * a₁⁻¹ = z := by
        have hval := congrArg Subtype.val hgt
        simpa only [t, GxSelf, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          using hval
      have hconj : (q : G) * a₁ * (q : G)⁻¹ = a₁ * z := by
        have h1 : (q : G) * a₁ * (q : G)⁻¹ = z * a₁ := by
          have h2 : (q : G) * a₁ * (q : G)⁻¹ * a₁⁻¹ * a₁ = z * a₁ := by
            rw [hG]
          simpa [mul_assoc] using h2
        rw [h1]
        exact mem_Gx.mp ha₁z
      have hconjA : IsConj a₁ (a₁ * z) := isConj_iff.mpr ⟨(q : G), hconj⟩
      have hmem : z ∈ orb2AB a₁ z a₁ := ⟨IsConj.refl z, hconjA⟩
      exact ha₁Q ((hF3 a₁ z ha₁ (IsConj.refl z)).shape_2AB z hmem).2
  refine Nat.card_le_card_of_injective
    (fun q => ⟨q.1, Subgroup.mem_inf.mpr ⟨q.2.1, hcomm q.1 q.2.1 q.2.2⟩⟩) ?_
  intro q q' hq
  have h := congrArg Subtype.val hq
  exact Subtype.ext h

end CFSG.EvenSporadicStandard.HNRecog.Section3
