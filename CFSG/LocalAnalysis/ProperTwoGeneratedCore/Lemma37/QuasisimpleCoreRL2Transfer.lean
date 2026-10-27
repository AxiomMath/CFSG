module

public import CFSG.Quasithin.Background.A1cTransfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G]

theorem relIndex_eq_two_of_mul_mem {H K : Subgroup G} {g : G} (hgH : g ∈ H) (hgK : g ∉ K)
    (hcos : ∀ t ∈ H, t ∉ K → t * g ∈ K) : K.relIndex H = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨g, hgH, fun b hb => ?_⟩
  by_cases hbK : b ∈ K
  · exact Or.inr ⟨hbK, fun h => hgK (by simpa using K.mul_mem (K.inv_mem hbK) h)⟩
  · exact Or.inl ⟨hcos b hb hbK, hbK⟩

theorem mul_mem_iff_of_relIndex_eq_two {H K : Subgroup G} (hK : K.relIndex H = 2) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ K ↔ (a ∈ K ↔ b ∈ K) := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := K.subgroupOf H) hK (a := ⟨a, ha⟩)
    (b := ⟨b, hb⟩)
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using h

theorem commutator_le_of_relIndex_eq_two {H K : Subgroup G} (hK : K.relIndex H = 2) :
    ⁅H, H⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def,
    mul_mem_iff_of_relIndex_eq_two hK (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb),
    mul_mem_iff_of_relIndex_eq_two hK (H.mul_mem ha hb) (H.inv_mem ha),
    mul_mem_iff_of_relIndex_eq_two hK ha hb, K.inv_mem_iff, K.inv_mem_iff]
  tauto

theorem not_mem_commutator_of_relIndex_eq_two [Finite G] {H K : Subgroup G}
    (hindex : Nat.Coprime 2 H.index) (hKH : K ≤ H) (hK : K.relIndex H = 2) {g : G}
    (hgH : g ∈ H) (hgK : g ∉ K) (hgp : ∃ n : ℕ, g ^ 2 ^ n = 1)
    (hcond : ∀ (m : ℤ) (a : G), a⁻¹ * g ^ m * a ∈ H → (g ^ m ∈ K ↔ a⁻¹ * g ^ m * a ∈ K)) :
    g ∉ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.Quasithin.generalized_thompson_transfer_one hindex
    ⟨hKH, Subgroup.normal_of_index_eq_two hK⟩ (commutator_le_of_relIndex_eq_two hK) hgH hgK hgp
    fun m a ha => ?_
  rw [mul_mem_iff_of_relIndex_eq_two hK (H.inv_mem (H.zpow_mem hgH m)) ha, K.inv_mem_iff]
  exact hcond m a ha

theorem false_of_relIndex_eq_two [Finite G] (hperf : Group.IsPerfect G) (S : Sylow 2 G)
    {K : Subgroup G} (hKS : K ≤ S) (hK : K.relIndex S = 2) {g : G} (hgS : g ∈ (S : Subgroup G))
    (hgK : g ∉ K)
    (hcond : ∀ (m : ℤ) (a : G), a⁻¹ * g ^ m * a ∈ (S : Subgroup G) →
      (g ^ m ∈ K ↔ a⁻¹ * g ^ m * a ∈ K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : Nat.Coprime 2 (S : Subgroup G).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, hgS⟩
  exact not_mem_commutator_of_relIndex_eq_two hindex hKS hK hgS hgK
    ⟨k, by simpa using congrArg Subtype.val hk⟩ hcond
    (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top g)

theorem not_mem_commutator_of_central [Finite G] {C R K : Subgroup G} (hRC : R ≤ C)
    (hindex : Nat.Coprime 2 (R.relIndex C)) (hKR : K ≤ R) (hK : K.relIndex R = 2) {z : G}
    (hzR : z ∈ R) (hzK : z ∉ K) (hzz : z * z = 1) (hcen : ∀ c ∈ C, c * z = z * c) :
    z ∉ ⁅C, C⁆ := by
  intro hz
  have hzC : z ∈ C := hRC hzR
  have hz' : (⟨z, hzC⟩ : C) ∈ commutator C := by
    rw [← Subgroup.map_subtype_commutator] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    rwa [show w = ⟨z, hzC⟩ from Subtype.ext hwz] at hw
  refine not_mem_commutator_of_relIndex_eq_two (H := R.subgroupOf C) (K := K.subgroupOf C)
    hindex (fun x hx => Subgroup.mem_subgroupOf.mpr (hKR (Subgroup.mem_subgroupOf.mp hx)))
    (by rw [Subgroup.relIndex_subgroupOf hRC]; exact hK) (Subgroup.mem_subgroupOf.mpr hzR)
    (fun h => hzK (Subgroup.mem_subgroupOf.mp h)) ⟨1, Subtype.ext (by simpa [sq] using hzz)⟩
    (fun m a _ => ?_) hz'
  have hcomm : Commute a (⟨z, hzC⟩ : C) := Subtype.ext (hcen a a.2)
  rw [mul_assoc, ← (hcomm.zpow_right m).eq, inv_mul_cancel_left]

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
