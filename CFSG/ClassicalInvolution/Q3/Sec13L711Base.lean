module

public import CFSG.ClassicalInvolution.Q3.Sec13L711Def
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Q8Omega

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isSylow2In_self {J : Subgroup G} (h2 : IsPGroup 2 J) : IsSylow2In J J :=
  ⟨le_rfl, h2, fun _ hV _ hle => le_antisymm hV hle⟩

theorem eq_of_isSylow2In {J R : Subgroup G} (h2 : IsPGroup 2 J) (hR : IsSylow2In R J) : R = J :=
  (hR.eq_of_le h2 le_rfl hR.1).symm

variable (hΩ : Q8Omega Ω)
include hΩ

theorem mem_RSet_iff {R : Subgroup G} : R ∈ RSet Ω ↔ R ∈ Ω := by
  constructor
  · intro hR
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    rwa [eq_of_isSylow2In (hΩ.two J hJ) hRJ]
  · intro hR
    exact mem_RSet_of_isSylow2In hR (isSylow2In_self (hΩ.two R hR))

theorem isQuatSub {K : Subgroup G} (hK : K ∈ Ω) : IsQuatSub K :=
  Sec6Gen.isQuatSub_of_mem_RSet hΩ.hyp ((hΩ.mem_RSet_iff).mpr hK)

theorem exists_uniqueInvolution {K : Subgroup G} (hK : K ∈ Ω) : ∃ z : G, IsUniqueInvolution K z :=
  Sec6Gen.exists_uniqueInvolution hΩ.hyp hK

theorem natCard_of_mem_USet {U : Subgroup G} (hU : U ∈ USet Ω) : Nat.card U = 4 := by
  obtain ⟨R, hR, J, hJ, hRJ, -, -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ.hyp hU
  rw [eq_of_isSylow2In (hΩ.two J hJ) hRJ, hΩ.card J hJ] at hcard
  omega

theorem isCyclic_of_mem_USet {U : Subgroup G} (hU : U ∈ USet Ω) : IsCyclic U :=
  (Sec6Gen.exists_data_of_mem_USet hΩ.hyp hU).choose_spec.2.choose_spec.2.2.2.1

theorem isPGroup_of_mem_USet {U : Subgroup G} (hU : U ∈ USet Ω) : IsPGroup 2 U :=
  Sec6Gen.isPGroup_of_mem_USet hΩ.hyp hU

section Quat

variable {K U : Subgroup G} (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hUK : U ≤ K)
include hK hU hUK

theorem natCard_eq_two_mul : Nat.card K = 2 * Nat.card U := by
  rw [hΩ.card K hK, hΩ.natCard_of_mem_USet hU]

theorem conj_eq_inv {k : G} (hk : k ∈ K) (hkU : k ∉ U) {u : G} (hu : u ∈ U) :
    k * u * k⁻¹ = u⁻¹ := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  exact AscL62.conj_eq_inv_of_not_mem (hΩ.isQuatSub hK) hz hUK (hΩ.isCyclic_of_mem_USet hU)
    (natCard_eq_two_mul hΩ hK hU hUK) hk hkU hu

theorem le_normalizer_of_le : K ≤ Subgroup.normalizer (U : Set G) := by
  have key : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
    intro k hk u hu
    by_cases hkU : k ∈ U
    · exact U.mul_mem (U.mul_mem hkU hu) (U.inv_mem hkU)
    · rw [conj_eq_inv hΩ hK hU hUK hk hkU hu]
      exact U.inv_mem hu
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key k hk u, fun hu => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hu
  simpa [mul_assoc] using this

end Quat

end Q8Omega

end CFSG.ClassicalInvolution.Q3.Sec13
