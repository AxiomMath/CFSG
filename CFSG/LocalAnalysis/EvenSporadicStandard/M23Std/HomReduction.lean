module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.OneClass

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

namespace OneClassData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} (h : OneClassData L z t)
include h

theorem exists_fused [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ l ∈ L, l * l = 1 ∧ l ≠ 1 ∧ IsConj z (l * z) := by
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.z_mul_self) h.z_ne_one
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution hnonab hz2
  set z' : G := g * z * g⁻¹ with hz'
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply h.z_ne_one
    have : g * z * g⁻¹ = 1 := h1
    simpa using this
  obtain ⟨l, hl, hcases⟩ := h.centralizer_z z' hcomm.symm
  have hconj : IsConj z z' := (isConj_iff.2 ⟨g, rfl⟩ : IsConj z z')
  rcases hcases with hl' | hl'
  · exfalso
    rw [hl'] at hz'2 hz'1 hconj
    exact h.not_isConj_z_of_mem hl hz'2 hz'1 hconj
  · rw [hl'] at hz'2 hconj hne
    have hl2 : l * l = 1 := by rw [← h.mul_z_sq hl]; exact hz'2
    refine ⟨l, hl, hl2, ?_, hconj⟩
    rintro rfl
    exact hne (by simp)

theorem false_of_hom [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (M : Subgroup G)
    (hM : ∀ g : G, g ∈ M ↔ g * t = t * g) (φ : M →* Multiplicative (ZMod 2)) (hzt : z ∈ M)
    (hφ : φ ⟨z, hzt⟩ ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.z_mul_self) h.z_ne_one
  have hZ := h.exists_fused hnonab
  have hMeq : M = Subgroup.centralizer ({t} : Set G) :=
    Subgroup.ext fun g => by rw [hM, Subgroup.mem_centralizer_singleton_iff]
  have hodd : Odd M.index := by rw [hMeq]; exact h.odd_index_centralizer hZ
  let zM : M := ⟨z, hzt⟩
  have hzM2 : orderOf zM = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hP : IsPGroup 2 (Subgroup.zpowers zM) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hzM2, pow_one])
  obtain ⟨S₀, hS₀⟩ := hP.exists_le_sylow
  let S : Subgroup G := (S₀ : Subgroup M).map M.subtype
  have hSM : S ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hzS : z ∈ S := ⟨zM, hS₀ (Subgroup.mem_zpowers zM), rfl⟩
  have hSp : IsPGroup 2 S :=
    (S₀.isPGroup').of_equiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)
  have hSrel : S.relIndex M = (S₀ : Subgroup M).index := by
    rw [Subgroup.relIndex, show S.subgroupOf M = S₀ from
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _]
  have hSidx : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_mul_index hSM, hSrel, Nat.Prime.dvd_mul Nat.prime_two]
    rintro (h1 | h1)
    · exact Sylow.not_dvd_index S₀ h1
    · exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)
  let U₀ : Subgroup M := (S₀ : Subgroup M) ⊓ φ.ker
  let U : Subgroup G := U₀.map M.subtype
  have hUS : U ≤ S := Subgroup.map_mono inf_le_left
  have hzU : z ∉ U := by
    rintro ⟨y, hy, hyz⟩
    have : y = zM := Subtype.ext hyz
    rw [this] at hy
    exact hφ (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hy).2)
  have hU2 : U.relIndex S = 2 := by
    have h1 : U.relIndex S = U₀.relIndex (S₀ : Subgroup M) :=
      Subgroup.relIndex_map_map_of_injective _ _ M.subtype_injective
    rw [h1, show U₀ = (S₀ : Subgroup M) ⊓ φ.ker from rfl, Subgroup.inf_relIndex_left]
    have h2 : φ.ker.relIndex (S₀ : Subgroup M) = (φ.comp (S₀ : Subgroup M).subtype).ker.index := by
      rw [← MonoidHom.comap_ker]; rfl
    rw [h2, Subgroup.index_ker]
    have hdvd : Nat.card (φ.comp (S₀ : Subgroup M).subtype).range ∣ 2 := by
      have := Subgroup.card_subgroup_dvd_card (φ.comp (S₀ : Subgroup M).subtype).range
      simpa using this
    have hne : Nat.card (φ.comp (S₀ : Subgroup M).subtype).range ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      apply hφ
      have hmem : φ (⟨zM, hS₀ (Subgroup.mem_zpowers zM)⟩ : (S₀ : Subgroup M)) ∈
          (φ.comp (S₀ : Subgroup M).subtype).range :=
        ⟨⟨zM, hS₀ (Subgroup.mem_zpowers zM)⟩, rfl⟩
      rw [h1] at hmem
      exact Subgroup.mem_bot.1 hmem
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h3 | h3
    · exact absurd h3 hne
    · exact h3
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hSp hSidx hUS hU2 hzS hzU hz2
  obtain ⟨y, hy, hyg⟩ := hg
  have hyg' : (y : G) = g⁻¹ * z * g := hyg
  have hconj : IsConj z (y : G) := isConj_iff.2 ⟨g⁻¹, by rw [hyg']; group⟩
  have hcomm : t * (y : G) = (y : G) * t := ((hM _).1 y.2).symm
  obtain ⟨m, hmt, hm⟩ := h.exists_conj_of_commute hZ hconj hcomm
  let mM : M := ⟨m, (hM m).2 hmt⟩
  have hyeq : y = mM * zM * mM⁻¹ := Subtype.ext (by simp [mM, zM, hm])
  have h1 : φ y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hy).2
  have hyz : y * mM = mM * zM := by rw [hyeq]; group
  have h3 := congrArg φ hyz
  rw [map_mul, map_mul, mul_comm (φ mM) (φ zM)] at h3
  apply hφ
  rw [← h1]
  exact (mul_right_cancel h3).symm

end OneClassData

end CFSG.EvenSporadicStandard.M23Std
