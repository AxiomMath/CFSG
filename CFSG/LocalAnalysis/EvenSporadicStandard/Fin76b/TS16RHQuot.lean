module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Quot

variable {G : Type} [Group G] (u : G)

@[expose] def uV : centralizer ({u} : Set G) := ⟨u, mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def NU : Subgroup (centralizer ({u} : Set G)) := zpowers (uV u)

theorem NU_le_center : NU u ≤ Subgroup.center (centralizer ({u} : Set G)) := by
  rw [NU, zpowers_le, mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

instance NU_normal : (NU u).Normal := normal_of_le_center (NU_le_center u)

abbrev Vbar : Type := ↥(centralizer ({u} : Set G)) ⧸ NU u

@[expose] def mkV : ↥(centralizer ({u} : Set G)) →* Vbar u := QuotientGroup.mk' (NU u)

variable {u}

theorem mkV_eq_one_iff (hu : u * u = 1) (v : ↥(centralizer ({u} : Set G))) :
    mkV u v = 1 ↔ (v : G) = 1 ∨ (v : G) = u := by
  rw [mkV, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, NU]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have hk' : (uV u) ^ k = v := hk
    have hval : (v : G) = u ^ k := by
      rw [← hk']
      exact (map_zpow (centralizer ({u} : Set G)).subtype (uV u) k)
    have hmem : (v : G) ∈ zpowers u := ⟨k, hval.symm⟩
    exact mem_zpowers_sq_eq_one hu hmem
  · rintro (h | h)
    · have : v = 1 := Subtype.ext h
      rw [this]; exact one_mem _
    · have : v = uV u := Subtype.ext h
      rw [this]; exact mem_zpowers _

variable [Finite G]

theorem isPGroup_NU (hu : u * u = 1) (hu1 : u ≠ 1) : IsPGroup 2 (NU u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (uV u) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa [uV, pow_two] using hu
    · intro h
      apply hu1
      simpa [uV] using congrArg Subtype.val h
  exact IsPGroup.of_card (n := 1) (by rw [NU, Nat.card_zpowers, hord]; norm_num)

theorem isPGroup_comap_mkV (hu : u * u = 1) (hu1 : u ≠ 1) {H : Subgroup (Vbar u)}
    (hH : IsPGroup 2 H) : IsPGroup 2 (H.comap (mkV u)) := by
  apply hH.comap_of_ker_isPGroup
  rw [mkV, QuotientGroup.ker_mk']
  exact isPGroup_NU hu hu1

end Quot

theorem exists_conj_le_sylow {K : Type} [Group K] [Finite K] (S : Sylow 2 K) {H : Subgroup K}
    (hH : IsPGroup 2 H) : ∃ x : K, ∀ h ∈ H, x⁻¹ * h * x ∈ (S : Subgroup K) := by
  obtain ⟨S₂, hS₂⟩ := hH.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq K S S₂
  refine ⟨x, fun h hh => ?_⟩
  have h1 : h ∈ ((x • S : Sylow 2 K) : Subgroup K) := by rw [hx]; exact hS₂ hh
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  simpa [MulAut.smul_def] using h1

end CFSG.EvenSporadicStandard.Fin76b
