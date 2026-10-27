module

public import CFSG.GH74.Uniqueness.SU.SU5A8
public import CFSG.GH74.Uniqueness.SU.SU5J2Emb2

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup

theorem IsA8Type.of_equiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P') (h : IsA8Type P) :
    IsA8Type P' := by
  obtain ⟨Q, ⟨eQ⟩⟩ := h
  exact ⟨Q, ⟨e.symm.trans eQ⟩⟩

variable {G : Type*} [Group G]

theorem IsZGen.normal_zpowers {S : Subgroup G} {z : G} (hz : IsZGen S z) :
    ((zpowers z).subgroupOf S).Normal := by
  have hc : ∀ s ∈ S, z * s = s * z := (hz.2.2 z hz.1).2 (Or.inr rfl)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 hn
  have hcomm : Commute (z ^ k) (g : G) := Commute.zpow_left (hc g g.2) k
  have h2 : g * n * g⁻¹ = n := by
    apply Subtype.ext
    show (g : G) * (n : G) * (g : G)⁻¹ = n
    rw [← hk, ← hcomm.eq, mul_inv_cancel_right]
  rw [h2]
  exact hn

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem isA8Type_quotient (h : J2Emb S T x) {z : G} (hz : IsZGen S z)
    [((zpowers z).subgroupOf S).Normal] : IsA8Type (↥S ⧸ (zpowers z).subgroupOf S) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  have hz1 : f J2Syl.z0 ≠ 1 := fun h1 => J2Syl.z0_ne_one (hf (by rw [h1, map_one]))
  have hz2 : f J2Syl.z0 * f J2Syl.z0 = 1 := by rw [← map_mul, J2Syl.z0_sq, map_one]
  let e : J2Syl ≃* ↥f.range := MonoidHom.ofInjective hf
  have he : (zpowers J2Syl.z0).map e.toMonoidHom =
      (zpowers (f J2Syl.z0)).subgroupOf f.range := by
    ext s
    rcases s with ⟨_, m, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    show _ ↔ f m ∈ zpowers (f J2Syl.z0)
    rw [J2Syl.mem_zpowers_of_sq_eq_one hz1 hz2]
    constructor
    · rintro ⟨m', hm', hm'e⟩
      have h1 : m' = m := e.injective hm'e
      subst h1
      rcases J2Syl.mem_zpowers_z0.1 hm' with rfl | rfl
      · left; exact map_one f
      · right; rfl
    · rintro (h1 | h1)
      · refine ⟨1, one_mem _, ?_⟩
        refine Subtype.ext ?_
        show f 1 = f m
        rw [map_one, h1]
      · refine ⟨J2Syl.z0, mem_zpowers _, ?_⟩
        apply Subtype.ext
        exact h1.symm
  exact IsA8Type.of_equiv (QuotientGroup.congr (zpowers J2Syl.z0)
    ((zpowers (f J2Syl.z0)).subgroupOf f.range) e he) J2Syl.isA8Type_quotient

end J2Emb

end CFSG.GH74.Uniqueness.SU.SU5
