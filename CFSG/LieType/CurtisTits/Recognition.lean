module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LieType.CurtisTits

open Subgroup

variable {K G : Type*} [Group K] [Group G]

theorem le_center_or_eq_top_of_isQuasisimple (hK : IsQuasisimple K) (N : Subgroup K)
    [N.Normal] : N ≤ center K ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hK
  let π : K →* K ⧸ center K := QuotientGroup.mk' (center K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNorm : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro x hx
    have hmem : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    simpa [π] using hmem
  · right
    have hNZ : ∀ x : K, ∃ n ∈ N, ∃ z ∈ center K, x = n * z := by
      intro x
      have hx : π x ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
      have : π (n⁻¹ * x) = 1 := by rw [map_mul, map_inv, hnx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have hcomm : ∀ a b : K ⧸ N, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
      obtain ⟨n, hn, z, hz, rfl⟩ := hNZ x
      obtain ⟨m, hm, w, hw, rfl⟩ := hNZ y
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      simp only [map_mul, hn1, hm1, one_mul]
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
    have : Group.IsPerfect K := hperf
    have : IsMulCommutative (K ⧸ N) := ⟨⟨hcomm⟩⟩
    have : Subsingleton (K ⧸ N) := Group.IsPerfect.subsingleton_of_isMulCommutative
    rw [eq_top_iff]
    intro x _
    have : (QuotientGroup.mk' N x) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp this

theorem center_quotient_center_eq_bot_of_isQuasisimple (hK : IsQuasisimple K) :
    center (K ⧸ center K) = ⊥ := by
  have : Group.IsPerfect K := hK.1
  exact Group.IsPerfect.center_quotient_center_eq_bot K

variable {φ : K →* G}

theorem ker_le_center_of_isQuasisimple (hK : IsQuasisimple K) (hφ : ∃ k, φ k ≠ 1) :
    φ.ker ≤ center K := by
  rcases le_center_or_eq_top_of_isQuasisimple hK φ.ker with h | h
  · exact h
  · obtain ⟨k, hk⟩ := hφ
    exact absurd (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top k)) hk

theorem center_eq_map_center_of_isQuasisimple (hK : IsQuasisimple K)
    (hsurj : Function.Surjective φ) (hker : φ.ker ≤ center K) : center G = (center K).map φ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, rfl⟩ := hsurj g
    refine ⟨k, ?_, rfl⟩
    have hc : (QuotientGroup.mk' (center K) k) ∈ center (K ⧸ center K) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      apply hker
      have hg' := Subgroup.mem_center_iff.mp hg (φ x)
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, mul_inv_rev]
      rw [← hg']
      group
    rw [center_quotient_center_eq_bot_of_isQuasisimple hK, Subgroup.mem_bot,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    exact hc
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk x]

noncomputable def centralQuotientEquivOfIsQuasisimple (hK : IsQuasisimple K)
    (hsurj : Function.Surjective φ) (hker : φ.ker ≤ center K) :
    K ⧸ center K ≃* G ⧸ center G :=
  let ψ : K →* G ⧸ center G := (QuotientGroup.mk' (center G)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hsurj
  have hkerψ : ψ.ker = center K := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, center_eq_map_center_of_isQuasisimple hK hsurj hker]
    constructor
    · rintro ⟨k', hk', hkk'⟩
      have hker' : k'⁻¹ * k ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkk', inv_mul_cancel]
      have := (center K).mul_mem hk' (hker hker')
      simpa using this
    · intro hk
      exact ⟨k, hk, rfl⟩
  (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

omit [Group G] in
theorem center_eq_of_isSimpleGroup_quotient (S : Subgroup K) [S.Normal] (hS : S ≤ center K)
    (hsimple : IsSimpleGroup (K ⧸ S)) (hnc : ∃ a b : K ⧸ S, a * b ≠ b * a) : center K = S := by
  refine le_antisymm ?_ hS
  intro z hz
  have hcent : QuotientGroup.mk' S z ∈ center (K ⧸ S) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective S a
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ S)) with h | h
  · rw [h, Subgroup.mem_bot] at hcent
    exact (QuotientGroup.eq_one_iff z).mp hcent
  · obtain ⟨a, b, hab⟩ := hnc
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

omit [Group G] in
theorem isQuasisimple_of_isSimpleGroup_quotient (S : Subgroup K) [S.Normal] (hS : S ≤ center K)
    (hperf : Group.IsPerfect K) (hsimple : IsSimpleGroup (K ⧸ S))
    (hnc : ∃ a b : K ⧸ S, a * b ≠ b * a) : IsQuasisimple K := by
  have hZ := center_eq_of_isSimpleGroup_quotient S hS hsimple hnc
  let e : K ⧸ S ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hZ.symm
  obtain ⟨a, b, hab⟩ := hnc
  have hne : e a ≠ e b := fun h => hab (by rw [e.injective h])
  have : Nontrivial (K ⧸ center K) := ⟨⟨e a, e b, hne⟩⟩
  refine ⟨hperf, IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective, e a, e b,
    ?_⟩
  rw [← map_mul, ← map_mul]
  exact fun h => hab (e.injective h)

theorem isQuasisimple_of_surjective (hK : IsQuasisimple K) (hsurj : Function.Surjective φ)
    (hφ : ∃ k, φ k ≠ 1) : IsQuasisimple G := by
  have hker := ker_le_center_of_isQuasisimple hK hφ
  let e := centralQuotientEquivOfIsQuasisimple hK hsurj hker
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hK
  have : Group.IsPerfect K := hperf
  have hne : e a ≠ e b := by
    intro h
    apply hab
    apply e.injective
    rw [map_mul, map_mul, h]
  have : Nontrivial (G ⧸ center G) := ⟨⟨e a, e b, hne⟩⟩
  refine ⟨Group.IsPerfect.ofSurjective hsurj, ?_, e a, e b, ?_⟩
  · exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective
  · rw [← map_mul, ← map_mul]
    exact fun h => hab (e.injective h)

end CFSG.LieType.CurtisTits
