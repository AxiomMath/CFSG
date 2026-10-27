module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module QuadraticMap CFSG.LargeExtraspecial
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_eq_mul_of_vanish (F : Submodule (ZMod 2) S.Qt) (a y : S.Qt)
    (h : ∀ v ∈ F, polar S.q a v = 0 → polar S.q y v = 0) :
    ∃ e : ZMod 2, ∀ v ∈ F, polar S.q y v = e * polar S.q a v := by
  by_cases hall : ∀ v ∈ F, polar S.q a v = 0
  · exact ⟨0, fun v hv => by rw [h v hv (hall v hv), zero_mul]⟩
  · push Not at hall
    obtain ⟨v₀, hv₀, hav₀⟩ := hall
    have h1 : polar S.q a v₀ = 1 := (zmod2_cases _).resolve_left hav₀
    refine ⟨polar S.q y v₀, fun v hv => ?_⟩
    have h2 : polar S.q a (v + polar S.q a v • v₀) = 0 := by
      rw [polar_add_right, polar_smul_right, h1, smul_eq_mul, mul_one, CharTwo.add_self_eq_zero]
    have h3 := h _ (F.add_mem hv (F.smul_mem _ hv₀)) h2
    rw [polar_add_right, polar_smul_right, smul_eq_mul, CharTwo.add_eq_zero] at h3
    exact h3.trans (mul_comm _ _)

theorem mem_of_perp_singular {W F : Submodule (ZMod 2) S.Qt}
    (hF : F = LinearMap.BilinForm.orthogonal S.q.polarBilin W) (hWsing : ∀ w ∈ W, S.q w = 0)
    {r y : S.Qt} (hrF : r ∈ F) (hr : r = 0 ∨ S.q r = 1)
    (hy : ∀ v ∈ F, polar S.q r v = 0 → polar S.q y v = 0) (hyq : S.q y = 0) : y ∈ W := by
  obtain ⟨e, he⟩ := exists_eq_mul_of_vanish F r y hy
  have hwF : y + e • r ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin F := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    rw [polarBilin_apply_apply, QuadraticMap.polar_comm, polar_add_left, polar_smul_left,
      he v hv, smul_eq_mul]
    exact CharTwo.add_self_eq_zero _
  have hwW : y + e • r ∈ W := by
    rwa [hF, LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl] at hwF
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, y = w + e • r :=
    ⟨y + e • r, hwW, by
      rw [add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2), add_zero]⟩
  have hwr : polar S.q w r = 0 := by
    have := LinearMap.BilinForm.mem_orthogonal_iff.mp (hF ▸ hrF) w hw
    rwa [polarBilin_apply_apply] at this
  rw [QuadraticMap.map_add (⇑S.q), hWsing w hw, QuadraticMap.map_smul, polar_smul_right, hwr,
    smul_eq_mul, smul_eq_mul, mul_zero, zero_add, add_zero] at hyq
  rcases hr with rfl | hr1
  · simpa using hw
  · rw [hr1, mul_one] at hyq
    rw [mul_self_eq_zero.mp hyq, zero_smul, add_zero]
    exact hw

theorem nine_le_finrank_inf_orthogonal {F : Submodule (ZMod 2) S.Qt}
    (hF : Module.finrank (ZMod 2) F = 10) (hq : Module.finrank (ZMod 2) S.Qt = 12) (r : S.Qt) :
    9 ≤ Module.finrank (ZMod 2)
      (F ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {r}) :
        Submodule (ZMod 2) S.Qt) := by
  have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {r}) ≤ 1 := by
    simpa using finrank_span_le_card (R := ZMod 2) ({r} : Set S.Qt)
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate
    (Submodule.span (ZMod 2) {r})
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq F
    (LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {r}))
  have h4 := Submodule.finrank_le
    (F ⊔ LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {r}))
  omega

theorem exists_polar_ne_zero (hq : Module.finrank (ZMod 2) S.Qt = 12)
    {U : Submodule (ZMod 2) S.Qt} (hU : 7 ≤ Module.finrank (ZMod 2) U) :
    ∃ u₁ ∈ U, ∃ u₂ ∈ U, polar S.q u₁ u₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : U ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin U := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [polarBilin_apply_apply]
    exact hcon n hn v hv
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate U
  omega

theorem exists_q_eq_one (hq : Module.finrank (ZMod 2) S.Qt = 12)
    {F : Submodule (ZMod 2) S.Qt} (hF : 7 ≤ Module.finrank (ZMod 2) F) :
    ∃ r ∈ F, S.q r = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ r ∈ F, S.q r = 0 := fun r hr => (zmod2_cases _).resolve_right (hcon r hr)
  obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := exists_polar_ne_zero hq hF
  have h := QuadraticMap.map_add (⇑S.q) u₁ u₂
  rw [h0 _ (F.add_mem hu₁ hu₂), h0 _ hu₁, h0 _ hu₂, zero_add, zero_add] at h
  exact hne h.symm

end CFSG.GF2Type.Smith1979.IdxFour
