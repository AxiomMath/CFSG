module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11b3
public import CFSG.ClassicalInvolution.Q3.Q3WASTAsm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD


section Dichotomy

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem M11Pic.layer_dichotomy (hA : M11AutInner) (c : LocOK Ω x) (P : M11Pic Ω x)
    {V : Subgroup G} (hV : V ∈ compMembers3 Ω x P.D P.i₀) {K : Subgroup G} {z : G}
    (hKm : K ∈ compMembers3 Ω x P.D P.i₁) (hz : IsClassicalMember3 K z) {s : G}
    (hs1 : s * x * s⁻¹ = x) (hs2 : s * s = 1) (hsK : K ≤ Subgroup.centralizer ({s} : Set G)) :
    (∀ N ∈ compMembers3 Ω x P.D P.i₁, N ≤ Subgroup.centralizer ({s} : Set G)) ∨
      (∀ N ∈ compMembers3 Ω x P.D P.i₁, N ≤ Subgroup.centralizer ({s * z} : Set G)) := by
  have hσσ : ∀ a, Gaps.locAut c.hΩ.conjInvariant hs1 (Gaps.locAut c.hΩ.conjInvariant hs1 a) = a :=
    Gaps.locAut_locAut c.hΩ.conjInvariant hs1 hs2
  have hcomp : ∀ N ∈ compMembers3 Ω x P.D P.i₁, conjSub s N ∈ compMembers3 Ω x P.D P.i₁ := by
    intro N hN
    have hN' : conjSub s N ∈ centralizingMembers Ω {x} :=
      conjSub_mem_centralizingMembers3 c.hΩ.conjInvariant hs1 hN.1
    rcases P.mem_cases c hN' with h | h
    · exfalso
      have h1 : conjSub s N = V := P.a1_eq c h hV
      have h2 : N = V := by
        have := congrArg (conjSub s) h1
        rw [← conjSub_mul, hs2, conjSub_one, P.conjSub_vertex c hV hs1] at this
        exact this
      rw [h2] at hN
      obtain ⟨j, -, hj⟩ := exists_unique_comp3 c.hΩ c.hex c.hP1 c.hO3 P.D hV.1
      exact P.ne ((hj _ hV).trans (hj _ hN).symm)
    · exact h
  obtain ⟨R_K, hRK⟩ := exists_corr_left3 c.hΩ c.hex c.hP1 c.hO3 P.D hKm
  have hfund : ∀ R ∈ (P.D.kind P.i₁).fund, ∀ a ∈ R,
      Gaps.locAut c.hΩ.conjInvariant hs1 (P.D.hom P.i₁ a) ∈ (P.D.hom P.i₁).range := by
    intro R hR a ha
    obtain ⟨N, hN⟩ := exists_corr_right3 c.hΩ P.D (m11_singleClass_gen P.k₁) hR
    have hNm : N ∈ compMembers3 Ω x P.D P.i₁ :=
      ⟨hN.1, by rw [hN.2.2]; exact Subgroup.map_le_range _ _⟩
    have h1 : Gaps.locAut c.hΩ.conjInvariant hs1 (P.D.hom P.i₁ a) ∈ locImg Ω x (conjSub s N) := by
      rw [← Gaps.locAut_locImg c.hΩ.conjInvariant hs1 N]
      exact ⟨P.D.hom P.i₁ a, by rw [hN.2.2]; exact ⟨a, ha, rfl⟩, rfl⟩
    exact (hcomp N hNm).2 h1
  have hstab : ∀ y, Gaps.locAut c.hΩ.conjInvariant hs1 (P.D.hom P.i₁ y) ∈
      (P.D.hom P.i₁).range := by
    have htop : (P.D.hom P.i₁).range.comap
        ((Gaps.locAut c.hΩ.conjInvariant hs1).toMonoidHom.comp (P.D.hom P.i₁)) = ⊤ := by
      rw [eq_top_iff, ← m11_fund_iSup_eq_top_gen P.k₁ hRK.2.1]
      exact iSup₂_le fun R hR a ha => hfund R hR a ha
    intro y
    have : y ∈ (P.D.hom P.i₁).range.comap
        ((Gaps.locAut c.hΩ.conjInvariant hs1).toMonoidHom.comp (P.D.hom P.i₁)) := by
      rw [htop]
      trivial
    exact this
  have hfix : ∀ r ∈ R_K, Gaps.locAut c.hΩ.conjInvariant hs1 (P.D.hom P.i₁ r) =
      P.D.hom P.i₁ r := by
    intro r hr
    exact (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 hs1 hKm.1).mp hsK (P.D.hom P.i₁ r)
      (by rw [hRK.2.2]; exact ⟨r, hr, rfl⟩)
  obtain ⟨k, hk, hk'⟩ := m11_aut_dichotomy_gen hA P.k₁ (P.D.hom P.i₁) (P.D.ker_le_center P.i₁)
    (Gaps.locAut c.hΩ.conjInvariant hs1) hσσ hstab hRK.2.1 hfix
  rcases hk with hk1 | ⟨r₀, hr₀, hkr⟩
  ·
    rw [hk1] at hk'
    left
    intro N hN
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 hs1 hN.1).mpr fun a ha => ?_
    obtain ⟨y, rfl⟩ := hN.2 ha
    simpa using hk' y
  ·
    rw [hkr] at hk'
    right
    have hzY : z ∈ locLayer Ω x := le_centralizingLayer hKm.1 hz.mem
    have hzx : z * x * z⁻¹ = x := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hKm.1.2 hz.mem)
      rw [mul_inv_eq_iff_eq_mul]
      exact h1
    have hsz : (s * z) * x * (s * z)⁻¹ = x := by
      calc (s * z) * x * (s * z)⁻¹ = s * (z * x * z⁻¹) * s⁻¹ := by group
        _ = s * x * s⁻¹ := by rw [hzx]
        _ = x := hs1
    have hlm : Gaps.locMk Ω x ⟨z, hzY⟩ = P.D.hom P.i₁ r₀ :=
      P.locMk_eq c hKm.1 hz (u := r₀) ⟨R_K, hRK, hr₀⟩
    have hr2 : r₀ * r₀ = 1 := by
      have := pow_orderOf_eq_one r₀
      rwa [hr₀.orderOf_eq_two, pow_two] at this
    have hri : r₀⁻¹ = r₀ := inv_eq_of_mul_eq_one_right hr2
    have hfixed : ∀ y, Gaps.locAut c.hΩ.conjInvariant hsz (P.D.hom P.i₁ y) =
        P.D.hom P.i₁ y := by
      intro y
      rw [locAut_mul3 c.hΩ.conjInvariant hs1 hzx hsz, locAut_eq_conj3 c.hΩ.conjInvariant hzY hzx,
        hlm]
      have e1 : P.D.hom P.i₁ r₀ * P.D.hom P.i₁ y * (P.D.hom P.i₁ r₀)⁻¹ =
          P.D.hom P.i₁ (r₀ * y * r₀⁻¹) := by simp [map_mul, map_inv]
      rw [e1, hk' (r₀ * y * r₀⁻¹)]
      have e2 : r₀ * (r₀ * y * r₀⁻¹) * r₀⁻¹ = y := by
        rw [hri]
        calc r₀ * (r₀ * y * r₀) * r₀ = (r₀ * r₀) * y * (r₀ * r₀) := by group
          _ = y := by rw [hr2]; group
      rw [e2]
    intro N hN
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 hsz hN.1).mpr fun a ha => ?_
    obtain ⟨y, rfl⟩ := hN.2 ha
    exact hfixed y

end Dichotomy

end CFSG.ClassicalInvolution.Q3.Q3W
