module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommGen
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

section Twist

variable {G : Type*} [Group G] [Finite G] {t : G}

theorem centralizerPerfectCore_sup_le_centralizer_of_twist {D X Y R : Subgroup G}
    (P : SwapParam t D) (hinj : Function.Injective P.Ψ)
    (hrange : P.Ψ.range = centralizerPerfectCore X) (hYD : Y ≤ D) {ι : Type*}
    (J : ι → Subgroup G) (hJO : ∀ i, J i ≤ perfectCore (D ⊓ centralizer (Y : Set G)))
    (hOJ : perfectCore (D ⊓ centralizer (Y : Set G)) ≤ ⨆ i, J i)
    (hsimple : ∀ i, IsSimpleGroup (J i)) (hperf : ∀ i, ⁅J i, J i⁆ = J i)
    (u : ∀ i, J i) (hu2 : ∀ i, u i * u i = 1) (hy : ∀ i, ∃ y : J i, u i * y ≠ y * u i)
    (T : ι → Subgroup G) (hTD : ∀ i, T i ≤ D) (hJT : ∀ i, J i ≤ centralizer (T i : Set G))
    (hJR : ∀ i, J i ≤ centralizer (R : Set G))
    (hORTH : ∀ i, ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
      S ≤ centralizer ({t * (u i : G)} : Set G) → S ≤ centralizer (T i : Set G) →
      (u i : G) ∈ S → S ≤ centralizer (R : Set G)) :
    centralizerPerfectCore (X ⊔ Y) ≤ centralizer (R : Set G) := by
  set O := perfectCore (D ⊓ centralizer (Y : Set G)) with hOdef
  have hOD : O ≤ D := (perfectCore_le _).trans inf_le_left
  have hJD : ∀ i, J i ≤ D := fun i => (hJO i).trans hOD
  have hstep : ∀ i, (P.Ψ.comp ((Subgroup.inclusion (hJD i)).prodMap
      (Subgroup.inclusion (hJD i)))).range ≤ centralizer (R : Set G) := by
    intro i
    have := hsimple i
    have : Group.IsPerfect (J i) := Subgroup.isPerfect_iff.mpr (hperf i)
    set ψ := P.Ψ.comp ((Subgroup.inclusion (hJD i)).prodMap (Subgroup.inclusion (hJD i)))
      with hψ
    have hψa : ∀ x y : J i, ψ (x, y) = P.Ψ (Subgroup.inclusion (hJD i) x,
      Subgroup.inclusion (hJD i) y) := fun x y => rfl
    have hψd : ∀ y : J i, ψ (y, y) = (y : G) := fun y => by rw [hψa, P.diag]; rfl
    obtain ⟨y₀, hy₀⟩ := hy i
    refine range_le_centralizer_of_swapTwist ψ (fun x y => by rw [hψa, hψa, P.swap])
      (hu2 i) hy₀ (T := T i) ?_ (fun y => by rw [hψd]; exact hJR i y.2) ?_
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [mem_centralizer_iff]
      intro τ hτ
      have hτD := hTD i hτ
      have hc : ((⟨τ, hτD⟩, ⟨τ, hτD⟩) : D × D) * (Subgroup.inclusion (hJD i) x,
          Subgroup.inclusion (hJD i) y) = (Subgroup.inclusion (hJD i) x,
          Subgroup.inclusion (hJD i) y) * (⟨τ, hτD⟩, ⟨τ, hτD⟩) := by
        ext
        · exact (mem_centralizer_iff.1 (hJT i x.2) τ hτ)
        · exact (mem_centralizer_iff.1 (hJT i y.2) τ hτ)
      have hττ : P.Ψ (⟨τ, hτD⟩, ⟨τ, hτD⟩) = τ := P.diag _
      rw [hψa, ← hττ, ← map_mul, ← map_mul, hc]
    · intro S hSp hSs hSt hST hzS
      rw [hψd] at hSt hzS
      exact hORTH i S hSp hSs hSt hST hzS
  set F₁ : D →* G := P.Ψ.comp (MonoidHom.inl D D) with hF₁
  set F₂ : D →* G := P.Ψ.comp (MonoidHom.inr D D) with hF₂
  have hF₁J : ∀ i, (J i).subgroupOf D ≤ (centralizer (R : Set G)).comap F₁ := by
    intro i x hx
    have hx' : (x : G) ∈ J i := mem_subgroupOf.1 hx
    have h := hstep i ⟨(⟨x, hx'⟩, 1), rfl⟩
    change P.Ψ (Subgroup.inclusion (hJD i) ⟨x, hx'⟩, Subgroup.inclusion (hJD i) 1) ∈ _ at h
    rw [map_one] at h
    exact h
  have hF₂J : ∀ i, (J i).subgroupOf D ≤ (centralizer (R : Set G)).comap F₂ := by
    intro i x hx
    have hx' : (x : G) ∈ J i := mem_subgroupOf.1 hx
    have h := hstep i ⟨(1, ⟨x, hx'⟩), rfl⟩
    change P.Ψ (Subgroup.inclusion (hJD i) 1, Subgroup.inclusion (hJD i) ⟨x, hx'⟩) ∈ _ at h
    rw [map_one] at h
    exact h
  have hOsub : O.subgroupOf D ≤ (⨆ i, J i).subgroupOf D := fun x hx =>
    mem_subgroupOf.2 (hOJ (mem_subgroupOf.1 hx))
  have hiSup : (⨆ i, J i).subgroupOf D = ⨆ i, (J i).subgroupOf D := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : G) ∈ ⨆ i, J i := mem_subgroupOf.1 hx
      have hmap : (⨆ i, (J i).subgroupOf D).map D.subtype = ⨆ i, J i := by
        rw [Subgroup.map_iSup]
        exact congrArg iSup (funext fun i => by
          rw [subgroupOf_map_subtype, inf_eq_left.2 (hJD i)])
      rw [← hmap] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rw [← Subtype.ext hyx]
      exact hy
    · exact iSup_le fun i x hx => mem_subgroupOf.2 (le_iSup J i (mem_subgroupOf.1 hx))
  have hO₁ : O.subgroupOf D ≤ (centralizer (R : Set G)).comap F₁ :=
    hOsub.trans (hiSup ▸ iSup_le hF₁J)
  have hO₂ : O.subgroupOf D ≤ (centralizer (R : Set G)).comap F₂ :=
    hOsub.trans (hiSup ▸ iSup_le hF₂J)
  rw [P.centralizerPerfectCore_sup_eq hinj hrange hYD]
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  obtain ⟨hx, hy⟩ := Subgroup.mem_prod.1 hxy
  have hsplit : P.Ψ (x, y) = F₁ x * F₂ y := by
    rw [hF₁, hF₂, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    congr 1
    ext <;> simp
  rw [hsplit]
  exact mul_mem (hO₁ hx) (hO₂ hy)

end Twist

end CFSG.SeitzReduction.OmegaPilot
