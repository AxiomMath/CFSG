module

public import CFSG.LargeExtraspecial.S13TwoM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

theorem V_le_Qa_of_Vt_le (H : Hyp4 S g) {t : S.O}
    (h : Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g)) : V S g t ≤ S.Qa g := by
  intro x hx
  have hx' : x ∈ S.clPre (Vt S g t) := hx
  exact (mem_Qa_iff_cl_mem H.conj_mem H.conj_ne hx'.1).mpr (h hx'.2)

section Three

variable (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K)
include hCE Y hg hperp hne

theorem timmesfeld_13_3 :
    finrank (ZMod 2) (Fbar S g₁ K ⊓ S.clSub (S.QG ⊓ S.Qa g) : Submodule (ZMod 2) S.Qt) = 1 := by
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  obtain ⟨-, x, hx, -, X, hVx⟩ := timmesfeld_13_2 hCE Y hg hperp hne
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have hF₁V : Fbar S g₁ K ≤ Vt S g x := hVx ▸ le_sup_right
  set f : Fbar S g₁ K →ₗ[ZMod 2] ZMod 2 :=
    (beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht)).comp (Submodule.inclusion hF₁V) with hf
  have hker : (LinearMap.ker f).map (Fbar S g₁ K).subtype ≤ Fbar S g₁ K ⊓ P := by
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
    have := (beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ (Submodule.inclusion hF₁V v)).mp hv
    exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  rw [Y₁.finrank_Fbar] at h1
  have h4 : finrank (ZMod 2) (Fbar S g₁ K ⊓ P : Submodule (ZMod 2) S.Qt) ≠ 2 := by
    intro h2'
    have hle : Fbar S g₁ K ≤ P := by
      have heq := Submodule.eq_of_le_of_finrank_eq (inf_le_left : Fbar S g₁ K ⊓ P ≤ _)
        (by rw [h2', Y₁.finrank_Fbar])
      rw [← heq]
      exact inf_le_right
    apply X.hVQ
    apply V_le_Qa_of_Vt_le X.H
    rw [hVx]
    exact sup_le Y.Fbar_le_clSub hle
  have h5 := Submodule.finrank_mono (inf_le_left : Fbar S g₁ K ⊓ P ≤ Fbar S g₁ K)
  rw [Y₁.finrank_Fbar] at h5
  omega

end Three

end CFSG.LargeExtraspecial.S13
