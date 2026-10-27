module

public import CFSG.LargeExtraspecial.S10Frame
public import CFSG.LargeExtraspecial.S13Gen
public import CFSG.LargeExtraspecial.S13TwoE
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

theorem pf_act_act : ∀ (γ : Gm) (A B : M2), pf (act γ A) (act γ B) = pf A B := by
  decide +kernel

@[expose] def chk3 (A B C : M2) : Bool :=
  !(qf A == 0 && qf B == 0 && qf C == 0 && A != 0 && B != 0 && A != B && pf A B == 0 &&
    pf A C == 0 && pf B C == 0) || (C == 0 || C == A || C == B || C == A + B)

theorem chk3_all : ∀ A B C : M2, chk3 A B C = true := by decide +kernel

theorem three_sing_dep (A B C : M2) (hA : qf A = 0) (hB : qf B = 0) (hC : qf C = 0)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B) (h1 : pf A B = 0) (h2 : pf A C = 0)
    (h3 : pf B C = 0) : C = 0 ∨ C = A ∨ C = B ∨ C = A + B := by
  have := chk3_all A B C
  simpa [chk3, hA, hB, hC, hA0, hB0, hAB, h1, h2, h3, or_assoc] using this

theorem act_E00_sing : ∀ γ : Gm, qf (act γ E00) = 0 ∧ act γ E00 ≠ 0 := by
  decide +kernel

namespace Hyp10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} (X : Hyp10 S g t)
include X

theorem frame_apply_orb (F : Frame X) (r : Rbar S g t) :
    F.φ (resV X.haQ t r (aV X.ht)) = act (F.π r) E00 := by
  rw [F.compat, F.base]

theorem pf_eq_zero_of_linked (F : Frame X) (r₁ r₂ : Rbar S g t)
    (hl : (((r₁ : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((r₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) ∈
        S.clSub (S.QG ⊓ S.Qa g)) :
    pf (act (F.π r₁) E00) (act (F.π r₂) E00) = 0 := by
  have hb := (beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ
    (resV X.haQ t (r₁⁻¹ * r₂) (aV X.ht))).mpr (by
      rw [coe_resV_apply]
      have e : ((aV X.ht : Vt S g t) : S.Qt) = S.cl (g * S.z * g⁻¹) := rfl
      rw [e]
      simpa [Subgroup.coe_mul, LinearEquiv.mul_apply] using hl)
  rw [F.beta_eq, F.base, frame_apply_orb, map_mul, map_inv, act_mul] at hb
  rw [← pf_act_act (F.π r₁)⁻¹, ← act_mul, inv_mul_cancel, act_one]
  exact hb

theorem exists_rep {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    ∃ r : Rbar S g t, ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∧
      ∀ v, v ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ↔
        ((((r : S.O))⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨r, hr, hra⟩ := exists_Rbar_apply_eq X.H X.C X.ht hth
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  refine ⟨⟨r, hr⟩, hra, fun v => ?_⟩
  have hcl : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_z S m X.haQ, hm, hra]
  have hmQ := conj_mem_QG' S m.2 X.haQ
  have hmz := conj_ne_z' S m.2 X.H.conj_ne
  have hhQ := conj_mem_QG' S h.2 X.haQ
  rw [clSub_eq_of_cl_eq hmQ hmz hhQ hcl, clSub_Qa_mul_eq m g, hm]

theorem mem_span_of_linked {h₁ h₂ h₃ : S.M} (ht₁ : t ∈ S.Lbar ((h₁ : G) * g))
    (ht₂ : t ∈ S.Lbar ((h₂ : G) * g)) (ht₃ : t ∈ S.Lbar ((h₃ : G) * g))
    (hne : S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) ≠
      S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹))
    (h12 : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g)))
    (h13 : S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₁ : G) * g)))
    (h23 : S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((h₂ : G) * g))) :
    S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) ∈ Submodule.span (ZMod 2)
      {S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹),
        S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹)} := by
  obtain ⟨F⟩ := X.exists_frame
  obtain ⟨r₁, e₁, l₁⟩ := Hyp10.exists_rep X ht₁
  obtain ⟨r₂, e₂, l₂⟩ := Hyp10.exists_rep X ht₂
  obtain ⟨r₃, e₃, -⟩ := Hyp10.exists_rep X ht₃
  set v₁ := resV X.haQ t r₁ (aV X.ht) with hv₁
  set v₂ := resV X.haQ t r₂ (aV X.ht) with hv₂
  set v₃ := resV X.haQ t r₃ (aV X.ht) with hv₃
  have c₁ : (v₁ : S.Qt) = S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) := e₁
  have c₂ : (v₂ : S.Qt) = S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) := e₂
  have c₃ : (v₃ : S.Qt) = S.cl ((h₃ : G) * g * S.z * ((h₃ : G) * g)⁻¹) := e₃
  have p12 := Hyp10.pf_eq_zero_of_linked X F r₁ r₂ (by rw [e₂]; exact (l₁ _).mp h12)
  have p13 := Hyp10.pf_eq_zero_of_linked X F r₁ r₃ (by rw [e₃]; exact (l₁ _).mp h13)
  have p23 := Hyp10.pf_eq_zero_of_linked X F r₂ r₃ (by rw [e₃]; exact (l₂ _).mp h23)
  have hAB : act (F.π r₁) E00 ≠ act (F.π r₂) E00 := by
    intro hAB
    apply hne
    rw [← c₁, ← c₂]
    congr 1
    apply F.φ.injective
    rw [Hyp10.frame_apply_orb X F r₁, Hyp10.frame_apply_orb X F r₂]
    exact hAB
  have hm₁ : S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹) ∈ Submodule.span (ZMod 2)
      {S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹),
        S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹)} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hm₂ : S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) ∈ Submodule.span (ZMod 2)
      {S.cl ((h₁ : G) * g * S.z * ((h₁ : G) * g)⁻¹),
        S.cl ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹)} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  rcases three_sing_dep _ _ _ (act_E00_sing _).1 (act_E00_sing _).1 (act_E00_sing _).1
    (act_E00_sing _).2 (act_E00_sing _).2 hAB p12 p13 p23 with h | h | h | h
  · exact absurd h (act_E00_sing _).2
  · have h' : v₃ = v₁ := F.φ.injective (by
      rw [Hyp10.frame_apply_orb X F r₃, Hyp10.frame_apply_orb X F r₁]; exact h)
    rw [← c₃, h', c₁]
    exact hm₁
  · have h' : v₃ = v₂ := F.φ.injective (by
      rw [Hyp10.frame_apply_orb X F r₃, Hyp10.frame_apply_orb X F r₂]; exact h)
    rw [← c₃, h', c₂]
    exact hm₂
  · have h' : v₃ = v₁ + v₂ := F.φ.injective (by
      rw [map_add, Hyp10.frame_apply_orb X F r₃, Hyp10.frame_apply_orb X F r₁,
        Hyp10.frame_apply_orb X F r₂]
      exact h)
    rw [← c₃, h', Submodule.coe_add, c₁, c₂]
    exact add_mem hm₁ hm₂

end Hyp10

end CFSG.LargeExtraspecial.S13
