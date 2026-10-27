module

public import CFSG.LargeExtraspecial.GLW4FusCore
public import CFSG.LargeExtraspecial.GLRLinPair
public import CFSG.LargeExtraspecial.GLW4FusB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {K : Type*} [Group K] [Finite K]

omit [Finite G] in
theorem linMap_eq_of_add_eq_zero {x y : S.Qt →ₗ[ZMod 2] S.Qt} (h : x + y = 0) : x = y := by
  rw [eq_neg_of_add_eq_zero_left h, ZModModule.neg_eq_self]

namespace Lev

variable {T : Setting K} {ι : K →* S.O} {V W : Submodule (ZMod 2) S.Qt} (L : Lev T ι V W)
include L

theorem Emap_eq_of_vanishing {X : Subgroup T.O} {A B : Submodule (ZMod 2) T.Qt}
    (hP : Pair T X A B)
    (hH : ∀ α ∈ T.QG, ∀ β ∈ T.QG, T.cl α ∈ A → T.cl β ∈ B →
      polar T.q (T.cl α) (T.cl β) = 0 → Emap (ι α) (ι β) = 0)
    {α β α' β' : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG) (hα' : α' ∈ T.QG) (hβ' : β' ∈ T.QG)
    (hαA : T.cl α ∈ A) (hβB : T.cl β ∈ B) (hα'A : T.cl α' ∈ A) (hβ'B : T.cl β' ∈ B)
    (h1 : polar T.q (T.cl α) (T.cl β) = 1) (h2 : polar T.q (T.cl α') (T.cl β') = 1) :
    Emap (ι α) (ι β) = Emap (ι α') (ι β') := by
  have hlin : ∀ {α β β₁ : K}, α ∈ T.QG → β ∈ T.QG → β₁ ∈ T.QG → T.cl α ∈ A → T.cl β ∈ B →
      T.cl β₁ ∈ B → polar T.q (T.cl α) (T.cl β) = 1 → polar T.q (T.cl α) (T.cl β₁) = 1 →
      Emap (ι α) (ι β) = Emap (ι α) (ι β₁) := by
    intro α β β₁ hα hβ hβ₁ hαA hβB hβ₁B h1 h2
    have h0 := hH α hα (β * β₁) (T.QG.mul_mem hβ hβ₁) hαA
      (by rw [T.cl_mul hβ hβ₁]; exact B.add_mem hβB hβ₁B)
      (by rw [T.cl_mul hβ hβ₁, polar_add_right, h1, h2]; decide)
    rw [L.Emap_mul_right' hα hβ hβ₁] at h0
    exact linMap_eq_of_add_eq_zero h0
  by_cases he : T.cl α = T.cl α'
  · rw [L.Emap_cl_left hα hα' hβ he]
    exact hlin hα' hβ hβ' hα'A hβB hβ'B (he ▸ h1) h2
  · have hne0 : ∀ {u : T.Qt} {v : T.Qt}, polar T.q u v = 1 → u ≠ 0 := fun h hu => by
      rw [hu, polar_zero_left] at h
      exact zero_ne_one h
    have hnot : ∀ {u u' : T.Qt}, u ≠ 0 → u ≠ u' → u ∉ Submodule.span (ZMod 2) {u'} :=
      fun hu hne hm => by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · exact hu (by rw [← hc, zero_smul])
        · exact hne (by rw [← hc, one_smul])
    obtain ⟨c₁, hc₁B, hc₁U, hc₁⟩ := hP.exists_polar_sep
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hα'A) hαA (hnot (hne0 h1) he)
    obtain ⟨c₂, hc₂B, hc₂U, hc₂⟩ := hP.exists_polar_sep
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hαA) hα'A
      (hnot (hne0 h2) (Ne.symm he))
    have e₁ : polar T.q (T.cl α') c₁ = 0 := hc₁U _ (Submodule.mem_span_singleton_self _)
    have e₂ : polar T.q (T.cl α) c₂ = 0 := hc₂U _ (Submodule.mem_span_singleton_self _)
    obtain ⟨γ, hγ, hγc⟩ := T.exists_cl (c₁ + c₂)
    have hγB : T.cl γ ∈ B := hγc ▸ B.add_mem hc₁B hc₂B
    have g₁ : polar T.q (T.cl α) (T.cl γ) = 1 := by rw [hγc, polar_add_right, hc₁, e₂, add_zero]
    have g₂ : polar T.q (T.cl α') (T.cl γ) = 1 := by
      rw [hγc, polar_add_right, hc₂, e₁, zero_add]
    have h0 := hH (α * α') (T.QG.mul_mem hα hα') γ hγ
      (by rw [T.cl_mul hα hα']; exact A.add_mem hαA hα'A) hγB
      (by rw [T.cl_mul hα hα', polar_add_left, g₁, g₂]; decide)
    rw [L.Emap_mul_left' hα hα' hγ] at h0
    rw [hlin hα hβ hγ hαA hβB hγB h1 g₁, linMap_eq_of_add_eq_zero h0,
      hlin hα' hγ hβ' hα'A hγB hβ'B g₂ h2]

theorem false_of_vanishing {X : Subgroup T.O} {A B : Submodule (ZMod 2) T.Qt}
    (hP : Pair T X A B) (hV6 : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {R : Set K} (hRM : ∀ r ∈ R, r ∈ T.M)
    (hRA : ∀ r (hr : r ∈ R), ∀ a ∈ A, (T.ρ ⟨r, hRM r hr⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) a ∈ A)
    (hRB : ∀ r (hr : r ∈ R), ∀ b ∈ B, (T.ρ ⟨r, hRM r hr⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) b ∈ B)
    (hR : ∀ g ∈ omegaGroup q hq, ∃ r ∈ R, ∀ v : V,
      ((g v : V) : S.Qt) = (ι r : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    {a₀ : T.Qt} (ha₀ : a₀ ∈ A) (ha₀0 : a₀ ≠ 0)
    (hH : ∀ α ∈ T.QG, ∀ β ∈ T.QG, T.cl α ∈ A → T.cl β ∈ B →
      polar T.q (T.cl α) (T.cl β) = 0 → Emap (ι α) (ι β) = 0) : False := by
  obtain ⟨b₀, hb₀B, hb₀⟩ : ∃ b ∈ B, polar T.q a₀ b = 1 := by
    obtain ⟨b, hb, hb1⟩ := hP.symm.exists_polar_eq_one ha₀ ha₀0
    exact ⟨b, hb, by rw [polar_comm]; exact hb1⟩
  obtain ⟨α₀, hα₀, rfl⟩ := T.exists_cl a₀
  obtain ⟨β₀, hβ₀, rfl⟩ := T.exists_cl b₀
  have hT₀R : ∀ r ∈ ι '' R, ∀ x, Emap (ι α₀) (ι β₀) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (Emap (ι α₀) (ι β₀) x) := by
    rintro _ ⟨r, hr, rfl⟩ x
    have hrM := hRM r hr
    have hα' : r * α₀ * r⁻¹ ∈ T.QG := T.conj_mem_QG hrM hα₀
    have hβ' : r * β₀ * r⁻¹ ∈ T.QG := T.conj_mem_QG hrM hβ₀
    have hclα : T.cl (r * α₀ * r⁻¹) = (T.ρ ⟨r, hrM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) (T.cl α₀) :=
      (T.ρ_cl ⟨r, hrM⟩ hα₀).symm
    have hclβ : T.cl (r * β₀ * r⁻¹) = (T.ρ ⟨r, hrM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) (T.cl β₀) :=
      (T.ρ_cl ⟨r, hrM⟩ hβ₀).symm
    have heq : Emap (ι (r * α₀ * r⁻¹)) (ι (r * β₀ * r⁻¹)) = Emap (ι α₀) (ι β₀) :=
      L.Emap_eq_of_vanishing hP hH hα' hβ' hα₀ hβ₀ (hclα ▸ hRA r hr _ ha₀)
        (hclβ ▸ hRB r hr _ hb₀B) ha₀ hb₀B
        (by rw [hclα, hclβ, Config.polar_apply_apply]; exact hb₀) hb₀
    have hc₁ : ι (r * α₀ * r⁻¹) = ι r * ι α₀ * (ι r)⁻¹ := by simp only [map_mul, map_inv]
    have hc₂ : ι (r * β₀ * r⁻¹) = ι r * ι β₀ * (ι r)⁻¹ := by simp only [map_mul, map_inv]
    have := Emap_conj (ι r) (ι α₀) (ι β₀) ((ι r : S.Qt ≃ₗ[ZMod 2] S.Qt) x)
    rw [← hc₁, ← hc₂, heq, Config.inv_apply_apply] at this
    exact this
  have hrt : ∀ r ∈ ι '' R, r * ι T.z = ι T.z * r := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, T.z_comm (hRM r hr)]
  have hT₀ := eq_zero_or_eq_dm L.dm_mem L.dm_onto hV6 hq hrt
    (fun g hg => by
      obtain ⟨r, hr, hrg⟩ := hR g hg
      exact ⟨ι r, ⟨r, hr, rfl⟩, hrg⟩)
    (fun x hx => Emap_eq_zero_of_mem (L.layered _ hα₀) (L.layered _ hβ₀) (L.mem_W_of_dm x hx))
    (fun x => Emap_mem (L.layered _ hα₀) (L.layered _ hβ₀) x) hT₀R
  have hswap := L.Emap_add_swap_of_polar hα₀ hβ₀ hb₀
  have hnd := S.q_nondegenerate
  have hsep : ∀ {E E' : S.Qt →ₗ[ZMod 2] S.Qt},
      (∀ x y, polar S.q x (E y) = polar S.q x (E' y)) → E = E' := fun {E E'} h =>
    LinearMap.ext fun y => sub_eq_zero.mp (hnd.2 _ fun x => by
      rw [polarBilin_apply_apply, polar_sub_right, h, sub_self])
  have hdm0 : dm (ι T.z) = 0 := by
    rcases hT₀ with h0 | h0
    · have hE : Emap (ι β₀) (ι α₀) = 0 := hsep fun x y => by
        rw [← L.polar_Emap_swap hα₀ hβ₀, h0, LinearMap.zero_apply, LinearMap.zero_apply,
          polar_zero_left, polar_zero_right]
      rw [← hswap, h0, hE, add_zero]
    · have hE : Emap (ι β₀) (ι α₀) = dm (ι T.z) := hsep fun x y => by
        rw [← L.polar_Emap_swap hα₀ hβ₀, h0, polar_dm, ← map_inv, T.z_inv]
      rw [← hswap, h0, hE, ZModModule.add_self]
  apply L.ne_one
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  have := LinearMap.congr_fun hdm0 x
  rw [dm_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

end Lev

end CFSG.LargeExtraspecial.GLW4
