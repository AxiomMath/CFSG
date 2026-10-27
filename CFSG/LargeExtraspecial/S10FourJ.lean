module

public import CFSG.LargeExtraspecial.S10FourI
public import CFSG.LargeExtraspecial.S10Dec
public import CFSG.LargeExtraspecial.S10FourF
public import CFSG.LargeExtraspecial.S10SixA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem apply_sub_mem_clSub_of_perp (X : Hyp10 S g t) {h : S.M} {v : S.Qt}
    (hperp : polar S.q v (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) = 0) {l : S.O}
    (hl : l ∈ S.Lbar ((h : G) * g)) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
  obtain ⟨y, hyQ, rfl⟩ := S.exists_cl v
  have hcQ := conj_mem_QG' S h.2 X.haQ
  have hyc : y * ((h : G) * g * S.z * ((h : G) * g)⁻¹) =
      (h : G) * g * S.z * ((h : G) * g)⁻¹ * y := (S.polar_cl_eq_zero_iff hyQ hcQ).mp hperp
  exact (X.C.mul h).comm_le y ⟨hyQ, mem_centralizer_singleton_iff.mpr hyc⟩ l hl

theorem StronglyClosedL.mem_Vt_of_mem_clSub_inf_Wt (hSC : StronglyClosedL S g t)
    (X : Hyp10 S g t) (F : Frame X) {h : S.M}
    (hcP : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hcW : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Wt S g t) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t := by
  have haQ := X.haQ
  by_contra hcV
  have hca : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) :=
    fun hmem => hcV ((Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt X.ht) hmem)
  by_cases hAK : ∀ x ∈ S.Lbar g ⊓ Nbar S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)
  · apply hcV
    have hmem : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈
        S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := ⟨hcP, hAK⟩
    rw [clSub_inf_fixSub_Abar X] at hmem
    exact hmem.2
  push Not at hAK
  obtain ⟨x, hxA, hxc⟩ := hAK
  have hLZ := hSC.Lbar_le_sup X hcP hca hxA hxc
  have hZst : ∀ γ ∈ stabA, ∃ z ∈ S.Lbar g ⊓ S.Lbar ((h : G) * g),
      ∃ hzR : z ∈ Rbar S g t, F.π ⟨z, hzR⟩ = γ := by
    intro γ hγ
    obtain ⟨l, hl, hπl⟩ := F.exists_Lbar_of_stab hγ
    obtain ⟨a', ha', z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun p hp q hq => Lbar_comm S haQ (Subgroup.mem_inf.mp hp).1 (Subgroup.mem_inf.mp hq).1)
      (hLZ hl)
    have ha'R : a' ∈ Rbar S g t := Nbar_le_Rbar (Subgroup.mem_inf.mp ha').2
    have hzR : z ∈ Rbar S g t := Lbar_le_Rbar X.ht (Subgroup.mem_inf.mp hz).1
    refine ⟨z, hz, hzR, ?_⟩
    have e : (⟨a' * z, Lbar_le_Rbar X.ht hl⟩ : Rbar S g t) = ⟨a', ha'R⟩ * ⟨z, hzR⟩ := rfl
    rw [e, map_mul, (F.ker _).mpr (Subgroup.mem_inf.mp ha').2, one_mul] at hπl
    exact hπl
  obtain ⟨z₁, hz₁, hz₁R, hπ₁⟩ := hZst τ₁ (mem_stabA.mpr ((act_E00_iff τ₁).mpr
    (Or.inr (Or.inl rfl))))
  obtain ⟨z₂, hz₂, hz₂R, hπ₂⟩ := hZst τ₂ (mem_stabA.mpr ((act_E00_iff τ₂).mpr
    (Or.inr (Or.inr (Or.inl rfl)))))
  obtain ⟨m₀, hm₀⟩ := exists_comm_comm_ne_zero
  set v : Vt S g t := F.φ.symm m₀ with hv
  set V₁ : Vt S g t := resV haQ t ⟨z₁, hz₁R⟩ v - v with hV₁
  set V₂ : Vt S g t := resV haQ t ⟨z₂, hz₂R⟩ V₁ - V₁ with hV₂
  have hφ₂ : F.φ V₂ = act τ₂ (act τ₁ m₀ - m₀) - (act τ₁ m₀ - m₀) := by
    rw [hV₂, map_sub, F.compat, hπ₂, hV₁, map_sub, F.compat, hπ₁, hv,
      LinearEquiv.apply_symm_apply]
  have hV₂0 : (V₂ : S.Qt) ≠ 0 := fun h0 => hm₀ (by
    rw [← hφ₂, show V₂ = 0 from Subtype.ext h0, map_zero])
  have hvW : (v : S.Qt) ∈ Wt S g t := Vt_le_Wt X.H X.ht1 v.2
  have hpa : polar S.q (v : S.Qt) (S.cl (g * S.z * g⁻¹)) = 0 := by
    rw [polar_comm]
    exact (mem_Wt.mp hvW) _ (cl_a_mem_Vt X.ht)
  have hpc : polar S.q (v : S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) = 0 :=
    (mem_Wt.mp hcW) _ v.2
  have hpa' : polar S.q (v : S.Qt) (S.cl (((1 : S.M) : G) * g * S.z *
      (((1 : S.M) : G) * g)⁻¹)) = 0 := by simpa using hpa
  have hw₁a : (V₁ : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    have := apply_sub_mem_clSub_of_perp X hpa' (l := z₁) (by
      simpa using (Subgroup.mem_inf.mp hz₁).1)
    simpa [hV₁, coe_resV_apply] using this
  have hw₁c : (V₁ : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
    have := apply_sub_mem_clSub_of_perp X hpc (Subgroup.mem_inf.mp hz₁).2
    simpa [hV₁, coe_resV_apply] using this
  have hV₂a : (V₂ : S.Qt) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    have := Lbar_apply_sub_mem_span' haQ hw₁a (Subgroup.mem_inf.mp hz₂).1
    simpa [hV₂, coe_resV_apply] using this
  have hV₂c : (V₂ : S.Qt) ∈ (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    have := Lbar_apply_sub_mem_span' (conj_mem_QG' S h.2 haQ) hw₁c (Subgroup.mem_inf.mp hz₂).2
    simpa [hV₂, coe_resV_apply] using this
  rcases mem_span_singleton_zmod2.mp hV₂a with h1 | h1
  · exact hV₂0 h1
  rcases mem_span_singleton_zmod2.mp hV₂c with h2 | h2
  · exact hV₂0 h2
  exact hca (by rw [← h2, h1]; exact Submodule.mem_span_singleton_self _)

theorem StronglyClosedL.mem_Vt_of_mem_clSub_inf_Wt' (hSC : StronglyClosedL S g t)
    (X : Hyp10 S g t) (F : Frame X) {k h : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hcP : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)))
    (hcW : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Wt S g t) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t := by
  have hki : (S.ρ k)⁻¹ ∈ Rbar S g t := inv_mem hk
  have e : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl (((k⁻¹ * h : S.M) : G) * g * S.z * (((k⁻¹ * h : S.M) : G) * g)⁻¹) := by
    rw [← map_inv, ρ_cl_conj_mul X]
  have h1 := hSC.mem_Vt_of_mem_clSub_inf_Wt X F (h := k⁻¹ * h)
    (by rw [← e]; exact (mem_clSub_Qa_mul_iff k).mp hcP)
    (by rw [← e]; exact apply_mem_Wt X.H hki hcW)
  rw [← e] at h1
  have := apply_mem_Vt_of_mem_Rbar X.haQ hk h1
  rwa [apply_inv_apply_O] at this

end CFSG.LargeExtraspecial.S10
