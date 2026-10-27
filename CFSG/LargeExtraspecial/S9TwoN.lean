module

public import CFSG.LargeExtraspecial.S8FiveA
public import CFSG.LargeExtraspecial.S6TwoD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S8

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem conj_eq_of_normalizer_Abar_of (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
    (hR : RadBound S g t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxL : x ∈ normalizer (S.Lbar g : Set S.O))
    (hxA : x ∈ normalizer ((S.Lbar g ⊓ Nbar S g t : Subgroup S.O) : Set S.O)) :
    x * t * x⁻¹ = t := by
  have haQ := H.conj_mem
  have hne := H.conj_ne
  have htA : t ∈ S.Lbar g ⊓ Nbar S g t := ⟨ht, self_mem_Nbar H ht⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = x * t * x⁻¹ := ⟨_, rfl⟩
  have hτA : τ ∈ S.Lbar g ⊓ Nbar S g t := by rw [hτ]; exact (mem_normalizer_iff.mp hxA t).mp htA
  rw [← hτ]
  by_contra hτt
  obtain ⟨P, hP⟩ : ∃ P, P = S.clSub (S.QG ⊓ S.Qa g) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = P ⊓ Vt S g t := ⟨_, rfl⟩
  have hfixA := clSub_inf_fixSub_Abar H C ht ht1 hVQ hA
  rw [← hP] at hfixA
  have hxa : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    fix_of_mem_normalizer H hxL
  have hxinv_a : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    conv_lhs => rw [← hxa]
    exact inv_apply_apply_O x _
  have hxP : ∀ p ∈ P, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ P := fun p hp => by
    rw [hP] at hp ⊢
    exact apply_mem_clSub_of_apply_cl_eq haQ hne (inv_mem hxM) hxinv_a hp
  have hVτ : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hτ, S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hAV : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, ∀ v ∈ Vt S g t, (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
    fun α hα v hv => (mem_Nbar.mp hα.2).2 v hv
  have hAVτ : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, ∀ v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro α hα v hv
    rw [hVτ] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hα' : x⁻¹ * α * x ∈ S.Lbar g ⊓ Nbar S g t := by
      have := (mem_normalizer_iff.mp (inv_mem hxA) α).mp hα
      rwa [inv_inv] at this
    have h1 := hAV _ hα' w hw
    change ((x⁻¹ * α * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w at h1
    change (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w
    have e : ((x⁻¹ * α * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := rfl
    rw [e] at h1
    have h2 := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2
  have hUτ : U ≤ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro u hu
    rw [hU] at hu
    have hxu : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ P ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := by
      refine ⟨hxP u hu.1, (mem_fixSub S).mpr fun α hα => ?_⟩
      have hα' : x * α * x⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := (mem_normalizer_iff.mp hxA α).mp hα
      have h1 := hAV _ hα' u hu.2
      change ((x * α * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u at h1
      have e : ((x * α * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) := rfl
      rw [e] at h1
      have h2 := congrArg (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
      rwa [inv_apply_apply_O] at h2
    rw [hfixA] at hxu
    rw [hVτ]
    exact ⟨_, hxu.2, apply_inv_apply_O x u⟩
  have hUV : U ≤ Vt S g t := by rw [hU]; exact inf_le_right
  have hdimU : finrank (ZMod 2) U + 1 = finrank (ZMod 2) (Vt S g t) := by
    rw [hU, hP]; exact finrank_clSub_inf_Vt H C ht ht1 hVQ
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hVτ, LinearEquiv.finrank_map_eq]
  have hne' : ¬ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t := by
    intro hle
    apply hτt
    exact eq_t_of_commSpace_eq H C ht ht1 hVQ hτA.1
      (Submodule.eq_of_le_of_finrank_eq hle hdimτ)
  obtain ⟨v, hvτ, hvV⟩ := IsConcreteLE.not_le_iff_exists.mp hne'
  have hinf : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ Vt S g t = U := by
    refine (Submodule.eq_of_le_of_finrank_le (le_inf hUτ hUV) ?_).symm
    have h1 : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ Vt S g t <
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      lt_of_le_of_ne inf_le_left fun h => hne' (h ▸ inf_le_right)
    have h2 := Submodule.finrank_lt_finrank_of_lt h1
    omega
  have hLv : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := by
    intro l hl
    have hlτ : l * τ = τ * l := Lbar_comm S haQ hl hτA.1
    have hlvτ : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      obtain ⟨q, rfl⟩ := mem_commSpace.mp hvτ
      refine mem_commSpace.mpr ⟨(l : S.Qt ≃ₗ[ZMod 2] S.Qt) q, ?_⟩
      rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, hlτ]
    have hdiff : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      sub_mem hlvτ hvτ
    by_contra hcon
    have hlvU : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∉ U := fun h => hcon (hUV h)
    have hspan : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = U ⊔ (ZMod 2) ∙ v := by
      have hvU : v ∉ U := fun h => hvV (hUV h)
      have hle : U ⊔ (ZMod 2) ∙ v ≤ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        sup_le hUτ ((Submodule.span_singleton_le_iff_mem _ _).mpr hvτ)
      refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
      have hdisj : U ⊓ (ZMod 2) ∙ v = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy.2
        rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
        · simp
        · rw [one_smul] at hy
          exact absurd hy.1 hvU
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq U ((ZMod 2) ∙ v)
      have hv0 : v ≠ 0 := by
        rintro rfl
        exact hvV (zero_mem _)
      rw [hdisj, finrank_bot, finrank_span_singleton hv0] at h1
      omega
    rw [hspan] at hdiff
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hdiff
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul, add_zero] at hyz
      exact hlvU (hyz ▸ hy)
    ·
      rw [one_smul] at hyz
      have hlv : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v = y := by
        have : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v = y + v + v := by rw [hyz]; abel
        have hvv : v + v = 0 := by
          rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]
        rw [this, add_assoc, hvv, add_zero]
      have hyV : y ∈ Vt S g t := hUV hy
      have hvV' : v ∈ Vt S g t := by
        have h1 := apply_mem_Vt_of_mem_Rbar haQ (inv_mem (Lbar_le_Rbar ht hl)) hyV
        rwa [← hlv, inv_apply_apply_O] at h1
      exact hvV hvV'
  have hvW : v ∈ Wt S g t := commSpace_le_Wt_of_fix (fun w hw => hAV τ hτA w hw) hvτ
  have hPI := pairInt_of_radBound H C ht ht1 hVQ hR
  have hmem := (forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hvW).mp hLv
  obtain ⟨p, hp, v₀, hv₀, rfl⟩ := Submodule.mem_sup.mp hmem
  have hpfix : p ∈ P ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := by
    refine ⟨hP ▸ hp.1, (mem_fixSub S).mpr fun α hα => ?_⟩
    have h1 := hAVτ α hα _ hvτ
    have h2 := hAV α hα v₀ hv₀
    rw [map_add, h2] at h1
    exact add_right_cancel h1
  rw [hfixA] at hpfix
  exact hvV (add_mem hpfix.2 hv₀)

end CFSG.LargeExtraspecial.S9
