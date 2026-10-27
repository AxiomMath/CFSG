module

public import CFSG.LargeExtraspecial.DW2AAlphaComp
public import CFSG.LargeExtraspecial.S12ARS
public import CFSG.LargeExtraspecial.S14LitRoot
public import CFSG.Timmesfeld.Skeleton

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}
  (hA : Hyp S W)
include hA

theorem noNormalTwo_Xbar : S12NoNormalTwo (Xbar S W) :=
  S.s12_noNormalTwo_Mbar.of_normal Xbar_le_Mbar (Mbar_le_normalizer_Xbar hA)

variable [IsSimpleGroup G] (hn : 2 ≤ S.width) {h₀ : G} (hx₀ : IsDx S W h₀) {t₀ : S.O}
  (ht₀ : t₀ ∈ Abar S (S.clPre W) h₀) (ht₀1 : t₀ ≠ 1)
include hn hx₀ ht₀ ht₀1

theorem Tset_conj {τ : S.O} (hτ : τ ∈ Tset S W) : ∃ x ∈ Xbar S W, τ = x * t₀ * x⁻¹ := by
  have ht₀T := mem_Tset_of_mem_Abar hA hx₀ ht₀ ht₀1
  obtain ⟨x, hx, hxτ⟩ := S14.rootInvolutionComponentsInput S.Qt S.q S.q_nondegenerate
    (Xbar S W) (noNormalTwo_Xbar hA) (Tset S W) rfl t₀ ht₀T τ (mem_tcomp hA hn hx₀ ht₀ ht₀1 hτ)
  refine ⟨x, ?_, hxτ⟩
  refine (closure_le _).mpr (fun f hf => ?_) hx
  exact (mem_Tset_of_mem_tcomp ht₀T hf).1

theorem transpositionData : S12TranspositionData (Xbar S W) (Tset S W) t₀ where
  subset := fun _ h => h.1
  gen := le_antisymm (Xbar_le_closure_Tset hA) closure_Tset_le_Xbar
  mem := mem_Tset_of_mem_Abar hA hx₀ ht₀ ht₀1
  cls := fun τ hτ => Tset_conj hA hn hx₀ ht₀ ht₀1 hτ
  conj := fun x hx τ hτ => by
    refine ⟨(Xbar S W).mul_mem ((Xbar S W).mul_mem hx hτ.1) ((Xbar S W).inv_mem hx), ?_⟩
    have e : ((x * τ * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (x : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := by simp
    rw [e]
    exact s12_isTypeA_conj hτ.2 x.2
  invol := fun τ hτ => Tset_mul_self hτ
  ne_one := fun τ hτ => Tset_ne_one hτ
  ord := fun d hd e he => by
    have h := (aschbacher_3_7 S.q_nondegenerate hd.2 he.2).1
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega
  sq := fun d hd e he h4 => by
    have h := (aschbacher_3_7 S.q_nondegenerate hd.2 he.2).2
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
    refine ⟨(Xbar S W).pow_mem ((Xbar S W).mul_mem hd.1 he.1) 2, ?_⟩
    have := h h4
    simpa using this

omit ht₀ ht₀1 in

theorem exists_orderOf_eq_four : ∃ d ∈ Tset S W, ∃ e ∈ Tset S W, orderOf (d * e) = 4 := by
  have h2 : 2 ≤ S.width := by omega
  obtain ⟨t₁, ht₁, t₂, ht₂, h1, h2', h12⟩ := exists_two_mem_Abar hA h2 hx₀
  have hT₁ := mem_Tset_of_mem_Abar hA hx₀ ht₁ h1
  have hT₂ := mem_Tset_of_mem_Abar hA hx₀ ht₂ h2'
  have hcomm := Abar_comm hA hx₀ ht₁ ht₂
  have h121 : t₁ * t₂ ≠ 1 := by
    intro e
    apply h12
    calc t₁ = t₁ * (t₂ * t₂) := by rw [Tset_mul_self hT₂, mul_one]
      _ = (t₁ * t₂) * t₂ := by group
      _ = t₂ := by rw [e, one_mul]
  have hT₁₂ := mem_Tset_of_mem_Abar hA hx₀ (mul_mem ht₁ ht₂) h121
  obtain ⟨h, hx, s, hs, hs1, hns⟩ := exists_not_commute_gen hA h2 hT₁
  have hsT := mem_Tset_of_mem_Abar hA hx hs hs1
  have hord : ∀ d ∈ Tset S W, ∀ e ∈ Tset S W,
      orderOf (d * e) ∈ ({1, 2, 3, 4} : Finset ℕ) := by
    intro d hd e he
    have h := (aschbacher_3_7 S.q_nondegenerate hd.2 he.2).1
    rwa [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
  rcases orderOf_eq_four_of_four_group (Tset_mul_self hsT) (Tset_mul_self hT₁)
      (Tset_mul_self hT₂) h2' hcomm h12 (fun e => hns e.symm) (hord s hsT t₁ hT₁)
      (hord s hsT t₂ hT₂) (hord s hsT _ hT₁₂) with e | e | e
  · exact ⟨s, hsT, t₁, hT₁, e⟩
  · exact ⟨s, hsT, t₂, hT₂, e⟩
  · exact ⟨s, hsT, t₁ * t₂, hT₁₂, e⟩

theorem outcome_Xbar (hARS : CFSG.Timmesfeld.ARSInput) : CFSG.Timmesfeld.Outcome (Xbar S W) :=
  hARS _ _ ((transpositionData hA hn hx₀ ht₀ ht₀1).arsHyp
    (fun y hy hc => eq_one_of_mem_center hA (by omega) hy fun x hx => hc x hx)
    (noNormalTwo_Xbar hA) (exists_orderOf_eq_four hA hn hx₀))

end Alpha

end CFSG.LargeExtraspecial.DW
