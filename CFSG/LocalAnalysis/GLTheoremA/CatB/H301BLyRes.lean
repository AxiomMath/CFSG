module

public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier
  CFSG.ComponentClassification.PerfectAutomorphisms

section Centre


private theorem mulConj_lyJ (α : MulAut J) (x : J) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  apply MulEquiv.ext
  intro u
  change α (x * α.symm u * x⁻¹) = α x * u * (α x)⁻¹
  rw [map_mul, map_mul, map_inv, α.apply_symm_apply]

theorem center_lyJ_eq_bot : Subgroup.center J = ⊥ := by
  haveI : IsSimpleGroup J := isSimpleGroup_J
  have hnc : ¬ IsMulCommutative J := by
    intro hcomm
    haveI : IsMulCommutative J := hcomm
    have hp : (Nat.card J).Prime := (Group.is_simple_iff_prime_card).mp inferInstance
    rw [card_J] at hp
    exact (by norm_num : ¬ Nat.Prime 51765179004000000) hp
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc

theorem conj_injective_lyJ {g h : J} (hgh : MulAut.conj g = MulAut.conj h) : g = h := by
  have key : ∀ u : J, (g⁻¹ * h)⁻¹ * u * (g⁻¹ * h) = u := fun u => by
    have hu : g * u * g⁻¹ = h * u * h⁻¹ := by
      have := DFunLike.congr_fun hgh u
      rwa [MulAut.conj_apply, MulAut.conj_apply] at this
    calc (g⁻¹ * h)⁻¹ * u * (g⁻¹ * h) = h⁻¹ * (g * u * g⁻¹) * h := by group
      _ = h⁻¹ * (h * u * h⁻¹) * h := by rw [hu]
      _ = u := by group
  have hc : g⁻¹ * h ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro u
    calc u * (g⁻¹ * h) = (g⁻¹ * h) * ((g⁻¹ * h)⁻¹ * u * (g⁻¹ * h)) := by group
      _ = (g⁻¹ * h) * u := by rw [key]
  rw [center_lyJ_eq_bot, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.1 hc

end Centre

section Act


theorem mem_autZ_of_commute {α : MulAut J}
    (h : α * MulAut.conj lyz = MulAut.conj lyz * α) : α ∈ autZ := by
  rw [mem_autZ]
  refine conj_injective_lyJ ?_
  rw [← mulConj_lyJ α lyz, h, mul_inv_cancel_right]

private noncomputable def autPerm11 {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 11)) :
    MulAut K ≃* Perm (Fin 11) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11 (by norm_num)
      (by norm_num))).symm

noncomputable def autZPerm : autZ →* Perm (Fin 11) :=
  (autPerm11 lyCenterEquiv).toMonoidHom.comp ((centerQuotientHom lyC).comp restrictC)

theorem ker_autZPerm {a : autZ} (ha : autZPerm a = 1) :
    (a : MulAut J) = 1 ∨ (a : MulAut J) = MulAut.conj lyz := by
  have h1 : centerQuotientHom lyC (restrictC a) = 1 :=
    (autPerm11 lyCenterEquiv).injective (ha.trans (map_one (autPerm11 lyCenterEquiv)).symm)
  have h2 : restrictC a = 1 := by
    apply centerQuotientHom_injective lyC
    rw [h1, map_one]
  refine fixes_C_cases fun c hc => ?_
  have h3 := congrArg (fun γ : MulAut lyC => (γ ⟨c, hc⟩ : J)) h2
  simpa [restrictC_apply] using h3

theorem card_ker_autZPerm_le : Nat.card autZPerm.ker ≤ 2 := by
  classical
  refine le_trans (Nat.card_le_card_of_injective
    (fun a : autZPerm.ker => decide (((a : autZ) : MulAut J) = 1)) ?_)
    (Nat.card_eq_fintype_card.trans Fintype.card_bool).le
  intro a b hab
  have ha := ker_autZPerm (MonoidHom.mem_ker.1 a.2)
  have hb := ker_autZPerm (MonoidHom.mem_ker.1 b.2)
  by_cases h1 : ((a : autZ) : MulAut J) = 1
  · have h2 : ((b : autZ) : MulAut J) = 1 := by
      by_contra h2
      simp [h1, h2] at hab
    exact Subtype.ext (Subtype.ext (h1.trans h2.symm))
  · have h2 : ((b : autZ) : MulAut J) ≠ 1 := by
      intro h2
      simp [h1, h2] at hab
    exact Subtype.ext (Subtype.ext ((ha.resolve_left h1).trans (hb.resolve_left h2).symm))

noncomputable def autZPermOf {G : Type*} [Group G] (θ : G →* MulAut J) :
    autZ.comap θ →* Perm (Fin 11) :=
  autZPerm.comp (θ.subgroupComap autZ)

theorem card_ker_autZPermOf_le {G : Type*} [Group G] {θ : G →* MulAut J}
    (hθ : Function.Injective θ) : Nat.card (autZPermOf θ).ker ≤ 2 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : (autZPermOf θ).ker => (⟨θ.subgroupComap autZ x.1, x.2⟩ : autZPerm.ker)) ?_)
    card_ker_autZPerm_le
  intro x y hxy
  have h := congrArg (fun w : autZPerm.ker => ((w : autZ) : MulAut J)) hxy
  exact Subtype.ext (Subtype.ext (hθ h))

end Act

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
