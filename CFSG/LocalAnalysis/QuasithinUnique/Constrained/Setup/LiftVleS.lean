module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Main

variable {G : Type} [Group G]

theorem V_le_baum_of_data {R V L : Subgroup G} (hVR : V ≤ R)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hEsplit : omegaOneCenterOf (thompsonJ R) =
      (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
        (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)))
    (hAE : V ⊓ Subgroup.centralizer (thompsonJ R : Set G) ≤ omegaOneCenterOf (thompsonJ R))
    (hVspan : (⨆ l ∈ L, cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V) :
    V ≤ baum R := by
  set J := thompsonJ R
  have hEJ : omegaOneCenterOf J ≤ J ⊓ Subgroup.centralizer (J : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact hx.1
  have hEcomm : ∀ e ∈ omegaOneCenterOf J, ∀ e' ∈ omegaOneCenterOf J, e * e' = e' * e := by
    intro e he e' he'
    exact (Subgroup.mem_centralizer_iff.1 (hEJ he).2 e' (hEJ he').1).symm
  have hUV : ∀ u ∈ omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G),
      ∀ v ∈ V, u * v = v * u := by
    intro u hu
    have hVle : V ≤ Subgroup.centralizer ({u} : Set G) := by
      rw [← hVspan]
      refine iSup₂_le fun l' hl' => ?_
      intro y hy
      have hy' : (l' : G) * y * (l' : G)⁻¹ ∈ V ⊓ Subgroup.centralizer (J : Set G) := mem_cj.1 hy
      have ha : (l' : G) * y * (l' : G)⁻¹ ∈ omegaOneCenterOf J := hAE hy'
      have hua : Commute u ((l' : G) * y * (l' : G)⁻¹) := hEcomm u hu.1 _ ha
      have hcu : Commute u (l' : G) := (Subgroup.mem_centralizer_iff.1 hu.2 l' hl').symm
      have hy_eq : y = (l' : G)⁻¹ * ((l' : G) * y * (l' : G)⁻¹) * (l' : G) := by group
      have hcy : Commute u ((l' : G)⁻¹ * ((l' : G) * y * (l' : G)⁻¹) * (l' : G)) :=
        (hcu.inv_right.mul_right hua).mul_right hcu
      rw [← hy_eq] at hcy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcy.eq
    intro v hv
    exact Subgroup.mem_centralizer_iff.1 (hVle hv) u (Set.mem_singleton u)
  have hEC : omegaOneCenterOf J ≤ Subgroup.centralizer (V : Set G) := by
    rw [hEsplit]
    refine sup_le (fun u hu => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun v hv => (hUV u hu v hv).symm
    · exact Subgroup.mem_centralizer_iff.2 fun v hv => hVc v hv a ha.1
  refine le_inf hVR fun v hv => Subgroup.mem_centralizer_iff.2 fun e he => ?_
  exact (Subgroup.mem_centralizer_iff.1 (hEC he) v hv).symm

end Main

section NatVleS

theorem natVleSProp
    : NatVleSProp := by
  intro G _ _ R M V n F _ r Lc ctx
  have hS := ctx.setting
  have hout := even_SL2_natural_baumann hS ctx.comps ctx.natural
  obtain ⟨-, -, -, -, hVR⟩ := even_SL2_setting_basic hS
  exact V_le_baum_of_data hVR
    (fun a ha b hb => congrArg Subtype.val (hS.reduced.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    hout.E_split hout.A_le_E hout.V_span

end NatVleS

end CFSG.QuasithinUnique.Setup.Lift
