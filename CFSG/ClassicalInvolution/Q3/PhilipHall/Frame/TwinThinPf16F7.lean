module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf16Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G]

@[expose] def F7Cent (K₀ : Subgroup G) (π : Set (Subgroup G)) (g : G) : Prop :=
  ∀ u : G, u ∈ pCoreOf 2 (conjSub g (piGen π)) → (∀ x ∈ piGen π, x * u = u * x) → u ≠ 1 →
    ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u, ∀ M ∈ centMembers (CoreAssembly.conjClass K₀) u,
      (¬ ∃ w ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub w L = M) → Commutes L M

variable {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)} {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem iso_q8 {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K₀) :
    Nonempty (↥L ≃* QuaternionGroup 2) := by
  obtain ⟨x, rfl⟩ := TwinSecXg.conj_trans_of_mem_conjClass S.hK L hL
  exact ⟨(Subgroup.equivMapOfInjective K (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).symm.trans S.hq8.some⟩

theorem f7Cent {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hG : Nat.card G ≤ n)
    (hS : IsSimpleGroup ↥(genFittingFStar G)) (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    {m : ℕ} (hm : 6 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥) :
    F7Cent K₀ π g := by
  intro u huO huX hu1 L hL M hM hnc
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K₀) := S.hs.hyp
  have hLY : L ≤ centLayer (CoreAssembly.conjClass K₀) u := le_centLayer hL
  have hMY : M ≤ centLayer (CoreAssembly.conjClass K₀) u := le_centLayer hM
  have hZ : Subgroup.center G = ⊥ := InductionBridge.center_eq_bot_of_fstar_simple hS hnab
  have hYu : centLayer (CoreAssembly.conjClass K₀) u ≤ Subgroup.centralizer ({u} : Set G) :=
    centLayer_le fun L hL => hL.2
  have hYtop : centLayer (CoreAssembly.conjClass K₀) u ≠ ⊤ := by
    intro htop
    apply hu1
    have hcent : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ Subgroup.centralizer ({u} : Set G) := hYu (htop ▸ Subgroup.mem_top x)
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hZ] at hcent
    exact (Subgroup.mem_bot).mp hcent
  have hlt : Nat.card ↥(centLayer (CoreAssembly.conjClass K₀) u) < n :=
    lt_of_lt_of_le (natCard_lt_of_ne_top hYtop) hG
  have hΔ := hypOmegaGen_restrict hΩ (centLayer (CoreAssembly.conjClass K₀) u)
  have h2Δ : ∀ L' ∈ restrictFamily (CoreAssembly.conjClass K₀) (centLayer (CoreAssembly.conjClass K₀) u),
      IsPGroup 2 (↥L' ⧸ classicalInvolutionOddCore ↥L') := by
    rintro _ ⟨L₀, hL₀, hL₀Y, rfl⟩
    exact ((S.hs.two L₀ hL₀).of_equiv (Subgroup.subgroupOfEquivOfLe hL₀Y).symm).to_quotient _
  have hq8Δ : ∀ L' ∈ restrictFamily (CoreAssembly.conjClass K₀) (centLayer (CoreAssembly.conjClass K₀) u),
      ∀ P : Subgroup ↥(centLayer (CoreAssembly.conjClass K₀) u), IsSylow2In P L' →
        Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rintro _ ⟨L₀, hL₀, hL₀Y, rfl⟩ P hP
    have h2L' : IsPGroup 2 ↥(L₀.subgroupOf (centLayer (CoreAssembly.conjClass K₀) u)) :=
      (S.hs.two L₀ hL₀).of_equiv (Subgroup.subgroupOfEquivOfLe hL₀Y).symm
    have hPL : L₀.subgroupOf (centLayer (CoreAssembly.conjClass K₀) u) = P :=
      hP.2.2 _ le_rfl h2L' hP.1
    exact ⟨(MulEquiv.subgroupCongr hPL.symm).trans
      ((Subgroup.subgroupOfEquivOfLe hL₀Y).trans (S.iso_q8 hL₀).some)⟩
  have hAΔ : ∀ J' ∈ restrictFamily (CoreAssembly.conjClass K₀) (centLayer (CoreAssembly.conjClass K₀) u),
      AEmpty (restrictFamily (CoreAssembly.conjClass K₀) (centLayer (CoreAssembly.conjClass K₀) u)) J' := by
    rintro _ ⟨L₀, hL₀, hL₀Y, rfl⟩
    exact aEmpty_restrictFamily hΩ S.hs.two subset_rfl hL₀Y (S.aEmpty L₀ hL₀)
  have hO := S.oddCore_centLayer_eq_bot hm J hodd huO huX
  have hnc' : ¬ ∃ y : ↥(centLayer (CoreAssembly.conjClass K₀) u),
      conjSub y (L.subgroupOf (centLayer (CoreAssembly.conjClass K₀) u)) =
        M.subgroupOf (centLayer (CoreAssembly.conjClass K₀) u) := by
    rintro ⟨y, hy⟩
    apply hnc
    refine ⟨y, y.2, ?_⟩
    rw [conjSub_subgroupOf] at hy
    have hyL : conjSub (y : G) L ≤ centLayer (CoreAssembly.conjClass K₀) u := by
      have := conjSub_mono (n := (y : G)) hLY
      rwa [conjSub_eq_self_of_mem y.2] at this
    have h1 := Subgroup.subgroupOf_inj.mp hy
    rwa [inf_of_le_left hyL, inf_of_le_left hMY] at h1
  have hc := h4 ↥(centLayer (CoreAssembly.conjClass K₀) u) hlt _ hΔ h2Δ hq8Δ hAΔ hO
    (L.subgroupOf (centLayer (CoreAssembly.conjClass K₀) u)) (subgroupOf_mem_restrictFamily hL.1 hLY)
    (M.subgroupOf (centLayer (CoreAssembly.conjClass K₀) u)) (subgroupOf_mem_restrictFamily hM.1 hMY)
    hnc'
  intro x hx y hy
  have := hc ⟨x, hLY hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hMY hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
  exact congrArg Subtype.val this

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
