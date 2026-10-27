module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSetupA
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuSym

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem aviol_symmGen (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    {zK zJ : G} (hK : K ∈ Ω) (h : AViol Ω K J zK zJ) : AViol Ω J K zJ zK where
  star := Q3T6.Mu.omegaStarNbr_symm hΩ hK h.mem h.star
  not_nbr := fun hn => h.not_nbr (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.mem hK hn)
  hzK := h.hzJ
  hzJ := h.hzK
  no_conj := by
    intro g hg hcon
    have hg' : g ∈ pairNormalizers K J zK zJ := by
      unfold pairNormalizers at hg ⊢
      rw [Set.pair_comm, sup_comm]
      exact hg
    apply h.no_conj g⁻¹ ((pairNormalizers K J zK zJ).inv_mem hg')
    rw [← hcon, conjSub_inv_conjSub]

theorem t_mem_sup_of_aviolGen (hΩ : HypOmegaGen Ω)
    {K₁ K₂ J₂ : Subgroup G} {z t₂ : G} (hK₁ : K₁ ∈ Ω) (h : AViol Ω K₁ J₂ z t₂)
    (htw : twinSet Ω K₁ = {K₁, K₂}) : t₂ ∈ K₁ ⊔ K₂ := by
  obtain ⟨v, Ks, hVU, hVJ, -, hKs, htw', hvv⟩ := exists_hexagon_data3 hΩ hK₁ h.mem h.hzK
    h.hzJ h.star h.not_nbr h.no_conj
  have hKsK₂ : Ks = K₂ := by
    have hm : Ks ∈ twinSet Ω K₁ := by rw [htw']; exact Or.inr rfl
    rw [htw] at hm
    rcases hm with h1 | h1
    · exact absurd h1 hKs
    · exact h1
  subst hKsK₂
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := Sec6Gen.isPGroup_of_mem_USet hΩ hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have htV : t₂ ∈ Subgroup.zpowers v := mem_of_isPGroup h.hzJ hVJ hV2 (by omega)
  obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic h.hzJ hVJ hVc hV2 h4V
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hww, ← (Commute.refl v).mul_zpow]
  exact Subgroup.zpow_mem _ hvv k

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
