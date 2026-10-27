module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Ax01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement

section ZStar


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_T_of_std8 (hs : Std8 Ω K J S R T W z t) : t ∈ T := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hTsyl : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hs.hT.1
  exact T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTsyl.2.1 (by omega)

theorem layer_exists_zStar_conj (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hS₂Y : IsSylow2In ((S₂ : Subgroup G) ⊓ nbrLayer Ω K z) (nbrLayer Ω K z))
    (hcen : Subgroup.center (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z)) = ⊥) :
    ∃ g ∈ nbrLayer Ω K z, g⁻¹ * t * g ∈ (S₂ : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
  classical
  by_contra hcon
  push Not at hcon
  set Y : Subgroup G := nbrLayer Ω K z with hYdef
  have hTY : T ≤ Y := (layerT_le_exactCore hs).trans (exactCore3_le_nbrLayer hs.hJ)
  have htT : t ∈ T := mem_T_of_std8 hs
  have htY : t ∈ Y := hTY htT
  have htS₂ : t ∈ (S₂ : Subgroup G) := hTS₂ htT
  let SH : Sylow 2 ↥Y := AscP1Nine3.sylowOfIsSylow2In₉ hS₂Y
  have hSH : (SH : Subgroup ↥Y) = ((S₂ : Subgroup G) ⊓ Y).subgroupOf Y := rfl
  have htSH : (⟨t, htY⟩ : ↥Y) ∈ (SH : Subgroup ↥Y) := by
    rw [hSH, Subgroup.mem_subgroupOf]
    exact ⟨htS₂, htY⟩
  let zt : ↥(SH : Subgroup ↥Y) := ⟨⟨t, htY⟩, htSH⟩
  have hzZ : zt ∈ Subgroup.center ↥(SH : Subgroup ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hsmem : (s : ↥Y) ∈ ((S₂ : Subgroup G) ⊓ Y).subgroupOf Y := s.2
    rw [Subgroup.mem_subgroupOf] at hsmem
    have h := layer_sY_centralizes_t hs hE hRS₂ hTS₂ hsmem.1 hsmem.2
    apply Subtype.ext
    apply Subtype.ext
    show (s : ↥Y).1 * t = t * (s : ↥Y).1
    calc (s : ↥Y).1 * t = ((s : ↥Y).1 * t * (s : ↥Y).1⁻¹) * (s : ↥Y).1 := by group
      _ = t * (s : ↥Y).1 := by rw [h]
  have hzo : orderOf zt = 2 := by
    have h2 : orderOf (t : G) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs.ht.sq) hs.ht.ne_one
    have h3 : orderOf (⟨t, htY⟩ : ↥Y) = 2 := (Subgroup.orderOf_mk t htY).trans h2
    exact (Subgroup.orderOf_mk _ htSH).trans h3
  have hwc : ∀ g : ↥Y, g⁻¹ * (zt : ↥Y) * g ∈ (SH : Subgroup ↥Y) → g⁻¹ * (zt : ↥Y) * g = zt := by
    intro g hg
    have hg' : g⁻¹ * (zt : ↥Y) * g ∈ ((S₂ : Subgroup G) ⊓ Y).subgroupOf Y := hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have := hcon g.1 g.2 hg'.1
    apply Subtype.ext
    show g.1⁻¹ * t * g.1 = t
    exact this
  obtain ⟨-, hcen'⟩ := CFSG.Adapters.glauberman_zStar SH zt hzZ hzo hwc
  set N : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hNdef
  have hcen'' : (QuotientGroup.mk' N) ⟨t, htY⟩ ∈ Subgroup.center (↥Y ⧸ N) := hcen'
  rw [hcen, Subgroup.mem_bot] at hcen''
  have h2 : (⟨t, htY⟩ : ↥Y) ∈ N := (QuotientGroup.eq_one_iff _).mp hcen''
  have h3 : t ∈ oddCoreOf Y := mem_oddCoreOf_iff.mpr ⟨htY, h2⟩
  exact hs.ht.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h3
    (isPGroup_zpowers_of_mul_self_eq_one hs.ht.sq hs.ht.ne_one))

end ZStar

end CFSG.ClassicalInvolution.Q3.Q3AM
