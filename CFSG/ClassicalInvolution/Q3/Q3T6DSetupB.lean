module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSetupA
public import CFSG.ClassicalInvolution.Asc77.AscR10G2Q
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem rset_inf_sylow3 (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'})
    (nbr : ∀ L ∈ omegaNbr Ω K, L ∈ twinSet Ω K) (S : Sylow 2 G)
    (hR : IsSylow2In (K ⊓ (S : Subgroup G)) K) (hR' : IsSylow2In (K' ⊓ (S : Subgroup G)) K') :
    ∀ T ∈ RSet Ω, T ≤ (S : Subgroup G) → T = K ⊓ (S : Subgroup G) ∨ T = K' ⊓ (S : Subgroup G) := by
  intro T hT hTS
  by_cases hTR : T = K ⊓ (S : Subgroup G)
  · exact Or.inl hTR
  refine Or.inr ?_
  have hRset : K ⊓ (S : Subgroup G) ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have hzR : z ∈ K ⊓ (S : Subgroup G) := mem_of_isPGroup hz hR.1 hR.2.1 (by omega)
  obtain ⟨L, hLΩ, hTL⟩ := exists_isSylow2In_of_mem_RSet hT
  have hcomm := Q3CP.l67Gen G Ω hΩ S T hT _ hRset hTS inf_le_right hTR
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have h8T := Sec6Gen.eight_le_of_mem_RSet hΩ hT
  by_cases hLK : L = K
  · subst hLK
    exact absurd (hTL.eq_of_le hR.2.1 hR.1 (le_inf hTL.1 hTS)).symm hTR
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hLΩ (Ne.symm hLK) hz hTL.1 hTL.2.1
      (by omega) hTc
  have hLmem : L ∈ twinSet Ω K := nbr L ⟨hLΩ, hLK, T, hT, hTL.1, hTN⟩
  rw [htw] at hLmem
  rcases hLmem with h | h
  · exact absurd h hLK
  · subst h
    exact (hTL.eq_of_le hR'.2.1 hR'.1 (le_inf hTL.1 hTS)).symm

theorem exists_W_setup3 (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) :
    ∃ η : Set (Subgroup G), η ∈ etaSet Ω (S : Subgroup G) ∧
      (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
      (⨆ U ∈ η, U) ∈ WSet Ω ∧ (⨆ U ∈ η, U) ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  refine ⟨η, hη, hinv, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2, ?_⟩
  intro s hs
  exact mem_normalizer_of_conjSub_le (conjSub_iSup_le' (hinv s hs))

end Sylow

section Setup


theorem sec20Setup3_of : Sec20Setup3 := by
  have hn := CFSG.ClassicalInvolution.Q3.Q3T6D.omegaNbrTwin3
  intro G _ _ _ K J z t a g h
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := h.hypGen
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hJΩ : J ∈ CoreAssembly.conjClass K := h.viol.mem
  have hzK := h.viol.hzK
  have hzJ := h.viol.hzJ
  obtain ⟨v, Ks, hVU, hVJ, hVsyl, -, htw, hvv⟩ :=
    exists_hexagon_data3 hΩ hKΩ hJΩ hzK hzJ h.viol.star h.viol.not_nbr h.viol.no_conj
  set K' : Subgroup G := conjSub a J with hK'
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := hΩ.conjInvariant a J hJΩ
  have hzK' : IsUniqueInvolution K' z := by
    have := hzJ.conj a
    rwa [h.haz] at this
  have hK'tw : K' ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hK'Ω, z, hzK, hzK'⟩
  have hK's : K' = Ks := by
    rw [htw] at hK'tw
    rcases hK'tw with h1 | h1
    · exact absurd h1 h.hne
    · exact h1
  have htw' : twinSet (CoreAssembly.conjClass K) K = {K, K'} := by rw [htw, hK's]
  have hvv' : v * v ∈ K ⊔ K' := by rw [hK's]; exact hvv
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := Sec6Gen.isPGroup_of_mem_USet hΩ hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have htV : t ∈ Subgroup.zpowers v :=
    mem_of_isPGroup hzJ hVJ hV2 (by omega)
  have htKK : t ∈ K ⊔ K' := by
    obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic hzJ hVJ hVc hV2 h4V
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hww, ← (Commute.refl v).mul_zpow]
    exact Subgroup.zpow_mem _ hvv' k
  have hswap : ∃ g' ∈ Subgroup.centralizer ({z} : Set G), conjSub g' K = K' :=
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h.hgz), h.hg⟩
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hKΩ hK'Ω (Ne.symm h.hne) hzK hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hKΩ h.hne hzK' hzK
  obtain ⟨S, hVS, hR, hR'⟩ := exists_sylow_setup hΩ.conjInvariant hzK hzK' htw' h.hne hKN hK'N
    hV2 (hVsyl.1.trans inf_le_right)
  have hRset : K ⊓ (S : Subgroup G) ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In hKΩ hR
  have hrset := rset_inf_sylow3 hΩ hKΩ hzK htw' (hn G K J z t a g h) S hR hR'
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have hzR : z ∈ K ⊓ (S : Subgroup G) := mem_of_isPGroup hzK hR.1 hR.2.1 (by omega)
  have hRset' : K' ⊓ (S : Subgroup G) ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In hK'Ω hR'
  have h8' := Sec6Gen.eight_le_of_mem_RSet hΩ hRset'
  have hzR' : z ∈ K' ⊓ (S : Subgroup G) := mem_of_isPGroup hzK' hR'.1 hR'.2.1 (by omega)
  have hSz := sylow_le_centralizer hΩ.conjInvariant hzK hzK' S hR hR' hRset hzR hzR' hrset
  obtain ⟨η, hηS, hinv, hW, hWS, hWN⟩ := exists_W_setup3 hΩ S
  have hηS' : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  have hVW : Subgroup.zpowers v ≤ ⨆ U ∈ η, U := by
    obtain ⟨V', ⟨hV'η, hcase⟩, -⟩ := Sec6Gen.six_eight hΩ S hVU hVS ⟨S, hηS, hinv⟩ hηS'
    rcases hcase with h1 | h1
    · rw [h1]
      exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) V' hV'η
    · exfalso
      have hle : Subgroup.zpowers v ⊔ V' ≤ (S : Subgroup G) := sup_le hVS (hηS' V' hV'η)
      rcases hrset _ h1 hle with h2 | h2
      · have hmem : t ∈ Subgroup.zpowers v ⊔ V' := Subgroup.mem_sup_left htV
        rw [h2] at hmem
        have htK : t ∈ K := (Subgroup.mem_inf.mp hmem).1
        rcases hzK.unique t htK hzJ.sq with h3 | h3
        · exact hzJ.ne_one h3
        · exact AViol.ne_involution_gen hΩ hKΩ h.viol h3
      · have hmem : t ∈ Subgroup.zpowers v ⊔ V' := Subgroup.mem_sup_left htV
        rw [h2] at hmem
        have htK : t ∈ K' := (Subgroup.mem_inf.mp hmem).1
        rcases hzK'.unique t htK hzJ.sq with h3 | h3
        · exact hzJ.ne_one h3
        · exact AViol.ne_involution_gen hΩ hKΩ h.viol h3
  exact ⟨K', S, K ⊓ (S : Subgroup G), K' ⊓ (S : Subgroup G), ⨆ U ∈ η, U, Subgroup.zpowers v,
    ⟨h.branch, h.hyp, h.ih, h.viol, h.hne, htw', hswap, htKK, h.star, hSz, hR,
      inf_le_right, hR', inf_le_right, hrset, hW, hWS, hWN, hVU, hVS, hVW, htV⟩⟩

theorem sec20Setup3_proved : Sec20Setup3 := sec20Setup3_of

end Setup

end CFSG.ClassicalInvolution.Q3.Q3T6D
