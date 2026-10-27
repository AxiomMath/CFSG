module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SubgroupNormalizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalNormal
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryGeneration

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.SignalizerFunctor.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem coprime_normal_quotient_preimage_le_overgroup
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (hrank : 3 ≤ pRank 2 (S : Subgroup G))
    (Q : Subgroup G) [Q.Normal] (hQH : Q ≤ H)
    (L : Subgroup (G ⧸ Q)) [L.Normal] (hcoprime : Nat.Coprime 2 (Nat.card L)) :
    L.comap (QuotientGroup.mk' Q) ≤ H := by
  let pi := QuotientGroup.mk' Q
  obtain ⟨E, hES, hE, hEcard⟩ := pRank_attained 2 (S : Subgroup G) (by omega)
  let := hE.1
  let : CommGroup E := { E.toGroup with mul_comm := mul_comm' }
  let actionHom : E →* MulAut L :=
    (MulAut.conjNormal : (G ⧸ Q) →* MulAut L).comp (pi.comp E.subtype)
  let := MulDistribMulAction.compHom L actionHom
  have hEexponent : ∀ e : E, e ^ 2 = 1 := by
    intro e
    exact Subtype.ext (hE.2 e e.property)
  have hElarge : 2 ^ (2 + 1) ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (by decide) hrank
  have hgenerated := elementary_abelian_order_generation 2 2 Nat.prime_two
    E hEexponent hElarge L hcoprime
  have hfixed : ∀ V : Subgroup E, Nat.card V = 2 ^ 2 →
      (FixedPoints.subgroup V L).map L.subtype ≤ H.map pi := by
    intro V hVcard y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Q (x : G ⧸ Q)
    let W := V.map E.subtype
    have hWE : W ≤ E := Subgroup.map_subtype_le V
    have hWrank : 2 ≤ pRank 2 W := by
      apply le_csSup (pRank_set_bddAbove 2 (by decide) W)
      refine ⟨W, le_rfl, elementary_abelian_of_le 2 hE hWE, ?_⟩
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      exact hVcard
    have hcentral : pi l ∈ Subgroup.centralizer (W.map pi : Set (G ⧸ Q)) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro w hw
      obtain ⟨v, hv, rfl⟩ := hw
      obtain ⟨e, he, rfl⟩ := hv
      have hfix := congrArg (fun z : L => (z : G ⧸ Q)) (hx (⟨e, he⟩ : V))
      change pi e.val * x.val * (pi e.val)⁻¹ = x.val at hfix
      rw [← hl] at hfix
      exact mul_inv_eq_iff_eq_mul.mp hfix
    have hnormalizer : l ∈ Subgroup.normalizer ((W ⊔ Q : Subgroup G) : Set G) := by
      have hpreimage := Subgroup.le_normalizer_comap pi
        ((Subgroup.centralizer_le_normalizer (W.map pi : Set (G ⧸ Q))) hcentral)
      simpa only [Subgroup.comap_map_eq, pi, QuotientGroup.ker_mk'] using hpreimage
    have hproduct : W ⊔ Q ≤ H :=
      sup_le ((hWE.trans hES).trans hSH) hQH
    have hproductRank : 2 ≤ pRank 2 (W ⊔ Q) :=
      hWrank.trans (pRank_mono 2 (by decide) le_sup_left)
    have hlH := two_generated_core_subgroup_normalizer_le S H hSH hcore
      (W ⊔ Q) hproduct hproductRank hnormalizer
    exact ⟨l, hlH, hl⟩
  have hLimage : L ≤ H.map pi := by
    have hmapTop : (⊤ : Subgroup L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, L.subtype_range]
    rw [← hmapTop, ← hgenerated, Subgroup.map_iSup]
    apply iSup_le
    intro V
    rw [Subgroup.map_iSup]
    exact iSup_le (hfixed V)
  apply le_trans (Subgroup.comap_mono hLimage)
  change (H.map (QuotientGroup.mk' Q)).comap (QuotientGroup.mk' Q) ≤ H
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact sup_le le_rfl hQH

theorem solvable_core_eq_top_of_sylow_rank [Group.IsSolvable G]
    (S : Sylow 2 G) (hrank : 3 ≤ pRank 2 (S : Subgroup G)) :
    properTwoGenCoreGamma (S : Subgroup G) 2 = ⊤ := by
  classical
  let H := properTwoGenCoreGamma (S : Subgroup G) 2
  have hSH : (S : Subgroup G) ≤ H := sylow_le_gamma S (by omega)
  by_contra hproper
  change H ≠ ⊤ at hproper
  let Q := H.normalCore
  have hQH : Q ≤ H := H.normalCore_le
  have hQproper : Q ≠ ⊤ := by
    intro htop
    exact hproper (top_le_iff.mp (htop ▸ hQH))
  let : Nontrivial (G ⧸ Q) := QuotientGroup.nontrivial_iff.mpr hQproper
  let pi := QuotientGroup.mk' Q
  obtain ⟨L, hLnormal, hLne, _, p, r, hp, _, hL, hLcard⟩ :=
    solvable_minimal_normal_exists (GroupType := G ⧸ Q)
  let := hLnormal
  have hpreimage : L.comap pi ≤ H := by
    by_cases hpTwo : p = 2
    · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hLtwo : IsPGroup 2 L := by
        rw [← hpTwo]
        exact elementary_isPGroup p L hL
      have hLS := hLtwo.le_sylow_of_normal
        (S.mapSurjective (QuotientGroup.mk'_surjective Q))
      rw [Sylow.coe_mapSurjective] at hLS
      apply le_trans (Subgroup.comap_mono hLS)
      change ((S : Subgroup G).map (QuotientGroup.mk' Q)).comap
        (QuotientGroup.mk' Q) ≤ H
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_le hSH hQH
    · apply coprime_normal_quotient_preimage_le_overgroup S H hSH le_rfl hrank Q hQH L
      rw [hLcard]
      exact ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hpTwo)).pow_right r
  have hpreimageQ : L.comap pi ≤ Q :=
    Subgroup.normal_le_normalCore.mpr hpreimage
  have hmapQ : Q.map pi = ⊥ := by
    apply (Subgroup.map_eq_bot_iff Q).mpr
    change Q ≤ (QuotientGroup.mk' Q).ker
    rw [QuotientGroup.ker_mk']
  have hLbot := Subgroup.map_mono (f := pi) hpreimageQ
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q),
    hmapQ] at hLbot
  exact hLne (le_bot_iff.mp hLbot)

theorem solvable_rank_three_full_core [Group.IsSolvable G]
    (hrank : 3 ≤ twoRank G) (S : Sylow 2 G) :
    properTwoGenCoreGamma (S : Subgroup G) 2 = ⊤ := by
  apply solvable_core_eq_top_of_sylow_rank S
  rwa [sylow_two_rank_eq]

end CFSG.ProperTwoGeneratedCore
