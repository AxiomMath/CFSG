module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAltTwoPGammaCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltLocal
import CFSG.LocalAnalysis.AGLEmbedding.AltBeta

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Equiv Equiv.Perm CFSG.AGLEmbedding.KFactProofs.SmallIdent
  CFSG.AGLEmbeddingD2.AltSurvivor

theorem kFactAltTwoPGamma : KFactAltTwoPGamma := by
  intro K _ _ p hp hp5 hK T
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := hK
  set ι := altPermEmbed e with hι'
  have hι : Function.Injective ι := altPermEmbed_injective e
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  obtain ⟨a₁, ha₁, a₂, ha₂, O₁, O₂, hO₁, hO₂, hd, hm₁, hm₂⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 (by omega) hEab hEcard
  have hcov := mem_or_mem_of_card hO₁ hO₂ hd (Fintype.card_fin _)
  have hcyc : TwoCycles p a₁ a₂ O₁ O₂ :=
    ⟨hp, hEab.2 a₁ ha₁, hEab.2 a₂ ha₂, hO₁, hO₂, hd, hcov, hm₁, hm₂⟩
  obtain ⟨t₁, ht₁, ht₁ι⟩ := Subgroup.mem_map.1 ha₁
  obtain ⟨t₂, ht₂, ht₂ι⟩ := Subgroup.mem_map.1 ha₂
  set Γ := GLBCore p 1 (T : Subgroup K) with hΓ
  let ψ : ↥Γ →* Perm (Fin (2 * p)) := ι.comp Γ.subtype
  have hψ : Function.Injective ψ := hι.comp Subtype.val_injective
  have hΓpres : Γ ≤ (blockStab O₁).comap ι := by
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQr, rfl⟩ n hn
    have hQne : Q ≠ ⊥ := ne_bot_of_one_le_pRank' hp.two_le hQr
    have hcomm : ∀ q ∈ Q.map ι, q * a₁ = a₁ * q ∧ q * a₂ = a₂ * q := by
      rintro _ ⟨k, hk, rfl⟩
      have hkE : ι k ∈ (T : Subgroup K).map ι := ⟨k, hQT hk, rfl⟩
      exact ⟨congrArg Subtype.val (hEab.1.is_comm.comm ⟨ι k, hkE⟩ ⟨a₁, ha₁⟩),
        congrArg Subtype.val (hEab.1.is_comm.comm ⟨ι k, hkE⟩ ⟨a₂, ha₂⟩)⟩
    have hnorm : ι n ∈ Subgroup.normalizer ((Q.map ι : Subgroup (Perm (Fin (2 * p)))) :
        Set (Perm (Fin (2 * p)))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h'
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨n * k * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn k).1 hk, by simp⟩
      · rintro ⟨k, hk, hkh⟩
        refine ⟨n⁻¹ * k * n, ?_, ?_⟩
        · refine (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * k * n)).2 ?_
          have : n * (n⁻¹ * k * n) * n⁻¹ = k := by group
          rw [this]
          exact hk
        · simp only [map_mul, map_inv]
          rw [hkh]
          group
    exact mem_blockStab_of_mem_normalizer hcyc (fun q hq => (hcomm q hq).1)
      (fun q hq => (hcomm q hq).2)
      (fun h => hQne ((Subgroup.map_eq_bot_iff_of_injective Q hι).1 h)) hnorm
  have hpres : ∀ g : ↥Γ, ψ g ∈ blockStab O₁ := fun g => hΓpres g.2
  have hord : ∀ {t : K} {a : Perm (Fin (2 * p))} {O : Finset (Fin (2 * p))}, t ∈ (T : Subgroup K) →
      ι t = a → (∀ x, a x ≠ x ↔ x ∈ O) → O.card = p → orderOf t = p := by
    intro t a O ht hta hm hO
    have hne : t ≠ 1 := by
      intro h1
      obtain ⟨x, hx⟩ : O.Nonempty := Finset.card_pos.1 (by rw [hO]; exact hp.pos)
      exact (hm x).2 hx (by rw [← hta, h1, map_one]; rfl)
    exact orderOf_eq_prime (pow_eq_one_of_mem_isAltTwoP hp hp2 ⟨e⟩ T ht) hne
  have hAlt : ∀ {t : K} {a : Perm (Fin (2 * p))} {O O' : Finset (Fin (2 * p))},
      t ∈ (T : Subgroup K) → ι t = a → orderOf t = p → (∀ x, a x ≠ x ↔ x ∈ O) →
      Disjoint O O' → altOn O' ≤ ψ.range := by
    intro t a O O' ht hta hot hm hOO' g hg
    have hgA : g ∈ alternatingGroup (Fin (2 * p)) :=
      Perm.mem_alternatingGroup.2 (mem_altOn.1 hg).1
    set k : K := e.symm ⟨g, hgA⟩ with hk
    have hιk : ι k = g := by simp [hk, hι', altPermEmbed]
    have hdis : Perm.Disjoint g a := by
      intro x
      by_cases hx : x ∈ O
      · left
        exact (mem_altOn.1 hg).2 x (fun h => Finset.disjoint_left.1 hOO' hx h)
      · right
        by_contra h
        exact hx ((hm x).1 h)
    have hcomm : k * t = t * k := by
      apply hι
      rw [map_mul, map_mul, hιk, hta]
      exact hdis.commute.eq
    have hkΓ : k ∈ Γ := by
      refine CFSG.AGLEmbedding.normalizer_zpowers_le_glbCore hp ht hot ?_
      apply Subgroup.centralizer_le_normalizer
      exact CFSG.AGLEmbedding.mem_centralizer_zpowers hcomm
    exact ⟨⟨k, hkΓ⟩, hιk⟩
  have hAlt₁ : altOn O₁ ≤ ψ.range := hAlt ht₂ ht₂ι (hord ht₂ ht₂ι hm₂ hO₂) hm₂ hd.symm
  have hAlt₂ : altOn O₂ ≤ ψ.range := hAlt ht₁ ht₁ι (hord ht₁ ht₁ι hm₁ hO₁) hm₁ hd
  refine ⟨?_, fun V hV => exists_injective_hom_of_perfect hcyc ψ hψ hpres hV⟩
  unfold CFSG.pCore
  rw [sSup_eq_bot]
  rintro N ⟨hN, hNp⟩
  exact eq_bot_of_normal_pGroup hcyc hp5 ψ hψ hpres hAlt₁ hAlt₂ hN hNp

end CFSG.AGLEmbedding
