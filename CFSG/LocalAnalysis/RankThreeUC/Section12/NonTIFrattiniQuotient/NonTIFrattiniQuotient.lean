module

public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.LocalAnalysis.RankThreeUC.NormalModules
import all CFSG.LocalAnalysis.RankThreeUC.NormalModules
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank.NonTISigmaPrimeRank
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section12.NonTIFrattiniQuotient

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem quotient_rank_le_of_normalizer {M T V : Subgroup G} (hc : Context G M T)
    (hV : V ∈ normalElemAbelian2 M) [(centralizerInSubgroup M V).Normal] {p : ℕ}
    (hp : p ∈ SourceSetting.sigmaOf G M)
    (h : CFSG.Assembly.pRank p (normalizerCentralizerIn M T V) ≤ 1) :
    CFSG.pRank p (M ⧸ centralizerInSubgroup M V) ≤ 1 := by
  have normalizerCentralizerIn_le (M T V : Subgroup G) : normalizerCentralizerIn M T V ≤ M := by
    unfold normalizerCentralizerIn
    exact inf_le_left
  have frattini_surjective {M T V : Subgroup G} (hc : Context G M T)
      (hV : V ∈ normalElemAbelian2 M) [(centralizerInSubgroup M V).Normal] :
      Function.Surjective
        ((QuotientGroup.mk' (centralizerInSubgroup M V)).comp
          (Subgroup.inclusion (normalizerCentralizerIn_le M T V))) := by
    classical
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, -, -, hMn⟩ := hV
    have hTM : T ≤ M := hc.sylow.le
    have key : ∀ g ∈ M, ∀ x ∈ M ⊓ Subgroup.centralizer (V : Set G),
        g * x * g⁻¹ ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
      intro g hg x hx
      refine ⟨M.mul_mem (M.mul_mem hg hx.1) (M.inv_mem hg), ?_⟩
      show _ ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hMn (M.inv_mem hg))) v
        simpa using this.mp hv
      have h2 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
      calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
        _ = g * x * g⁻¹ * v := by group
    have hMC : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact ⟨fun hx => key g hg x hx, fun hx => by
        simpa [mul_assoc] using key g⁻¹ (M.inv_mem hg) _ hx⟩
    have hS : IsSylowOf 2 (T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)))
        (M ⊓ Subgroup.centralizer (V : Set G)) :=
      hc.sylow.inf_of_le_normalizer inf_le_left hMC
    have hSeq : T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) = T ⊓ Subgroup.centralizer (V : Set G) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hTM h.1, h.2⟩⟩
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨g, hgM⟩ := g
      have hS' : IsSylowOf 2 ((T ⊓ (M ⊓ Subgroup.centralizer (V : Set G))).map
          (MulAut.conj g).toMonoidHom) (M ⊓ Subgroup.centralizer (V : Set G)) := by
        refine isSylowOf_of_card ?_ ?_
        · rintro x ⟨s, hs, rfl⟩
          simpa [MulAut.conj_apply] using key g hgM s hs.2
        · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
          exact IsSylowOf.card_eq hS
      obtain ⟨k, hk, hkiff⟩ := IsSylowOf.exists_mem_conj hS hS'
      have hkM : k ∈ M := hk.1
      have hmM : k⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hkM) hgM
      have hmN : k⁻¹ * g ∈ normalizerCentralizerIn M T V := by
        unfold normalizerCentralizerIn
        refine ⟨hmM, ?_⟩
        rw [← hSeq]
        show k⁻¹ * g ∈ Subgroup.normalizer _
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have e : (k⁻¹ * g) * h * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * h * g⁻¹) * k := by group
        rw [e]
        constructor
        · intro hh
          exact (hkiff _).mp ⟨h, hh, by simp [MulAut.conj_apply]⟩
        · intro hh
          obtain ⟨s, hs, hsh⟩ := (hkiff _).mpr hh
          have : s = h := by simpa [MulAut.conj_apply] using hsh
          exact this ▸ hs
      refine ⟨⟨k⁻¹ * g, hmN⟩, ?_⟩
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      rw [centralizerInSubgroup, Subgroup.mem_subgroupOf]
      have : g⁻¹ * k * g ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
        have := key g⁻¹ (M.inv_mem hgM) k hk
        simpa [mul_assoc] using this
      show (k⁻¹ * g)⁻¹ * g ∈ Subgroup.centralizer (V : Set G)
      simpa using this.2
  obtain ⟨hpp, hp2, -⟩ := CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank.sigma_prime_rank hp
  refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective hpp hp2 ?_ _
    (frattini_surjective hc hV)
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact h

end CFSG.LocalAnalysis.RankThreeUC.Section12.NonTIFrattiniQuotient
