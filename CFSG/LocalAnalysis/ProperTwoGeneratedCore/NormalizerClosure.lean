module

public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NormalizerClosure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem gamma_eq_rankThreeGamma (S : Subgroup G) (k : ℕ) :
    properTwoGenCoreGamma S k = rankThreeGamma k 2 S := by
  apply le_antisymm
  · apply iSup_le
    intro Q
    apply iSup_le
    intro hQS
    apply iSup_le
    intro hrank
    exact gamma_normalizer_le k 2 S Q hQS hrank
  · apply sSup_le
    rintro N ⟨Q, hQS, hrank, rfl⟩
    exact le_iSup_of_le Q (le_iSup_of_le hQS (le_iSup_of_le hrank le_rfl))

theorem gamma_le_iff (S H : Subgroup G) (k : ℕ) :
    properTwoGenCoreGamma S k ≤ H ↔
      ∀ Q : Subgroup G, Q ≤ S → k ≤ pRank 2 Q →
        Subgroup.normalizer (Q : Set G) ≤ H := by
  rw [gamma_eq_rankThreeGamma]
  exact CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff k 2 S H

theorem gamma_antitone (S : Subgroup G) {k l : ℕ} (hkl : k ≤ l) :
    properTwoGenCoreGamma S l ≤ properTwoGenCoreGamma S k := by
  apply (gamma_le_iff S _ l).mpr
  intro Q hQS hrank
  exact (gamma_le_iff S _ k).mp le_rfl Q hQS (hkl.trans hrank)

theorem sylow_normalizer_le_gamma (S : Sylow 2 G) {k : ℕ}
    (hrank : k ≤ pRank 2 (S : Subgroup G)) :
    Subgroup.normalizer (S : Set G) ≤ properTwoGenCoreGamma (S : Subgroup G) k :=
  (gamma_le_iff _ _ k).mp le_rfl _ le_rfl hrank

theorem sylow_le_gamma (S : Sylow 2 G) {k : ℕ}
    (hrank : k ≤ pRank 2 (S : Subgroup G)) :
    (S : Subgroup G) ≤ properTwoGenCoreGamma (S : Subgroup G) k :=
  Subgroup.le_normalizer.trans (sylow_normalizer_le_gamma S hrank)

theorem normalizer_le_overgroup (S : Sylow 2 G) (H : Subgroup G) (k : ℕ)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) k ≤ H)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQH : Q ≤ H)
    (hrank : k ≤ pRank 2 Q) : Subgroup.normalizer (Q : Set G) ≤ H := by
  exact gamma_rank_normalizer_le_overgroup k 2 Nat.prime_two S H hSH
    ((gamma_eq_rankThreeGamma (S : Subgroup G) k) ▸ hcore) Q hQ hQH hrank

theorem pGroup_le_of_large_intersection (S : Sylow 2 G) (H : Subgroup G) (k : ℕ)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) k ≤ H)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hrank : k ≤ pRank 2 (Q ⊓ H)) : Q ≤ H := by
  exact gamma_pGroup_le_of_large_intersection k 2 Nat.prime_two S H hSH
    ((gamma_eq_rankThreeGamma (S : Subgroup G) k) ▸ hcore) Q hQ hrank

theorem transporter_mem (S : Sylow 2 G) (H : Subgroup G) (k : ℕ)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) k ≤ H)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQH : Q ≤ H)
    (hrank : k ≤ pRank 2 Q) (g : G) (hg : Q.conjBy g⁻¹ ≤ H) : g ∈ H := by
  have hinverse := normalizer_closure_transporter_mem k 2 Nat.prime_two H
    (normalizer_le_overgroup S H k hSH hcore) Q hQ hQH hrank g⁻¹ hg
  exact H.inv_mem_iff.mp hinverse

theorem conjugate_intersection_rank_lt (S : Sylow 2 G) (H : Subgroup G) {k : ℕ}
    (hk : 0 < k) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) k ≤ H)
    (g : G) (hg : g ∉ H) : pRank 2 (H ⊓ H.conjBy g⁻¹) < k := by
  exact gamma_conjugate_intersection_rank_lt k 2 Nat.prime_two hk S H hSH
    ((gamma_eq_rankThreeGamma (S : Subgroup G) k) ▸ hcore) g⁻¹
    (fun hginv => hg (H.inv_mem_iff.mp hginv))

theorem gamma_le_iff_conjugate_intersection_rank_lt
    (S : Sylow 2 G) (H : Subgroup G) {k : ℕ} (hk : 0 < k)
    (hSH : (S : Subgroup G) ≤ H) :
    properTwoGenCoreGamma (S : Subgroup G) k ≤ H ↔
      ∀ g : G, g ∉ H → pRank 2 (H ⊓ H.conjBy g⁻¹) < k := by
  constructor
  · intro hcore g hg
    exact conjugate_intersection_rank_lt S H hk hSH hcore g hg
  · intro hintersection
    apply (gamma_le_iff _ H k).mpr
    intro Q hQS hrank g hg
    by_contra hgH
    have hQH : Q ≤ H := hQS.trans hSH
    have hQconj : Q ≤ H.conjBy g⁻¹ := by
      have hfixed := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (Q : Set G)).inv_mem hg)
      change Q ≤ H.map (MulAut.conj g⁻¹).toMonoidHom
      rw [← hfixed]
      exact Subgroup.map_mono hQH
    have hlarge := hrank.trans (pRank_mono 2 (by decide) (le_inf hQH hQconj))
    exact (not_lt_of_ge hlarge) (hintersection g hgH)

theorem two_generated_core_le_iff_intersection_rank_le_one
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H) :
    properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H ↔
      ∀ g : G, g ∉ H → pRank 2 (H ⊓ H.conjBy g⁻¹) ≤ 1 := by
  rw [gamma_le_iff_conjugate_intersection_rank_lt S H (by decide) hSH]
  simp only [Nat.lt_succ_iff]

end CFSG.ProperTwoGeneratedCore
