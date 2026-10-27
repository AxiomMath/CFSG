module

public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_one (S : Subgroup G) : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun g => by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one,
        MonoidHom.id_apply]
  rw [h1, Subgroup.map_id]

theorem exists_mem_map_conj_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {A B Y : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf p A Y) (hB : CFSG.ABGLocalTools.IsSylowOf p B Y) :
    ∃ m ∈ Y, A.map (MulAut.conj m).toMonoidHom = B := by
  obtain ⟨QA, rfl⟩ := hA
  obtain ⟨QB, rfl⟩ := hB
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq Y QA QB
  refine ⟨m, m.2, ?_⟩
  rw [← hm, sylow_conjugate_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_conj_mem_of_isSylowOf {p : ℕ} [Fact p.Prime] {M T S : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hS : IsPGroup p S) (hSM : S ≤ M) :
    ∃ g ∈ M, ∀ s ∈ S, g * s * g⁻¹ ∈ T := by
  obtain ⟨T', rfl⟩ := hT
  obtain ⟨P, hP⟩ := (hS.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P T'
  refine ⟨g, g.2, fun s hs => ?_⟩
  have h2 : (MulAut.conj g) ⟨s, hSM hs⟩ ∈ ((g • P : Sylow p M) : Subgroup M) := by
    rw [sylow_conjugate_eq_map]
    exact Subgroup.mem_map_of_mem _ (hP hs)
  rw [hg] at h2
  exact ⟨_, h2, rfl⟩

theorem le_sup_inf_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {H Y S : Subgroup G}
    (hYH : Y ≤ H) (hn : H ≤ normalizer (Y : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) : H ≤ Y ⊔ (H ⊓ normalizer (S : Set G)) := by
  intro x hx
  have hxY : x ∈ normalizer (Y : Set G) := hn hx
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj x).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (mem_normalizer_iff.1 hxY s).1 (hS.le hs)
    · rw [card_map_of_injective (MulAut.conj x).injective, hS.card_eq]
  obtain ⟨k, hk, hkS⟩ := exists_mem_map_conj_eq_of_isSylowOf hS hS'
  have hkx : k⁻¹ * x ∈ normalizer (S : Set G) := by
    have hSkx : S.map (MulAut.conj (k⁻¹ * x)).toMonoidHom = S := by
      rw [← conjugate_map_mul S k⁻¹ x, ← hkS, conjugate_map_mul S k⁻¹ k, inv_mul_cancel,
        map_conj_one]
    exact mem_normalizer_iff_map_conj_eq.mpr hSkx
  rw [show x = k * (k⁻¹ * x) by group]
  exact mul_mem_sup hk ⟨H.mul_mem (H.inv_mem (hYH hk)) hx, hkx⟩

theorem IsWitnessGen.exists_le_conj_of_two_le_pRank
    (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G) {p : ℕ} {P : Sylow p G}
    (hp : IsWitnessPrime p P) {M : Subgroup G} (hw : IsWitnessGen p P M)
    {H : Subgroup G} (hH : IsTwoLocal H) (h2 : 2 ≤ CFSG.Open.pRank p H) :
    ∃ g : G, H ≤ M.map (MulAut.conj g).toMonoidHom := by
  have hprime := hp.prime
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨E, hEH, hE, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨P', hEP'⟩ := (elementary_isPGroup p E hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hEg : ∀ e ∈ E, (MulAut.conj g⁻¹).toMonoidHom e ∈ (P : Subgroup G) := by
    intro e he
    have he' : e ∈ ((g • P : Sylow p G) : Subgroup G) := by
      rw [hg]
      exact hEP' he
    rw [sylow_conjugate_eq_map] at he'
    obtain ⟨q, hq, rfl⟩ := he'
    have hqq : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom q) = q := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hqq]
    exact hq
  have hE'M : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ H.map (MulAut.conj g⁻¹).toMonoidHom ⊓ M := by
    refine le_inf (map_mono hEH) ?_
    rintro _ ⟨e, he, rfl⟩
    exact hw.sylow_le hp (hEg e he)
  have hE'rank : 2 ≤ CFSG.Open.pRank p (E.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rw [pRank_map_automorphism p hprime.one_lt E]
    have := CFSG.SectionRank.le_pRank hprime.one_lt (le_refl E) hE hEc
    omega
  have hH'M : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ M :=
    hw.u2 _ (twoLocal_map_automorphism H hH _) (hE'rank.trans (pRank_mono p hprime.one_lt hE'M))
  refine ⟨g, fun x hx => ⟨(MulAut.conj g⁻¹) x, hH'M ⟨x, hx, rfl⟩, ?_⟩⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem IsWitness.exists_le_conj_of_two_le_pRank (hS : Standing G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hw : IsWitness p P M)
    {H : Subgroup G} (hH : IsTwoLocal H) (h2 : 2 ≤ CFSG.Open.pRank p H) :
    ∃ g : G, H ≤ M.map (MulAut.conj g).toMonoidHom :=
  IsWitnessGen.exists_le_conj_of_two_le_pRank hS.toGen
    (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen hH h2

theorem normalizer_le_of_normalizer_le_conj {M T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {g : G}
    (h : normalizer (T : Set G) ≤ M.map (MulAut.conj g).toMonoidHom) :
    normalizer (T : Set G) ≤ M := by
  have hT'M : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨m, hm, hmt⟩ := h (le_normalizer ht)
    have : (MulAut.conj g⁻¹).toMonoidHom t = m := by
      rw [← hmt]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [this]
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (T.map (MulAut.conj g⁻¹).toMonoidHom) M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hT'M ?_
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hT.card_eq]
  obtain ⟨m, hmM, hm⟩ := exists_mem_map_conj_eq_of_isSylowOf hT hT'
  have hgm : g * m ∈ normalizer (T : Set G) := by
    have hTgm : T.map (MulAut.conj (g * m)).toMonoidHom = T := by
      rw [← conjugate_map_mul T g m, hm, conjugate_map_mul T g g⁻¹, mul_inv_cancel, map_conj_one]
    exact mem_normalizer_iff_map_conj_eq.mpr hTgm
  obtain ⟨m', hm'M, hm'⟩ := h hgm
  have hgM : g ∈ M := by
    have h1 : m' * g⁻¹ = m := by
      have h2 : g * (m' * g⁻¹) = g * m := by
        simpa [MulAut.conj_apply, mul_assoc] using hm'
      exact mul_left_cancel h2
    have h3 : g⁻¹ = m'⁻¹ * m := by rw [← h1]; group
    have h4 : g⁻¹ ∈ M := h3 ▸ M.mul_mem (M.inv_mem hm'M) hmM
    simpa using M.inv_mem h4
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h hx
  exact M.mul_mem (M.mul_mem hgM hy) (M.inv_mem hgM)

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.normalizer_le_of_two_le_pRank_normalizer
    (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G) (hp : IsWitnessPrime p P)
    (hw : IsWitnessGen p P M) {T C : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hC1 : C ≠ ⊥) (hCT : C ≤ T) (hN : normalizer (T : Set G) ≤ normalizer (C : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank p (normalizer (C : Set G))) : normalizer (T : Set G) ≤ M := by
  obtain ⟨g, hg⟩ := IsWitnessGen.exists_le_conj_of_two_le_pRank hS hp hw
    ⟨C, hC1, hT.isPGroup.to_le hCT, rfl⟩ h2
  exact normalizer_le_of_normalizer_le_conj hT (hN.trans hg)

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
