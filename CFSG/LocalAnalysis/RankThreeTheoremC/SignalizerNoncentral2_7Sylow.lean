module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Rank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement
public import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}
  (hc : NoncentralConfig G p P M D U u)

include hc

theorem R_le_centralizer : R P U ≤ centralizer ({u} : Set G) :=
  inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hc.uU))

theorem PR' : (P : Subgroup G) ≤ normalizer ((R P U : Subgroup G) : Set G) := by
  have := hc.PR
  rwa [hc.inf_centralizer_eq] at this

theorem card_index' : Nat.card (P : Subgroup G) = p * Nat.card (R P U) := by
  have := hc.card_index
  rwa [hc.inf_centralizer_eq] at this

theorem sylow_or_fused : IsSylowOf p (R P U) (centralizer ({u} : Set G)) ∨
    ∃ g ∈ M, g * u * g⁻¹ ∈ (center D).map D.subtype := by
  classical
  by_cases hsyl : IsSylowOf p (R P U) (centralizer ({u} : Set G))
  · exact Or.inl hsyl
  right
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  set C : Subgroup G := centralizer ({u} : Set G) with hCdef
  have hRC : R P U ≤ C := hc.R_le_centralizer
  have hRp : IsPGroup p (R P U) := P.isPGroup'.to_le inf_le_left
  obtain ⟨T, hT⟩ := (hRp.comap_subtype (K := C)).exists_le_sylow
  set R' : Subgroup G := (T : Subgroup C).map C.subtype with hR'def
  have hR'syl : IsSylowOf p R' C := ⟨T, rfl⟩
  have hRR' : R P U ≤ R' := fun y hy => ⟨⟨y, hRC hy⟩, hT hy, rfl⟩
  have hne : R P U ≠ R' := fun h => hsyl (h ▸ hR'syl)
  have hlt : R P U < R' := lt_of_le_of_ne hRR' hne
  have hgrow : R P U < R' ⊓ normalizer ((R P U : Subgroup G) : Set G) :=
    pGroup_proper_subgroup_lt_internal_normalizer p hprime R' (R P U) hR'syl.isPGroup hlt
  set N : Subgroup G := normalizer ((R P U : Subgroup G) : Set G) with hNdef
  set S₁ : Subgroup G := R' ⊓ N with hS₁def
  have hS₁p : IsPGroup p S₁ := hR'syl.isPGroup.to_inf_left
  obtain ⟨T₂, hT₂⟩ := (hS₁p.comap_subtype (K := N)).exists_le_sylow
  set P₂ : Subgroup G := (T₂ : Subgroup N).map N.subtype with hP₂def
  have hP₂syl : IsSylowOf p P₂ N := ⟨T₂, rfl⟩
  have hS₁P₂ : S₁ ≤ P₂ := fun y hy => ⟨⟨y, (hy : y ∈ R' ⊓ N).2⟩, hT₂ hy, rfl⟩
  have hPN : (P : Subgroup G) ≤ N := hc.PR'
  have hPsyl : IsSylowOf p (P : Subgroup G) N :=
    ⟨P.subtype hPN, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPN]⟩
  have hcardP₂ : Nat.card P₂ = Nat.card (P : Subgroup G) := by
    obtain ⟨T₁, hT₁⟩ := hPsyl
    have e1 := Sylow.card_eq_multiplicity T₂
    have e2 := Sylow.card_eq_multiplicity T₁
    have e3 : Nat.card T₁ = Nat.card T₂ := by rw [e1, e2]
    rw [hP₂def, ← hT₁, card_map_of_injective N.subtype_injective,
      card_map_of_injective N.subtype_injective]
    exact e3.symm
  have hRS₁ : R P U ≤ S₁ := le_inf hRR' le_normalizer
  have hlt_card : Nat.card (R P U) < Nat.card S₁ := Subgroup.card_lt_of_lt hgrow
  have hd1 : Nat.card (R P U) ∣ Nat.card S₁ := Subgroup.card_dvd_of_le hRS₁
  have hd2 : Nat.card S₁ ∣ Nat.card P₂ := Subgroup.card_dvd_of_le hS₁P₂
  have hRpos : 0 < Nat.card (R P U) := Nat.card_pos
  rw [hcardP₂, hc.card_index', mul_comm] at hd2
  have hS₁eq : Nat.card S₁ = Nat.card P₂ := by
    obtain ⟨t, ht⟩ := hd1
    rw [ht] at hd2 hlt_card
    have hlt2 : 1 < t := by
      by_contra h
      have : t ≤ 1 := by omega
      interval_cases t <;> simp_all
    have htdvd : t ∣ p := (Nat.mul_dvd_mul_iff_left hRpos).1 hd2
    have ht' : t = p := ((Nat.dvd_prime hprime).1 htdvd).resolve_left (by omega)
    rw [ht, ht', hcardP₂, hc.card_index', mul_comm]
  have hS₁P₂eq : S₁ = P₂ := Subgroup.eq_of_le_of_card_ge hS₁P₂ hS₁eq.ge
  have huP₂ : u ∈ P₂ := hS₁P₂eq ▸ hRS₁ (hc.u_mem_R)
  have hP₂C : P₂ ≤ C := hS₁P₂eq ▸ (inf_le_left.trans hR'syl.le)
  obtain ⟨k, hkN, hconj⟩ := hPsyl.exists_mem_conj hP₂syl
  have hwP : k⁻¹ * u * k ∈ (P : Subgroup G) := (hconj u).1 huP₂
  have hwc : k⁻¹ * u * k ∈ centralizer ((P : Subgroup G) : Set G) := by
    refine mem_centralizer_iff.mpr fun q hq => ?_
    have hy : k * q * k⁻¹ ∈ P₂ := (hconj _).2 (by
      have e : k⁻¹ * (k * q * k⁻¹) * k = q := by group
      rw [e]
      exact hq)
    have hyu : k * q * k⁻¹ * u = u * (k * q * k⁻¹) := mem_centralizer_singleton_iff.mp (hP₂C hy)
    calc q * (k⁻¹ * u * k) = k⁻¹ * (k * q * k⁻¹ * u) * k := by group
      _ = k⁻¹ * (u * (k * q * k⁻¹)) * k := by rw [hyu]
      _ = k⁻¹ * u * k * q := by group
  have hwp : (k⁻¹ * u * k) ^ p = 1 := by
    have h := conj_pow (α := G) (i := p) (a := k⁻¹) (b := u)
    simp only [inv_inv] at h
    rw [h, hc.pow_U hc.uU]
    group
  have hZ := hc.ext.mem_center_of_mem_centralizer_sylow hprime hc.odd hc.nonab hwP hwc hwp
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hc.setting hc.sigma hc.ext.obstruction.1).1
  have hkM : k ∈ M := by
    by_contra hk
    have hk' : k⁻¹ ∉ M := fun h => hk (by simpa using M.inv_mem h)
    have hrk := CFSG.PreuniquenessRankFour.Helpers.escaping_GLBConj_intersection_rank_le_two p
      hprime P hPM hc.ext.obstruction.1.2 (by rw [hc.pRank_P]) k⁻¹ hk'
    have hB : omegaOneOf p (R P U) ≤ M ⊓ GLBConj k⁻¹ M := by
      intro y hy
      have hyR : y ∈ R P U := B_le_R hy
      have hyP₂ : y ∈ P₂ := hS₁P₂eq ▸ hRS₁ hyR
      have hyP : k⁻¹ * y * k ∈ (P : Subgroup G) := (hconj y).1 hyP₂
      refine ⟨hPM (B_le_P hy), ?_⟩
      refine ⟨k⁻¹ * y * k, hPM hyP, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    have h3 : 3 ≤ CFSG.Open.pRank p (omegaOneOf p (R P U)) := by
      unfold CFSG.Open.pRank
      exact (Nat.le_refl 3).trans (le_csSup (pRank_set_bddAbove p hprime.one_lt _)
        ⟨_, le_rfl, hc.isElemAbelian_B, hc.card_B⟩)
    have := pRank_mono p hprime.one_lt hB
    omega
  exact ⟨k⁻¹, M.inv_mem hkM, by simpa using hZ⟩

end NoncentralConfig

end CFSG.LocalAnalysis.RankThreeTheoremC
