module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRSyl
public import CFSG.ClassicalInvolution.Asc77.AscT7CHyp
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_2_t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∃ t' ∈ (S : Subgroup G), (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R'

@[expose] def C25_17_idx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') ∨
        Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')

theorem c25_2_t_of (h : C25_2 p f) : C25_2_t p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨t', ht', hg, hconj, -, -⟩ := h G Ω K K' W S R R' z t u₁ u₂ hyp
  exact ⟨t', ht', hg, hconj⟩

theorem c25_17_idx_of (h : C25_17 p f) : C25_17_idx p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  exact (h G Ω K K' W S R R' z t u₁ u₂ hyp).2.2

namespace T7DR

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem tf4_of_index_two [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ t' : G} (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    (h2 : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R')) (ht' : t' ∈ (S : Subgroup G))
    (hg : ∃ g : G, g * z * g⁻¹ = t') (hconj : conjSub t' R = R') :
    TwoSubgroupsFourGenerated G := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' hRsyl.1
    hR'syl.1 (S.isPGroup'.to_le (sup_le hRS hR'S))
  have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1
  obtain ⟨a, b, haR, hbR, hclos, hbab, k, hk⟩ := exists_gens_of_isQuatSub hquat
  have hR8 : 8 ≤ Nat.card ↥R := hquat.eight_le
  have hRR' : R ≠ R' := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK hK' hKK'.symm hRsyl.2.1 hRsyl.1 (by rw [h]; exact hR'syl.1)
    omega
  obtain ⟨g, hg'⟩ := hg
  have ht2 : t' * t' = 1 := by
    rw [← hg']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    rw [← hconj]
    exact conj_mem_conjSub haR
  have h5 : a * (t' * a * t'⁻¹) = (t' * a * t'⁻¹) * a := hc a haR _ ha'R'
  have h6 : b * (t' * a * t'⁻¹) = (t' * a * t'⁻¹) * b := hc b hbR _ ha'R'
  have haT : a ∈ (S : Subgroup G) := hRS haR
  have hbT : b ∈ (S : Subgroup G) := hRS hbR
  set U : Subgroup G := Subgroup.closure ({a, b, t'} : Set G) with hU
  have hUT : U ≤ (S : Subgroup G) := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact haT
    · exact hbT
    · exact ht'
  have hRU : R ≤ U := by
    rw [← hclos]
    exact Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.mpr
      (Set.mem_insert _ _)))
  have ht'U : t' ∈ U := Subgroup.subset_closure (by simp)
  have hR'U : R' ≤ U := by
    intro x hx
    have hx' : x ∈ conjSub t' R := by rw [hconj]; exact hx
    rw [mem_conjSub_iff] at hx'
    have h1 : t'⁻¹ * x * t' ∈ U := hRU hx'
    have : x = t' * (t'⁻¹ * x * t') * t'⁻¹ := by group
    rw [this]
    exact U.mul_mem (U.mul_mem ht'U h1) (U.inv_mem ht'U)
  have hNU : R ⊔ R' ≤ U := sup_le hRU hR'U
  have ht'N : t' ∉ R ⊔ R' := by
    intro htN
    have hnorm : R ⊔ R' ≤ Subgroup.normalizer (R : Set G) := by
      refine sup_le Subgroup.le_normalizer ?_
      intro x hx
      exact Subgroup.mem_normalizer_fintype (fun n hn => by
        have h1 : n * x = x * n := hc n hn x hx
        have hxn : x * n * x⁻¹ = n := by
          calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [h1]
            _ = n := by group
        rw [hxn]
        exact hn)
    have : conjSub t' R = R := mem_normalizer_iff_conjSub_eq.mp (hnorm htN)
    exact hRR' (this.symm.trans hconj)
  have hNpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hltNU : Nat.card ↥(R ⊔ R') < Nat.card ↥U := by
    by_contra hge
    push Not at hge
    exact ht'N ((Subgroup.eq_of_le_of_card_ge hNU hge) ▸ ht'U)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hNU
  have hdvd2 : Nat.card ↥U ∣ Nat.card ↥(S : Subgroup G) := Subgroup.card_dvd_of_le hUT
  rw [h2, hm, mul_comm 2] at hdvd2
  have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hNpos hdvd2
  have hm2' : m = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h | h
    · rw [h, mul_one] at hm
      omega
    · exact h
  have hUS : U = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hUT (by rw [h2, hm, hm2']; omega)
  refine twoSubgroupsFourGenerated_of_sylow S fun H hH => ?_
  exact genLE_four_of_omega5_sub haT hbT ht' hUS hbab ⟨(k : ℤ), by simpa using hk⟩ ht2 h5 h6 hH

end T7DR

theorem c25_19_of_sylow (h2 : C25_2_t p f) (h17 : C25_17_idx p f) : C25_19 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  by_cases h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
  · exact Or.inl h4
  · refine Or.inr (Or.inr ?_)
    have hidx : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') := by
      rcases h17 G Ω K K' W S R R' z t u₁ u₂ hyp with h | h
      · exact h
      · exact absurd h h4
    obtain ⟨t', ht'S, hg, hconj⟩ := h2 G Ω K K' W S R R' z t u₁ u₂ hyp
    exact T7DR.tf4_of_index_two hyp hidx ht'S hg hconj

end CFSG.ClassicalInvolution.Asc77
