module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_mem_USet_le [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) : ∃ U ∈ USet Ω, U ≤ J := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨U, hUR, hc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hc hcard, hUR.trans hRJ.1⟩

theorem dstarAdj_of_commutes [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hJ : J ∈ Ω) (hne : J ≠ K) (hc : Commutes J K) : dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := exists_mem_USet_le hp hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes (hUJ hu) hc)⟩⟩

theorem dstarAdj_of_le_normalizer [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hJ : J ∈ Ω) (hne : J ≠ K) (hN : J ≤ Subgroup.normalizer (K : Set G)) :
    dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := exists_mem_USet_le hp hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu => hN (hUJ hu)⟩⟩

theorem dichotomy_of_thm4 [Finite G] {n : ℕ} (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h4 : Thm4Below p f n)
    (hlt : Nat.card G < n) (hΩ : HypOmegaMod p f Ω) (hO : classicalInvolutionOddCore G = ⊥)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) {L : Subgroup G} (hL : L ∈ Ω) :
    (∀ M ∈ Ω, M ∈ dstarComp Ω L) ∨ (∀ M ∈ Ω, ∃ y : G, conjSub y L = M) := by
  by_cases hall : ∀ M ∈ Ω, ∃ y : G, conjSub y L = M
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨M₀, hM₀, hM₀c⟩ := hall
  have hLM₀ : M₀ ≠ L := fun h => hM₀c 1 (by rw [conjSub_one, h])
  have hc0 : Commutes L M₀ := h4 hp hq G hlt Ω hΩ hO hA L hL M₀ hM₀ (fun ⟨g, hg⟩ => hM₀c g hg)
  have hadj0 : dstarAdj Ω L M₀ := dstarAdj_of_commutes hp hΩ hM₀ hLM₀ hc0.symm
  intro M hM
  by_cases hMc : ∃ y : G, conjSub y L = M
  · obtain ⟨y, rfl⟩ := hMc
    have hnot : ¬ ∃ g : G, conjSub g (conjSub y L) = M₀ := by
      rintro ⟨g, hg⟩
      exact hM₀c (g * y) (by rw [conjSub_mul]; exact hg)
    have hc1 : Commutes (conjSub y L) M₀ :=
      h4 hp hq G hlt Ω hΩ hO hA _ hM M₀ hM₀ hnot
    have hne : M₀ ≠ conjSub y L := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj0)
      (dstarAdj_of_commutes hp hΩ hM hne.symm hc1)
  · have hc : Commutes L M := h4 hp hq G hlt Ω hΩ hO hA L hL M hM (fun ⟨g, hg⟩ => hMc ⟨g, hg⟩)
    have hne : M ≠ L := fun h => hMc ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.single (dstarAdj_of_commutes hp hΩ hM hne hc.symm)

section Lift

variable {N : Subgroup G} [N.Normal]

theorem exists_good_lift (good : Subgroup G → Prop) {K : Subgroup G} (hK : K ∈ Ω) (hgK : good K)
    (hstep : ∀ L ∈ Ω, ∀ L' ∈ Ω, good L →
      dstarAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N)) (L'.map (QuotientGroup.mk' N)) →
      ∃ L'' ∈ Ω, L''.map (QuotientGroup.mk' N) = L'.map (QuotientGroup.mk' N) ∧ good L'')
    {Mb : Subgroup (G ⧸ N)}
    (hMb : Mb ∈ dstarComp (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ M ∈ Ω, M.map (QuotientGroup.mk' N) = Mb ∧ good M := by
  induction hMb with
  | refl => exact ⟨K, hK, rfl, hgK⟩
  | tail _ hbc ih =>
    obtain ⟨M, hM, hMb, hgood⟩ := ih
    obtain ⟨L', hL', hL'eq⟩ := hbc.1
    have hL'eq' : L'.map (QuotientGroup.mk' N) = _ := hL'eq
    subst hMb hL'eq'
    obtain ⟨M'', hM'', hM''eq, hgood''⟩ := hstep M hM L' hL' hgood hbc
    exact ⟨M'', hM'', hM''eq, hgood''⟩

theorem E187C.good_lift_step_of (good : Subgroup G → Prop) (hc : ConjInvariant Ω)
    (hexn : ∀ {L L' : Subgroup G}, L ∈ Ω → L' ∈ Ω →
      L'.map (QuotientGroup.mk' N) ∈
        omegaStarNbr (quotFamily Ω N) (L.map (QuotientGroup.mk' N)) →
      ∃ n ∈ N, L' ∈ omegaStarNbr Ω (conjSub n L))
    (hgood : ∀ L ∈ Ω, ∀ L' ∈ Ω, good L → dstarAdj Ω L L' → good L') :
    ∀ L ∈ Ω, ∀ L' ∈ Ω, good L →
      dstarAdj (quotFamily Ω N) (L.map (QuotientGroup.mk' N)) (L'.map (QuotientGroup.mk' N)) →
      ∃ L'' ∈ Ω, L''.map (QuotientGroup.mk' N) = L'.map (QuotientGroup.mk' N) ∧ good L'' := by
  intro L hL L' hL' hgL hadj
  obtain ⟨-, hadj | hadj⟩ := hadj
  · obtain ⟨n, hn, hn'⟩ := hexn hL hL' hadj
    have h1 := omegaStarNbr_conj hc hn' (n⁻¹ : G)
    rw [conjSub_inv_conjSub] at h1
    have hnn : QuotientGroup.mk' N n⁻¹ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (N.inv_mem hn)
    refine ⟨conjSub n⁻¹ L', hc _ L' hL', ?_, ?_⟩
    · rw [AscQuot.map_conjSub, hnn, conjSub_one]
    · exact hgood L hL _ (hc _ L' hL') hgL ⟨hc _ L' hL', Or.inl h1⟩
  · obtain ⟨n, hn, hn'⟩ := hexn hL' hL hadj
    have hnn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    refine ⟨conjSub n L', hc _ L' hL', ?_, ?_⟩
    · rw [AscQuot.map_conjSub, hnn, conjSub_one]
    · exact hgood L hL _ (hc _ L' hL') hgL ⟨hc _ L' hL', Or.inr hn'⟩

end Lift

end CFSG.ClassicalInvolution.Asc77
