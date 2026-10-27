module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveHSide
import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_three_threeCycles {n : ℕ} (hn : 9 ≤ n) :
    ∃ c : Fin 3 → alternatingGroup (Fin n),
      (∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle) ∧
      ∀ i j, i ≠ j →
        Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support := by
  classical
  let t : Fin 3 → Finset (Fin n) := fun i =>
    {⟨3 * i.1, by have := i.2; omega⟩, ⟨3 * i.1 + 1, by have := i.2; omega⟩,
      ⟨3 * i.1 + 2, by have := i.2; omega⟩}
  have ht : ∀ i, (t i).card = 3 := fun i =>
    Finset.card_eq_three.mpr ⟨_, _, _, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], rfl⟩
  choose x hx hxs using fun i =>
    CFSG.AlternatingAutomorphism.exists_isThreeCycle_support_eq (ht i)
  refine ⟨fun i => ⟨x i, (hx i).mem_alternatingGroup⟩, hx, fun i j hij => ?_⟩
  change Disjoint (x i).support (x j).support
  rw [hxs, hxs, Finset.disjoint_left]
  intro a hai haj
  have hij' : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  simp only [t, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hai haj
  omega

theorem le_pRank_of_alt_le_range {W Y : Type*} [Group W] [Finite W] [Group Y] (f : W →* Y)
    {n : ℕ} (hn : 9 ≤ n) (J : Subgroup Y) (hJ : J ≤ f.range)
    (e : J ≃* alternatingGroup (Fin n)) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup W) ∧
      (3 ∣ Nat.card f.ker → 4 ≤ Open.pRank 3 (⊤ : Subgroup W)) := by
  obtain ⟨c, hc, hdisj⟩ := exists_three_threeCycles hn
  let φ : W ⧸ f.ker ≃* f.range := QuotientGroup.quotientKerEquivRange f
  let J' : Subgroup (W ⧸ f.ker) := (J.subgroupOf f.range).map φ.symm.toMonoidHom
  have e' : J' ≃* alternatingGroup (Fin n) :=
    ((J.subgroupOf f.range).equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hJ).trans e)
  exact le_pRank_of_alt_section hn J' e' c hc hdisj

theorem IsElemAbelian.subgroupOf {X : Type*} [Group X] {p : ℕ} {E : Subgroup X}
    (hE : IsElemAbelian p E) (K : Subgroup X) : IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

@[expose] def D2GuestThreeDatum (L : Type*) [Group L] [Finite L] (p : ℕ) : Prop :=
  ¬ p ∣ Nat.card (Outer L) ∧ 4 ≤ Open.pRank 3 (⊤ : Subgroup L) ∧
    (∃ (n : ℕ) (J : Subgroup L), 9 ≤ n ∧ Nonempty (J ≃* alternatingGroup (Fin n))) ∧
    ∀ A : Subgroup L, IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ (n : ℕ) (J : Subgroup L), 9 ≤ n ∧ Nonempty (J ≃* alternatingGroup (Fin n)) ∧
        J ≤ ⨆ (Y : Subgroup L) (_ : Y ≤ A) (_ : Y ≠ ⊥), Subgroup.normalizer (Y : Set L)

theorem d2IndexCaseAt_of_guestThree {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) → ∀ p, Pp p →
      p ≠ 3 ∧ D2GuestThreeDatum L p) : D2IndexCaseAt i Pp := by
  intro G _ _ hglob hD1 p hpc P M A H R hesc _ hβ Rbar K _ hK he
  obtain ⟨-, hout, hK4, ⟨n₁, J₁, hn₁, ⟨e₁⟩⟩, hloc⟩ := h K he p hpc
  have : Fact p.Prime := ⟨hK.prime⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h31 : 1 < 3 := by norm_num
  set N : Subgroup H := primeComplementCore (G := H) p with hN
  set Abar : Subgroup (H ⧸ N) := (A.subgroupOf H).map (QuotientGroup.mk' N) with hAbar
  set X₀ : Subgroup (H ⧸ N) := ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N) with hX₀
  have hH4 : 4 ≤ Open.pRank 3 H := by
    rw [SectionRank.pRank_eq_pRank_top_subgroup H]
    have hsec := le_pRank_of_alt_le_range (QuotientGroup.mk' N) hn₁ (J₁.map K.subtype)
      (by rw [QuotientGroup.range_mk']; exact le_top)
      ((J₁.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e₁)
    by_cases h3N : 3 ∣ Nat.card N
    · exact hsec.2 (by rwa [QuotientGroup.ker_mk'])
    · have heq := pRank_quotient_map_of_coprime_normal 3 Nat.prime_three N h3N ⊤
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at heq
      rw [← heq]
      have hKX : Open.pRank 3 (⊤ : Subgroup K) ≤ Open.pRank 3 (⊤ : Subgroup (H ⧸ N)) := by
        rw [← SectionRank.pRank_eq_pRank_top_subgroup K]
        exact SectionRank.pRank_mono h31 le_top
      omega
  have h3 : 3 ∈ GLBBetaFour G :=
    ⟨Nat.prime_three, by norm_num,
      prime_dvd_card_of_positive_rank 3 Nat.prime_three H (by omega),
      hH4.trans (le_csSup (twoLocalRank_bddAbove 3 Nat.prime_three) ⟨H, hesc.maxTwoLocal_H.1, rfl⟩)⟩
  have hAK : Abar ≤ K := hK.A_le.trans (hK.sylow_le_of_not_dvd_card_outer hout)
  have hAKel : IsElemAbelian p (Abar.subgroupOf K) := IsElemAbelian.subgroupOf hK.elem K
  have hAKcard : Nat.card (Abar.subgroupOf K) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hK.card_A
  obtain ⟨n₂, J₂, hn₂, ⟨e₂⟩, hJ₂⟩ := hloc _ hAKel hAKcard
  have hJ₂X : J₂.map K.subtype ≤ X₀ := by
    rw [Subgroup.map_le_iff_le_comap]
    refine hJ₂.trans (iSup_le fun Y => iSup_le fun hY => iSup_le fun hYne => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    refine (Subgroup.le_normalizer_map K.subtype).trans (hK.normalizer_le_of_le_A _ ?_ ?_)
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      exact hY hy
    · intro hbot
      apply hYne
      rw [eq_bot_iff]
      intro y hy
      have hy' : (y : H ⧸ N) ∈ Y.map K.subtype := ⟨y, hy, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hy'
      exact Subgroup.mem_bot.mpr (Subtype.ext hy')
  have hHM3 : 3 ≤ Open.pRank 3 (H ⊓ M) := by
    rw [SectionRank.pRank_eq_pRank_top_subgroup (H ⊓ M)]
    let f : ↥(H ⊓ M) →* H ⧸ N :=
      (QuotientGroup.mk' N).comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H))
    have hrange : f.range = X₀ := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact (le_pRank_of_alt_le_range f hn₂ (J₂.map K.subtype) (hrange ▸ hJ₂X)
      ((J₂.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e₂)).1
  exact hesc.false_of_three_le_pRank_both hglob.toAGLGlobal.pre hβ h3 (hD1 3 h3)
    (by omega) (hHM3.trans (SectionRank.pRank_mono h31 inf_le_right))

@[expose] def KFactFi22GuestThree : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) →
    D2GuestThreeDatum L 5

theorem d2IndexCaseAt_fi22_five (h : KFactFi22GuestThree) :
    D2IndexCaseAt (.sporadic .Fi22) fun p => p = 5 :=
  d2IndexCaseAt_of_guestThree fun L _ _ he p hp => ⟨by omega, hp ▸ h L he⟩

end CFSG.AGLEmbeddingD2
