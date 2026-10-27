module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBQLevi
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcBQComp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity CFSG.LieType.TitsSimplicity.Levi
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

theorem leviSubAt_of_borelQuotient {Y : Type} [Group Y] [Finite Y] [Finite K] {π : K →* Y}
    {M : ℕ} (h : BorelQuotient D n H π M) (hdiv : D.divisible = ∅) (hBU : BruhatExtras D H)
    (hE : RootGroupCommutators D)
    (hcomm : ∀ i j, i ≠ j → D.cartan i j = 0 → ∀ u ∈ rankOne D.rootGroup i,
      ∀ v ∈ rankOne D.rootGroup j, u * v = v * u)
    (hM : ∀ p, p.Prime → 5 ≤ p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 1 → ¬ p ∣ M)
    (hperf : ∀ C : Finset (Fin D.rank), C.Nonempty → C ≠ Finset.univ →
      IsIndecomposable (D.cartan.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)) →
      ∀ p, p.Prime → 5 ≤ p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 1 →
        p ∣ Nat.card (levi D.rootGroup C) → Group.IsPerfect ↥(levi D.rootGroup C))
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hf5 : f < 5)
    (hfr : 2 ≤ CFSG.Open.pRank f (⊤ : Subgroup Y))
    (hfC : ∀ i, f ∣ Nat.card (rankOne D.rootGroup i))
    (hZ : ∀ i, center ↥(rankOne D.rootGroup i) = ⊥) :
    LeviSubAt Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent D).map π).index := fun hd =>
    h.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ h.surj))
  refine leviSubAt_of_standard_sylow ((hU2.map π).toSylow hidx) fun K₀ p hN => ?_
  intro _ hp h5 hrank _ hne hsyl
  rw [IsPGroup.toSylow_coe, h.normalizer_map_posUnipotent] at hN
  have hBA : borel D H ≤ K₀.comap π := fun b hb => hN ⟨b, hb, rfl⟩
  obtain ⟨I, -, hLA, hAle⟩ := exists_levi_decomposition hdiv h.ct h.extras hBA
  have hK₀A : Nat.card K₀ ∣ Nat.card (K₀.comap π) := by
    have := Subgroup.card_map_dvd (H := K₀.comap π) π
    rwa [Subgroup.map_comap_eq_self_of_surjective h.surj] at this
  have hpR : ¬ p ∣ Nat.card (radicalOff D I) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_radicalOff hU2 I)
    rw [hk]
    intro hd
    have := Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow hd)
    omega
  have hpT : ¬ p ∣ Nat.card (⨆ i, H i : Subgroup K) := not_dvd_card_torus h hp (hM p hp h5 hrank)
  have hpI : p ∣ Nat.card (levi D.rootGroup I) := by
    have h1 := ((dvd_card_of_sylow_hyp hp hsyl).trans hK₀A).trans
      (card_dvd_of_le_radicalOff_sup h.ct h.extras I hAle)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact absurd h2 hpR
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · exact absurd h3 hpT
    · exact h3
  obtain ⟨C, hCI, hCne, hind, hpC⟩ := exists_indecomposable_dvd_card_levi hcomm hp I hpI
  have hCuniv : C ≠ Finset.univ := by
    rintro rfl
    apply hne
    have hAtop : K₀.comap π = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [eq_borel_sup_rankOne h.ct h.extras (A := ⊤) le_top]
      exact sup_le hBA (iSup₂_le fun i _ =>
        (rankOne_le_levi D.rootGroup (hCI (Finset.mem_univ i))).trans hLA)
    rw [← Subgroup.map_comap_eq_self_of_surjective h.surj K₀, hAtop, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 h.surj
  haveI : Nontrivial ↥(levi D.rootGroup C) :=
    Finite.one_lt_card_iff_nontrivial.1 (lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpC))
  have hQ := isQuasisimple_levi hdiv h.ct h.extras hBU hE C hind
    (hperf C hCne hCuniv hind p hp h5 hrank hpC)
  have hpZ : ¬ p ∣ Nat.card (center ↥(levi D.rootGroup C)) := by
    intro hd
    apply hpT
    refine hd.trans ?_
    rw [← Subgroup.card_map_of_injective (levi D.rootGroup C).subtype_injective]
    exact Subgroup.card_dvd_of_le (center_levi_le hdiv h.ct h.extras hBU hE C)
  obtain ⟨W, hsec, hidxW, hWZ⟩ :=
    exists_simpleSection_map π (fun z hz => h.ker_central z hz) (levi D.rootGroup C) hQ
  have hYK₀ : (levi D.rootGroup C).map π ≤ K₀ :=
    Subgroup.map_le_iff_le_comap.2 ((levi_mono D.rootGroup hCI).trans hLA)
  have hpQ : p ∣ Nat.card (↥(levi D.rootGroup C) ⧸ center ↥(levi D.rootGroup C)) := by
    have hpC' := hpC
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(levi D.rootGroup C))] at hpC'
    rcases (Nat.Prime.dvd_mul hp).1 hpC' with h1 | h1
    · exact h1
    · exact absurd h1 hpZ
  obtain ⟨i, hi⟩ := hCne
  refine ⟨f, (levi D.rootGroup C).map π, W, hf, hf2, by omega, hfr, hYK₀, hsec, ?_, ?_, ?_⟩
  · rw [hidxW]
    exact dvd_card_quotient_center_levi hi (hZ i) (hfC i)
  · rw [hidxW]
    exact hpQ
  · exact fun hd => hpZ (hd.trans hWZ)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.BQ
