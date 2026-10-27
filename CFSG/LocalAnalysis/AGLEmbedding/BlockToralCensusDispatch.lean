module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

theorem isClassicalTwoOrG2_family_cases {X : Type} [Group X] (h : IsClassicalTwoOrG2 X) :
    IsLieOf IdxA X ∨ IsLieOf IdxTwistedA X ∨ IsLieOf IdxB X ∨ IsLieOf IdxD X ∨
      IsLieOf IdxTwistedD X ∨ IsLieOf IdxG2 X ∨ IsSmallTwoOrG2 X := by
  rcases h with ⟨⟨d, hv⟩, hd, he⟩ | h | h
  · cases d with
    | A r q => exact Or.inl ⟨⟨_, hv⟩, hd, he⟩
    | twistedA r q => exact Or.inr (Or.inl ⟨⟨_, hv⟩, hd, he⟩)
    | B r q => exact Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, he⟩))
    | D r q => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, he⟩)))
    | twistedD r q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, he⟩))))
    | G2 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, he⟩)))))
    | C r q => exact hd.elim
    | E6 q => exact hd.elim
    | E7 q => exact hd.elim
    | E8 q => exact hd.elim
    | F4 q => exact hd.elim
    | twistedE6 q => exact hd.elim
    | trialityD4 q => exact hd.elim
    | suzuki m => exact hd.elim
    | reeG2 m => exact hd.elim
    | reeF4 m => exact hd.elim
    | tits => exact hd.elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem FixThreeHyp.of_data (hG : GlueVhyp) {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    {u : Y} (h : FixThreeData L J u) : FixThreeHyp L J u := by
  obtain ⟨V, hV, hVL, hVO, huV⟩ := h.perfect
  exact ⟨h.parab, h.cyc, h.mem, h.pow, h.not_mem, hG Y L J h.parab V hV hVL hVO huV, h.fix⟩

theorem FixPrimeHyp.of_data (hG : GlueVhyp) {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    {p : ℕ} {u : Y} (h : FixPrimeData L J p u) : FixPrimeHyp L J p u := by
  obtain ⟨V, hV, hVL, hVO, huV⟩ := h.perfect
  exact ⟨h.parab, h.prime, h.five_le, h.cyc, h.mem, h.pow, h.not_mem,
    hG Y L J h.parab V hV hVL hVO huV, h.fix⟩

theorem kFactFixCensusThree_of_reduced (hG : GlueVhyp) (hA : FixThreeA)
    (h2A : FixThreeVoid (IsLieOf IdxTwistedA)) (hB : FixThreeVoid (IsLieOf IdxB))
    (hD : FixThreeVoid (IsLieOf IdxD)) (h2D : FixThreeVoid (IsLieOf IdxTwistedD))
    (hG2 : FixThreeVoid (IsLieOf IdxG2)) (hS : FixThreeVoid IsSmallTwoOrG2) :
    KFactFixCensusThree := by
  intro Y _ _ L J hCP hcyc u hu hu3 huC hV hfix
  have hd : FixThreeHyp L J u := FixThreeHyp.of_data hG ⟨hCP, hcyc, hu, hu3, huC, hV, hfix⟩
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  · exact hA Y L J u hd h
  · exact (h2A Y L J u hd h).elim
  · exact (hB Y L J u hd h).elim
  · exact (hD Y L J u hd h).elim
  · exact (h2D Y L J u hd h).elim
  · exact (hG2 Y L J u hd h).elim
  · exact (hS Y L J u hd h).elim

theorem fixCensusCenterVoid_rest (hZ : OddCenterRest) : FixCensusCenterVoid IsRestTwoOrG2 := by
  intro Y _ _ L J u hd h
  rcases hZ Y L hd.parab.comp hd.parab.odd h with h1 | h3
  · have h3 := hd.three_dvd
    rw [h1] at h3
    exact absurd h3 (by norm_num)
  · exact hd.not_threeASix h3

theorem kFactFixCensusCenter_of_families (hA : FixCensusCenterA)
    (h2A : FixCensusCenterVoid (IsLieOf IdxTwistedA)) (hZ : OddCenterRest) :
    KFactFixCensusCenter := by
  intro Y _ _ L J hCP hcyc h3 hA6 u hu hu3 huC hfix
  have hd : FixCenterData L J u := ⟨hCP, hcyc, h3, hA6, hu, hu3, huC, hfix⟩
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  · exact hA Y L J u hd h
  · exact (h2A Y L J u hd h).elim
  all_goals exact (fixCensusCenterVoid_rest hZ Y L J u hd (by unfold IsRestTwoOrG2; tauto)).elim

theorem not_dvd_card_center_rest (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (h : IsRestTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
  rcases hZ Y L hL hodd h with h1 | ⟨h3, -⟩
  · rw [h1]
    exact hp.not_dvd_one
  · rw [h3]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem kFactFixCensusPrime_of_reduced (hG : GlueVhyp) (hA : FixPrimeA)
    (h2A : FixPrimeTwistedA) (hB : FixPrimeCyc (IsLieOf IdxB))
    (hD : FixPrimeCyc (IsLieOf IdxD)) (h2D : FixPrimeCyc (IsLieOf IdxTwistedD))
    (hG2 : FixPrimeCyc (IsLieOf IdxG2)) (hS : FixPrimeCyc IsSmallTwoOrG2)
    (hZ : OddCenterRest) : KFactFixCensusPrime := by
  intro Y _ _ L J hCP p hp hp5 hcyc u hu hup huC hV hfix
  have hd : FixPrimeHyp L J p u :=
    FixPrimeHyp.of_data hG ⟨hCP, hp, hp5, hcyc, hu, hup, huC, hV, hfix⟩
  have hrest : IsRestTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    fun h => not_dvd_card_center_rest hZ hCP.comp hCP.odd h hp hp5
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  · exact hA Y L J p u hd h
  · exact ⟨(h2A Y L J p u hd h).1, Or.inl (h2A Y L J p u hd h).2⟩
  · exact ⟨hrest (Or.inl h), Or.inl (hB Y L J p u hd h)⟩
  · exact ⟨hrest (Or.inr (Or.inl h)), Or.inl (hD Y L J p u hd h)⟩
  · exact ⟨hrest (Or.inr (Or.inr (Or.inl h))), Or.inl (h2D Y L J p u hd h)⟩
  · exact ⟨hrest (Or.inr (Or.inr (Or.inr (Or.inl h)))), Or.inl (hG2 Y L J p u hd h)⟩
  · exact ⟨hrest (Or.inr (Or.inr (Or.inr (Or.inr h)))), Or.inl (hS Y L J p u hd h)⟩

theorem kFactFixCensusPerfThree_of_families (hA : FixPerfThreeVoid (IsLieOf IdxA))
    (h2A : FixPerfThreeVoid (IsLieOf IdxTwistedA)) (hB : FixPerfThreeVoid (IsLieOf IdxB))
    (hD : FixPerfThreeVoid (IsLieOf IdxD)) (h2D : FixPerfThreeVoid (IsLieOf IdxTwistedD))
    (hG2 : FixPerfThreeVoid (IsLieOf IdxG2)) (hS : FixPerfThreeSmall) :
    KFactFixCensusPerfThree := by
  intro Y _ _ L J u hd
  rcases isClassicalTwoOrG2_family_cases hd.parab.type with h | h | h | h | h | h | h
  · exact (hA Y L J u hd h).elim
  · exact (h2A Y L J u hd h).elim
  · exact (hB Y L J u hd h).elim
  · exact (hD Y L J u hd h).elim
  · exact (h2D Y L J u hd h).elim
  · exact (hG2 Y L J u hd h).elim
  · exact hS Y L J u hd h

theorem not_centPerfectNoncyc {Y : Type} [Group Y] {L J : Subgroup Y} {u : Y} {p : ℕ}
    (hcyc : CycPerfect p J) (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ¬ CentPerfectNoncyc p L u := by
  rintro ⟨V, hVC, hV, Q, hQV, hQ, hnc⟩
  refine hnc (hcyc V (fun v hv => hfix v (hVC hv).1 ?_) hV Q hQV hQ)
  have := Subgroup.mem_centralizer_iff.mp (hVC hv).2 u (Set.mem_singleton u)
  rw [this, mul_inv_cancel_right]

theorem fixThreeVoid_of_centNoncyc {𝔉 : (X : Type) → [Group X] → Prop}
    (h : KFactCentNoncycThree 𝔉) : FixThreeVoid 𝔉 := by
  intro Y _ _ L J u hd hF
  exact not_centPerfectNoncyc hd.cyc hd.fix
    (h Y L hd.parab.comp hd.parab.odd hF u hd.mem hd.pow hd.not_mem)

end CFSG.AGLEmbedding
