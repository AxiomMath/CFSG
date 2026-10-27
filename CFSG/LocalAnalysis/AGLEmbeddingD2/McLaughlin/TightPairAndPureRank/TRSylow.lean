module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_sup_dvd_of_commute {A B PA PB : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hPA : PA ≤ A) (hPB : PB ≤ B) :
    (PA ⊔ PB).relIndex (A ⊔ B) ∣ PA.relIndex A * PB.relIndex B := by
  let φ : ↥A × ↥B →* G := A.subtype.noncommCoprod B.subtype (fun x y => (hc x x.2 y y.2 : _))
  have hφ : ∀ (x : A) (y : B), φ (x, y) = (x : G) * y := fun x y => rfl
  have hrange : φ.range = A ⊔ B := by
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun x y => (hc x x.2 y y.2 : _))
    simpa using this
  set H : Subgroup (↥A × ↥B) := (PA.subgroupOf A).prod (PB.subgroupOf B) with hH
  have hmap : H.map φ = PA ⊔ PB := by
    apply le_antisymm
    · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
      rw [hφ]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hxy.1) (Subgroup.mem_subgroupOf.mp hxy.2)
    · refine sup_le ?_ ?_
      · intro a ha
        exact ⟨(⟨a, hPA ha⟩, 1), ⟨Subgroup.mem_subgroupOf.mpr ha, Subgroup.one_mem _⟩, by simp [hφ]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hPB hb⟩), ⟨Subgroup.one_mem _, Subgroup.mem_subgroupOf.mpr hb⟩, by simp [hφ]⟩
  have key := Subgroup.relIndex_map_map φ H ⊤
  rw [← MonoidHom.range_eq_map, hrange, hmap] at key
  rw [key, top_sup_eq, Subgroup.relIndex_top_right]
  calc (H ⊔ φ.ker).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
    _ = PA.relIndex A * PB.relIndex B := by rw [hH, Subgroup.index_prod]; rfl


omit [Finite G] in
theorem relIndex_barM_eq {M A B : Subgroup G} (hAB : A ≤ B) (hBM : B ≤ M)
    (hQA : pCoreOf 2 M ≤ A) : (barM M A).relIndex (barM M B) = A.relIndex B := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker ≤ A.subgroupOf M := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    apply Subgroup.mem_subgroupOf.mpr
    apply hQA
    have : (x : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨x, hx, rfl⟩
    assumption
  have hker' : (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker ≤ B.subgroupOf M :=
    hker.trans fun x hx => hAB hx
  unfold barM
  rw [Subgroup.relIndex_map_map, sup_eq_left.mpr hker, sup_eq_left.mpr hker',
    Subgroup.relIndex_subgroupOf hBM]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal' {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem relIndex_sup_eq {J T : Subgroup G} (hN : T ≤ Subgroup.normalizer (J : Set G)) :
    T.relIndex (J ⊔ T) = (J ⊓ T).relIndex J := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer' hN
  have h2 := Subgroup.relIndex_mul_card (H := T) (K := J ⊔ T)
  have h3 := Subgroup.relIndex_mul_card (H := J ⊓ T) (K := J)
  rw [inf_eq_left.mpr (le_sup_right : T ≤ J ⊔ T)] at h2
  rw [inf_eq_left.mpr (inf_le_left : J ⊓ T ≤ J)] at h3
  have hpos1 : 0 < Nat.card T := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(J ⊓ T) := Nat.card_pos
  have : T.relIndex (J ⊔ T) * (Nat.card T * Nat.card ↥(J ⊓ T)) =
      (J ⊓ T).relIndex J * (Nat.card T * Nat.card ↥(J ⊓ T)) := by
    calc T.relIndex (J ⊔ T) * (Nat.card T * Nat.card ↥(J ⊓ T))
        = (T.relIndex (J ⊔ T) * Nat.card T) * Nat.card ↥(J ⊓ T) := by ring
      _ = Nat.card ↥(J ⊔ T) * Nat.card ↥(J ⊓ T) := by rw [h2]
      _ = Nat.card ↥J * Nat.card ↥T := h1
      _ = ((J ⊓ T).relIndex J * Nat.card ↥(J ⊓ T)) * Nat.card ↥T := by rw [h3]
      _ = (J ⊓ T).relIndex J * (Nat.card T * Nat.card ↥(J ⊓ T)) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos1 hpos2) this

theorem isSylowTwoOf_trX {M S L₁ L₂ T : Subgroup G} (h₁ : IsWeakSBlock M S L₁)
    (h₂ : IsWeakSBlock M S L₂) (hne : barM M L₁ ≠ barM M L₂) (hT2 : IsPGroup 2 T)
    (hN : ∀ t ∈ T, ∀ j ∈ trJ M L₁ L₂, t * j * t⁻¹ ∈ trJ M L₁ L₂)
    (hQT : pCoreOf 2 M ≤ T)
    (hP₁ : IsSylowTwoOf (barM M (T ⊓ L₁)) (barM M L₁))
    (hP₂ : IsSylowTwoOf (barM M (T ⊓ L₂)) (barM M L₂)) :
    IsSylowTwoOf T (trX M L₁ L₂ T) := by
  refine ⟨le_trX_right, hT2, ?_⟩
  have hle : T ≤ Subgroup.normalizer (trJ M L₁ L₂ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => hN t ht j hj, fun hj => ?_⟩
    have := hN t⁻¹ (T.inv_mem ht) _ hj
    simpa [mul_assoc] using this
  have hJM : trJ M L₁ L₂ ≤ M := sup_le (sup_le h₁.le h₂.le) (pCoreOf_le 2 M)
  have hc : ∀ a ∈ barM M L₁, ∀ b ∈ barM M L₂, a * b = b * a := by
    have hc : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component h₂.component hne
    intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm
  set U₀ : Subgroup G := (T ⊓ L₁) ⊔ (T ⊓ L₂) ⊔ pCoreOf 2 M with hU₀
  have hU₀J : U₀ ≤ trJ M L₁ L₂ :=
    sup_le (sup_le (inf_le_right.trans le_trJ_left) (inf_le_right.trans le_trJ_right))
      pCoreOf_le_trJ
  have hU₀T : U₀ ≤ T := sup_le (sup_le inf_le_left inf_le_left) hQT
  have hbU : barM M U₀ = barM M (T ⊓ L₁) ⊔ barM M (T ⊓ L₂) := by
    rw [hU₀, barM_sup_eq (sup_le (inf_le_right.trans h₁.le) (inf_le_right.trans h₂.le))
      (pCoreOf_le 2 M), barM_sup_eq (inf_le_right.trans h₁.le) (inf_le_right.trans h₂.le),
      barM_pCoreOf_eq_bot, sup_bot_eq]
  have hbJ : barM M (trJ M L₁ L₂) = barM M L₁ ⊔ barM M L₂ := by
    rw [trJ, barM_sup_eq (sup_le h₁.le h₂.le) (pCoreOf_le 2 M), barM_sup_eq h₁.le h₂.le,
      barM_pCoreOf_eq_bot, sup_bot_eq]
  have h1 : (U₀).relIndex (trJ M L₁ L₂) =
      (barM M (T ⊓ L₁) ⊔ barM M (T ⊓ L₂)).relIndex (barM M L₁ ⊔ barM M L₂) := by
    rw [← hbU, ← hbJ, relIndex_barM_eq hU₀J hJM (le_sup_right)]
  have h2 := relIndex_sup_dvd_of_commute hc hP₁.1 hP₂.1
  have h4 : (trJ M L₁ L₂ ⊓ T).relIndex (trJ M L₁ L₂) ∣ U₀.relIndex (trJ M L₁ L₂) :=
    Subgroup.relIndex_dvd_of_le_left _ (le_inf hU₀J hU₀T)
  show ¬ 2 ∣ T.relIndex (trX M L₁ L₂ T)
  rw [trX, relIndex_sup_eq hle]
  intro hd
  have h5 := hd.trans (h4.trans (h1 ▸ h2))
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h5 with h | h
  · exact hP₁.2.2 h
  · exact hP₂.2.2 h

omit [Finite G] in
theorem isSylowTwoOf_map_hom' {K : Type*} [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem isSylowTwoOf_barM_inf_of_sylow_le {M H L T : Subgroup G}
    (hw : IsWeakSBlock M (pCoreOf 2 H) L) (hT : IsSylowTwoOf T (H ⊓ M))
    (hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H)
    {Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hQ : IsSylowTwoOf Q (barM M L))
    (hQJ : Q ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) :
    IsSylowTwoOf (barM M (T ⊓ L)) (barM M L) := by
  set K : Subgroup G := H ⊓ M with hK
  set D : Subgroup G := L ⊓ K with hD
  have hKM : K ≤ M := inf_le_right
  have hDM : D ≤ M := inf_le_right.trans hKM
  have hsub : (D.subgroupOf K).IsSubnormal := by
    have := isSubnormal_inf' hw.subnormal K
    rw [inf_eq_right.mpr hKM] at this
    exact isSubnormal_subgroupOf' this
  have hSyl := CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hT
    (inf_le_right : D ≤ K) hsub
  have hTD : T ⊓ D = T ⊓ L := by
    ext x
    simp only [hD, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hT.1 h.1⟩⟩
  rw [hTD] at hSyl
  have hPD : T ⊓ L ≤ D := hSyl.1
  have hbar : IsSylowTwoOf (barM M (T ⊓ L)) (barM M D) := by
    have := isSylowTwoOf_map_hom' hSyl (rhoX M D hDM)
    rwa [map_subgroupOf_rhoX hDM hPD, MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self (H := D),
      map_subgroupOf_rhoX hDM le_rfl] at this
  have hJD : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) = barM M D := by
    rw [hNH]
    congr 1
    apply le_antisymm
    · exact fun x hx => ⟨hx.2, hx.1, hw.le hx.2⟩
    · exact fun x hx => ⟨hx.2.1, hx.1⟩
  have hT'J : Q ≤ barM M D := by
    rw [← hJD]
    exact hQJ
  have hDL : barM M D ≤ barM M L := barM_mono inf_le_left
  refine ⟨hbar.1.trans hDL, hbar.2.1, ?_⟩
  show ¬ 2 ∣ (barM M (T ⊓ L)).relIndex (barM M L)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hbar.1 hDL]
  have h1 : (barM M D).relIndex (barM M L) ∣ Q.relIndex (barM M L) :=
    Subgroup.relIndex_dvd_of_le_left _ hT'J
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · exact hbar.2.2 h
  · exact hQ.2.2 (h.trans h1)

theorem isSylowTwoOf_barM_inf_of_parabolic {M H L T : Subgroup G}
    (hw : IsWeakSBlock M (pCoreOf 2 H) L) (hT : IsSylowTwoOf T (H ⊓ M))
    (hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H)
    (h9 : NineThreeTwo M (pCoreOf 2 H) L) :
    IsSylowTwoOf (barM M (T ⊓ L)) (barM M L) := by
  obtain ⟨-, hpar, -⟩ := h9
  obtain ⟨-, T', hT', hnorm⟩ := hpar
  exact isSylowTwoOf_barM_inf_of_sylow_le hw hT hNH hT'
    (fun x hx => hnorm ⟨hT'.1 hx, Subgroup.le_normalizer hx⟩)

theorem isSylowTwoOf_trX_of_nineThreeTwo {M H L₁ L₂ T : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hT : IsSylowTwoOf T (H ⊓ M)) (hQT : pCoreOf 2 M ≤ T)
    (hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H)
    (t₁ : NineThreeTwo M (pCoreOf 2 H) L₁) (t₂ : NineThreeTwo M (pCoreOf 2 H) L₂) :
    IsSylowTwoOf T (trX M L₁ L₂ T) := by
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hN := normalizes_trJ h₁ h₂ hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  exact isSylowTwoOf_trX h₁ h₂ hne hT.2.1 hN hQT
    (isSylowTwoOf_barM_inf_of_parabolic h₁ hT hNH t₁) (isSylowTwoOf_barM_inf_of_parabolic h₂ hT hNH t₂)

theorem isSylowTwoOf_trX_of_sylow_le {M H L₁ L₂ T : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hT : IsSylowTwoOf T (H ⊓ M)) (hQT : pCoreOf 2 M ≤ T)
    (hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H)
    (q₁ : ∃ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf Q (barM M L₁) ∧
      Q ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁))
    (q₂ : ∃ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf Q (barM M L₂) ∧
      Q ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂)) :
    IsSylowTwoOf T (trX M L₁ L₂ T) := by
  have hTHM : T ≤ H ⊓ M := hT.1
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hN := normalizes_trJ h₁ h₂ hk2 hTM
    (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  obtain ⟨Q₁, hQ₁, hQ₁J⟩ := q₁
  obtain ⟨Q₂, hQ₂, hQ₂J⟩ := q₂
  exact isSylowTwoOf_trX h₁ h₂ hne hT.2.1 hN hQT
    (isSylowTwoOf_barM_inf_of_sylow_le h₁ hT hNH hQ₁ hQ₁J)
    (isSylowTwoOf_barM_inf_of_sylow_le h₂ hT hNH hQ₂ hQ₂J)

end CFSG.AGLEmbeddingD2.McLaughlin
