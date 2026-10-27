module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOrbit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem exists_noncentral (h72 : KFactOmegaNotCentral) (h : NineSettingGen G M p Q H E k)
    {C : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) :
    ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hdvd : p ∣ Nat.card C := by
    by_contra hnd
    have hcop : Nat.Coprime p (Nat.card C) := (h.prime.coprime_iff_not_dvd).mpr hnd
    have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
    have hle : C ≤ CFSG.pPrimeCore p (StarGroup p H) :=
      CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hC.2 hcop
    rw [hO] at hle
    have hbot : C = ⊥ := le_bot_iff.mp hle
    have hnt : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
    exact (Subgroup.nontrivial_iff_ne_bot C).mp hnt hbot
  exact h72 (StarGroup p H) h.isKGroup_star C hC p h.prime h.ne_two hdvd

theorem add_card_le_three (h72 : KFactOmegaNotCentral) (h : NineSettingGen G M p Q H E k)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M) {A : Subgroup (StarGroup p H)} {a : ℕ}
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ a) (s : Finset (Subgroup (StarGroup p H)))
    (hs : ∀ C ∈ s, CFSG.IsComponent C ∧ A ≤ centralizer (C : Set (StarGroup p H))) :
    a + s.card ≤ 3 := by
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 := by
    rw [← starImg_self p H, pRank_starImg_eq h.prime le_rfl]
    exact (h.pRank_le_of_mem_H2Fam hH2 hp).1
  refine (add_card_le_pRank_of_components h.prime hA hAc s ?_).trans h3
  intro C hC
  exact ⟨(hs C hC).1, (hs C hC).2, h.exists_noncentral h72 (hs C hC).1⟩

theorem three_components (h72 : KFactOmegaNotCentral) (h : NineSettingGen G M p Q H E k)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hQN : ¬ starImg p H Q ≤ compNormalizer (StarGroup p H)) :
    p = 3 ∧ ∃ (C : Subgroup (StarGroup p H)) (q : StarGroup p H), q ∈ starImg p H Q ∧
      CFSG.IsComponent C ∧
      (∀ D : Subgroup (StarGroup p H), CFSG.IsComponent D ↔
        ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) ∧
      Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom) ∧
      (∀ D : Subgroup (StarGroup p H), CFSG.IsComponent D → CFSG.Open.pRank p D = 1) ∧
      CFSG.pCore p (StarGroup p H) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  classical
  obtain ⟨q, hqQ, hqN⟩ := SetLike.not_le_iff_exists.mp hQN
  rw [mem_compNormalizer_iff] at hqN
  push Not at hqN
  obtain ⟨C, hCcomp, hqC⟩ := hqN
  have hQp : IsPGroup p Q := QSet.isPGroup_of_mem h.mem_Q
  have hstarQp : IsPGroup p (starImg p H Q) := (hQp.comap_subtype (K := H)).map _
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hstarQp ⟨q, hqQ⟩
  have hn' : orderOf q = p ^ n := (Subgroup.orderOf_coe ⟨q, hqQ⟩).trans hn
  let f : Fin p → Subgroup (StarGroup p H) :=
    fun i => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom
  have hfcomp : ∀ i, CFSG.IsComponent (f i) :=
    fun i => CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (q ^ (i : ℕ))) hCcomp
  have hfinj : Function.Injective f := conj_pow_injective h.prime hn' hqC
  have hcard : (Finset.univ.image f).card = p := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  have hp_le_three : p ≤ 3 := by
    have hle := h.add_card_le_three h72 hH2 hp (A := ⊥) (a := 0)
      (CFSG.SectionRank.isElemAbelian_bot p) (by simp) (Finset.univ.image f)
      (fun D hD => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hD
        exact ⟨hfcomp i, bot_le⟩)
    rwa [hcard, Nat.zero_add] at hle
  have hp3 : p = 3 := by
    rcases eq_or_lt_of_le hp_le_three with h3 | hlt
    · exact h3
    · exact absurd (le_antisymm (Nat.lt_succ_iff.mp hlt) h.prime.two_le) h.ne_two
  subst hp3
  have hiff : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔ ∃ i : Fin 3, D = f i := by
    intro D
    constructor
    · intro hD
      by_contra hnot
      push Not at hnot
      have hDnotmem : D ∉ Finset.univ.image f := by
        intro hmem
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
        exact hnot i hi.symm
      have hcard4 : (insert D (Finset.univ.image f)).card = 4 := by
        rw [Finset.card_insert_of_notMem hDnotmem, hcard]
      have hle := h.add_card_le_three h72 hH2 hp (A := ⊥) (a := 0)
        (CFSG.SectionRank.isElemAbelian_bot 3) (by simp) (insert D (Finset.univ.image f))
        (fun E hE => by
          rcases Finset.mem_insert.mp hE with rfl | hE'
          · exact ⟨hD, bot_le⟩
          · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hE'
            exact ⟨hfcomp i, bot_le⟩)
      rw [hcard4, Nat.zero_add] at hle
      omega
    · rintro ⟨i, rfl⟩
      exact hfcomp i
  refine ⟨rfl, C, q, hqQ, hCcomp, hiff, hfinj, ?_, ?_⟩
  · intro D hD
    apply le_antisymm
    · obtain ⟨B, hBD, hBab, hBcard⟩ := CFSG.SectionRank.exists_pRank (show 1 < 3 by norm_num) D
      obtain ⟨i, hi⟩ := (hiff D).mp hD
      let s : Finset (Subgroup (StarGroup 3 H)) := (Finset.univ.erase i).image f
      have hscard : s.card = 2 := by
        dsimp only [s]
        rw [Finset.card_image_of_injective (Finset.univ.erase i) hfinj,
          Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
      have hs : ∀ E ∈ s, CFSG.IsComponent E ∧
          B ≤ centralizer (E : Set (StarGroup 3 H)) := by
        intro E hE
        dsimp only [s] at hE
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hE
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        refine ⟨hfcomp k, ?_⟩
        have hDne : D ≠ f k := by
          rw [hi]
          intro h
          exact hki (hfinj h).symm
        have hcomm : ⁅D, f k⁆ = ⊥ :=
          (CFSG.LocalCores.distinct_components_commute hD (hfcomp k)).resolve_left hDne
        exact hBD.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      have hle := h.add_card_le_three h72 hH2 hp hBab hBcard s hs
      rw [hscard] at hle
      omega
    · obtain ⟨e, heD, hord, hnce⟩ := h.exists_noncentral h72 hD
      have hep : e ^ 3 = 1 := by simpa [hord] using pow_orderOf_eq_one e
      have hEab : IsElemAbelian 3 (Subgroup.zpowers e) := isElemAbelian_zpowers hep
      have hEcard : Nat.card (Subgroup.zpowers e) = 3 ^ 1 := by
        rw [Nat.card_zpowers, hord, pow_one]
      exact CFSG.SectionRank.le_pRank (show 1 < 3 by norm_num)
        (Subgroup.zpowers_le.mpr heD) hEab hEcard
  · by_contra hRne
    have hRp : IsPGroup 3 (CFSG.pCore 3 (StarGroup 3 H)) :=
      CFSG.pCore_isPGroup (p := 3) (G := StarGroup 3 H)
    have hcard_ne_one : Nat.card (CFSG.pCore 3 (StarGroup 3 H)) ≠ 1 := by
      intro h1
      have hbot : CFSG.pCore 3 (StarGroup 3 H) = ⊥ := by
        rw [Subgroup.eq_bot_iff_card]
        exact h1
      exact hRne hbot
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hRp
    have hmpos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, pow_zero] at hm
        exact absurd hm hcard_ne_one
      · exact hpos
    have h3dvd : 3 ∣ Nat.card (CFSG.pCore 3 (StarGroup 3 H)) := by
      rw [hm]
      exact dvd_pow_self 3 (by omega)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(CFSG.pCore 3 (StarGroup 3 H))) 3 h3dvd
    let z0 : StarGroup 3 H := (z : StarGroup 3 H)
    have hz0ord : orderOf z0 = 3 := (Subgroup.orderOf_coe z).trans hz
    let A : Subgroup (StarGroup 3 H) := Subgroup.zpowers z0
    have hAab : IsElemAbelian 3 A :=
      isElemAbelian_zpowers (by simpa [hz0ord] using pow_orderOf_eq_one z0)
    have hAcard : Nat.card A = 3 ^ 1 := by rw [Nat.card_zpowers, hz0ord, pow_one]
    have hAle : A ≤ CFSG.pCore 3 (StarGroup 3 H) := Subgroup.zpowers_le.mpr z.2
    have hs : ∀ D ∈ Finset.univ.image f, CFSG.IsComponent D ∧
        A ≤ centralizer (D : Set (StarGroup 3 H)) := by
      intro D hD
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hD
      refine ⟨hfcomp i, ?_⟩
      refine hAle.trans ?_
      refine (pCore_le_centralizer_layer (p := 3) (by norm_num) H).trans ?_
      exact Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer (hfcomp i))
    have hle := h.add_card_le_three h72 hH2 hp hAab hAcard (Finset.univ.image f) hs
    rw [hcard] at hle
    omega

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
