module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Lift
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Cases
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD2028S
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA.I113
  CFSG.LocalAnalysis.GLTheoremA.I1132

theorem t1010S_of_mulEquiv {K₁ K₂ : Type} [Group K₁] [Group K₂] [Finite K₁] [Finite K₂]
    (e : K₁ ≃* K₂)
    (h : ∀ R : Sylow 3 K₁, Nat.card (R : Subgroup K₁) = 27 ∧
      (∃ r ∈ (R : Subgroup K₁), ∃ s ∈ (R : Subgroup K₁), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K₁), r ^ 3 = 1) :
    ∀ R : Sylow 3 K₂, Nat.card (R : Subgroup K₂) = 27 ∧
      (∃ r ∈ (R : Subgroup K₂), ∃ s ∈ (R : Subgroup K₂), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K₂), r ^ 3 = 1 := by
  intro R
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hc, ⟨r, hr, s, hs, hrs⟩, hexp⟩ :=
    h (Sylow.mapSurjective (f := (e.symm : K₂ →* K₁)) e.symm.surjective R)
  have hmap : ((Sylow.mapSurjective (f := (e.symm : K₂ →* K₁)) e.symm.surjective R :
      Sylow 3 K₁) : Subgroup K₁) = (R : Subgroup K₂).map (e.symm : K₂ →* K₁) := rfl
  rw [hmap] at hc hr hs hexp
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc]
    exact (Subgroup.card_map_of_injective e.symm.injective).symm
  · obtain ⟨r', hr', rfl⟩ := hr
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨r', hr', s', hs', fun h' => hrs ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e.symm h'
  · intro r' hr'
    have := hexp (e.symm r') ⟨r', hr', rfl⟩
    rw [← map_pow] at this
    exact e.symm.injective (by simpa using this)

variable {G : Type} [Group G] [Finite G]

theorem i1132UsedAt_of_kd (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (h2028 : KD2028S) (hSU3 : KDSU3) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : I1132UsedAt G p := by
  classical
  intro B x L hB hx hL hnL
  set X : Subgroup G := Subgroup.centralizer ({x} : Set G) with hXdef
  have hBX : B ≤ X := le_centralizer_of_mem hB.1 hx.1
  obtain ⟨-, hBmax⟩ := glaIsBmax_subgroupOf_centralizer hp hB hx
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B :=
    glaTwoLocalRank_le_pRank_of_isBmax hp hB X
  obtain ⟨hXne, h3, hrel, haut, -, htype⟩ :=
    i112c_full T TL TT hsimple hKP hp hp2 hB.1 hBX hr hL hnL
  subst h3
  have hp3 : Nat.Prime 3 := hp
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hLX : L ≤ X := hL.1
  have hnL2 : ¬ IsLTwoOddPow (barOf 3 L) := fun hL2 =>
    kernel11_3a_of_tables T TL ↥X (isKGroup_of_isKProper hKP hXne) (B.subgroupOf X) hBmax
      (L.subgroupOf X) (glaPComponent_top_subgroupOf hp hL)
      (fun h => hnL ((le_normalizer_subgroupOf_iff hLX hBX).1 h))
      ((relIndex_normalizer_subgroupOf hLX hBX).trans hrel)
      (isL2TwoPowOdd_of_mulEquiv (pQuotSubgroupOfEquiv 3 hLX).symm
        (isL2TwoPowOdd_of_isLTwoOddPow hL2))
  have hty : IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨ IsHatMTwentyTwo (barOf 3 L) ∨
      IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L) := by
    rcases htype with h | h | h | h | h | h | h
    · exact absurd h hnL2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (isSUThreeExc_of_isSUThreeTwoPow h))))
  have hKK : CFSG.Open.IsKGroup ↥L :=
    isKGroup_of_isKProper hKP (ne_top_of_le_ne_top hXne hLX)
  have hKg : CFSG.Open.IsKGroup (barOf 3 L) := isKGroup_quotient' hKK (GLAPPrimeCore 3 ↥L)
  set e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp3 hL.1 hL.2.1 with he
  obtain ⟨c, hcB, hcL⟩ : ∃ c ∈ B, c ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnL fun b hb => hcon b hb
  have hTr : Triple3 (barX 3 X B) (barX 3 X L)
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨c, hBX hcB⟩) :=
    { elem := isElemAbelian_barX hB.1
      comp := hL.2.2.1
      mem := ⟨⟨c, hBX hcB⟩, Subgroup.mem_subgroupOf.2 hcB, rfl⟩
      not_mem := fun h => hcL (by
        have h2 : (⟨c, hBX hcB⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
          rw [← i112f_comap_normalizer_barX hL]
          exact h
        exact Subgroup.mem_subgroupOf.1 h2)
      index := (i112f_relIndex_barX hL hBX).trans hrel }
  have hall : ∀ M' : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsComponentOf M' ⊤ →
      (Subgroup.normalizer (M' : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).relIndex (barX 3 X B) ∣ 3 := by
    intro M' hM'
    obtain ⟨L', hL', rfl⟩ := exists_glaPComponent_barX_eq (p := 3) X hM'
    rw [i112f_relIndex_barX hL' hBX]
    by_cases h : B ≤ Subgroup.normalizer (L' : Set G)
    · rw [Subgroup.relIndex_eq_one.2 h]
      exact one_dvd _
    · rw [(i112c_full T TL TT hsimple hKP hp3 (by norm_num) hB.1 hBX hr hL' h).2.2.1]
  have hH9 : ∀ E : Subgroup (MulAut ↥(barX 3 X L)), IsElemAbelian 3 E → Nat.card E ≤ 9 :=
    card_le_nine_of_pRank (by rw [← i112f_pRank_mulAut_of_mulEquiv e]; exact haut)
  have h2M : 2 ∣ Nat.card ↥(barX 3 X L) := by
    rw [← Nat.card_congr e.toEquiv]
    exact two_dvd_card_of_quasisimple hq
  have hSylM : ∀ R : Sylow 3 ↥(barX 3 X L), Nat.card (R : Subgroup ↥(barX 3 X L)) = 27 ∧
      (∃ r ∈ (R : Subgroup ↥(barX 3 X L)), ∃ s ∈ (R : Subgroup ↥(barX 3 X L)), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup ↥(barX 3 X L)), r ^ 3 = 1 :=
    t1010S_of_mulEquiv e (fun R => TM.T10_10S (barOf 3 L) hq hKg hty R)
  have hS : QSetting (barX 3 X B) (barX 3 X L)
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨c, hBX hcB⟩) := ⟨hTr, hall, hH9, hSylM, h2M⟩
  by_cases hOeven : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 X)
  · obtain ⟨D, E1, E2, M4, hG⟩ := exists_good_noT hS
    exact i1132_of_good hB hBX hL hG (Or.inl hOeven)
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU : ∃ S : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), S ≠ ⊥ ∧ IsPGroup 2 S ∧
        barX 3 X B ≤ Subgroup.normalizer (S : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      obtain ⟨U, hUX, hU2, hBU, hUB, -⟩ := hx.2.2
      have hUne : U ≠ ⊥ := fun h => hUB (by rw [h]; exact Subgroup.commutator_bot_left B)
      have hU2' : IsPGroup 2 (U.subgroupOf X) :=
        hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
      refine ⟨barX 3 X U, ?_, hU2'.map _, ?_⟩
      · intro hbot
        have hle : U.subgroupOf X ≤ GLAPPrimeCore 3 ↥X := by
          intro u hu
          have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) u ∈
              (barX 3 X U : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) := ⟨u, hu, rfl⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact (QuotientGroup.eq_one_iff u).1 this
        have hd : Nat.card (U.subgroupOf X) ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
          Subgroup.card_dvd_of_le hle
        obtain ⟨k, hk⟩ := hU2.exists_card_eq
        have hk0 : k ≠ 0 := by
          rintro rfl
          exact hUne (Subgroup.eq_bot_of_card_eq U (by simpa using hk))
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv, hk] at hd
        apply hOeven
        have hc : Nat.card (GLAPPrimeCoreOf 3 X) = Nat.card (GLAPPrimeCore 3 ↥X) :=
          Subgroup.card_map_of_injective X.subtype_injective
        rw [hc]
        exact (dvd_pow_self 2 hk0).trans hd
      · have h1 : B.subgroupOf X ≤
            Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
          rw [normalizer_subgroupOf_eq hUX]
          intro b hb
          exact hBU hb
        exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
    have hmode : (∀ y ∈ barX 3 X L, orderOf y = 3 → ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X),
          T ≤ barX 3 X L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
          y ∈ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ∨
        (∀ E T : Subgroup (MulAut ↥(barX 3 X L)), IsElemAbelian 3 E → T ≠ ⊥ → IsPGroup 2 T →
          E ≤ Subgroup.normalizer (T : Set (MulAut ↥(barX 3 X L))) → Nat.card E ≤ 3) := by
      by_cases hTP : IsSUThreeTwoPow (barOf 3 L)
      · exact Or.inr (hSU3 ↥(barX 3 X L) (isSUThreeTwoPow_of_mulEquiv e hTP))
      ·
        left
        have hty' : IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨ IsHatMTwentyTwo (barOf 3 L) ∨
            IsSLThreeExc (barOf 3 L) ∨ (IsSUThreeExc (barOf 3 L) ∧ ¬ IsSUThreeTwoPow (barOf 3 L)) := by
          rcases hty with h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hTP⟩)))
        intro y hy hyo
        set φ : barOf 3 L →* ↥X ⧸ GLAPPrimeCore 3 ↥X := (barX 3 X L).subtype.comp e.toMonoidHom
          with hφdef
        have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
        have hφM : ∀ t : barOf 3 L, φ t ∈ barX 3 X L := fun t => (e t).2
        set x0 : barOf 3 L := e.symm ⟨y, hy⟩ with hx0
        have hφx0 : φ x0 = y := by
          simp [hφdef, hx0]
        have hx0o : orderOf x0 = 3 := by
          rw [hx0, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hyo]
        obtain ⟨T0, hT0, hT02, hx0T⟩ := h2028 (barOf 3 L) hq hty' x0 hx0o
        refine ⟨T0.map φ, ?_, ?_, hT02.map φ, ?_⟩
        · rintro _ ⟨t, -, rfl⟩
          exact hφM t
        · exact fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h)
        · rw [← hφx0]
          exact Subgroup.le_normalizer_map φ ⟨x0, hx0T, rfl⟩
    obtain ⟨D, E1, E2, M4, hG, T', hT'ne, hT'2, hT'⟩ := exists_good_T hS hU hmode
    exact i1132_of_good hB hBX hL hG (Or.inr ⟨T', hT'ne, hT'2, hT'⟩)

end CFSG.LocalAnalysis.GLTheoremA
