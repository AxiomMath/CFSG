module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Lift
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Bar
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Setup
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD2028
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131
public import CFSG.LocalAnalysis.GLTheoremA.PartIInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA.I113

variable {G : Type} [Group G] [Finite G]

theorem i113UsedAt_of_kd (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (h2028 : KD2028) (hSU3 : KDSU3) (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I113UsedAt G p := by
  classical
  intro B x K hB hx hK hnK
  set X : Subgroup G := Subgroup.centralizer ({x} : Set G) with hXdef
  have hBX : B ≤ X := le_centralizer_of_mem hB.1 hx.1
  obtain ⟨-, hBmax⟩ := glaIsBmax_subgroupOf_centralizer hp hB hx
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B :=
    glaTwoLocalRank_le_pRank_of_isBmax hp hB X
  obtain ⟨hXne, h3, hrel, haut, -, htype⟩ :=
    i112c_full T TL TT hsimple hKP hp hp2 hB.1 hBX hr hK hnK
  subst h3
  have hp3 : Nat.Prime 3 := hp
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hKX : K ≤ X := hK.1
  have hnL2 : ¬ IsLTwoOddPow (barOf 3 K) := fun hL2 =>
    kernel11_3a_of_tables T TL ↥X (isKGroup_of_isKProper hKP hXne) (B.subgroupOf X) hBmax
      (K.subgroupOf X) (glaPComponent_top_subgroupOf hp hK)
      (fun h => hnK ((le_normalizer_subgroupOf_iff hKX hBX).1 h))
      ((relIndex_normalizer_subgroupOf hKX hBX).trans hrel)
      (isL2TwoPowOdd_of_mulEquiv (pQuotSubgroupOfEquiv 3 hKX).symm
        (isL2TwoPowOdd_of_isLTwoOddPow hL2))
  have hty : IsHatSix (barOf 3 K) ∨ IsHatSeven (barOf 3 K) ∨ IsHatMTwentyTwo (barOf 3 K) ∨
      IsSLThreeExc (barOf 3 K) ∨ IsSUThreeExc (barOf 3 K) := by
    rcases htype with h | h | h | h | h | h | h
    · exact absurd h hnL2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (isSUThreeExc_of_isSUThreeTwoPow h))))
  have hKK : CFSG.Open.IsKGroup ↥K :=
    isKGroup_of_isKProper hKP (ne_top_of_le_ne_top hXne hKX)
  have hKg : CFSG.Open.IsKGroup (barOf 3 K) := isKGroup_quotient' hKK (GLAPPrimeCore 3 ↥K)
  set e : barOf 3 K ≃* ↥(barX 3 X K) := quotEquivBarX hp3 hK.1 hK.2.1 with he
  obtain ⟨c, hcB, hcK⟩ : ∃ c ∈ B, c ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnK fun b hb => hcon b hb
  have hTr : Triple3 (barX 3 X B) (barX 3 X K) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨c, hBX hcB⟩) :=
    { elem := isElemAbelian_barX hB.1
      comp := hK.2.2.1
      mem := ⟨⟨c, hBX hcB⟩, Subgroup.mem_subgroupOf.2 hcB, rfl⟩
      not_mem := fun h => hcK (by
        have h2 : (⟨c, hBX hcB⟩ : ↥X) ∈ (Subgroup.normalizer (K : Set G)).subgroupOf X := by
          rw [← i112f_comap_normalizer_barX hK]
          exact h
        exact Subgroup.mem_subgroupOf.1 h2)
      index := (i112f_relIndex_barX hK hBX).trans hrel }
  have hall : ∀ M' : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsComponentOf M' ⊤ →
      (Subgroup.normalizer (M' : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).relIndex (barX 3 X B) ∣ 3 := by
    intro M' hM'
    obtain ⟨L', hL', rfl⟩ := exists_glaPComponent_barX_eq (p := 3) X hM'
    rw [i112f_relIndex_barX hL' hBX]
    by_cases h : B ≤ Subgroup.normalizer (L' : Set G)
    · rw [Subgroup.relIndex_eq_one.2 h]
      exact one_dvd _
    · rw [(i112c_full T TL TT hsimple hKP hp3 (by norm_num) hB.1 hBX hr hL' h).2.2.1]
  have hH9 : ∀ E : Subgroup (MulAut ↥(barX 3 X K)), IsElemAbelian 3 E → Nat.card E ≤ 9 :=
    card_le_nine_of_pRank (by rw [← i112f_pRank_mulAut_of_mulEquiv e]; exact haut)
  have h2M : 2 ∣ Nat.card ↥(barX 3 X K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact two_dvd_card_of_quasisimple hq
  have hxo : ∃ y ∈ barX 3 X K, orderOf y = 3 ∧ ∃ m ∈ barX 3 X K, y * m ≠ m * y := by
    obtain ⟨R⟩ : Nonempty (Sylow 3 (barOf 3 K)) := inferInstance
    obtain ⟨-, ⟨r, hr', s, hs, hrs⟩, hexp⟩ := TM.T10_10S (barOf 3 K) hq hKg hty R
    have hr1 : r ≠ 1 := fun h => hrs (by rw [h]; simp)
    have hro : orderOf r = 3 := orderOf_eq_prime (hexp r hr') hr1
    refine ⟨(e r : _), (e r).2, ?_, (e s : _), (e s).2, fun h => hrs ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hro]
    · apply e.injective
      exact Subtype.ext (by simpa using h)
  obtain ⟨y, hy, hyo, hyn⟩ := hxo
  have hGood : ∀ E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X),
      GoodE (barX 3 X B) (barX 3 X K) E →
      (2 ∣ Nat.card (GLAPPrimeCoreOf 3 X) ∨
        ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≠ ⊥ ∧ IsPGroup 2 T ∧
          t113B0 (barX 3 X B) (barX 3 X K) ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) ∧
          E ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) →
      ∃ A : Subgroup G, GLAIsBmax 3 A ∧ B ⊓ centModSubgroup 3 K ≤ A ∧
        (∀ b ∈ B, A ≤ Subgroup.normalizer (GLBConj b K : Set G)) ∧
        (∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ closureIn K B, a = u * v) ∧
        ¬ IsCyclic (A ⊓ closureIn K B ⊓ centModSubgroup 3 K : Subgroup G) := by
    intro E hE h2
    refine i113_lift hB hBX hK E ?_ hE.elem hE.nonCyc ?_ ?_ ?_
    · rw [i112f_barX_bClosure hBX hK.1]
      exact hE.le_K
    · rw [barX_B0_eq hBX hB.1 hK]
      exact hE.inf_bot
    · rw [barX_B0_eq hBX hB.1 hK, ← i113g_card_barX hp3 (isPGroup_of_isElemAbelian hB.1) hBX]
      exact hE.card_le
    · rw [barX_B0_eq hBX hB.1 hK]
      exact h2
  by_cases hOeven : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 X)
  · exact hGood _ (hTr.goodE_Y hH9 hy hyo hyn) (Or.inl hOeven)
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
    by_cases hTP : IsSUThreeTwoPow (barOf 3 K)
    ·
      have hSU : ∀ E T' : Subgroup (MulAut ↥(barX 3 X K)), IsElemAbelian 3 E → T' ≠ ⊥ →
          IsPGroup 2 T' → E ≤ Subgroup.normalizer (T' : Set (MulAut ↥(barX 3 X K))) →
          Nat.card E ≤ 3 := hSU3 ↥(barX 3 X K) (isSUThreeTwoPow_of_mulEquiv e hTP)
      obtain ⟨E, hE, T', hT'ne, hT'2, h1, h2⟩ :=
        exists_goodE_norm2 hTr hall hH9 hU h2M (Or.inr ⟨⟨y, hy, hyo, hyn⟩, hSU⟩)
      exact hGood E hE (Or.inr ⟨T', hT'ne, hT'2, h1, h2⟩)
    ·
      have hty' : IsHatSix (barOf 3 K) ∨ IsHatSeven (barOf 3 K) ∨ IsHatMTwentyTwo (barOf 3 K) ∨
          IsSLThreeExc (barOf 3 K) ∨ (IsSUThreeExc (barOf 3 K) ∧ ¬ IsSUThreeTwoPow (barOf 3 K)) := by
        rcases hty with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hTP⟩)))
      obtain ⟨x0, hx0o, hx0c, T0, hT0, hT02, hx0T⟩ := h2028 (barOf 3 K) hq hty'
      obtain ⟨s0, hs0⟩ : ∃ s : barOf 3 K, x0 * s ≠ s * x0 := by
        by_contra hcon
        push Not at hcon
        exact hx0c (Subgroup.mem_center_iff.2 fun s => (hcon s).symm)
      set φ : barOf 3 K →* ↥X ⧸ GLAPPrimeCore 3 ↥X := (barX 3 X K).subtype.comp e.toMonoidHom
        with hφdef
      have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
      have hφM : ∀ t : barOf 3 K, φ t ∈ barX 3 X K := fun t => (e t).2
      have hmode : (∃ y ∈ barX 3 X K, orderOf y = 3 ∧ (∃ m ∈ barX 3 X K, y * m ≠ m * y) ∧
          ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≤ barX 3 X K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
            y ∈ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ∨
          ((∃ y ∈ barX 3 X K, orderOf y = 3 ∧ ∃ m ∈ barX 3 X K, y * m ≠ m * y) ∧
            ∀ E T : Subgroup (MulAut ↥(barX 3 X K)), IsElemAbelian 3 E → T ≠ ⊥ →
              IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set (MulAut ↥(barX 3 X K))) →
              Nat.card E ≤ 3) := by
        refine Or.inl ⟨φ x0, hφM x0, ?_, ⟨φ s0, hφM s0, fun h => hs0 (hφ (by simpa using h))⟩,
          T0.map φ, ?_, ?_, hT02.map φ, ?_⟩
        · rw [orderOf_injective φ hφ x0, hx0o]
        · rintro _ ⟨t, -, rfl⟩
          exact hφM t
        · exact fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h)
        · exact Subgroup.le_normalizer_map φ ⟨x0, hx0T, rfl⟩
      obtain ⟨E, hE, T', hT'ne, hT'2, h1, h2⟩ := exists_goodE_norm2 hTr hall hH9 hU h2M hmode
      exact hGood E hE (Or.inr ⟨T', hT'ne, hT'2, h1, h2⟩)

end CFSG.LocalAnalysis.GLTheoremA
