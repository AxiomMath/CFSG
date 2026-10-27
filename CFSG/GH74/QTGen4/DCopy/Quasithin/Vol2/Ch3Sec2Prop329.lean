module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL5C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec2Lem327
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem stmt3_2_9C_of_rows_F4
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (h3228 : Stmt3_2_2_eight) (h332 : Stmt3_3_2MTwo) (h316 : Theorem316Statement)
    (hB45 : AsB45) (hA7 : Row329Alt7) (hG2 : Row329G2) (hOrth : Row329Orth)
    (hNine : Row329Nine) (hM12 : Row329M12) (hHat : Row329HatM22) (hM22 : Row329M22)
    (hM23 : Row329M23) (hM24 : Row329M24) : Stmt3_2_9C_F4 := by
  intro G _ _ T L V₀ hfsu hLT hV₀T ⟨hcomm, hFF⟩
  refine ⟨hcomm, ?_⟩
  have hirrIn := hfsu.irrPlus
  rw [← hLT] at hirrIn
  obtain ⟨hVR, hV1, hLN, hVL, hlt, hirr', -⟩ := hirrIn
  obtain ⟨hsq, -, hO2R⟩ := reducedAggregate_props (L ⊔ T)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLT]
    exact le_normalizer_conjClosure L T
  have hTN : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hV₀T]
    exact le_normalizer_conjClosure V₀ T
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hO2 : ∀ x ∈ CFSG.pCore 2 ↥L, (x : G) ∈ Subgroup.centralizer (V₀ : Set G) := by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L :=
      ⟨x, by exact hx, rfl⟩
    exact Subgroup.centralizer_le (fun v hv => hVR hv) (hO2R (hQL h1))
  have hnt : ∃ l ∈ L, l ∉ Subgroup.centralizer (V₀ : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hV1
    rw [← hVL, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    have := Subgroup.mem_centralizer_iff.1 (hcon l hl) v hv
    rw [Subgroup.mem_bot, commutatorElement_def, this]
    group
  have hq := isQuasisimple_autOn hLN hfsu.quasisimple hO2 hnt
  have hV2 : IsPGroup 2 ↥V₀ := fun v => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hsq v (hVR v.2)]; rfl)⟩
  have hNV : pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) ≠ ⊥ := by
    have hle : V₀ ≤ pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV2
    exact fun h => hV1 (le_bot_iff.1 (h ▸ hle))
  have hSQ := sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hNV
  have hsqtk := sqtkGroup_autOn hSQ hLN hLN hq
  obtain ⟨htop, hIrr⟩ := top_mem_irrPlus_autOn hLN ⟨le_rfl, hV1, hLN, hVL, hlt, hirr'⟩
  have hT2 : IsPGroup 2 ↥T := hfsu.sylow.1
  have hsec : Sec328 (autOn L V₀) (autOn T V₀) :=
    { sq := fun v => Subtype.ext (by rw [Subgroup.coe_pow, hsq v (hVR v.2)]; rfl)
      quasi := hq
      sqtk := hsqtk
      irr := by rw [htop]; exact hIrr
      top := htop
      two := Lem328.isPGroup_autOn hT2
      norm := autOn_le_normalizer hLN hTN hTL }
  have hsup : autOn (L ⊔ T) V₀ = autOn L V₀ ⊔ autOn T V₀ := autOn_sup hLN hTN
  have hLTN : autOn (L ⊔ T) V₀ ≤ Subgroup.normalizer (autOn L V₀ : Set (MulAut ↥V₀)) := by
    rw [hsup]
    exact hsec.sup_le_normalizer
  have hnFF : ¬ IsFFModule (V := ↥V₀) (autOn (L ⊔ T) V₀) := fun h =>
    hFF (Prop329.isFFModule_of_le hLTN h)
  obtain ⟨⟨hMmax, hTM⟩, ⟨-, huniq⟩, -⟩ := h323 G T L hfsu.simple hfsu.nonabelian hfsu.qtke
    hfsu.sylow hfsu.maximal hfsu.faithful hfsu.quasisimple
  rw [← hLT] at hMmax hTM huniq
  obtain ⟨hVLT, hVred, hcent⟩ := h3228 G T L V₀ hfsu
  rw [← hLT, ← hV₀T] at hVLT hVred hcent
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hTM₁, hTM₂⟩ := h332 G T hfsu.simple hfsu.nonabelian hfsu.qtke
    hfsu.sylow L hfsu.maximal hfsu.quasisimple
  have hHstar : ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H := by
    by_cases h₁ : M₁ = Subgroup.normalizer (L : Set G)
    · exact exists_isHStar_of hMmax hM₂ hTM₂ (fun h₂ => hne (h₁.trans h₂.symm))
    · exact exists_isHStar_of hMmax hM₁ hTM₁ h₁
  have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L V₀ :=
    { inM := ⟨hMmax, hTM⟩
      nonempty := hHstar
      perfect := (C2Nine.oTwoUpper_eq_of_perfect hfsu.faithful.1.2.1.2.1).symm
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTM⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩
      centralizer := hcent }
  have hcV : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rcases theorem318_three hC58 h317 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow h318 with
      ⟨-, hFFi⟩ | ⟨-, -, hZ⟩
    · exact absurd hFFi hnFF
    · exact Prop329.inf_centralizer_eq_bot hT2 hV2 hVLT hTN hTL hZ
  have hfix : XMod.fixed ↥(autOn L V₀) (⊤ : Subgroup ↥V₀) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : v ∈ fixV (autOn L V₀) := by
      rw [mem_fixV]
      intro a ha
      exact hv.2 ⟨a, ha⟩
    rw [fixV_autOn hLN, Subgroup.mem_subgroupOf] at hv'
    have h1 : (v : G) ∈ V₀ ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv'⟩
    rw [hcV] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))
  have hB4 : B4Hyp (autOn (L ⊔ T) V₀) (autOn L V₀) := by
    rw [hsup]
    refine ⟨hsec.sqtk_sup, hsec.genFitting_eq.symm, hq, ?_⟩
    have h3 := hIrr.2.2.2
    rw [hfix] at h3
    exact h3
  have hqhat : qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ≤ ((2 : ℚ) : WithTop ℚ) := by
    have key : ∀ W : Subgroup G, W = V₀ →
        (∃ _ : IsMulCommutative ↥W, qhatOf (V := ↥W) (autOn (L ⊔ T) W) ≤ 2) →
          qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ≤ ((2 : ℚ) : WithTop ℚ) := by
      rintro W rfl ⟨_, h⟩
      exact_mod_cast h
    exact key _ hV₀T.symm (h325 G T L V₀ hfsu hLT).1
  have hTI : IsTISetIn V₀ (Subgroup.normalizer (L : Set G)) := by
    have h := isTISetUnder_of_stmt3_2_5_F4 h325 hfsu hLT
    rw [← hLT, ← hV₀T] at h
    exact ⟨hVLT.trans (sup_le Subgroup.le_normalizer hTM), h⟩
  have hdich : qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ≤ ((2 : ℚ) : WithTop ℚ) ∨
      qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) < ((2 : ℚ) : WithTop ℚ) := by
    rcases theorem318_two_of_316 h316 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow h318 with
      h | ⟨-, h⟩
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h hTI
  rcases hB45 ↥V₀ hsec.sq _ _ hB4 hqhat with ⟨-, ⟨A, hA⟩, -⟩ | ⟨hq1, hrow⟩ | ⟨hq2, h2q, -⟩
  · exact absurd (Prop329.isFFModule_of_offender hA) hnFF
  · have hTLN : autOn T V₀ ≤ Subgroup.normalizer (autOn L V₀ : Set (MulAut ↥V₀)) :=
      autOn_le_normalizer hLN hTN hTL
    rcases hrow with ⟨hA7r, -, -⟩ | ⟨m, hm1, hO, hqO, hqhO⟩ | ⟨m, hU, hqU, hqhU⟩ |
        ⟨f, hSz, hqS, hqhS⟩ | ⟨m, hm1, hN, hqN, hqhN⟩ | ⟨hG2r, -, -⟩ | ⟨hM, hqM⟩ |
        ⟨hH, -⟩ | ⟨hC, hqC⟩ | ⟨hC, hqC⟩ | ⟨hM, hqM⟩
    ·
      exact absurd (hA7 ↥V₀ _ hA7r) hFF
    ·
      rcases Nat.lt_or_ge m 2 with hm | hm
      · obtain rfl : m = 1 := by omega
        exact absurd (OrthFF.isFFModule_normalizer_of_binaryOrthogonalFour_one hO) hFF
      · exact Or.inl ⟨m, by omega, hOrth ↥V₀ _ _ hB4 m hm hO, hO, hqO, hq1, hqhO⟩
    ·
      exact Or.inr (Or.inl ⟨m, hU, hqU, hqhU⟩)
    ·
      exact Or.inr (Or.inr (Or.inl ⟨f, hSz, hqS, hqhS⟩))
    ·
      obtain ⟨K, hK, hKf, hKc, hcardK, hLie, hcardV, π, hπ, hng⟩ := hNine ↥V₀ _ _ hB4 m hm1 hN
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, K, hK, hKf, hKc, hm1, hcardK, hLie, hcardV, hqN,
        hqhN, π, hπ, fun t ht => hng t (hTLN ht)⟩)))
    ·
      exact absurd (hG2 ↥V₀ _ hG2r) hFF
    ·
      obtain ⟨hcard, hAut | hge⟩ := hM12 ↥V₀ _ _ hB4 hM
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hAut, hcard, hqM, hq1⟩))))
      · exfalso
        rcases hdich with h | h
        · exact absurd (hqM.trans_le h) (lt_irrefl _)
        · exact absurd (h.trans_le hge) (lt_irrefl _)
    ·
      obtain ⟨hperf, hZ3, hquot, hcard⟩ := hHat ↥V₀ _ hH
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hperf, hZ3, hquot, hcard, hq1⟩)))))
    ·
      obtain ⟨hiso, hcard, -⟩ := hM22 ↥V₀ _ _ hB4 (Or.inr hC)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hiso, hcard, hqC.le, hq1, fun _ => hqC⟩))))))
    ·
      obtain ⟨hiso, hcard, hcoc⟩ := hM22 ↥V₀ _ _ hB4 (Or.inl hC)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hiso, hcard, hqC, hq1, hcoc⟩))))))
    ·
      rcases hM with hc | hc | hc | hc
      · obtain ⟨hiso, hcard⟩ := hM23 ↥V₀ _ _ hB4 (Or.inr hc)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hiso, hcard, hqM, hq1⟩)))))))
      · obtain ⟨hiso, hcard⟩ := hM23 ↥V₀ _ _ hB4 (Or.inl hc)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hiso, hcard, hqM, hq1⟩)))))))
      · obtain ⟨hiso, hcard⟩ := hM24 ↥V₀ _ _ hB4 (Or.inr hc)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hiso, hcard, hqM, hq1⟩)))))))
      · obtain ⟨hiso, hcard⟩ := hM24 ↥V₀ _ _ hB4 (Or.inl hc)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hiso, hcard, hqM, hq1⟩)))))))
  · exfalso
    rcases hdich with h | h
    · exact absurd (h2q.trans_le h) (lt_irrefl _)
    · rw [hq2] at h
      exact lt_irrefl _ h

end CFSG.Quasithin.H13
