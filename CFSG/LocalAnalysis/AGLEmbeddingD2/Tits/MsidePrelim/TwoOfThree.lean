module

public import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.ThompsonTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.QuaternionEscape
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.QuasithinUnique
open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3 D2Amb3)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_map_subtype_of_normal {X : Subgroup G} {N : Subgroup ↥X} (hN : N.Normal) :
    X ≤ Subgroup.normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hN.conj_mem n hn ⟨x, hx⟩, rfl⟩
  · rintro ⟨n, hn, hne⟩
    refine ⟨⟨x, hx⟩⁻¹ * n * ⟨x, hx⟩, by simpa using hN.conj_mem n hn ⟨x, hx⟩⁻¹, ?_⟩
    have hne' : (n : G) = x * y * x⁻¹ := hne
    show x⁻¹ * (n : G) * x = y
    rw [hne']
    group

omit [Finite G] in
theorem generalizedFitting_eq_pCore_of_charTwo [Finite G] {X : Subgroup G} (h : CharTwo X) :
    CFSG.generalizedFitting ↥X = CFSG.pCore 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X 2).mp ?_
  intro x hx
  have hx' : (x : G) ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx r hr)
  obtain ⟨y, hy, hyx⟩ := h hx'
  rwa [← Subtype.ext hyx]

theorem charTwo_of_le_of_pCoreOf_le {Y P : Subgroup G} (hYP : Y ≤ P) (hP : CharTwo P)
    (hR : pCoreOf 2 P ≤ Y) : CharTwo Y := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hP hYP hR

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_permute {T B U : Subgroup G} (hUT : U ≤ T)
    (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hTBU : T ≤ Subgroup.normalizer ((B ⊔ U : Subgroup G) : Set G)) {x : G} (hx : x ∈ T ⊔ B) :
    ∃ t ∈ T, ∃ b ∈ B, t * b = x := by
  have hsup : T ⊔ B = T ⊔ (U ⊔ B) := le_antisymm (sup_le_sup_left le_sup_right _)
    (sup_le le_sup_left (sup_le (hUT.trans le_sup_left) le_sup_right))
  rw [hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T (U ⊔ B)
    (by rw [sup_comm]; exact hTBU), Set.mem_mul] at hx
  obtain ⟨t, ht, y, hy, rfl⟩ := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left U B hBU, Set.mem_mul] at hy
  obtain ⟨u, hu, b, hb, rfl⟩ := hy
  exact ⟨t * u, T.mul_mem ht (hUT hu), b, hb, by group⟩

theorem card_sup_of_permute {T B U : Subgroup G} (hT2 : IsPGroup 2 T) (hB9 : Nat.card B = 9)
    (hUT : U ≤ T) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hTBU : T ≤ Subgroup.normalizer ((B ⊔ U : Subgroup G) : Set G)) :
    Nat.card (T ⊔ B : Subgroup G) = Nat.card T * 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 U := hT2.to_le hUT
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hBU
  have hUB : U ⊓ B = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hk, hB9]
      exact Nat.Coprime.pow_left _ (by norm_num))).eq_bot
  rw [hUB, Subgroup.card_bot, mul_one, hB9, hk] at h1
  have hTn : T ≤ Subgroup.normalizer ((U ⊔ B : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hTBU
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTn
  have hI : (U ⊔ B) ⊓ T = U := by
    have hle : U ≤ (U ⊔ B) ⊓ T := le_inf le_sup_left hUT
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hp : IsPGroup 2 ((U ⊔ B) ⊓ T : Subgroup G) := hT2.to_le inf_le_right
    obtain ⟨a, ha⟩ := hp.exists_card_eq
    have hdvd : Nat.card ((U ⊔ B) ⊓ T : Subgroup G) ∣ 2 ^ k * 9 := by
      rw [← h1]
      exact Subgroup.card_dvd_of_le inf_le_left
    rw [ha] at hdvd ⊢
    rw [hk]
    have h29 : Nat.Coprime (2 ^ a) 9 := Nat.Coprime.pow_left _ (by norm_num)
    exact Nat.le_of_dvd (by positivity) (h29.dvd_of_dvd_mul_right hdvd)
  have hsup : U ⊔ B ⊔ T = T ⊔ B := le_antisymm
    (sup_le (sup_le (hUT.trans le_sup_left) le_sup_right) le_sup_left)
    (sup_le le_sup_right (le_sup_right.trans le_sup_left))
  rw [hI, hsup, h1, hk] at h2
  have hpos : 0 < 2 ^ k := by positivity
  have : Nat.card (T ⊔ B : Subgroup G) * 2 ^ k = Nat.card T * 9 * 2 ^ k := by
    rw [h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem two_of_three_normalized {T B U : Subgroup G} (hT2 : IsPGroup 2 T)
    (hBel : IsElemAbelian 3 B) (hB9 : Nat.card B = 9) (hUT : U ≤ T)
    (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hTBU : T ≤ Subgroup.normalizer ((B ⊔ U : Subgroup G) : Set G)) (hchar : CharTwo (T ⊔ B))
    (hQ8 : ∃ Q : Subgroup (MulAut B),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (B : Set G))).map B.normalizerMonoidHom ∧
      Nonempty (Q ≃* QuaternionGroup 2)) :
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := T ⊔ B with hXdef
  have hTX : T ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXc : Nat.card X = Nat.card T * 9 := card_sup_of_permute hT2 hB9 hUT hBU hTBU
  have hTc : Nat.card (T.subgroupOf X) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv
  have hBc : Nat.card (B.subgroupOf X) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv, hB9]
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hT'p : IsPGroup 2 (T.subgroupOf X) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hB'p : IsPGroup 3 (B.subgroupOf X) := IsPGroup.of_card (n := 2) (by rw [hBc]; norm_num)
  have hTidx : ¬ 2 ∣ (T.subgroupOf X).index := by
    have h := (T.subgroupOf X).index_mul_card
    rw [hTc, hXc] at h
    have : (T.subgroupOf X).index = 9 :=
      Nat.eq_of_mul_eq_mul_right hTpos (h.trans (mul_comm _ _))
    rw [this]
    norm_num
  have hBidx : ¬ 3 ∣ (B.subgroupOf X).index := by
    have h := (B.subgroupOf X).index_mul_card
    rw [hBc, hXc] at h
    have : (B.subgroupOf X).index = Nat.card T := Nat.eq_of_mul_eq_mul_right (by norm_num) h
    rw [this]
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  obtain ⟨S₂, hS₂⟩ : ∃ S : Sylow 2 ↥X, (S : Subgroup ↥X) = T.subgroupOf X :=
    ⟨hT'p.toSylow hTidx, IsPGroup.toSylow_coe _ _⟩
  obtain ⟨S₃, hS₃⟩ : ∃ S : Sylow 3 ↥X, (S : Subgroup ↥X) = B.subgroupOf X :=
    ⟨hB'p.toSylow hBidx, IsPGroup.toSylow_coe _ _⟩
  have hTB : ((S₂ : Subgroup ↥X) : Set ↥X) * ((S₃ : Subgroup ↥X) : Set ↥X) = Set.univ := by
    rw [hS₂, hS₃]
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨t, ht, b, hb, he⟩ := exists_mul_of_mem_sup_of_permute hUT hBU hTBU x.2
    exact Set.mem_mul.mpr ⟨⟨t, hTX ht⟩, Subgroup.mem_subgroupOf.mpr ht, ⟨b, hBX hb⟩,
      Subgroup.mem_subgroupOf.mpr hb, Subtype.ext he⟩
  have hBel' : CFSG.Assembly.IsElemAbelian 3 (S₃ : Subgroup ↥X) := by
    rw [hS₃]
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · show ((a : ↥X) : G) * ((b : ↥X) : G) = ((b : ↥X) : G) * ((a : ↥X) : G)
      exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩)
    · simpa using hBel.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hB9' : Nat.card (S₃ : Subgroup ↥X) = 9 := by rw [hS₃, hBc]
  have hF : CFSG.generalizedFitting ↥X = CFSG.pCore 2 ↥X :=
    generalizedFitting_eq_pCore_of_charTwo hchar
  have hQ8' : ∃ K : Subgroup (MulAut (S₃ : Subgroup ↥X)),
      K ≤ ((S₂ : Subgroup ↥X).subgroupOf
        (Subgroup.normalizer ((S₃ : Subgroup ↥X) : Set ↥X))).map
          (S₃ : Subgroup ↥X).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2) := by
    have key : ∀ S S' : Subgroup ↥X, S = T.subgroupOf X → S' = B.subgroupOf X →
        ∃ K : Subgroup (MulAut S'), K ≤ (S.subgroupOf
          (Subgroup.normalizer (S' : Set ↥X))).map S'.normalizerMonoidHom ∧
          Nonempty (K ≃* QuaternionGroup 2) := by
      intro S S' hS hS'
      subst hS hS'
      obtain ⟨Q, hQle, ⟨eQ⟩⟩ := hQ8
      let φ : ↥(B.subgroupOf X) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBX
      let Ψ : MulAut ↥B ≃* MulAut ↥(B.subgroupOf X) := MulAut.congr φ.symm
      refine ⟨Q.map Ψ.toMonoidHom, ?_,
        ⟨(Subgroup.equivMapOfInjective Q Ψ.toMonoidHom Ψ.injective).symm.trans eQ⟩⟩
      rintro _ ⟨σ, hσ, rfl⟩
      obtain ⟨⟨n, hnN⟩, hnT, rfl⟩ := hQle hσ
      have hnT' : n ∈ T := Subgroup.mem_subgroupOf.mp hnT
      have hnX : n ∈ X := hTX hnT'
      have hnN' : (⟨n, hnX⟩ : ↥X) ∈
          Subgroup.normalizer ((B.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hBX]
        exact Subgroup.mem_subgroupOf.mpr hnN
      refine ⟨⟨⟨n, hnX⟩, hnN'⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hnT'),
        ?_⟩
      ext y
      rfl
    exact key _ _ hS₂ hS₃
  have h := CFSG.RankThree.PartTwo.Sec3.rank3II_3_17 S₂ S₃ hTB hBel' hB9' hF hQ8'
  have hZ : ∀ S : Subgroup ↥X, S = T.subgroupOf X →
      ((CFSG.omegaOneCenter (⊤ : Subgroup ↥S)).map S.subtype).Normal →
      B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) := by
    intro S hS hN
    subst hS
    have h1 := le_normalizer_map_subtype_of_normal hN
    rw [CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.map_omegaOneCenter_top_subgroupOf hTX] at h1
    exact hBX.trans h1
  have hJ : ∀ S : Subgroup ↥X, S = T.subgroupOf X →
      ((CFSG.higherElemThompson ↥S 0).map S.subtype).Normal →
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G) := by
    intro S hS hN
    subst hS
    have h1 := le_normalizer_map_subtype_of_normal hN
    rw [CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.map_higherElemThompson_subgroupOf hTX] at h1
    exact hBX.trans h1
  have hE : ∀ S : Subgroup ↥X, S = T.subgroupOf X →
      ((CFSG.higherElemThompsonOmega ↥S 1).map S.subtype).Normal →
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G) := by
    intro S hS hN
    subst hS
    have h1 := le_normalizer_map_subtype_of_normal hN
    rw [CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.map_higherElemThompsonOmega_subgroupOf hTX]
      at h1
    exact hBX.trans h1
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
  · exact Or.inl ⟨hZ _ hS₂ h1, hJ _ hS₂ h2⟩
  · exact Or.inr (Or.inl ⟨hZ _ hS₂ h1, hE _ hS₂ h2⟩)
  · exact Or.inr (Or.inr ⟨hJ _ hS₂ h1, hE _ hS₂ h2⟩)

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.two_of_three_normalized_of_nine
    [D2Amb3 G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {T B : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) (hBHM : B ≤ H ⊓ M)
    (hBel : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBU : B ≤ Subgroup.normalizer ((T ⊓ GLBPrimeCore 3 (H ⊓ M) : Subgroup G) : Set G))
    (hTBU : T ≤ Subgroup.normalizer
      ((B ⊔ (T ⊓ GLBPrimeCore 3 (H ⊓ M)) : Subgroup G) : Set G)) :
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.omegaOneCenter (⊤ : Subgroup ↥T)).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) ∨
    (B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompson ↥T 0).map T.subtype : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        (((CFSG.higherElemThompsonOmega ↥T 1).map T.subtype : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hBH : B ≤ H := hBHM.trans inf_le_left
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hHc : CharTwo H := (D2Amb3.glob (G := G)).charTwo H hc.esc.maxTwoLocal_H.1
  have hO2 : pCoreOf 2 H ≤ T := by
    have hO2p : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    have hO2W : pCoreOf 2 H ≤ GLBPrimeCore 3 H := by
      refine le_glbPrimeCore (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) ?_
      obtain ⟨k, hk⟩ := hO2p.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hO2HM : pCoreOf 2 H ≤ H ⊓ M :=
      le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hO2W.trans hc.esc.primeCore_le)
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2HM
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) hO2p
    exact hle.trans (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hchar : CharTwo (T ⊔ B) :=
    charTwo_of_le_of_pCoreOf_le (sup_le hTH hBH) hHc (hO2.trans le_sup_left)
  exact CFSG.AGLEmbeddingD2.Tits.MsidePrelim.two_of_three_normalized hT.2.1 hBel hB9 inf_le_left
    hBU hTBU hchar
    (D2L34BetaConf3.exists_quaternion_le_autIn_of_nine hc hR9 hT hBHM hBp hB9 hBU hTBU)

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
