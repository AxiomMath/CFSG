module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsL34Index (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q

@[expose] def KFactL34Outer : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ A : Subgroup X, IsElemAbelian 3 A → Nat.card A = 3 ^ 2 → ¬ A ≤ K → GLBCore 3 1 A = ⊤

@[expose] def KFactL34Inner : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ A : Subgroup X, IsElemAbelian 3 A → Nat.card A = 3 ^ 2 → A ≤ K →
        ∀ Y : Subgroup X, Subgroup.normalizer (A : Set X) ≤ Y →
          Y = Subgroup.normalizer (A : Set X) ∨ Y = ⊤

@[expose] def KFactL34NormalizerSolvable : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ A : Subgroup K, Nat.card A = 3 ^ 2 → Group.IsSolvable (Subgroup.normalizer (A : Set K))

@[expose] def D2OnlyL34At {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) :
    Prop :=
  ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → D2EscapeMax 3 P M R' →
    ∀ (Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)),
      (Rbar' : Subgroup _) = (R'.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (H' ⧸ primeComplementCore (G := H') 3) Rbar'
        ((A'.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore 3)))
        (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore 3))) K' →
      ∃ d' : TauCeti.ValidLieTypeIndex, IsL34Index d' ∧
        Nonempty (K' ≃* (TauCeti.CFSGIndex.lie d').Group)

@[expose] def D2OnlyL34Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G → 3 ∈ GLBBetaFour G →
    ∀ (P : Sylow 3 G) (M : Subgroup G), D2OnlyL34At P M

@[expose] def D2L34BetaCase : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (P : Sylow 3 G) (M A H R : Subgroup G), D2Escape 3 P M A H R →
    D2EscapeMax 3 P M R → 3 ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K →
      ¬ Subgroup.centralizer
          (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
            Set (H ⧸ primeComplementCore (G := H) 3)) ≤
        (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2OnlyL34At P M → False

theorem D2AlmostSimple.false_of_glbCore_one_eq_top {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (h : GLBCore p 1 A = ⊤) : False := by
  refine hK.ne_top (eq_top_iff.mpr (h ▸ ?_))
  refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 1 A X₀).mpr fun Q hQA hrank => ?_
  refine hK.normalizer_le_of_le_A Q hQA fun hQ => ?_
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hK.prime Q
  rw [hQ, le_bot_iff] at hE
  rw [hE, Subgroup.card_bot] at hEcard
  have := Nat.one_lt_pow (by omega : Open.pRank p Q ≠ 0) hK.prime.one_lt
  omega

theorem D2AlmostSimple.eq_normalizer_of_l34 (hI : KFactL34Inner) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple 3 X R A X₀ K) (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : A ≤ K) : X₀ = Subgroup.normalizer (A : Set X) := by
  have hAne : A ≠ ⊥ := by
    intro hA
    have hc := hK.card_A
    rw [hA, Subgroup.card_bot] at hc
    norm_num at hc
  have hNX₀ : Subgroup.normalizer (A : Set X) ≤ X₀ := hK.normalizer_le_of_le_A A le_rfl hAne
  rcases hI d hd X K hK.normal hK.centralizer_eq_bot he A hK.elem hK.card_A hAK X₀ hNX₀ with
    hX | hX
  · exact hX
  · exact absurd hX hK.ne_top

theorem primeComplementCore_eq_bot_of_l34 (hI : KFactL34Inner) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple 3 X R A X₀ K) (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : A ≤ K) (hC : Subgroup.centralizer (A : Set X) ≤ A) :
    primeComplementCore (G := X₀) 3 = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAne : A ≠ ⊥ := by
    intro hA
    have hc := hK.card_A
    rw [hA, Subgroup.card_bot] at hc
    norm_num at hc
  have hNX₀ : Subgroup.normalizer (A : Set X) ≤ X₀ := hK.normalizer_le_of_le_A A le_rfl hAne
  have hX₀ : X₀ = Subgroup.normalizer (A : Set X) := by
    rcases hI d hd X K hK.normal hK.centralizer_eq_bot he A hK.elem hK.card_A hAK X₀ hNX₀ with
      hX | hX
    · exact hX
    · exact absurd hX hK.ne_top
  subst hX₀
  have hAp : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by simpa using hK.elem.2 x x.2)⟩
  exact primeComplementCore_normalizer_eq_bot hAp hC

theorem D2AlmostSimple.le_of_l34 (hO : KFactL34Outer) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple 3 X R A X₀ K) (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    A ≤ K := by
  by_contra hAK
  exact hK.false_of_glbCore_one_eq_top
    (hO d hd _ K hK.normal hK.centralizer_eq_bot he _ hK.elem hK.card_A hAK)

theorem D2Escape.not_centralizer_le_of_l34 (hI : KFactL34Inner) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hS : D2PairStrongThree) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {G : Type} [Group G] [Finite G] (hglob : D2Global G) (hD1 : D1For G)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hesc : D2Escape 3 P M A H R)
    (hmax : D2EscapeMax 3 P M R) (hβ : 3 ∈ GLBBetaFour G)
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K) :
    ¬ Subgroup.centralizer
        (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) ≤
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) := by
  intro hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU := primeComplementCore_eq_bot_of_l34 hI hd hK he hAK hC
  have hpr : AGLPair 3 M H R := hesc.toPair hglob.toAGLGlobal
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
  have hsolv := isSolvable_normalizer_of_card_eq_nine_of_le hK.card_A hC
  rw [← hK.eq_normalizer_of_l34 hI hd he hAK] at hsolv
  exact hS G hglob hD1 P M A H R hesc hmax hβ hpr
    (hesc.stronglyEmbedded_of_pair hglob hβ hpr h84 (hD2.noXBlockFor hglob.toD1Global))
    (d2PerfectThreePrime_of_isSolvable hsolv)

theorem d2IndexCaseAt_l34_three (hO : KFactL34Outer) (hI : KFactL34Inner) (hβ : D2L34BetaCase)
    (hOnly : D2OnlyL34Three) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hS : D2PairStrongThree) (d : TauCeti.ValidLieTypeIndex) (hd : IsL34Index d) :
    D2IndexCaseAt (.lie d) fun p => p = 3 := by
  intro G _ _ hglob hD1 p hp3 P M A H R hesc hmax hβ4 Rbar K hRbar hK he
  subst hp3
  have hAK := hK.le_of_l34 hO hd he
  exact hβ d hd G hglob hD1 P M A H R hesc hmax hβ4 Rbar K hRbar hK he hAK
    (hesc.not_centralizer_le_of_l34 hI h84 hD2 hS hd hglob hD1 hmax hβ4 hK he hAK)
    (hOnly G hglob hD1 hβ4 P M)

end CFSG.AGLEmbeddingD2
