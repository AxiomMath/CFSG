module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem card_le_card_of_isSylowTwoOf {T K U : Subgroup G} (hT : IsSylowTwoOf T K) (hUK : U ≤ K)
    (hU : IsPGroup 2 U) : Nat.card U ≤ Nat.card T := by
  have hT' : IsPGroup 2 (T.subgroupOf K) := hT.2.1.comap_subtype
  have h := card_le_card_map_sylow (hT'.toSylow hT.2.2) hU hUK
  rwa [IsPGroup.toSylow_coe, Subgroup.map_subgroupOf_eq_of_le hT.1] at h

theorem isSylowTwoOf_eq_of_le {T K U : Subgroup G} (hT : IsSylowTwoOf T K) (hUK : U ≤ K)
    (hU : IsPGroup 2 U) (hTU : T ≤ U) : U = T :=
  (Subgroup.eq_of_le_of_card_ge hTU (card_le_card_of_isSylowTwoOf hT hUK hU)).symm

theorem le_of_isSylowTwoOf_of_le_normalizer {T K S : Subgroup G} (hT : IsSylowTwoOf T K)
    (hSK : S ≤ K) (hS : IsPGroup 2 S) (hKS : K ≤ Subgroup.normalizer (S : Set G)) : S ≤ T :=
  le_sup_left.trans (isSylowTwoOf_eq_of_le hT (sup_le hSK hT.1)
    (IsPGroup.to_sup_of_normal_left' hS hT.2.1 (hT.1.trans hKS)) le_sup_right).le

theorem isSylowTwoOf_of_forall_normalizer_le {T M : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (h : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → T ≤ U →
      U ≤ Subgroup.normalizer (T : Set G) → U ≤ T) :
    IsSylowTwoOf T M := by
  obtain ⟨Q, hQ⟩ := (hT.comap_subtype (K := M)).exists_le_sylow
  have hQM : (Q : Subgroup M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hQ2 : IsPGroup 2 ((Q : Subgroup M).map M.subtype) := Q.isPGroup'.map _
  have hTQ : T ≤ (Q : Subgroup M).map M.subtype := fun x hx => ⟨⟨x, hTM hx⟩, hQ hx, rfl⟩
  have hsyl : IsSylowTwoOf ((Q : Subgroup M).map M.subtype) M := by
    refine ⟨hQM, hQ2, ?_⟩
    change ¬ 2 ∣ (Subgroup.comap M.subtype ((Q : Subgroup M).map M.subtype)).index
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact Sylow.not_dvd_index Q
  rcases eq_or_lt_of_le hTQ with heq | hlt
  · rwa [heq]
  · obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_not_mem_of_lt_of_isPGroup hQ2 hlt
    exact absurd (h _ (inf_le_left.trans hQM) (hQ2.to_le inf_le_left)
      (le_inf hTQ Subgroup.le_normalizer) inf_le_right ⟨hxQ, hxN⟩) hxT

omit [Finite G] in
theorem le_normalizer_omegaOneCenterOf_of_le_normalizer {T U : Subgroup G}
    (hU : U ≤ Subgroup.normalizer (T : Set G)) :
    U ≤ Subgroup.normalizer (omegaOneCenterOf T : Set G) := by
  have := QuasithinUnique.Setup.characteristic_omegaOneCenterOf T
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((omegaOneCenterOf T).subgroupOf T)
  rw [Subgroup.map_subgroupOf_eq_of_le (QuasithinUnique.Setup.omegaOneCenterOf_le T)] at h
  exact hU.trans h

omit [Finite G] in
theorem omegaOneCenterOf_le_of_le_centralizer {S T : Subgroup G} (hST : S ≤ T)
    (hT : T ≤ Subgroup.centralizer (omegaOneCenterOf S : Set G)) :
    omegaOneCenterOf S ≤ omegaOneCenterOf T :=
  Subgroup.closure_mono fun x hx => ⟨⟨hST hx.1.1, Subgroup.mem_centralizer_iff.mpr fun _ ht =>
    (Subgroup.mem_centralizer_iff.mp (hT ht) x (Subgroup.subset_closure hx)).symm⟩, hx.2⟩

omit [Finite G] in
theorem omegaOneCenterOf_le_of_inf_centralizer_le {S T : Subgroup G} (hST : S ≤ T)
    (hC : T ⊓ Subgroup.centralizer (S : Set G) ≤ S) :
    omegaOneCenterOf T ≤ omegaOneCenterOf S :=
  Subgroup.closure_mono fun _ hx =>
    ⟨⟨hC ⟨hx.1.1, Subgroup.centralizer_le hST hx.1.2⟩, Subgroup.centralizer_le hST hx.1.2⟩, hx.2⟩

end Sylow

section Escape

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R T : Subgroup G}

theorem D1Escape.twoCore_le_of_isSylowTwoOf_inf (h : D1Escape p P M H R)
    (hT : IsSylowTwoOf T (H ⊓ M)) : pCoreOf 2 H ≤ T :=
  le_of_isSylowTwoOf_of_le_normalizer hT (_root_.le_inf (pCoreOf_le 2 H) h.twoCore_le)
    (pCoreOf_isPGroup 2 H) (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 H))

theorem D1Escape.omegaOneCenter_le_of_isSylowTwoOf_inf (h : D1Escape p P M H R)
    (hchar : IsCharTwoType G) (hT : IsSylowTwoOf T (H ⊓ M)) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 H) :=
  omegaOneCenterOf_le_of_inf_centralizer_le (h.twoCore_le_of_isSylowTwoOf_inf hT)
    ((inf_le_inf_right _ (hT.1.trans inf_le_left)).trans (hchar H h.maxTwoLocal_H.1))

end Escape

section PhaseThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

theorem D1PhaseThree.timmesfeldE_of_le_centralizer (h : D1PhaseThree p P M H R) :
    ∀ T : Subgroup G, IsSylowTwoOf T (H ⊓ M) →
      T ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) →
      IsSylowTwoOf T M ∧ omegaOneCenterOf T = omegaOneCenterOf (pCoreOf 2 H) ∧
        TimmesfeldE M H := by
  intro T hT hTC
  have heq : omegaOneCenterOf T = omegaOneCenterOf (pCoreOf 2 H) :=
    le_antisymm (h.omegaOneCenter_le_of_isSylowTwoOf_inf h.glob.charTwo hT)
      (omegaOneCenterOf_le_of_le_centralizer (h.twoCore_le_of_isSylowTwoOf_inf hT) hTC)
  have hNZ := h.normalizer_thompsonJ_eq.2
  have hTM : IsSylowTwoOf T M := by
    refine isSylowTwoOf_of_forall_normalizer_le (hT.1.trans inf_le_right) hT.2.1
      fun U hUM hU hTU hUN => (isSylowTwoOf_eq_of_le hT (_root_.le_inf ?_ hUM) hU hTU).le
    rw [← hNZ, ← heq]
    exact le_normalizer_omegaOneCenterOf_of_le_normalizer hUN
  exact ⟨hTM, heq, omegaOneCenterOf (pCoreOf 2 H), T,
    QuasithinUnique.Setup.omegaOneCenterOf_ne_bot (pCoreOf_isPGroup 2 H) h.twoCore_H_ne_bot,
    hTM, heq.ge, (QuasithinUnique.Setup.omegaOneCenterOf_le _).trans (pCoreOf_le 2 H), hNZ.ge⟩

theorem D1PhaseThree.weakSBlock_type_of_timmesfeldE (h : D1PhaseThree p P M H R)
    (h34 : Timmesfeld34) (he : TimmesfeldE M H) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IsSLSpG2Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
      IsParabolicTwo (barM M L) (barM M (L ⊓ (H ⊓ M))) := by
  obtain ⟨Z, T, hZ1, hTM, hZT, -, hHZ⟩ := he
  have hNZ : Subgroup.normalizer (Z : Set G) = H :=
    maxTwoLocal_normalizer_eq_of_le_normalizer h.maxTwoLocal_H hZ1
      (hTM.2.1.to_le (hZT.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T))) hHZ
  have hA : TimmesfeldHypA M Z (pCoreOf 2 H) :=
    { kGroup := h.isKGroup.1
      charTwo := h.charTwo.1
      center := ⟨T, hTM, hZT⟩
      ne_bot := hZ1
      le_normalizer := by
        rw [hNZ, h.normalizer_twoCore_H]
        exact inf_le_right
      le_core := h.twoCore_M_le h.twoCore_inf
      core_le := by rw [hNZ, inf_comm, h.twoCore_inf]
      cgs := by
        rw [hNZ]
        exact h.cgsIn_eq
      lt := by
        rw [hNZ, inf_comm]
        exact h.inf_lt_right }
  obtain ⟨-, hSL, -, hpar⟩ := h34 G M Z (pCoreOf 2 H) L hA hL.toIsTwoPrimeComponent
    fun hle => hL.not_le_normalizer (hle.trans (hNZ.trans h.normalizer_twoCore_H.symm).le)
  have hLHM : L ⊓ (H ⊓ M) = L ⊓ Subgroup.normalizer (Z : Set G) := by
    rw [hNZ, ← inf_assoc]
    exact inf_of_le_left (inf_le_left.trans hL.le)
  refine ⟨hSL, ?_⟩
  rw [hLHM]
  exact hpar

structure D1Extremal2 (p : ℕ) (P : Sylow p G) (M H R : Subgroup G) : Prop
    extends D1Extremal p P M H R where
  extremal2 : ∀ H' : Subgroup G, IsTwoLocal H' → ¬ H' ≤ M → 3 ≤ Open.pRank p (H' ⊓ M) →
    (∃ X : Subgroup G, X ≤ H' ⊓ M ∧ IsPGroup p X ∧ Nat.card X = Nat.card R ∧
      Open.pRank p X = Open.pRank p R) →
    ∀ T : Subgroup G, T ≤ H' ⊓ M → IsPGroup 2 T →
      ∃ T₀ : Subgroup G, T₀ ≤ H ⊓ M ∧ IsPGroup 2 T₀ ∧ Nat.card T ≤ Nat.card T₀

theorem D1Extremal.exists_extremal2 (h : D1Extremal p P M H R) :
    ∃ H' R' : Subgroup G, D1Extremal2 p P M H' R' := by
  have : Fact p.Prime := ⟨h.prime⟩
  let 𝒮 : Set (Subgroup G) := {T | IsPGroup 2 T ∧ ∃ H' : Subgroup G, IsTwoLocal H' ∧
    ¬ H' ≤ M ∧ 3 ≤ Open.pRank p (H' ⊓ M) ∧
    (∃ X : Subgroup G, X ≤ H' ⊓ M ∧ IsPGroup p X ∧ Nat.card X = Nat.card R ∧
      Open.pRank p X = Open.pRank p R) ∧ T ≤ H' ⊓ M}
  obtain ⟨T, ⟨hT, H₁, hH₁, hH₁M, hH₁rank, ⟨X, hXH₁, hX, hXR, hXr⟩, hTH₁⟩, hmax⟩ :=
    𝒮.exists_max_image (fun T : Subgroup G => Nat.card T) 𝒮.toFinite
      ⟨⊥, IsPGroup.of_bot, H, h.maxTwoLocal_H.1, h.not_le, h.three_le_pRank_inf,
        ⟨R, h.le_inf, h.isPGroup, rfl, rfl⟩, bot_le⟩
  obtain ⟨K, hH₁K, hK⟩ := PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hH₁
  have hKM : ¬ K ≤ M := fun hle => hH₁M (hH₁K.trans hle)
  have hKrank : 3 ≤ Open.pRank p (K ⊓ M) :=
    hH₁rank.trans (PreuniquenessRankFour.Helpers.pRank_mono p h.prime (inf_le_inf_right M hH₁K))
  obtain ⟨Tp, hTpM, -, -⟩ :=
    PreuniquenessRankFour.Helpers.intersecting_local_has_contained_sylow p h.prime P h.sylow_le
      h.weakCore_le hKrank
  have hXK : X ≤ K := (hXH₁.trans inf_le_left).trans hH₁K
  have hcard : Nat.card ((Tp : Subgroup K).map K.subtype) = Nat.card R :=
    le_antisymm (h.extremal K hK.1 hKM hKrank _ (_root_.le_inf (Subgroup.map_subtype_le _) hTpM)
      (Tp.isPGroup'.map K.subtype))
      (hXR ▸ card_le_card_map_sylow Tp hX hXK)
  obtain ⟨TX, hTXle⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  have hXTX : X ≤ (TX : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXK]
    exact Subgroup.map_mono hTXle
  have hTXeq : (TX : Subgroup K).map K.subtype = X := by
    refine (Subgroup.eq_of_le_of_card_ge hXTX ?_).symm
    rw [Subgroup.card_map_of_injective K.subtype_injective, TX.card_eq_multiplicity,
      ← Tp.card_eq_multiplicity, ← Subgroup.card_map_of_injective K.subtype_injective, hcard,
      hXR]
  obtain ⟨m, hm⟩ := PreuniquenessRankFour.Helpers.exists_conjugate_le_sylow_of_le p P h.sylow_le
    (hXH₁.trans inf_le_right) hX
  let σ := MulAut.conj (m : G)
  have hσM : ∀ Y : Subgroup G, Y ≤ M → Y.map σ.toMonoidHom ≤ M := by
    rintro Y hY _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem m.2 (hY hy)) (M.inv_mem m.2)
  have hXσ : Nat.card (X.map σ.toMonoidHom) = Nat.card R := by
    rw [Subgroup.card_map_of_injective σ.injective, hXR]
  have hXσr : Open.pRank p (X.map σ.toMonoidHom) = Open.pRank p R := by
    rw [PreuniquenessRankFour.Helpers.pRank_map_of_injective p h.prime _ σ.injective, hXr]
  refine ⟨K.map σ.toMonoidHom, X.map σ.toMonoidHom,
    { prime := h.prime
      ne_two := h.ne_two
      sylow_le := h.sylow_le
      weakCore_le := h.weakCore_le
      maxTwoLocal_M := h.maxTwoLocal_M
      maxTwoLocal_H := glbIsMaxTwoLocal_map_mulAut hK σ
      le_H := Subgroup.map_mono hXK
      le_P := hm
      isSylow := ⟨sylowMapMulAut TX σ, by rw [map_subtype_sylowMapMulAut TX σ, hTXeq]⟩
      three_le_pRank := by
        rw [hXσr]
        exact h.three_le_pRank
      not_le := fun hle => hKM (le_of_map_conj_le m.2 hle)
      extremal := fun H' hH' hH'M hrank X' hX'H' hX' => by
        rw [hXσ]
        exact h.extremal H' hH' hH'M hrank X' hX'H' hX'
      extremal3 := fun H' hH' hH'M hrank X' hX'H' hX' hX'c => by
        rw [hXσr]
        exact h.extremal3 H' hH' hH'M hrank X' hX'H' hX' (hX'c.trans hXσ)
      extremal2 := fun H' hH' hH'M hrank ⟨X', hX'H', hX', hX'R, hX'r⟩ T' hT'H' hT' =>
        ⟨T.map σ.toMonoidHom,
          _root_.le_inf (Subgroup.map_mono ((hTH₁.trans inf_le_left).trans hH₁K))
            (hσM T (hTH₁.trans inf_le_right)),
          hT.map _, by
            rw [Subgroup.card_map_of_injective σ.injective]
            exact hmax T' ⟨hT', H', hH', hH'M, hrank,
              ⟨X', hX'H', hX', hX'R.trans hXσ, hX'r.trans hXσr⟩, hT'H'⟩⟩ }⟩

theorem D1PhaseThree.isSylowTwoOf_M_of_extremal2 (h : D1PhaseThree p P M H R)
    (h2 : D1Extremal2 p P M H R)
    (hC : ¬ H ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) ≤ M)
    (hR : R ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G)) :
    ∀ T : Subgroup G, IsSylowTwoOf T (H ⊓ M) → IsSylowTwoOf T M := by
  intro T hT
  have hCN : Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) ≤
      Subgroup.normalizer (omegaOneCenterOf T : Set G) :=
    (Subgroup.centralizer_le (h.omegaOneCenter_le_of_isSylowTwoOf_inf h.glob.charTwo hT)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hT1 : T ≠ ⊥ := fun hT1 => h.twoCore_H_ne_bot
    (eq_bot_iff.mpr (hT1 ▸ h.twoCore_le_of_isSylowTwoOf_inf hT))
  have hNY : IsTwoLocal (Subgroup.normalizer (omegaOneCenterOf T : Set G)) :=
    ⟨_, QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1,
      hT.2.1.to_le (QuasithinUnique.Setup.omegaOneCenterOf_le T), rfl⟩
  have hRN : R ≤ Subgroup.normalizer (omegaOneCenterOf T : Set G) ⊓ M :=
    _root_.le_inf (hR.trans hCN) h.le_M
  refine isSylowTwoOf_of_forall_normalizer_le (hT.1.trans inf_le_right) hT.2.1
    fun U hUM hU hTU hUN => ?_
  obtain ⟨T₀, hT₀, hT₀2, hcard⟩ := h2.extremal2 _ hNY
    (fun hle => hC ((inf_le_right.trans hCN).trans hle))
    (h.three_le_pRank.trans (PreuniquenessRankFour.Helpers.pRank_mono p h.prime hRN))
    ⟨R, hRN, h.isPGroup, rfl, rfl⟩ U
    (_root_.le_inf (le_normalizer_omegaOneCenterOf_of_le_normalizer hUN) hUM) hU
  exact (Subgroup.eq_of_le_of_card_ge hTU
    (hcard.trans (card_le_card_of_isSylowTwoOf hT hT₀ hT₀2))).ge

theorem D1PhaseThree.timmesfeldE_normalizer (h : D1PhaseThree p P M H R)
    (h2 : D1Extremal2 p P M H R)
    (hC : ¬ H ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) ≤ M)
    (hR : R ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G)) :
    ∀ T Y : Subgroup G, IsSylowTwoOf T (H ⊓ M) → Y ≠ ⊥ → Y ≤ omegaOneCenterOf T →
      GLBIsMaxTwoLocal (Subgroup.normalizer (Y : Set G)) →
      ¬ Subgroup.normalizer (Y : Set G) ≤ M ∧ R ≤ Subgroup.normalizer (Y : Set G) ∧
        TimmesfeldE M (Subgroup.normalizer (Y : Set G)) := by
  intro T Y hT hY hYT _
  have hCN : Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) ≤
      Subgroup.normalizer (Y : Set G) :=
    (Subgroup.centralizer_le
      (hYT.trans (h.omegaOneCenter_le_of_isSylowTwoOf_inf h.glob.charTwo hT))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact ⟨fun hle => hC ((inf_le_right.trans hCN).trans hle), hR.trans hCN,
    Y, T, hY, h.isSylowTwoOf_M_of_extremal2 h2 hC hR T hT, hYT, Subgroup.le_normalizer, le_rfl⟩

end PhaseThree

end CFSG.AGLEmbedding
