module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymplecticTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OrthPlus
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OrthMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.GTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Small
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SpTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenOneCZeroProof
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.Quasithin.SteinbergCDBestOffenderRestriction
public import CFSG.Quasithin.Vol2.Ch7Prop711Grp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding Subgroup TenThreeThree

theorem pCore_eq_bot_of_pCoreOf_eq_bot {A : Type} [Group A] {Y : Subgroup A}
    (hO : pCoreOf 2 Y = ⊥) : CFSG.pCore 2 ↥Y = ⊥ := by
  have hmap : (CFSG.pCore 2 ↥Y).map Y.subtype = ⊥ := by
    rw [← Open.pCoreOf]
    exact hO
  exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hmap

theorem index_wSup_eq_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (wSup Q).index = (wSup Q').index := by
  rw [← map_wSup_eq e]
  exact (Subgroup.index_map_equiv (wSup Q) e).symm

theorem nonempty_quotient_pCore_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Nonempty (Q ⧸ CFSG.pCore 2 Q ≃* Q' ⧸ CFSG.pCore 2 Q') :=
  ⟨QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)⟩

theorem index_pCore_eq_relIndex_pCoreOf {A : Type} [Group A] (P : Subgroup A) :
    (CFSG.pCore 2 ↥P).index = (pCoreOf 2 P).relIndex P := by
  have h : (pCoreOf 2 P).subgroupOf P = CFSG.pCore 2 ↥P := by
    change Subgroup.comap P.subtype (pCoreOf 2 P) = CFSG.pCore 2 ↥P
    rw [Open.pCoreOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  rw [Subgroup.relIndex, h]

theorem odd_relIndex_pCoreOf_of_le_normalizer {A : Type} [Group A] {T P Y : Subgroup A}
    (hT : IsSylowTwoOf T Y) (hTP : T ≤ P) (hPY : P ≤ Y)
    (hPN : P ≤ Subgroup.normalizer (T : Set A)) :
    ¬ 2 ∣ (pCoreOf 2 P).relIndex P ∧ ¬ 2 ∣ P.relIndex Y := by
  have hoddT : ¬ 2 ∣ T.relIndex Y := by
    change ¬ 2 ∣ (T.subgroupOf Y).index
    exact hT.2.2
  have hTleO : T ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTP hPN hT.2.1
  have hdvdTP : T.relIndex P ∣ T.relIndex Y := by
    rw [← Subgroup.relIndex_mul_relIndex T P Y hTP hPY]
    exact dvd_mul_right _ _
  refine ⟨?_, ?_⟩
  · exact fun h =>
      hoddT (h.trans ((Subgroup.relIndex_dvd_of_le_left P hTleO).trans hdvdTP))
  · exact fun h => hoddT (h.trans (Subgroup.relIndex_dvd_of_le_left Y hTP))

theorem isComponentOf_top_top_of_isQuasisimple {Q : Type} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : IsComponentOf (⊤ : Subgroup Q) ⊤ :=
  ⟨le_top, IsSubnormal.refl ⊤, CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hQ⟩

theorem card_center_top {Q : Type} [Group Q] :
    Nat.card (center ↥(⊤ : Subgroup Q)) = Nat.card (center Q) :=
  Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv

theorem nonempty_quotient_center_top {Q : Type} [Group Q] :
    Nonempty (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q) ≃* Q ⧸ center Q) :=
  ⟨QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)⟩

theorem isLieOf_quotient_center_top {Q : Type} [Group Q] {P : TauCeti.LieTypeIndex → Prop}
    (h : IsLieOf P (Q ⧸ center Q)) :
    IsLieOf P (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) := by
  obtain ⟨e⟩ := nonempty_quotient_center_top (Q := Q)
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.trans f⟩⟩

theorem not_isLieOf_quotient_center_top {Q : Type} [Group Q] {P : TauCeti.LieTypeIndex → Prop}
    (h : ¬ IsLieOf P (Q ⧸ center Q)) :
    ¬ IsLieOf P (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) := by
  intro h'
  apply h
  obtain ⟨e⟩ := nonempty_quotient_center_top (Q := Q)
  obtain ⟨d, hd, ⟨f⟩⟩ := h'
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem isClassicalTwoOrG2_quotient_center_top {Q : Type} [Group Q]
    (h : IsClassicalTwoOrG2 (Q ⧸ center Q)) :
    IsClassicalTwoOrG2 (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) := by
  obtain ⟨e⟩ := nonempty_quotient_center_top (Q := Q)
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.trans f⟩⟩)

theorem odd_card_center_of_pCoreOf_eq_bot {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hO : pCoreOf 2 Y = ⊥) : Odd (Nat.card (center ↥Y)) :=
  CFSG.Quasithin.SteinbergCD.odd_card_center_of_pCore_eq_bot
    (pCore_eq_bot_of_pCoreOf_eq_bot hO)

theorem parabolic_cases {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : CFSG.Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hcl : IsClassicalTwoOrG2 (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) :
    P = Y ∨ (∃ T : Subgroup A, IsSylowTwoOf T Y ∧ P = Y ⊓ normalizer (T : Set A)) ∨
      CompParab (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
  classical
  obtain ⟨hPY, T, hT, hNT⟩ := hP
  by_cases hPeqY : P = Y
  · exact Or.inl hPeqY
  by_cases hBorel : ∃ T : Subgroup A, IsSylowTwoOf T Y ∧ P = Y ⊓ normalizer (T : Set A)
  · exact Or.inr (Or.inl hBorel)
  refine Or.inr (Or.inr ?_)
  have hodd : Odd (Nat.card (center ↥(⊤ : Subgroup ↥Y))) := by
    rw [card_center_top]
    exact odd_card_center_of_pCoreOf_eq_bot hO
  have hcomp : IsComponentOf (⊤ : Subgroup ↥Y) ⊤ :=
    isComponentOf_top_top_of_isQuasisimple hY
  have htype : IsClassicalTwoOrG2 (↥(⊤ : Subgroup ↥Y) ⧸ center ↥(⊤ : Subgroup ↥Y)) :=
    isClassicalTwoOrG2_quotient_center_top (Q := ↥Y) hcl
  have hparab : IsParabolicTwo (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
    refine ⟨le_top, T.subgroupOf Y, CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT, ?_⟩
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) := by
      simpa using hx
    have hN : Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) =
        (Subgroup.normalizer (T : Set A)).comap Y.subtype := by
      have h := Subgroup.comap_normalizer_eq_of_le_range (f := Y.subtype) (H := T)
        (by rw [Subgroup.range_subtype]; exact hT.1)
      rw [Subgroup.comap_subtype] at h
      exact h.symm
    have hxT : (x : A) ∈ Subgroup.normalizer (T : Set A) := by
      have : x ∈ (Subgroup.normalizer (T : Set A)).comap Y.subtype := hN ▸ hxN
      exact this
    exact Subgroup.mem_subgroupOf.mpr (hNT ⟨x.2, hxT⟩)
  have hne_top : P.subgroupOf Y ≠ ⊤ := by
    intro htop
    exact hPeqY (le_antisymm hPY (Subgroup.subgroupOf_eq_top.mp htop))
  have hne_borel : ∀ T' : Subgroup ↥Y, IsSylowTwoOf T' ⊤ →
      P.subgroupOf Y ≠ ⊤ ⊓ Subgroup.normalizer (T' : Set ↥Y) := by
    intro T' hT' hEq
    apply hBorel
    let T0 : Subgroup A := T'.map Y.subtype
    have hT0 : IsSylowTwoOf T0 Y := by
      refine ⟨Subgroup.map_subtype_le _, hT'.2.1.map Y.subtype, ?_⟩
      have hidx : (T'.subgroupOf ⊤).index = T'.index := by
        change T'.relIndex ⊤ = T'.index
        rw [Subgroup.relIndex_top_right]
      rw [show T0.subgroupOf Y = T' from
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective T', ← hidx]
      exact hT'.2.2
    have hN : Subgroup.normalizer (T' : Set ↥Y) =
        (Subgroup.normalizer (T0 : Set A)).comap Y.subtype := by
      have hcomap : Subgroup.comap Y.subtype T0 = T' :=
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective T'
      have h := Subgroup.comap_normalizer_eq_of_le_range (f := Y.subtype) (H := T0)
        (Subgroup.map_le_range Y.subtype T')
      rw [hcomap] at h
      exact h.symm
    have hPmap : (P.subgroupOf Y).map Y.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPY]
    refine ⟨T0, hT0, ?_⟩
    rw [← hPmap, hEq, top_inf_eq, hN, Subgroup.map_comap_eq, Subgroup.range_subtype]
  exact ⟨hcomp, htype, hodd, hparab, hne_top, hne_borel⟩

theorem exists_mulEquiv_statedSp_of_isQuasisimple (hZ : OddCenterRest) {A : Type} [Group A]
    [Finite A] {Y : Subgroup A} (hY : CFSG.Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hB2 : IsLieOf IdxBTwo (↥Y ⧸ center ↥Y)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 3 ≤ r ∧
      Nat.card K = 2 ∧ Nonempty (↥Y ≃* CFSG.Open.StatedSp r K) := by
  have hcomp := isComponentOf_top_top_of_isQuasisimple hY
  have hodd : Odd (Nat.card (center ↥(⊤ : Subgroup ↥Y))) := by
    rw [card_center_top]
    exact odd_card_center_of_pCoreOf_eq_bot hO
  have hB2' : IsLieOf IdxBTwo
      (↥(⊤ : Subgroup ↥Y) ⧸ center ↥(⊤ : Subgroup ↥Y)) :=
    isLieOf_quotient_center_top (Q := ↥Y) hB2
  obtain ⟨r, K, hKf, hKfin, hKchar, hr, hK2, ⟨f⟩⟩ :=
    exists_mulEquiv_statedSp_of_idxBTwo hZ hcomp hodd hB2'
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hr3 : 3 ≤ r := by
    rcases Nat.eq_or_lt_of_le hr with h2 | h2
    · subst r
      have hperfSp : Group.IsPerfect ↥(StatedSp 2 K) := by
        haveI : Group.IsPerfect ↥Y := Group.isPerfect_def.mpr hY.1
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.topEquiv.symm.trans f).toMonoidHom)
          (Subgroup.topEquiv.symm.trans f).surjective
      exact absurd hperfSp (CFSG.Quasithin.H13.Prop711.not_isPerfect_statedSp_two hK2)
    · omega
  exact ⟨r, K, hKf, hKfin, hKchar, hr3, hK2, ⟨Subgroup.topEquiv.symm.trans f⟩⟩

theorem isSpTwoLeviProduct_of_parabolic (hZ : OddCenterRest) {A : Type} [Group A] [Finite A]
    {Y P : Subgroup A} (hY : CFSG.Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hB2 : IsLieOf IdxBTwo (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) :
    IsSpTwoLeviProduct ↥P := by
  classical
  have hcl : IsClassicalTwoOrG2 (↥Y ⧸ center ↥Y) := by
    obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hB2
    cases d with
    | B r q =>
      have hc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
      have hdvd : q.p ∣ 2 := by
        have h' : q.p ∣ q.p ^ q.exponent :=
          dvd_pow_self q.p (TauCeti.PrimePower.exponent_pos q).ne'
        rwa [← hc, hd] at h'
      have hp2 : q.p = 2 :=
        ((Nat.Prime.dvd_iff_eq Nat.prime_two q.prime_p.ne_one).mp hdvd).symm
      exact Or.inl ⟨⟨_, hv⟩, hp2, ⟨e⟩⟩
    | _ => exact hd.elim
  rcases parabolic_cases hY hO hcl hP with hPY | ⟨T, hT, hPNeq⟩ | hCP
  · subst P
    obtain ⟨r, K, hKf, hKfin, hKchar, hr, hK2, ⟨e⟩⟩ :=
      exists_mulEquiv_statedSp_of_isQuasisimple hZ hY hO hB2
    letI : Field K := hKf
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    have hpc := pCore_eq_bot_of_pCoreOf_eq_bot hO
    have hquot : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    refine ⟨1, fun _ => StatedSp r K, fun _ => inferInstance, fun _ => inferInstance, ?_⟩
    refine ⟨⟨hquot.trans
      (e.trans (MulEquiv.piUnique (fun _ : Fin 1 => StatedSp r K)).symm)⟩, ?_⟩
    intro i
    exact (statedSp_isSpTwoFactor hK2).1
  ·
    obtain ⟨r, K, hKf, hKfin, hKchar, hr, hK2, ⟨e⟩⟩ :=
      exists_mulEquiv_statedSp_of_isQuasisimple hZ hY hO hB2
    letI : Field K := hKf
    letI : Finite K := hKfin
    letI : CharP K 2 := hKchar
    have hself : ∀ S : Sylow 2 ↥Y,
        normalizer ((S : Subgroup ↥Y) : Set ↥Y) = (S : Subgroup ↥Y) :=
      forall_sylow_normalizer_eq_of_mulEquiv e.symm
        (fun S => normalizer_sylow_statedSp_eq_self (m := r) hK2 (by omega) S)
    obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.mp hT
    have hScoe : (S : Subgroup ↥Y) = T.subgroupOf Y := by
      rw [← Subgroup.comap_map_eq_self_of_injective Y.subtype_injective (S : Subgroup ↥Y),
        hS, Subgroup.comap_subtype]
    have hTP : T ≤ P := by
      rw [hPNeq]
      exact fun x hx => ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hnorm : Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) = T.subgroupOf Y := by
      rw [← hScoe]
      exact hself S
    have hNcomap : Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) =
        (Subgroup.normalizer (T : Set A)).comap Y.subtype := by
      have h := Subgroup.comap_normalizer_eq_of_le_range (f := Y.subtype) (H := T)
        (by rw [Subgroup.range_subtype]; exact hT.1)
      rw [Subgroup.comap_subtype] at h
      exact h.symm
    have hmapN : Subgroup.map Y.subtype
        (Subgroup.normalizer (T.subgroupOf Y : Set ↥Y)) = T := by
      rw [hnorm, Subgroup.map_subgroupOf_eq_of_le hT.1]
    have hPeqT : P = T := by
      rw [hPNeq, inf_comm]
      calc Subgroup.normalizer (T : Set A) ⊓ Y
          = Subgroup.map Y.subtype
              (Subgroup.normalizer (T.subgroupOf Y : Set ↥Y)) := by
            rw [hNcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
        _ = T := hmapN
    have hP2 : IsPGroup 2 P := by
      rw [hPeqT]
      exact hT.2.1
    have hpc_top : CFSG.pCore 2 ↥P = ⊤ := by
      refine top_unique ?_
      exact le_sSup ⟨inferInstance, hP2.of_equiv Subgroup.topEquiv.symm⟩
    haveI : Subsingleton (↥P ⧸ CFSG.pCore 2 ↥P) := by
      rw [hpc_top]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton (Fin 0 → PUnit) := inferInstance
    refine ⟨0, fun _ => PUnit, fun _ => inferInstance, fun _ => inferInstance, ?_⟩
    refine ⟨⟨MulEquiv.ofBijective
      (1 : (↥P ⧸ CFSG.pCore 2 ↥P) →* (Fin 0 → PUnit))
      ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨1, Subsingleton.elim _ _⟩⟩⟩, ?_⟩
    intro i
    exact i.elim0
  · exact IsSpTwoLeviProduct.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.1)
      (isSpTwoLeviProduct_idxBTwo hZ hCP (isLieOf_quotient_center_top (Q := ↥Y) hB2))


theorem not_two_dvd_index_wSup_of_compParab (hGA : GriessAllModelsStatement) {X : Type}
    [Group X] [Finite X] {L J : Subgroup X} (hCP : CompParab L J)
    (hB2 : ¬ IsLieOf IdxBTwo (↥L ⧸ center ↥L)) :
    ¬ 2 ∣ (wSup (↥J ⧸ CFSG.pCore 2 ↥J)).index := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  · exact (hasLeviCensus_idxA hGA hCP h).not_two_dvd_index_wSup
  · exact (hasLeviCensus_idxTwistedA hCP h).not_two_dvd_index_wSup
  · rcases isLieOf_idxB_cases h with h | h
    · exact absurd h hB2
    · exact (hasLeviCensus_idxBBig hZ hCP h).not_two_dvd_index_wSup
  · exact (hasLeviCensus_idxD hZ hCP h).not_two_dvd_index_wSup
  · exact (hasLeviCensus_idxTwistedD hZ hCP h).not_two_dvd_index_wSup
  · exact (hasLeviCensus_idxG2 hGA hCP h).not_two_dvd_index_wSup
  · exact not_two_dvd_index_wSup_small hCP h

theorem not_two_dvd_index_wSup_of_parabolic (hGA : GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] {Y P : Subgroup A} (hY : CFSG.Open.IsQuasisimple ↥Y)
    (hO : pCoreOf 2 Y = ⊥) (hcl : IsClassicalTwoOrG2 (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P)
    (hB2 : ¬ IsLieOf IdxBTwo (↥Y ⧸ center ↥Y)) :
    ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index := by
  classical
  rcases parabolic_cases hY hO hcl hP with hPY | ⟨T, hT, hPNeq⟩ | hCP
  · subst P
    have hpc := pCore_eq_bot_of_pCoreOf_eq_bot hO
    have hquot : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    rw [index_wSup_eq_of_mulEquiv hquot]
    exact not_two_dvd_index_wSup_of_isQuasisimple hY
  ·
    have hTP : T ≤ P := by
      rw [hPNeq]
      exact fun x hx => ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hPN : P ≤ Subgroup.normalizer (T : Set A) := by
      rw [hPNeq]
      exact inf_le_right
    obtain ⟨hoddO, -⟩ := odd_relIndex_pCoreOf_of_le_normalizer hT hTP hP.1 hPN
    have hcard : ¬ 2 ∣ Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) := by
      rw [← Subgroup.index_eq_card, index_pCore_eq_relIndex_pCoreOf]
      exact hoddO
    exact not_two_dvd_index_wSup_of_odd hcard
  ·
    have hB2' := not_isLieOf_quotient_center_top (Q := ↥Y) hB2
    have hodd := not_two_dvd_index_wSup_of_compParab hGA hCP hB2'
    obtain ⟨eq⟩ := nonempty_quotient_pCore_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.1)
    rw [← index_wSup_eq_of_mulEquiv eq]
    exact hodd

theorem kFactParabolicLeviMember_of_griess (hGA : GriessAllModelsStatement) :
    TenOneCZero.KFactParabolicLeviMember := by
  intro A _ _ Y P hY hO hcl hP hS
  classical
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  rcases parabolic_cases hY hO hcl hP with hPY | ⟨T, hT, hPNeq⟩ | hCP
  ·
    subst P
    have hpc := pCore_eq_bot_of_pCoreOf_eq_bot hO
    have hquot : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    exact CFSG.LocalAnalysis.RankThreeTheoremC.TenOneCZero.HasWGen.of_mulEquiv hquot
      ⟨⊤, IsSubnormal.refl ⊤, Or.inl (isComponentOf_top_top_of_isQuasisimple hY)⟩
  ·
    have hTP : T ≤ P := by
      rw [hPNeq]
      exact fun x hx => ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hPN : P ≤ Subgroup.normalizer (T : Set A) := by
      rw [hPNeq]
      exact inf_le_right
    obtain ⟨hoddO, hoddP⟩ := odd_relIndex_pCoreOf_of_le_normalizer hT hTP hP.1 hPN
    have hOleP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
    have hO2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
    have hidx : ¬ 2 ∣ ((pCoreOf 2 P).subgroupOf Y).index := by
      change ¬ 2 ∣ (pCoreOf 2 P).relIndex Y
      rw [← Subgroup.relIndex_mul_relIndex (pCoreOf 2 P) P Y hOleP hP.1]
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
      · exact hoddO h'
      · exact hoddP h'
    exact absurd ⟨hOleP.trans hP.1, hO2, hidx⟩ hS
  ·
    have hPkeep : IsParabolicTwo Y P := hP
    obtain ⟨hPYle, T, hT, hNT⟩ := hP
    have hTP : T ≤ P := fun x hx => hNT ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hoddT : ¬ 2 ∣ T.relIndex Y := by
      change ¬ 2 ∣ (T.subgroupOf Y).index
      exact hT.2.2
    have hoddP : ¬ 2 ∣ P.relIndex Y := fun h =>
      hoddT (h.trans (Subgroup.relIndex_dvd_of_le_left Y hTP))
    have hOleP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
    have hO2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
    have heven : 2 ∣ Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) := by
      by_contra h2
      have hcard_eq : Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) = (pCoreOf 2 P).relIndex P := by
        rw [← Subgroup.index_eq_card, index_pCore_eq_relIndex_pCoreOf]
      have hoddO : ¬ 2 ∣ (pCoreOf 2 P).relIndex P := by
        rwa [← hcard_eq]
      have hidx : ¬ 2 ∣ ((pCoreOf 2 P).subgroupOf Y).index := by
        change ¬ 2 ∣ (pCoreOf 2 P).relIndex Y
        rw [← Subgroup.relIndex_mul_relIndex (pCoreOf 2 P) P Y hOleP hPYle]
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
        · exact hoddO h'
        · exact hoddP h'
      exact hS ⟨hOleP.trans hPYle, hO2, hidx⟩
    by_cases hB2 : IsLieOf IdxBTwo (↥Y ⧸ center ↥Y)
    · exact (isSpTwoLeviProduct_of_parabolic hZ hY hO hB2 hPkeep).exists_wGen heven
    · exact exists_wGen_of_not_two_dvd_index
        (not_two_dvd_index_wSup_of_parabolic hGA hY hO hcl hPkeep hB2) heven

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
