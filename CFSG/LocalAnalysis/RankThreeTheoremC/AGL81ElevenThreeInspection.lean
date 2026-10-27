module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenThreeInspectTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransv
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

@[expose] def SylAct {A : Type} [Group A] [Finite A] (P : Subgroup A) (b : A) : Prop :=
  Odd (orderOf b) ∧ b ∈ normalizer (P : Set A) ∧
    ∃ T : Subgroup A, T ≤ P ∧ IsPGroup 2 T ∧ b ∈ normalizer (T : Set A) ∧
      (T.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) ≤
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) ∧
      ¬ 2 ∣ ((T.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).relIndex
        (wSup (↥P ⧸ CFSG.pCore 2 ↥P))

@[expose] def TrivOnW {A : Type} [Group A] [Finite A] (P : Subgroup A) (b : A) : Prop :=
  ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) →
    b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P

@[expose] def KFactSylNormTriv : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (P : Subgroup A) (b : A),
    ((∃ (k : ℕ) (d : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) ∧
        Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      Nonempty (↥P ≃* Equiv.Perm (Fin 6)) ∨ Nonempty (↥P ≃* Equiv.Perm (Fin 3))) →
    SylAct P b → TrivOnW P b

@[expose] def KFactSylNormSym : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (P : Subgroup A) (b : A) (n : ℕ),
    Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* Equiv.Perm (Fin n)) → SylAct P b → ¬ TrivOnW P b →
    3 ∣ orderOf b ∧ n = 5

@[expose] def KFactSylNormSymProd : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (P : Subgroup A) (b : A) (r m : ℕ),
    Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin m)) → SylAct P b →
    ¬ TrivOnW P b → 3 ∣ orderOf b ∧ (r = 5 ∨ m = 5)

@[expose] def KFactParabolicSyl : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), Open.IsQuasisimple ↥Y →
    pCoreOf 2 Y = ⊥ → IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index →
    ∀ b : A, b ∈ normalizer (Y : Set A) → SylAct P b → TrivOnW P b

variable (G : Type) [Group G] [Finite G]

variable {G}

theorem mem_normalizer_inf {M H L : Subgroup G} (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal)
    {b : G} (hb : b ∈ H ⊓ M) : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  have hbL : b ∈ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLM).mp hLn hb.2
  rw [mem_normalizer_iff]
  intro x
  have h1 := (mem_normalizer_iff.mp (le_normalizer hb.1 : b ∈ normalizer (H : Set G)) x)
  have h2 := mem_normalizer_iff.mp hbL x
  exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩

theorem sylAct_of {M H L T : Subgroup G} (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {b : G}
    (hb : b ∈ H ⊓ M) (hbo : Odd (orderOf b)) (hTJ : T ≤ jZero H L) (hT2 : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.relIndex (jZero H L)) (hbT : b ∈ normalizer (T : Set G)) :
    SylAct (barM M (H ⊓ L)) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩) := by
  have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
  have hTX : T ≤ H ⊓ L := hTJ.trans (jZero_le H L)
  have hbX := mem_normalizer_inf hLM hLn hb
  refine ⟨hbo.of_dvd_nat
    ((orderOf_map_dvd _ _).trans (Subgroup.orderOf_coe (⟨b, hb.2⟩ : ↥M)).symm.dvd),
    mem_normalizer_barM hb.2 hbX, barM M T, map_mono fun x hx => hTX hx,
    (hT2.comap_of_injective M.subtype M.subtype_injective).map _,
    mem_normalizer_barM hb.2 hbT, ?_, ?_⟩
  all_goals
    have he : ((barM M T).subgroupOf (barM M (H ⊓ L))).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M (H ⊓ L)))) =
        (T.subgroupOf (H ⊓ L)).map (hatHom M (H ⊓ L) hXM) := by
      rw [← map_barHom_subgroupOf hTX hXM, map_map]
      rfl
    rw [he]
  · rw [← map_jZero_eq_wSup M H L hXM]
    exact map_mono fun x hx => hTJ hx
  · exact not_two_dvd_relIndex_map hXM hTJ hTi

theorem not_trivOnW_of {M H L : Subgroup G} (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal)
    {b : G} (hb : b ∈ H ⊓ M) {x : G} (hx : x ∈ jZero H L)
    (hbx : b * x * b⁻¹ * x⁻¹ ∉ pCoreOf 2 (jZero H L)) :
    ¬ TrivOnW (barM M (H ⊓ L)) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb.2⟩) := by
  have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
  obtain ⟨w, hw, hwW, hbw⟩ := exists_nontrivial_of_not_commutator hXM hb.2
    (mem_normalizer_inf hLM hLn hb) hx hbx
  exact fun h => hbw (h w hw hwW)

theorem altFive_quasisimple : CFSG.Open.IsQuasisimple (alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  have hcen : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hperf : commutator (alternatingGroup (Fin 5)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5))) with
      h0 | h1
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 5)) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h1
  refine ⟨hperf, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientBot (G := alternatingGroup (Fin 5)))).isSimpleGroup

theorem exists_member_altFive {M X : Subgroup G} (hX : X ≤ M)
    {C : Subgroup (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X))} (hCn : C.Normal)
    (eC : ↥C ≃* alternatingGroup (Fin 5)) :
    ∃ I₀ ∈ cZero X, Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* alternatingGroup (Fin 5)) := by
  have hCs : IsSubnormal C ⊤ := IsSubnormal.step le_top (hCn.subgroupOf ⊤) (IsSubnormal.refl ⊤)
  have hc : IsComponentOf C ⊤ :=
    ⟨le_top, hCs, CFSG.Open.IsQuasisimple.of_mulEquiv eC altFive_quasisimple⟩
  obtain ⟨I, hI, himg⟩ := CZeroLift.exists_cZero_of_component (hatHom M X hX)
    (hatHom_surjective M X hX) (isPGroup_ker_hatHom M X hX) (pCore_hat_eq_bot M X) hc
  have hCO := CZeroLift.pCore_eq_bot_of_isSubnormal hCs (pCore_hat_eq_bot M X)
  obtain ⟨-, ⟨e⟩⟩ := CZeroLift.pCore_eq_and_equiv (hatHom M X hX) hI.le
    (isPGroup_ker_hatHom M X hX) (by rw [himg]; exact hCO)
  exact ⟨I, hI, ⟨(e.trans (MulEquiv.subgroupCongr himg)).trans eC⟩⟩

theorem exists_altFive_of_symFive {Q : Type} [Group Q] (e : Q ≃* Equiv.Perm (Fin 5)) :
    ∃ C : Subgroup Q, C.Normal ∧ Nonempty (↥C ≃* alternatingGroup (Fin 5)) :=
  ⟨(alternatingGroup (Fin 5)).map e.symm.toMonoidHom,
    (alternatingGroup.normal (α := Fin 5)).map _ e.symm.surjective,
    ⟨(equivMapOfInjective (alternatingGroup (Fin 5)) e.symm.toMonoidHom e.symm.injective).symm⟩⟩

theorem exists_altFive_of_symFive_prod {Q : Type} [Group Q] {m : ℕ}
    (e : Q ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin m)) :
    ∃ C : Subgroup Q, C.Normal ∧ Nonempty (↥C ≃* alternatingGroup (Fin 5)) := by
  haveI : (alternatingGroup (Fin 5)).Normal := alternatingGroup.normal
  set D : Subgroup (Equiv.Perm (Fin 5) × Equiv.Perm (Fin m)) :=
    (alternatingGroup (Fin 5)).prod ⊥ with hD
  refine ⟨D.map e.symm.toMonoidHom, (Subgroup.prod_normal _ _).map _ e.symm.surjective, ⟨?_⟩⟩
  exact ((equivMapOfInjective D e.symm.toMonoidHom e.symm.injective).symm.trans
    (Subgroup.prodEquiv _ _)).trans MulEquiv.prodUnique

theorem quotPCore_congr {M X X' : Subgroup G} (h : barM M X = barM M X') {T : Type} [Group T]
    (e : Nonempty (↥(barM M X') ⧸ CFSG.pCore 2 ↥(barM M X') ≃* T)) :
    Nonempty (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X) ≃* T) := by
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := nonempty_quotient_pCore_mulEquiv (MulEquiv.subgroupCongr h)
  exact ⟨e'.trans e⟩

theorem elevenThreeInspection_core (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (hPS : KFactParabolicSyl) (hTr : KFactSylNormTriv)
    (hSy : KFactSylNormSym) (hSyP : KFactSylNormSymProd) (hS : Setting G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {M H : Subgroup G} (hT : TwoLocalPhaseThree M H)
    (hMS : pCoreOf 2 M ≤ pCoreOf 2 H) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLn : (L.subgroupOf M).Normal) (hA7 : IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 7)))
    {B : Subgroup G} (hBHM : B ≤ H ⊓ M) (hB : IsPGroup p B) {T : Subgroup G}
    (hTJ : T ≤ jZero H L) (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.relIndex (jZero H L))
    (hBT : B ≤ normalizer (T : Set G))
    (heven : 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L)
    (hnt : ¬ (∀ b ∈ B, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))) :
    p = 3 ∧ (∃ N : ℕ, 10 ≤ N ∧ Even N ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin N))) ∧
    ∃ I₀ ∈ cZero (H ⊓ L), Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* alternatingGroup (Fin 5)) := by
  push Not at hnt
  obtain ⟨b, hb, x, hx, hbx⟩ := hnt
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, orderOf b = p ^ i := by
    obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
    have hdvd : orderOf b ∣ p ^ k := by
      refine orderOf_dvd_of_pow_eq_one ?_
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact ⟨i, hi⟩
  have hbo : Odd (orderOf b) := by rw [hi]; exact (hp.odd_of_ne_two hp2).pow
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLM : L ≤ M := hL.le
  have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
  have hbHM := hBHM hb
  have hsyl := sylAct_of hLM hLn hbHM hbo hTJ hT2 hTi (hBT hb)
  have hntr := not_trivOnW_of hLM hLn hbHM hx hbx
  have hk : L ⊓ pCoreOf 2 M ≤ H := fun y hy =>
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hMS hy.2)
  have hPY : barM M (H ⊓ L) ≤ barM M L := map_mono fun y hy => by
    rw [mem_subgroupOf] at hy ⊢
    exact hy.2
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hPP : barM M (H ⊓ L) = barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L) := by rw [hNS]
  have hbL : b ∈ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLM).mp hLn hbHM.2
  have hbLbar := mem_normalizer_barM (X := L) hbHM.2 hbL
  have hodd_abs : ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L → False :=
    fun h => h heven
  have hp3 : 3 ∣ orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbHM.2⟩) → p = 3 := by
    intro h3
    have h3b : 3 ∣ orderOf b := h3.trans
      ((orderOf_map_dvd _ _).trans (Subgroup.orderOf_coe (⟨b, hbHM.2⟩ : ↥M)).symm.dvd)
    rw [hi] at h3b
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3b)).symm
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 (hT.nineThree_not_one hK h85 hNX hL).1
  ·
    obtain ⟨hcl, hpar, -⟩ := h2
    rw [hNS] at hpar
    by_cases hWo : 2 ∣ (wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)))).index
    · exact absurd (hPS _ _ _ hL.component.2.2 (pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent)
        hcl hpar hWo _ hbLbar hsyl) hntr
    · exact (hodd_abs (not_two_dvd_relIndex_jZero hLM hk
        (not_two_dvd_relIndex_of_isParabolicTwo hpar) hWo)).elim
  ·
    have hX := (hT.nineThree_not_one hK h85 hNX hL).1
    have hSy2 := hT.not_isSylowTwoOf_inf hK h85 hNX hL
    obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ :=
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds G M
        (pCoreOf 2 H) L hK hA hL hX hSy2 h3
    set eP := MulEquiv.subgroupCongr (show barM M (H ⊓ L) = blockPL M (pCoreOf 2 H) L from hPP)
    have tr : ∀ {T' : Type} [Group T'], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ≃* T') →
        Nonempty (↥(barM M (H ⊓ L)) ≃* T') := fun ⟨e⟩ => ⟨eP.trans e⟩
    have triv : TrivOnW (barM M (H ⊓ L))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbHM.2⟩) ∨
        ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L := by
      rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · rcases hd' with hd' | hd' | ⟨rfl, hd'⟩
        · obtain ⟨d'', hd'', hP⟩ := hOrth m d ⟨q, hq, Or.inl hd'⟩ ⟨e⟩
          exact Or.inl (hTr _ _ _ (Or.inl ⟨m - 1, d'', hd'', quotPCore_congr hPP hP⟩) hsyl)
        · obtain ⟨d'', hd'', hP⟩ := hOrth m d ⟨q, hq, Or.inr hd'⟩ ⟨e⟩
          exact Or.inl (hTr _ _ _ (Or.inl ⟨m - 1, d'', hd'', quotPCore_congr hPP hP⟩) hsyl)
        · exact Or.inl (hTr _ _ _ (Or.inr (Or.inl (tr (hU4 d ⟨q, hq, hd'⟩ ⟨e⟩)))) hsyl)
      · rcases hn with rfl | rfl | rfl
        · exact Or.inl (hTr _ _ _ (Or.inr (Or.inr (tr (hA5 ⟨e⟩)))) hsyl)
        · right
          obtain ⟨e4⟩ := tr (hA6 ⟨e⟩)
          obtain ⟨h1, h2⟩ := altSix_sFour_odd hPY e e4
          exact not_two_dvd_relIndex_jZero hLM hk h1 h2
        · exact Or.inl (hTr _ _ _ (Or.inr (Or.inl (tr (hA8 ⟨e⟩)))) hsyl)
    rcases triv with h | h
    · exact (hntr h).elim
    · exact (hodd_abs h).elim
  ·
    obtain ⟨-, hZ, hA6, -, hS4⟩ := h4
    rw [hNS] at hS4
    obtain ⟨h1, h2⟩ := threeASix_odd hPY hZ hA6 hS4
    exact (hodd_abs (not_two_dvd_relIndex_jZero hLM hk h1 h2)).elim
  · exact (hA7.false h5.2.1.some).elim
  ·
    obtain ⟨-, n, ⟨eL⟩, hPn⟩ := h6
    obtain ⟨h3, rfl⟩ := hSy _ _ _ n (quotPCore_congr hPP hPn) hsyl hntr
    obtain ⟨e5⟩ := quotPCore_congr hPP hPn
    obtain ⟨C, hCn, ⟨eC⟩⟩ := exists_altFive_of_symFive e5
    exact ⟨hp3 h3, ⟨10, le_rfl, ⟨5, rfl⟩, ⟨eL⟩⟩, exists_member_altFive hXM hCn eC⟩
  ·
    obtain ⟨-, n, ⟨eL⟩, hPn⟩ := h7
    obtain ⟨h3, rfl⟩ := hSy _ _ _ n (quotPCore_congr hPP hPn) hsyl hntr
    obtain ⟨e5⟩ := quotPCore_congr hPP hPn
    obtain ⟨C, hCn, ⟨eC⟩⟩ := exists_altFive_of_symFive e5
    have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
      (by norm_num : 4 ≤ 4 * 5) eL
    exact ⟨hp3 h3, ⟨20, by norm_num, ⟨10, rfl⟩,
      ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans eL⟩⟩,
      exists_member_altFive hXM hCn eC⟩
  ·
    obtain ⟨-, N, r, hNe, h2r, h0, h2, h4', ⟨eL⟩, φ, -, -⟩ := h8
    obtain ⟨h3, hr⟩ := hSyP _ _ _ r (N - 2 * r) (quotPCore_congr hPP ⟨φ⟩) hsyl hntr
    have hr5 : r = 5 := by
      rcases hr with hr | hr
      · exact hr
      · obtain ⟨k, hk⟩ := hNe
        omega
    subst hr5
    obtain ⟨e5⟩ := quotPCore_congr hPP ⟨φ⟩
    obtain ⟨C, hCn, ⟨eC⟩⟩ := exists_altFive_of_symFive_prod e5
    have hN16 : 10 ≤ N := by omega
    have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
      (by omega : 4 ≤ N) eL
    exact ⟨hp3 h3, ⟨N, hN16, hNe,
      ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans eL⟩⟩,
      exists_member_altFive hXM hCn eC⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
