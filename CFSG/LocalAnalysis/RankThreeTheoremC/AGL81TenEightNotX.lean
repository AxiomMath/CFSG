module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenNormIOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightEscape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightNineSeventeen
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightNineTwelve
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightComponents
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34NoRem
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.Quasithin.Background.C41PfE
import CFSG.LocalAnalysis.GLTheoremA.S8.Close
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem aglCovers_d1KBar_of_pComponent_le {p : ℕ} [Fact p.Prime] {M H N : Subgroup G}
    (hY : ∀ Y : Subgroup G, RankThreeUC.AGL81C.IsPComponentIn p Y H → ¬ Y ≤ M → Y ≤ N) :
    AGLCovers p H N (d1KBar p M H) := by
  unfold AGLCovers d1KBar
  refine iSup₂_le fun L hL => ?_
  obtain ⟨Y', hY', hYL⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent
    p (isComponent_of_isComponentOf_top'' hL.1)
  have hYL' : Y'.map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = L := hYL
  have hYY : (Y'.map H.subtype).subgroupOf H = Y' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hYM : ¬ Y'.map H.subtype ≤ M := by
    intro hle
    apply hL.2
    rw [← hYL']
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨y.2, hle ⟨y, hy, rfl⟩⟩, rfl⟩
  have hYN : Y'.map H.subtype ≤ N :=
    hY (Y'.map H.subtype) ⟨Subgroup.map_subtype_le _, by rw [hYY]; exact hY'⟩ hYM
  rw [← hYL']
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, ⟨y.2, hYN ⟨y, hy, rfl⟩⟩, rfl⟩

theorem not_le_d1PlusCore_of_cover
    (h31 : KFactThreeOne) (h75 : KFactSevenFive) (hR1 : KFactNineThreeListRankOne)
    (hSyl : KFactCaseTwoSylowAut) (hSch : KFactCatalogSchreier) (h74 : AGL81SevenFourTwo)
    (hOutC : KFactOutCyclic) (hR2 : KFactNineThreeRankTwo)
    (hSchF : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hsec : KFactNineThreeAutSection) (hK342 : TenThirteen.KFactThreeFourTwo)
    (hclaim : AGL81TenTenClaimCfg G) (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h1031 : AGL81TenThreeOneAt G) (h105 : AGL81TenFiveXCfg G) (hS : Setting G)
    {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hNL : ¬ (L.subgroupOf M).Normal)
    {I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero (H ⊓ L))
    (hExcl : ∀ m ∈ M, ∀ (q : ℕ) (iK iJ : TauCeti.CFSGIndex),
      TenThirteen.IsThreeFourPair q iK iJ →
      ∀ f : ↥(L.map (MulAut.conj m).toMonoidHom) →* iJ.Group, ¬ Function.Surjective f)
    (hNorm : ∀ m ∈ M,
      normalizer ((L.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤ M) :
    ¬ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K := by
  intro hIX
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  haveI : Fact p.Prime := ⟨he.prime⟩
  set I := CFSG.ComponentClassification.AS76b.oUpperTwo I₀ with hIdef
  obtain ⟨-, hMH, hHM⟩ := hd.nineEightFour' hS h984
  have hT := hd.toTwoLocalPhaseThree' hS h984
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hVI : pCoreOf 2 H ≤ normalizer (I : Set G) :=
    pCoreOf_le_normalizer_oUpperTwo hL hI₀ hHM hNH
  have hgen : I ≤ closure {x : G | x ∈ I ∧ Odd (orderOf x)} := by
    have h := NoRem.oUpperTwo_idem I₀
    calc I = CFSG.ComponentClassification.AS76b.oUpperTwo I := h.symm
      _ ≤ _ := le_rfl
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hIH : I ≤ H := (oUpperTwo_le_self I₀).trans hI₀H
  have hIL : I ≤ L := (oUpperTwo_le_self I₀).trans (hI₀.le.trans inf_le_right)
  obtain ⟨m, hm, hne⟩ : ∃ m ∈ M, L.map (MulAut.conj m).toMonoidHom ≠ L := by
    by_contra hcon
    push Not at hcon
    apply hNL
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hcon g g.2
    rw [← h]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  set L' := L.map (MulAut.conj m).toMonoidHom with hL'
  have hL'N : L' ≤ normalizer (I : Set G) := by
    intro g hg
    refine TenTenNotX.mem_normalizer_of_commutator_mem hgen (hMH.trans hVI)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) fun x hx => ?_
    have h := TenTenNormI.commutator_mem_of_ne hL.toIsTwoPrimeComponent hm hne x (hIL hx) g hg
    have h' := (pCoreOf 2 M).inv_mem h
    have e : (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ := by group
    rwa [e] at h'
  have h3 : 3 ∣ Nat.card I := h1031 hS p P M H Q K hd L hL I₀ hI₀
  have hO2 : pCoreOf 2 I ≠ ⊥ := by
    intro hbot
    have hcen : I ≤ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
      intro i hi
      refine ⟨hIH hi, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hvI : v * i⁻¹ * v⁻¹ ∈ I := by
        have := (Subgroup.mem_normalizer_iff.mp (hVI hv) i⁻¹).mp (I.inv_mem hi)
        exact this
      have hc1 : i * (v * i⁻¹ * v⁻¹) ∈ I := I.mul_mem hi hvI
      have hc2 : i * v * i⁻¹ * v⁻¹ ∈ pCoreOf 2 H := by
        have := (Subgroup.mem_normalizer_iff.mp
          (localGroup_le_normalizer_pCoreOf 2 H (hIH hi)) v).mp hv
        exact (pCoreOf 2 H).mul_mem this ((pCoreOf 2 H).inv_mem hv)
      have hnormal : ((I ⊓ pCoreOf 2 H).subgroupOf I).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
        intro j hj
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hj) y
        have h2 := Subgroup.mem_normalizer_iff.mp
          (localGroup_le_normalizer_pCoreOf 2 H (hIH hj)) y
        exact (Subgroup.mem_inf.trans (and_congr h1 h2)).trans Subgroup.mem_inf.symm
      have hle := normal_pGroup_le_pCoreOf 2 (I ⊓ pCoreOf 2 H) I inf_le_left hnormal
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
      rw [hbot] at hle
      have h1 : i * v * i⁻¹ * v⁻¹ = 1 := by
        have e : i * (v * i⁻¹ * v⁻¹) = i * v * i⁻¹ * v⁻¹ := by group
        exact (Subgroup.mem_bot.mp (hle ⟨e ▸ hc1, hc2⟩))
      have : v * i = i * v := by
        have := mul_inv_eq_one.mp h1
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      exact this
    have hI2 : I ≤ pCoreOf 2 H := hcen.trans (hS.charTwo H hd.maxH.1)
    have h2 : IsPGroup 2 I := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hI2
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 I : Set G)) :=
    ⟨pCoreOf 2 I, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I, rfl⟩
  obtain ⟨N, hN, hNN⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le hloc
  have hIN : normalizer (I : Set G) ≤ N :=
    (normalizer_localGroup_le_normalizer_pCoreOf 2 I).trans hNN
  obtain ⟨Q₀, hQ₀, hQ₀N⟩ := hclaim hS p P M H Q K hd L hL hNL I₀ hI₀
  have hQ₀N' : Q₀ ≤ N := hQ₀N.trans hIN
  have hL'NN : L' ≤ N := hL'N.trans hIN
  have hNtop : N ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hS.simple hS.nonab hN.1
  have hHtop : H ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hS.simple hS.nonab hd.maxH.1
  have hS1 : ∀ Y : Subgroup G, RankThreeUC.AGL81C.IsPComponentIn p Y H → ¬ Y ≤ M →
      Y ≤ normalizer (I : Set G) := by
    intro Y hY hYM y hy
    exact TenTenNotX.mem_normalizer_of_commutator_mem hgen hVI
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (h105 hS p P M H Q K hd L hL I₀ hI₀ hIX Y hY hYM y hy)
  obtain ⟨Y₀, hY₀, hY₀M⟩ := exists_pComponent_not_le_of_cfg hd
  have hNM : ¬ N ≤ M := fun h => hY₀M (((hS1 Y₀ hY₀ hY₀M).trans hIN).trans h)
  have hcov : AGLCovers p H N (d1KBar p M H) :=
    aglCovers_d1KBar_of_pComponent_le fun Y hY hYM => (hS1 Y hY hYM).trans hIN
  have hK : ¬ d1KBar p M H ≤ d1X0 p M H := hd.kbar ▸ hd.not_le_X0
  obtain ⟨L₁, hL₁c, hL₁X⟩ : ∃ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p),
      IsComponentOf L₁ ⊤ ∧ ¬ L₁ ≤ d1X0 p M H := by
    by_contra hno
    push Not at hno
    exact hK (iSup₂_le fun L hL => absurd (hno L hL.1) hL.2)
  have hKN : d1KBar p M N ≠ ⊥ :=
    d1KBar_ne_bot_of_cover h31 h75 hR1 hSyl hSch h74 hOutC hS hS.kProper he hd.base hd.le_H
      hQ₀ hQ₀N' hHtop hN hNM hL₁c hL₁X hcov
  have hin := kFactInputs_of_escape h31 h75 hR2 hS he hQ₀ hQ₀N' hNtop hKN
  have hL'c : IsTwoPrimeComponent M L' := IsTwoPrimeComponent.map_conj hm hL.toIsTwoPrimeComponent
  have hXM : d1PlusCore p N (d1KBar p M N) ≤ M := d1PlusCore_le_of_escape he hQ₀ hQ₀N' hKN
  have hL'X : L' ≤ d1PlusCore p N (d1KBar p M N) := by
    rcases le_d1PlusCore_or_pair hK342 hin hL'c hL'NN with h | ⟨iK, iJ, hpair, f, hf⟩
    · exact h
    · exact (hExcl m hm p iK iJ hpair f hf).elim
  have hinj : ∀ n : G, Function.Injective (MulAut.conj n).toMonoidHom :=
    fun n => (MulAut.conj n).injective
  by_cases hp3 : p = 3
  ·
    subst hp3
    have hL'X2 : IsTwoPrimeComponent (d1PlusCore 3 N (d1KBar 3 M N)) L' :=
      IsTwoPrimeComponent.of_le hL'c hL'X hXM
    have h3L' : 3 ∣ Nat.card L' := by
      rw [hL', Subgroup.card_map_of_injective (hinj m)]
      exact h3.trans (Subgroup.card_dvd_of_le hIL)
    have hXnorm : N ≤ normalizer (d1PlusCore 3 N (d1KBar 3 M N) : Set G) :=
      le_normalizer_d1PlusCore (d1KBar_normal_of_escape he hQ₀ hQ₀N' hKN)
    have hnorm : ∀ n ∈ N, L'.map (MulAut.conj n).toMonoidHom = L' := by
      intro n hn
      have hXn : (d1PlusCore 3 N (d1KBar 3 M N)).map (MulAut.conj n).toMonoidHom =
          d1PlusCore 3 N (d1KBar 3 M N) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXnorm hn)
      have hA : IsTwoPrimeComponent (d1PlusCore 3 N (d1KBar 3 M N))
          (L'.map (MulAut.conj n).toMonoidHom) := by
        have h := IsTwoPrimeComponent.map_mulAut hL'X2 (MulAut.conj n)
        rwa [hXn] at h
      by_contra hne
      have h3A : 3 ∣ Nat.card (L'.map (MulAut.conj n).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (hinj n)]
        exact h3L'
      have h2 := two_le_pRank_three_of_two_components hL'X2 hA (Ne.symm hne) h3L' h3A
      exact absurd (h2.trans (pRank_d1PlusCore_le_one_of_escape he hQ₀ hQ₀N' hKN))
        (by norm_num)
    have hNL' : N ≤ normalizer (L' : Set G) := fun n hn =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hnorm n hn)
    exact hNM (hNL'.trans (hNorm m hm))
  ·
    obtain ⟨Y', hY', hY'M⟩ := exists_pComponent_not_le_of_ne_bot hKN
    have hY'c := isTwoPrimeComponentIn_of_escape h31 h75 hSchF hsec hS he hQ₀ hQ₀N' hN hp3 hY' hY'M
    have hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M :=
      core_le_of_base (muAt_of_escape he) hQ₀ hQ₀N'
    obtain ⟨R, -, hRN, hR, S, hSR⟩ := exists_sylowBase he hQ₀ hQ₀N'
    haveI : (d1KBar p M N).Normal := d1KBar_normal_of_escape he hQ₀ hQ₀N' hKN
    have hsyl := sylowK_of_sylow (K := d1KBar p M N) S hSR
    have hb3 := (h98 hS p P M H₁ R₁ he N R hR hRN hN hNM hsyl).resolve_right (fun h => hp3 h.1)
    have hO2M : pCoreOf 2 N ≤ M := (h984 hS p P M H₁ R₁ he N R hR hRN hN hNM hsyl hb3).2.2
    have hLNM : L' ≤ N ⊓ M := le_inf hL'NN hL'c.le
    have hsubN : IsSubnormal L' (N ⊓ M) :=
      CFSG.AGLEmbeddingD2.isSubnormal_of_le_of_isSubnormal hL'c.subnormal hLNM inf_le_right
    have h2 : pCoreOf 2 (N ⊓ M) ≤ normalizer (L' : Set G) :=
      TenTenNormI.pCoreOf_le_normalizer hLNM hsubN hL'c.perfect
    have hPN : pCoreOf 2 N ≤ N ⊓ M := le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 N) hO2M
    have hnormalN : ((pCoreOf 2 N).subgroupOf (N ⊓ M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr
        (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 N))
    have h1 : pCoreOf 2 N ≤ pCoreOf 2 (N ⊓ M) :=
      normal_pGroup_le_pCoreOf 2 (pCoreOf 2 N) (N ⊓ M) hPN hnormalN
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    have hRN' : pCoreOf 2 N ≤ normalizer (L' : Set G) := h1.trans h2
    have hY'N : Y' ≤ normalizer (L' : Set G) := by
      intro y hy
      have hle : L'.map (MulAut.conj y).toMonoidHom ≤ L' := by
        have hperf : ⁅L'.map (MulAut.conj y).toMonoidHom, L'.map (MulAut.conj y).toMonoidHom⁆ =
            L'.map (MulAut.conj y).toMonoidHom := by
          rw [← Subgroup.map_commutator, hL'c.perfect]
        have hPB : L'.map (MulAut.conj y).toMonoidHom ≤ L' ⊔ pCoreOf 2 N := by
          rintro _ ⟨x, hx, rfl⟩
          have hc := commutator_mem_pCoreOf_of_twoPrime he.prime hcore hY' hY'M hY'c
            (hL'X hx) hy
          have e : (MulAut.conj y).toMonoidHom x = (y * x * y⁻¹ * x⁻¹) * x := by
            show y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x
            group
          rw [e, sup_comm]
          exact Subgroup.mul_mem_sup hc hx
        exact CFSG.Quasithin.C41Pf.le_of_perfect_of_le_sup hRN'
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) hperf hPB
      have hcard : Nat.card L' ≤ Nat.card (L'.map (MulAut.conj y).toMonoidHom) :=
        (Subgroup.card_map_of_injective (hinj y)).symm.le
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard)
    exact hY'M (fun y hy => hNorm m hm (hY'N hy))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
