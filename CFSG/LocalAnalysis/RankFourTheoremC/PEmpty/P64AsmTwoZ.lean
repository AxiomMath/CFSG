module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmQuot
public import CFSG.LocalAnalysis.GL83PartI.I_6_10

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU CFSG.AGLEmbedding
  Subgroup

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem not_isCyclic_of_two_le_pRank (hp : p.Prime) {Q : Subgroup Z} (h2 : 2 ≤ Open.pRank p Q) :
    ¬ IsCyclic ↥Q := by
  intro hQc
  obtain ⟨E, hEQ, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank hp h2
  have hEcyc : IsCyclic ↥E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEQ).surjective
  exact not_isCyclic_of_elemAbelian hp hE (by rw [hEc]) hEcyc

theorem normal_sSup_components :
    (sSup {M : Subgroup Z | IsComponentOf M ⊤}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : sSup {M : Subgroup Z | IsComponentOf M ⊤} ≤
      (sSup {M : Subgroup Z | IsComponentOf M ⊤}).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_conj hM g)
  exact hle hn

theorem two_le_pRank_inf_of_center (hp : p.Prime) (hp2 : p ≠ 2) (Q : Sylow p Z) {K : Subgroup Z}
    (hK : IsComponentOf K ⊤) (hdvd : p ∣ Nat.card (Subgroup.center ↥K)) :
    2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : K.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hK.2.1
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsub
  have hnonab := (GL83.I_6_10_1_proved ↥K hK.2.2 p hp hp2 hdvd P).1
  have hnc : ¬ IsCyclic ↥(P : Subgroup ↥K) := fun hc => hnonab (by
    haveI := hc
    infer_instance)
  have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp hp2 P.isPGroup' hnc
  rw [← hP, pRank_map_subtype hp.one_lt]
  exact h2

theorem two_le_pRank_of_two_components (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) {L K : Subgroup Z}
    (hL : IsComponentOf L ⊤) (hK : IsComponentOf K ⊤) (hLK : L ≠ K) :
    2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ sSup {M : Subgroup Z | IsComponentOf M ⊤}) := by
  obtain ⟨y₁, hy₁, hy₁o, hy₁c⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hL
  obtain ⟨y₂, hy₂, hy₂o, hy₂c⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hK
  have hp₁ : y₁ ^ p = 1 := by
    have := pow_orderOf_eq_one y₁
    rwa [hy₁o] at this
  have hp₂ : y₂ ^ p = 1 := by
    have := pow_orderOf_eq_one y₂
    rwa [hy₂o] at this
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_two_of_components hp hL hK hLK hy₁.2 hy₂.2 hp₁ hp₂
    hy₁c hy₂c
  have hLN : L ≤ sSup {M : Subgroup Z | IsComponentOf M ⊤} := le_sSup hL
  have hKN : K ≤ sSup {M : Subgroup Z | IsComponentOf M ⊤} := le_sSup hK
  have hle : zpowers y₁ ⊔ zpowers y₂ ≤
      (Q : Subgroup Z) ⊓ sSup {M : Subgroup Z | IsComponentOf M ⊤} :=
    sup_le (zpowers_le.mpr ⟨hy₁.1, hLN hy₁.2⟩) (zpowers_le.mpr ⟨hy₂.1, hKN hy₂.2⟩)
  exact SU1.le_pRank hp.one_lt hle hel (k := 2) hcard

theorem dvd_card_center_of_pCore_ne_bot (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z)
    (hZc : IsCyclic (center (Q : Subgroup Z))) {w : Z} (hwQ : w ∈ (Q : Subgroup Z))
    (hwo : orderOf w = p) (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q) {L : Subgroup Z}
    (hL : IsComponentOf L ⊤) (huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L)
    (hne : CFSG.pCore p Z ≠ ⊥) : p ∣ Nat.card (Subgroup.center ↥L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hLn : L.Normal := normal_of_unique_component hL huniq
  haveI : (CFSG.pCore p Z).Normal := CFSG.pCore_normal
  have hlayer : CFSG.layer Z = L := layer_eq_of_unique_component hL huniq
  have hwO : w ∈ CFSG.pCore p Z := w_mem_of_normal hp hp2 hZ Q hZc hwQ hwo hwc hne
  obtain ⟨y, hyQL, hyo, hyc⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hL
  have hLbot : L ≠ ⊥ := by
    intro h
    have hy : y ∈ L := hyQL.2
    rw [h, Subgroup.mem_bot] at hy
    obtain ⟨l, -, hl⟩ := hyc
    exact hl (by rw [hy]; simp)
  have hwL : w ∈ L := w_mem_of_normal hp hp2 hZ Q hZc hwQ hwo hwc hLbot
  have hwc' : w ∈ centralizer (L : Set Z) := by
    have := CFSG.WholeGroup.pCore_le_centralizer_layer (G := Z) p hwO
    rwa [hlayer] at this
  have hwcen : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hwc') g g.2)
  have hord : orderOf (⟨⟨w, hwL⟩, hwcen⟩ : ↥(Subgroup.center ↥L)) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hwo]
  have := orderOf_dvd_natCard (⟨⟨w, hwL⟩, hwcen⟩ : ↥(Subgroup.center ↥L))
  rwa [hord] at this

theorem caseII (hRank1 : KDI278Rank1) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcat : CatalogSimpleSections Z) (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z)
    (hZc : IsCyclic (center (Q : Subgroup Z))) {w : Z} (hwQ : w ∈ (Q : Subgroup Z))
    (hwo : orderOf w = p) (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q) {L : Subgroup Z}
    (hL : IsComponentOf L ⊤)
    (hnc : ∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
      a * b ≠ b * a)
    (hI : Open.pRank p ((Q : Subgroup Z) ⊓ sSup {M : Subgroup Z | IsComponentOf M ⊤}) ≤ 1) :
    False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L := by
    intro K hK
    by_contra hKL
    have := two_le_pRank_of_two_components hp hp2 hZ Q hL hK (Ne.symm hKL)
    omega
  haveI hLn : L.Normal := normal_of_unique_component hL huniq
  have hNL : sSup {M : Subgroup Z | IsComponentOf M ⊤} = L :=
    le_antisymm (sSup_le fun M hM => (huniq M hM).le) (le_sSup hL)
  have hIL : Open.pRank p ((Q : Subgroup Z) ⊓ L) ≤ 1 := by
    rw [hNL] at hI
    exact hI
  have hOp : CFSG.pCore p Z = ⊥ := by
    by_contra hne
    have hdvd := dvd_card_center_of_pCore_ne_bot hp hp2 hZ Q hZc hwQ hwo hwc hL huniq hne
    have h2 := two_le_pRank_inf_of_center hp hp2 Q hL hdvd
    omega
  have hcore : CFSG.pPrimeCore p Z = ⊥ := hZ
  have hcenL : Subgroup.center ↥L = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ths_center_eq_bot hp hOp hcore
      ((CFSG.isComponent_iff_open L).mpr hL)
  have hCL : centralizer (L : Set Z) = ⊥ :=
    centralizer_eq_bot_of_unique_component hL huniq hcenL hZ hOp
  have hsimple := isSimpleGroup_of_center_eq_bot hL hcenL
  have hcatL : IsCatalogGroup ↥L := hcat.simple_subgroup L hsimple.1 hsimple.2
  have hsubL : L.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hL.2.1
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsubL
  have hPrk : Open.pRank p (P : Subgroup ↥L) ≤ 1 := by
    rw [← pRank_map_subtype hp.one_lt, hP]
    exact hIL
  obtain ⟨a, ha, b, hb, hap, hbp, hab⟩ := hnc
  exact hab (hRank1 p hp hp5 Z L hLn hsimple.1 hsimple.2 hcatL hCL ⟨P, hPrk⟩ Q a ha b hb hap hbp)

theorem layer_eq_sSup_components :
    CFSG.layer Z = sSup {M : Subgroup Z | IsComponentOf M ⊤} := by
  rw [CFSG.layer.eq_sSup]
  congr 1
  ext K
  exact CFSG.isComponent_iff_open K

theorem w_mem_component (hp : p.Prime) (hp2 : p ≠ 2) (hZ : primeComplementCore (G := Z) p = ⊥)
    (Q : Sylow p Z) (hZc : IsCyclic (center (Q : Subgroup Z))) {w : Z}
    (hwQ : w ∈ (Q : Subgroup Z)) (hwo : orderOf w = p)
    (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q) {M : Subgroup Z} (hM : IsComponentOf M ⊤)
    (hQM : (Q : Subgroup Z) ≤ normalizer (M : Set Z)) : w ∈ M := by
  obtain ⟨y, hyQM, hyo, hyc⟩ := exists_mem_inf_sylow_component hp hp2 hZ Q hM
  have hne : (Q : Subgroup Z) ⊓ M ≠ ⊥ := by
    intro h
    have hy : y ∈ (Q : Subgroup Z) ⊓ M := hyQM
    rw [h, Subgroup.mem_bot] at hy
    obtain ⟨l, -, hl⟩ := hyc
    exact hl (by rw [hy]; simp)
  obtain ⟨z, hzU, hzo, hzc⟩ := exists_central_of_inf hp Q hQM hne
  exact (zpowers_le.mpr hzU.2)
    (mem_zpowers_of_central_of_cyclic hp hZc hzU.1 hzo hzc hwQ hwo hwc)

theorem caseI (hp : p.Prime) (hp5 : 5 ≤ p) (hZ : primeComplementCore (G := Z) p = ⊥)
    (Q : Sylow p Z) (hZc : IsCyclic (center (Q : Subgroup Z)))
    (hQrk : Open.pRank p (Q : Subgroup Z) ≤ 2) {w : Z} (hwQ : w ∈ (Q : Subgroup Z))
    (hwo : orderOf w = p) (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q) {Y : Subgroup Z}
    (hY : ¬ ⊤ ≤ Y)
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hwN : normalizer ((zpowers w : Subgroup Z) : Set Z) ≤ Y) {L : Subgroup Z}
    (hL : IsComponentOf L ⊤)
    (hI : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ sSup {M : Subgroup Z | IsComponentOf M ⊤})) :
    ∃ K : Subgroup Z, IsComponentOf K ⊤ ∧ K.Normal ∧
      (∀ M : Subgroup Z, IsComponentOf M ⊤ → M = K) ∧ Subgroup.center ↥K = ⊥ ∧
      centralizer (K : Set Z) = ⊥ ∧ ¬ K ≤ Y ∧ 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  haveI hNn : (sSup {M : Subgroup Z | IsComponentOf M ⊤}).Normal := normal_sSup_components
  have hNY : ¬ sSup {M : Subgroup Z | IsComponentOf M ⊤} ≤ Y := fun h =>
    hY (top_le_of_normal hp Q h hI hΓ2)
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  have hOp : CFSG.pCore p Z = ⊥ := by
    by_contra hne
    haveI : (CFSG.pCore p Z).Normal := CFSG.pCore_normal
    have hwO : w ∈ CFSG.pCore p Z := w_mem_of_normal hp hp2 hZ Q hZc hwQ hwo hwc hne
    apply hNY
    have hcent : w ∈ centralizer ((sSup {M : Subgroup Z | IsComponentOf M ⊤} : Subgroup Z) :
        Set Z) := by
      have := CFSG.WholeGroup.pCore_le_centralizer_layer (G := Z) p hwO
      rwa [layer_eq_sSup_components] at this
    intro n hn
    exact hwN (P64Free.mem_normalizer_zpowers_of_commute
      ((Subgroup.mem_centralizer_iff.mp hcent) n hn))
  have hcore : CFSG.pPrimeCore p Z = ⊥ := hZ
  have hcen : ∀ M : Subgroup Z, IsComponentOf M ⊤ → Subgroup.center ↥M = ⊥ := fun M hM =>
    CFSG.LocalAnalysis.RankThreeTheoremC.ths_center_eq_bot hp hOp hcore
      ((CFSG.isComponent_iff_open M).mpr hM)
  have hQnorm : ∀ M : Subgroup Z, IsComponentOf M ⊤ →
      (Q : Subgroup Z) ≤ normalizer (M : Set Z) := by
    intro M hM
    by_contra h
    obtain ⟨_, _, E, hEQ, hE, hEc, -⟩ := exists_cube_of_not_normalizes hp hp2 hZ Q hM h
    have := SU1.le_pRank hp.one_lt hEQ hE (k := 3) hEc
    omega
  have huniq : ∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L := by
    intro K hK
    by_contra hKL
    have hwL : w ∈ L := w_mem_component hp hp2 hZ Q hZc hwQ hwo hwc hL (hQnorm L hL)
    have hwK : w ∈ K := w_mem_component hp hp2 hZ Q hZc hwQ hwo hwc hK (hQnorm K hK)
    have hcenw : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (component_commute hL hK (Ne.symm hKL) g.2 hwK)
    rw [hcen L hL, Subgroup.mem_bot] at hcenw
    exact hw1 (congrArg Subtype.val hcenw)
  have hNL : sSup {M : Subgroup Z | IsComponentOf M ⊤} = L :=
    le_antisymm (sSup_le fun M hM => (huniq M hM).le) (le_sSup hL)
  refine ⟨L, hL, normal_of_unique_component hL huniq, huniq, hcen L hL,
    centralizer_eq_bot_of_unique_component hL huniq (hcen L hL) hZ hOp, ?_, ?_⟩
  · rw [hNL] at hNY
    exact hNY
  · rw [hNL] at hI
    exact hI

theorem dispatch (hAlt : KDI278Alt) (hChevP : KDI278ChevP) (hL2 : KDI278L2p2) (hL3 : KDI278L3)
    (hChevQ : KDI278ChevQ) (hSpor : KDI278Spor) (hSporB : KDI278SporB) (hSporC : KDI278SporC)
    (hI204 : KDL64I204U3) (hp : p.Prime) (hp5 : 5 ≤ p) (hcat : CatalogSimpleSections Z)
    (Q : Sylow p Z) (hrk : Open.pRank p (⊤ : Subgroup Z) ≤ 2)
    (hrk2 : Open.pRank p (⊤ : Subgroup Z) = 2) {B U : Subgroup Z} (hBel : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2) (hUQ : U ≤ Q) (hUel : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hBU : ∀ g : Z, B.map (MulAut.conj g).toMonoidHom ≠ U) {w : Z} (hwQ : w ∈ (Q : Subgroup Z))
    (hwo : orderOf w = p) (hwc : ∀ q ∈ (Q : Subgroup Z), q * w = w * q)
    (hw : ∀ w ∈ (Q : Subgroup Z), orderOf w = p → (∀ q ∈ (Q : Subgroup Z), q * w = w * q) →
      ∀ g : Z, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w)
    (hnc : ∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
      a * b ≠ b * a)
    {Y : Subgroup Z}
    (hΓU : ∀ S : Subgroup Z, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    {K : Subgroup Z} (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hcenK : Subgroup.center ↥K = ⊥)
    (hCK : centralizer (K : Set Z) = ⊥) (hKY : ¬ K ≤ Y)
    (hK2 : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ K)) :
    ∀ W : Subgroup Z, B ⊔ U ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
      W = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hsimple := isSimpleGroup_of_center_eq_bot hK hcenK
  have hcatK : IsCatalogGroup ↥K := hcat.simple_subgroup K hsimple.1 hsimple.2
  have hK2' : Open.pRank p (K : Subgroup Z) = 2 :=
    le_antisymm ((SU1.pRank_mono hp.one_lt le_top).trans hrk)
      (hK2.trans (SU1.pRank_mono hp.one_lt inf_le_right))
  have hsubK : K.IsSubnormal := hKn.isSubnormal
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsubK
  have hSC : ∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B := by
    intro y hy hyp
    by_contra hyB
    have hcomm : ∀ e ∈ B, e * y = y * e := fun e he => (mem_centralizer_iff.mp hy) e he
    obtain ⟨hel, hcard⟩ := isElemAbelian_card_sup_zpowers_of_card hp hBel hBc hyp hyB hcomm
    have := SU1.le_pRank hp.one_lt le_top hel (k := 3) hcard
    omega
  have hQcomm : ¬ IsMulCommutative ↥(Q : Subgroup Z) := by
    intro hcomm
    obtain ⟨a, ha, b, hb, -, -, hab⟩ := hnc
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  intro W hBUW hcop
  have hBW : B ≤ normalizer (W : Set Z) := le_sup_left.trans hBUW
  rcases catalog_trichotomy hcatK hsimple.2 with halt | ⟨r, hlie⟩ | ⟨s, hspor⟩
  · exact absurd (hAlt p hp hp5 Z K hKn halt hCK hrk Q) hQcomm
  · by_cases hr : r = p
    · subst hr
      have hrk1 : Open.pRank r (⊤ : Subgroup ↥K) = 2 := by
        rw [← pRank_map_subtype hp.one_lt, Subgroup.map_top, Subgroup.range_subtype]
        exact hK2'
      rcases hChevP r hp hp5 ↥K hsimple.1 hsimple.2 hlie hrk1 with hl2 | hl3 | hu3
      · exact absurd (hL2 r hp hp5 Z K hKn hl2 hCK Q) hQcomm
      · exfalso
        have hY' := hL3 r hp hp5 ↥K hl3 P (Y.subgroupOf K) (fun S hSP hS2 => by
          have hSZ : S.map K.subtype ≤ (Q : Subgroup Z) := by
            have h1 : S.map K.subtype ≤ (P : Subgroup ↥K).map K.subtype := Subgroup.map_mono hSP
            rw [hP] at h1
            exact h1.trans inf_le_left
          have hrkS : 2 ≤ Open.pRank r (S.map K.subtype) := by
            rw [pRank_map_subtype hp.one_lt]
            exact hS2
          exact normalizer_subgroupOf_le S (fun x hx => hΓ2 _ hSZ hrkS hx.1))
        apply hKY
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ Y.subgroupOf K := by
          rw [hY']
          exact mem_top _
        exact this
      · exact hI204 r hp hp5 Z K hKn hu3 hCK B hBel hBc hSC W hBW hcop
    · exact absurd (hChevQ p hp hp5 Z K hKn hsimple.1 hsimple.2 ⟨r, hr, hlie⟩ hCK hK2' hrk2 Q hnc
        U hUQ hUel hUc Y hΓU) hKY
  · rcases hSpor p hp hp5 Z K hKn s hspor hCK hrk2 Q hnc with hB | hC
    · exfalso
      rcases hSporB p s hB Z K hKn hspor hCK hrk2 with h1 | h2
      · obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B, b ∉ zpowers w := by
          by_contra hcon
          push Not at hcon
          have hle : B ≤ zpowers w := fun b hb => hcon b hb
          have hcard := Subgroup.card_le_of_le hle
          rw [Nat.card_zpowers, hwo, hBc] at hcard
          have := hp.two_le
          nlinarith
        have hbp : b ^ p = 1 := hBel.2 b hb
        have hb1 : b ≠ 1 := fun h => hbw (h ▸ one_mem _)
        have hbo : orderOf b = p := orderOf_eq_prime hbp hb1
        obtain ⟨g, hg⟩ := h1 w b hwo hbo
        have hgw : g * w * g⁻¹ ∈ zpowers b := by
          rw [← hg]
          exact ⟨w, mem_zpowers w, by simp⟩
        have hgB : g * w * g⁻¹ ∈ B := (zpowers_le.mpr hb) hgw
        have hgz := hw w hwQ hwo hwc g hgB
        have hbmem : b ∈ (zpowers w).map (MulAut.conj g).toMonoidHom := by
          rw [hg]
          exact mem_zpowers b
        obtain ⟨x, hx, hxb⟩ := hbmem
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
        apply hbw
        have : b = (g * w * g⁻¹) ^ k := by
          rw [← hxb]
          simp [conj_zpow]
        rw [this]
        exact Subgroup.zpow_mem _ hgz k
      · obtain ⟨g, hg⟩ := h2 B U hBel hBc hUel hUc
        exact hBU g hg
    · exact hSporC p s hC Z K hKn hspor hCK B hBel hBc hSC W hBW hcop

theorem two_Z (hRank1 : KDI278Rank1) (hAlt : KDI278Alt) (hChevP : KDI278ChevP)
    (hL2 : KDI278L2p2) (hL3 : KDI278L3) (hChevQ : KDI278ChevQ) (hSpor : KDI278Spor)
    (hSporB : KDI278SporB) (hSporC : KDI278SporC) (hI204 : KDL64I204U3) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hcat : CatalogSimpleSections Z) (hZ : primeComplementCore (G := Z) p = ⊥)
    (Q : Sylow p Z) (hrk : Open.pRank p (⊤ : Subgroup Z) ≤ 2)
    (hZc : IsCyclic (center (Q : Subgroup Z))) (B U : Subgroup Z) (hBQ : B ≤ Q)
    (hBel : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hUQ : U ≤ Q)
    (hUel : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hBU : ∀ g : Z, B.map (MulAut.conj g).toMonoidHom ≠ U)
    (hw : ∀ w ∈ (Q : Subgroup Z), orderOf w = p → (∀ q ∈ (Q : Subgroup Z), q * w = w * q) →
      ∀ g : Z, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w)
    (Y : Subgroup Z) (hY : ¬ ⊤ ≤ Y)
    (hΓU : ∀ S : Subgroup Z, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y)
    (hΓ2 : ∀ S : Subgroup Z, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) :
    ∀ W : Subgroup Z, B ⊔ U ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
      W = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQrk : Open.pRank p (Q : Subgroup Z) ≤ 2 := (SU1.pRank_mono hp.one_lt le_top).trans hrk
  have hQ2 : 2 ≤ Open.pRank p (Q : Subgroup Z) := SU1.le_pRank hp.one_lt hBQ hBel (k := 2) hBc
  have hrk2 : Open.pRank p (⊤ : Subgroup Z) = 2 :=
    le_antisymm hrk (hQ2.trans (SU1.pRank_mono hp.one_lt le_top))
  have hQY : (Q : Subgroup Z) ≤ Y := Subgroup.le_normalizer.trans (hΓ2 _ le_rfl hQ2)
  have hBne : B ≠ U := by
    intro h
    apply hBU 1
    rw [← h]
    ext x
    simp
  obtain ⟨b, hb, u, hu, hbu⟩ := exists_noncomm_of_ne hp hQrk hBQ hUQ hBel hBc hUel hUc hBne
  have hnc : ∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
      a * b ≠ b * a := ⟨b, hBQ hb, u, hUQ hu, hBel.2 b hb, hUel.2 u hu, hbu⟩
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbu (by simp)
  have hQne : (Q : Subgroup Z) ⊓ (⊤ : Subgroup Z) ≠ ⊥ := by
    intro h
    have : b ∈ (Q : Subgroup Z) ⊓ (⊤ : Subgroup Z) := ⟨hBQ hb, mem_top b⟩
    rw [h, Subgroup.mem_bot] at this
    exact hb1 this
  have hQM : (Q : Subgroup Z) ≤ normalizer (((⊤ : Subgroup Z)) : Set Z) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨w, hwT, hwo, hwc⟩ := exists_central_of_inf hp Q hQM hQne
  have hwQ : w ∈ (Q : Subgroup Z) := hwT.1
  have hwp : w ^ p = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo] at this
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  have hwU : w ∈ U := P64Free.mem_of_central_of_pRank_le_two hp hQrk hUQ hUel hUc hwQ hwp hwc
  have hwN : normalizer ((zpowers w : Subgroup Z) : Set Z) ≤ Y :=
    hΓU _ (zpowers_le.mpr hwU) (P64Free.one_le_pRank_zpowers hp hwp hw1)
  have hQnc : ¬ IsCyclic ↥(Q : Subgroup Z) := not_isCyclic_of_two_le_pRank hp hQ2
  obtain ⟨L, hL⟩ := exists_isComponentOf_Z hp hp2 hZ Q hQnc hQY hΓ2 hY
  by_cases hI : 2 ≤ Open.pRank p ((Q : Subgroup Z) ⊓ sSup {M : Subgroup Z | IsComponentOf M ⊤})
  · obtain ⟨K, hK, hKn, -, hcenK, hCK, hKY, hK2⟩ :=
      caseI hp hp5 hZ Q hZc hQrk hwQ hwo hwc hY hΓ2 hwN hL hI
    exact dispatch hAlt hChevP hL2 hL3 hChevQ hSpor hSporB hSporC hI204 hp hp5 hcat Q hrk hrk2
      hBel hBc hUQ hUel hUc hBU hwQ hwo hwc hw hnc hΓU hΓ2 hK hKn hcenK hCK hKY hK2
  · exfalso
    exact caseII hRank1 hp hp5 hcat hZ Q hZc hwQ hwo hwc hL hnc (by omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
