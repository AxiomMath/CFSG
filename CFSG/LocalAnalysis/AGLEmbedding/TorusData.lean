module

public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section TorusData

variable {G : Type} [Group G] [Finite G]

structure D1TorusData (p : ℕ) (P : Sylow p G) (M H R X : Subgroup G) : Prop where
  ph3 : D1PhaseThree p P M H R
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  le_R : X ≤ R
  elem : IsElemAbelian p X
  card_le : p ^ 2 ≤ Nat.card X
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H
  irr : ∃ (r : ℕ) (t : G), 4 ≤ r ∧ t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (X : Set G) ∧
    ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X → t ^ k ∈ Subgroup.normalizer (Y : Set G) →
      Y = ⊥ ∨ Y = X

variable {p : ℕ} {P : Sylow p G} {M H R X : Subgroup G}

theorem D1TorusData.isElemAbelian_barM (h : D1TorusData p P M H R X) :
    IsElemAbelian p (barM M X) :=
  isElemAbelian_barM_of_isElemAbelian h.elem

theorem D1TorusData.card_barM (h : D1TorusData p P M H R X) : Nat.card (barM M X) = Nat.card X :=
  card_barM_of_isPGroup h.ph3.prime h.ph3.ne_two (h.le_R.trans h.ph3.le_M)
    fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩

theorem D1TorusData.false_of_oddCore_not_centralized (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (h : D1TorusData p P M H R X) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p)
    (hns : ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    False := by
  have hp : p.Prime := h.ph3.prime
  have : Fact p.Prime := ⟨hp⟩
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨r, t, hr4, htK, htX, hirr⟩ := h.irr
  have hXM : X ≤ M := h.le_R.trans h.ph3.le_M
  have htM : t ∈ M := htK.2
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : r ≤ Open.pRank s Sg := by
    refine stmtOddCoreRank' hs hs2 hp hsp Sg (barM M X) (mk ⟨t, htM⟩)
      CFSG.pCore_isPGroup (le_top.trans hSgN) h.isElemAbelian_barM ?_
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htX) (fun k hk Y₀ hY₀ hkY₀ => ?_)
      hns
    · rw [h.card_barM]
      exact h.card_le
    · have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
        rw [← map_pow]
        rfl
      rw [htk] at hkY₀
      exact eq_bot_or_eq_barM_of_mem_normalizer hXM (M.pow_mem htM k)
        (Subgroup.pow_mem _ htX k) (hirr k hk) hY₀ hkY₀
  set Sh : Subgroup G := (Sg.comap mk).map M.subtype with hSh
  have h4 : 4 ≤ Open.pRank s Sh := by
    have h1 := pRank_barM_le hs hs2 M Sh (Subgroup.map_subtype_le _)
    rw [barM_preimage] at h1
    exact (hr4.trans hrank).trans h1
  have hShN : Sh ≤ GLBPrimeCore p H := by
    have hShK : Sh ≤ H ⊓ M := h.ph3.preimage_le_inf (h.ph3.le_barM_inf_of_le_centralizer
      ((pCore_le_pPrimeCore_two hs hs2).trans (h.ph3.oddCore_le_centralizer h84 hD2)))
    have hShn : H ⊓ M ≤ Subgroup.normalizer (Sh : Set G) :=
      inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf Sg))
    refine (h.normal_dichotomy Sh hShK hShn).resolve_right fun hXSh => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    have hdvd := Subgroup.card_dvd_of_le (barM_le_of_le_preimage hXSh)
    rw [h.card_barM, hk] at hdvd
    have hXp : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hXp
    have hm1 : m ≠ 0 := by
      rintro rfl
      have := h.card_le
      rw [hm, pow_zero] at this
      have := Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) hp.one_lt
      omega
    have hpdvd : p ∣ s ^ k := (hm ▸ dvd_pow_self p hm1).trans hdvd
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow hpdvd)).symm
  exact h.ph3.false_of_preimage_le hs hs2
    (mem_glbBetaFour_of_le_pRank hs hs2 h.ph3.maxTwoLocal_M.1 (Subgroup.map_subtype_le _) h4)
    CFSG.pCore_isPGroup ((by norm_num : 3 ≤ 4).trans h4) (glbPrimeCore_le p H)
    (le_normalizer_glbPrimeCore p H) h.ph3.primeCore_le hShN

theorem D1TorusData.barM_le_centralizer_of_le_inf (hα : KFactThreeOrFiveDvd)
    (hβ : KFactOutElemRank) (h : D1TorusData p P M H R X) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL2 : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set _) := by
  by_contra hXC
  have hpp : p.Prime := h.ph3.prime
  have : Fact p.Prime := ⟨hpp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Kb := barM M (H ⊓ M) with hKb
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hXK : X ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  have hMtop : M ≠ ⊤ := fun hM => h.ph3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h.ph3.glob.kProper M hMtop).quotient _
  have hLcat := hcat.isCatalogGroup_center_quotient hLbC
  have hpL : ¬ p ∣ Nat.card Lb := by
    have hLN := h.perfect_le L hLK hL2.perfect
    have hcop : p.Coprime (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime p H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    intro hpd
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop (hpd.trans hdvd)
  have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLbC.2.2.2
  obtain ⟨q, hq, hq2, hqp, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q < p ∧
      q ∣ Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rcases hα _ hsimple (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hLbC.2.2) hLcat with h3 | h5
    · exact ⟨3, Nat.prime_three, by decide, by omega, h3⟩
    · refine ⟨5, Nat.prime_five, by decide, ?_, h5⟩
      have hdvdL : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) ∣ Nat.card Lb :=
        Subgroup.card_quotient_dvd_card _
      have hp5' : p ≠ 5 := fun he => hpL (he ▸ h5.trans hdvdL)
      omega
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
  have hLbK : Lb ≤ Kb := Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
    (hLK (Subgroup.mem_subgroupOf.mp hz)))
  have horbit : ∀ (m : ℕ) (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M), (∀ j, g j ∈ Kb) →
      Function.Injective (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) → m ≤ 3 := by
    intro m g hg hinj
    have hm := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift inf_le_right hq
      hq2 hLbC hLbK hyL hyq hlL hyl g hg hinj
    by_contra hm3
    exact h.ph3.false_of_four_le_pRank' h.ind hq hq2 hqp (by omega)
  by_cases hXN : barM M X ≤ Subgroup.normalizer (Lb : Set _)
  · obtain ⟨r, t, hr4, htK, htX, hirr⟩ := h.irr
    have htop : X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype ≠ X := by
      intro he
      apply hXC
      rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
      have hxCX : x ∈ X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype := by
        rw [he]
        exact Subgroup.mem_subgroupOf.mp hxX
      obtain ⟨m, hm, hmx⟩ := hxCX.2
      have : m = ⟨x, hxM⟩ := Subtype.ext hmx
      subst this
      exact hm
    have hbot : X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype ≠ ⊥ := by
      intro hCXbot
      have hinf : barM M X ⊓ Subgroup.centralizer (Lb : Set _) = ⊥ := by
        rw [eq_bot_iff]
        rintro z ⟨⟨⟨x, hxM⟩, hxX, rfl⟩, hzC⟩
        have hxCX : x ∈ X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype :=
          ⟨Subgroup.mem_subgroupOf.mp hxX, ⟨⟨x, hxM⟩, hzC, rfl⟩⟩
        rw [hCXbot, Subgroup.mem_bot] at hxCX
        have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxCX
        rw [Subgroup.mem_bot, this, map_one]
      have hle := hβ _ Lb (barM M X) hLbC hLcat p hpp hp5 hpL hXN h.isElemAbelian_barM hinf
      rw [h.card_barM] at hle
      have h2 := h.card_le
      have : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
      omega
    have hinj := injective_conj_pow_of_inf_preimage_centralizer htK.2 htX hirr hbot htop
    have := horbit r _ (fun j => Kb.pow_mem
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htK)) _) hinj
    omega
  · obtain ⟨xb, hxb, hxbN⟩ := Set.not_subset.mp hXN
    obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := hxb
    have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
    have hxbK : mk ⟨x, hxM⟩ ∈ Kb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXK hxX'))
    have hxp : IsPGroup p (Subgroup.zpowers (mk ⟨x, hxM⟩)) := by
      refine isPGroup_zpowers_of_pow_eq_one (k := 1) ?_
      have hx1 : x ^ p = 1 := h.elem.2 x hxX'
      have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hx1)
      rw [pow_one, ← map_pow, this, map_one]
    have hinj := injective_conj_pow_of_not_mem_normalizer hxp hxbN
    have := horbit p (fun j => (mk ⟨x, hxM⟩) ^ (j : ℕ)) (fun j => Kb.pow_mem hxbK _) hinj
    omega

theorem D1TorusData.barM_le_pCore (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hα : KFactThreeOrFiveDvd) (hβ : KFactOutElemRank) (h : D1TorusData p P M H R X)
    (hp5 : 5 ≤ p)
    (hblock : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have hp : p.Prime := h.ph3.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _) := by
    intro Lbar hL
    obtain ⟨L, hL2, rfl, hL'⟩ := h.ph3.exists_weakSBlock_or_le_inf hL
    rcases hL' with hw | hle
    · exact hblock L hw
    · exact h.barM_le_centralizer_of_le_inf hα hβ hp5 hL2 hle
  have hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) :=
    fun s hs hs2 hsp => by_contra fun hns =>
      h.false_of_oddCore_not_centralized h84 hD2 hs hs2 hsp hns
  set Ob := CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) with hOb
  set Y : Subgroup G := (Ob.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype
    with hY
  have hYK : Y ≤ H ⊓ M := h.ph3.preimage_le_inf (h.ph3.le_barM_inf_of_le_centralizer
    ((pCore_le_pPrimeCore_two hp h.ph3.ne_two).trans (h.ph3.oddCore_le_centralizer h84 hD2)))
  have hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf Ob))
  rcases h.normal_dichotomy Y hYK hYn with hYN | hXY
  · have hOp : Ob = ⊥ := by
      refine eq_bot_iff.mpr fun σ hσ => ?_
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) σ
      have hmN : (m : G) ∈ GLBPrimeCore p H := hYN ⟨m, hσ, rfl⟩
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M) ⟨_, hσ⟩
      have hord1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣ p ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hord2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣
          Nat.card (GLBPrimeCore p H) :=
        (orderOf_map_dvd _ _).trans (by
          rw [← Subgroup.orderOf_coe]
          exact Subgroup.orderOf_dvd_natCard _ hmN)
      exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left k (glbPrimeCore_coprime p H)) hord1 hord2))
    have hXp : IsPGroup p (barM M X) := fun x =>
      ⟨1, Subtype.ext (by simpa using h.isElemAbelian_barM.2 x x.2)⟩
    refine le_pCore_of_le_centralizer_components hXp hcomp fun l hl => ?_
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hlp : l = p
    · subst hlp
      rw [← hOb, hOp]
      exact Subgroup.le_centralizer_iff.mp bot_le
    exact hodd l hl hl2 hlp
  · exact barM_le_of_le_preimage hXY

end TorusData

end CFSG.AGLEmbedding
