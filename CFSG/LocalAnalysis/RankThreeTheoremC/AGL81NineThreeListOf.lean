module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeX
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeGamma
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeComponents
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeProduct
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.LocalAnalysis.GLTheoremA.S8.Close
import CFSG.HardMathSupport.Timmesfeld.SporadicRank.UpperBound

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem pRank_le_of_sylow_inf [Fact p.Prime] (R : Sylow p X) {L : Subgroup X}
    (hL : L.IsSubnormal) {k : ℕ} (hk : CFSG.Open.pRank p ((R : Subgroup X) ⊓ L) ≤ k) :
    CFSG.Open.pRank p L ≤ k := by
  have hp : p.Prime := Fact.out
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hL
  have hTop : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ k := by
    refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_sylow hp (T : Subgroup L)
      (Sylow.card_eq_multiplicity T) fun E hET hE => ?_
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hE)
    have hle : E.map L.subtype ≤ (R : Subgroup X) ⊓ L := hT ▸ Subgroup.map_mono hET
    have hcard : Nat.card (E.map L.subtype) = p ^ j := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hj]
    have hjk := (CFSG.SectionRank.le_pRank hp.one_lt hle
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _) hcard).trans hk
    rw [hj]
    exact Nat.pow_le_pow_right hp.pos hjk
  have e : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← e, CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype
    L.subtype_injective]
  exact hTop

theorem center_sup_eq_bot_of_le_centralizer {L₀ L₁ : Subgroup X}
    (h₁₀ : L₁ ≤ Subgroup.centralizer (L₀ : Set X)) (hZ₀ : Subgroup.center L₀ = ⊥)
    (hZ₁ : Subgroup.center L₁ = ⊥) : Subgroup.center (L₀ ⊔ L₁ : Subgroup X) = ⊥ := by
  have hcomm : ∀ (a : L₀) (b : L₁), Commute (L₀.subtype a) (L₁.subtype b) := fun a b =>
    Subgroup.mem_centralizer_iff.mp (h₁₀ b.2) a a.2
  have hrange : (MonoidHom.noncommCoprod L₀.subtype L₁.subtype hcomm).range = L₀ ⊔ L₁ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hab : ∀ x ∈ L₀, ∀ y ∈ L₁, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (h₁₀ hy) x hx
  rw [eq_bot_iff]
  rintro ⟨z, hz⟩ hzc
  rw [Subgroup.mem_bot]
  have hcen : ∀ y ∈ L₀ ⊔ L₁, y * z = z * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩)
  obtain ⟨⟨a, b⟩, hzab⟩ : z ∈ (MonoidHom.noncommCoprod L₀.subtype L₁.subtype hcomm).range :=
    hrange ▸ hz
  rw [MonoidHom.noncommCoprod_apply] at hzab
  simp only [Subgroup.coe_subtype] at hzab
  subst hzab
  have ha1 : a = 1 := by
    have : a ∈ Subgroup.center L₀ := Subgroup.mem_center_iff.mpr fun x => by
      apply Subtype.ext
      have h := hcen x (Subgroup.mem_sup_left x.2)
      have e : (x : X) * a * b = a * x * b := by
        calc (x : X) * a * b = x * (a * b) := by group
          _ = a * b * x := h
          _ = a * (b * x) := by group
          _ = a * (x * b) := by rw [hab x x.2 b b.2]
          _ = a * x * b := by group
      exact mul_right_cancel e
    rw [hZ₀, Subgroup.mem_bot] at this
    exact this
  have hb1 : b = 1 := by
    have : b ∈ Subgroup.center L₁ := Subgroup.mem_center_iff.mpr fun y => by
      apply Subtype.ext
      have h := hcen y (Subgroup.mem_sup_right y.2)
      have e : (a : X) * (y * b) = a * (b * y) := by
        calc (a : X) * (y * b) = y * (a * b) := by
              rw [← mul_assoc, hab a a.2 y y.2, mul_assoc]
          _ = a * b * y := h
          _ = a * (b * y) := by group
      exact mul_left_cancel e
    rw [hZ₁, Subgroup.mem_bot] at this
    exact this
  apply Subtype.ext
  simp [ha1, hb1]

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem cores_le_d1X0 {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N R : Subgroup G} (hB : IsAGLQ p M B) (hBR : B ≤ R)
    (hRM : R ≤ M) (hR : CFSG.Quasithin.IsSylowIn p R N) :
    ∃ E : Subgroup (N ⧸ primeComplementCore (G := N) p),
      E ≤ (R.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      (if 3 ≤ CFSG.Open.pRank p ((R.subgroupOf N).map
          (QuotientGroup.mk' (primeComplementCore (G := N) p)))
        then GLBWeakCore p ((R.subgroupOf N).map
          (QuotientGroup.mk' (primeComplementCore (G := N) p)))
        else GLBCore p 1 E) ≤ d1X0 p M N := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hRp : IsPGroup p (R.subgroupOf N) :=
    hR.isPGroup.comap_of_injective N.subtype N.subtype_injective
  have hrank : CFSG.Open.pRank p ((R.subgroupOf N).map π) = CFSG.Open.pRank p R := by
    rw [pRank_map_mk_eq_pRank_map_subtype hp O hO, Subgroup.map_subgroupOf_eq_of_le hR.le]
  by_cases h3 : 3 ≤ CFSG.Open.pRank p ((R.subgroupOf N).map π)
  · obtain ⟨E, hER, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := p) (k := 2) (H := (R.subgroupOf N).map π) (by omega)
    refine ⟨E, hER, hE, hEcard, ?_⟩
    rw [if_pos h3]
    exact weakCore_le_d1X0_of_escape he hR.le hRM hR.isPGroup
  ·
    obtain ⟨-, -, hB3 | ⟨E, hEB, hE, hEc, hΓ⟩⟩ := hB
    · exfalso
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hB3
      have := hB3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hBR)
      omega
    have hEN : E ≤ N := (hEB.trans hBR).trans hR.le
    have hEp : IsPGroup p (E.subgroupOf N) :=
      (hR.isPGroup.to_le (hEB.trans hBR)).comap_of_injective N.subtype N.subtype_injective
    refine ⟨(E.subgroupOf N).map π, Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hBR (hEB (Subgroup.mem_subgroupOf.mp hx))),
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
        (isElemAbelian_subgroupOf hE N) π, ?_, ?_⟩
    · rw [card_map_mk_of_isPGroup hp O hO hEp, ← hEc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
    · rw [if_neg h3]
      exact gammaOne_le_d1X0 hp hEN (hR.isPGroup.to_le (hEB.trans hBR)) hΓ

theorem exists_threeOneIndex_of_component (h31 : KFactThreeOne) (hKP : CFSG.Open.IsKProper G)
    {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁)
    {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N) (hNtop : N ≠ ⊤)
    {L : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M N) :
    (∃ i : TauCeti.CFSGIndex, IsThreeOneIndex p i ∧ Nonempty (L ≃* i.Group)) ∧
      Subgroup.center L = ⊥ := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨R, hBR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hB hBN
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  have hRbL : (Rb : Subgroup (N ⧸ O)) ≤ Subgroup.normalizer (L : Set (N ⧸ O)) := by
    rw [hRbeq]
    exact le_normalizer_component_of_escape he hR.le hRM ⟨hR.toSylow, by
      rw [CFSG.Quasithin.IsSylowIn.coe_toSylow]
      exact Subgroup.map_subgroupOf_eq_of_le hR.le⟩ hL hLX
  have hR2 : 2 ≤ CFSG.Open.pRank p (Rb : Subgroup (N ⧸ O)) := by
    rw [hRbeq, pRank_map_mk_eq_pRank_map_subtype hp O hO, Subgroup.map_subgroupOf_eq_of_le hR.le]
    obtain ⟨-, -, hB3 | ⟨E, hEB, hE, hEc, -⟩⟩ := hB
    · rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hB3
      exact (by omega : 2 ≤ 3).trans
        (hB3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hBR))
    · exact (le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp E)
        ⟨E, le_rfl, hE, hEc⟩).trans
        (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (hEB.trans hBR))
  obtain ⟨E, hER, hE, hEcard, hcore⟩ := cores_le_d1X0 he hB hBR hRM hR
  rw [← hRbeq] at hER hcore
  refine h31 p (N ⧸ O) (Subgroup.normalizer (L : Set (N ⧸ O))) L Rb E hp he.ne_two
    Subgroup.le_normalizer le_rfl hL.2.2 (isKGroup_component hKP hNtop L)
    (primeComplementCore_component_eq_bot (primeComplementCore_quotient_eq_bot p) hL)
    (hR2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hRbL))
    ⟨hRbL, Rb.isPGroup', fun hdvd => Rb.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hRbL))⟩ hER hE hEcard
    fun h => hLX (h.trans hcore)

theorem exists_nineThreeIndex_of_component (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hNtop : N ≠ ⊤) {L : Subgroup (N ⧸ primeComplementCore (G := N) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M N) :
    ∃ i : TauCeti.CFSGIndex, IsNineThreeIndex p i ∧ Nonempty (L ≃* i.Group) := by
  have hp := he.prime
  obtain ⟨⟨i, hi, hiL⟩, hZ⟩ := exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL hLX
  have hLs : IsSimpleGroup L := by
    haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  rcases hi with hi | ⟨hp5, rfl⟩ | ⟨n, hn, rfl, hn2 | hn3⟩
  · exact ⟨i, hi, hiL⟩
  · exact (false_of_sevenFive hS h75 (Or.inr (Or.inr ⟨hp5, rfl⟩)) hLs hiL).elim
  ·
    subst hn2
    by_cases hp7 : 7 ≤ p
    · exact (false_of_sevenFive hS h75 (Or.inl ⟨hp7, hn, rfl⟩) hLs hiL).elim
    have hp35 : p = 3 ∨ p = 5 := by
      have h2 := he.ne_two
      have := hp.two_le
      interval_cases p <;> first | (left; rfl) | (right; rfl) | exact absurd rfl h2 |
        exact absurd hp (by norm_num)
    refine ⟨_, ?_, hiL⟩
    rcases hp35 with rfl | rfl
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  ·
    subst hn3
    by_cases hp5 : 5 ≤ p
    · exact (false_of_sevenFive hS h75 (Or.inr (Or.inl ⟨hp5, hn, rfl⟩)) hLs hiL).elim
    have hp3 : p = 3 := by
      have h2 := he.ne_two
      have := hp.two_le
      interval_cases p <;> first | rfl | exact absurd rfl h2 | exact absurd hp (by norm_num)
    subst hp3
    refine ⟨_, ?_, hiL⟩
    exact Or.inl ⟨rfl, Or.inr rfl⟩

theorem eq_of_isNineThreeProductIndex {p : ℕ} {d₁ d₂ : TauCeti.ValidLieTypeIndex}
    (h₁ : IsNineThreeProductIndex p d₁) (h₂ : IsNineThreeProductIndex p d₂) : d₁ = d₂ := by
  rcases h₁ with ⟨rfl, q₁, hq₁, he₁, hd₁⟩ | ⟨rfl, hd₁⟩ <;>
    rcases h₂ with ⟨hp, q₂, hq₂, he₂, hd₂⟩ | ⟨hp, hd₂⟩
  · apply Subtype.ext
    rw [hd₁, hd₂]
    have hq : q₁ = q₂ := by
      cases q₁
      cases q₂
      simp only at hq₁ he₁ hq₂ he₂
      subst hq₁ he₁ hq₂ he₂
      rfl
    rw [hq]
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact Subtype.ext (hd₁.trans hd₂.symm)

theorem d1KBar_eq_or_eq_sup_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hK : d1KBar p M N ≠ ⊥) :
    ∃ L₀ : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L₀ ⊤ ∧
      ¬ L₀ ≤ d1X0 p M N ∧ (d1KBar p M N = L₀ ∨
        ∃ L₁ : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L₁ ⊤ ∧
          ¬ L₁ ≤ d1X0 p M N ∧ L₀ ≠ L₁ ∧ d1KBar p M N = L₀ ⊔ L₁ ∧
          CFSG.Open.pRank p L₀ ≤ 1 ∧ CFSG.Open.pRank p L₁ ≤ 1) := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  obtain ⟨Rb, -, -, hC, hu⟩ := exists_sylow_d1X0_of_escape he hB hBN
  obtain ⟨L₀, hL₀, hL₀X⟩ := exists_component_of_d1KBar_ne_bot hK
  refine ⟨L₀, hL₀, hL₀X, ?_⟩
  have hsub : ∀ L : Subgroup (N ⧸ O), IsComponentOf L ⊤ → L.IsSubnormal := fun L hL =>
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top
  have hS7 : ∀ L : Subgroup (N ⧸ O), IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M N →
      CFSG.Open.pRank p ((Rb : Subgroup (N ⧸ O)) ⊓ Subgroup.centralizer (L : Set (N ⧸ O))) ≤ 1 := by
    intro L hL hLX
    obtain ⟨u, huR, huL, hup, hunc⟩ := hu L hL
    exact pRank_inf_centralizer_component_le_one hp hC hLX huR huL hup hunc
  by_cases huniq : ∀ L : Subgroup (N ⧸ O), IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M N → L = L₀
  · exact Or.inl (d1KBar_eq_of_unique hL₀ hL₀X huniq)
  push Not at huniq
  obtain ⟨L₁, hL₁, hL₁X, hne⟩ := huniq
  have hrank : ∀ L L' : Subgroup (N ⧸ O), IsComponentOf L ⊤ → IsComponentOf L' ⊤ →
      ¬ L' ≤ d1X0 p M N → L ≠ L' → CFSG.Open.pRank p L ≤ 1 := by
    intro L L' hL hL' hL'X hLL'
    exact pRank_le_of_sylow_inf Rb (hsub L hL) ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p
      hp (inf_le_inf_left _ (le_centralizer_of_component_ne hL hL' hLL'))).trans (hS7 L' hL' hL'X))
  refine Or.inr ⟨L₁, hL₁, hL₁X, Ne.symm hne, ?_, hrank L₀ L₁ hL₀ hL₁ hL₁X (Ne.symm hne),
    hrank L₁ L₀ hL₁ hL₀ hL₀X hne⟩
  refine le_antisymm (iSup₂_le fun L hL => ?_) (sup_le (le_d1KBar hL₀ hL₀X) (le_d1KBar hL₁ hL₁X))
  by_cases h0 : L = L₀
  · exact h0 ▸ le_sup_left
  by_cases h1 : L = L₁
  · exact h1 ▸ le_sup_right
  exfalso
  obtain ⟨v, hvR, hvL, hvp, hvc⟩ := hu L hL.1
  obtain ⟨v₁, hv₁R, hv₁L, hv₁p, -⟩ := hu L₁ hL₁
  have hv₁' : v₁ ^ p = 1 := by
    have h := pow_orderOf_eq_one v₁
    rwa [hv₁p] at h
  have hv' : v ^ p = 1 := by
    have h := pow_orderOf_eq_one v
    rwa [hvp] at h
  have hE₁ : IsElemAbelian p (Subgroup.zpowers v₁) :=
    ⟨inferInstance, fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv₁', one_zpow]⟩
  have hcard₁ : Nat.card (Subgroup.zpowers v₁) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one, hv₁p]
  have hvv₁ : v ∉ Subgroup.zpowers v₁ := by
    intro h
    obtain ⟨c, hc, hvc'⟩ := hvc
    exact hvc' (Subgroup.mem_centralizer_iff.mp
      (le_centralizer_of_component_ne hL₁ hL.1 (Ne.symm h1) ((Subgroup.zpowers_le.mpr hv₁L) h))
        c hc).symm
  have hcomm : ∀ e ∈ Subgroup.zpowers v₁, e * v = v * e := fun e he =>
    Subgroup.mem_centralizer_iff.mp (le_centralizer_of_component_ne hL.1 hL₁ h1 hvL) e
      ((Subgroup.zpowers_le.mpr hv₁L) he)
  obtain ⟨hA, hAcard⟩ :=
    CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hp hE₁ hcard₁ hv' hvv₁ hcomm
  have hle : Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v ≤
      (Rb : Subgroup (N ⧸ O)) ⊓ Subgroup.centralizer (L₀ : Set (N ⧸ O)) :=
    le_inf (sup_le (Subgroup.zpowers_le.mpr hv₁R) (Subgroup.zpowers_le.mpr hvR))
      (sup_le (Subgroup.zpowers_le.mpr (le_centralizer_of_component_ne hL₁ hL₀ hne hv₁L))
        (Subgroup.zpowers_le.mpr (le_centralizer_of_component_ne hL.1 hL₀ h0 hvL)))
  have h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v) :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp _) ⟨_, le_rfl, hA, hAcard⟩
  have := h2.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hle).trans
    (hS7 L₀ hL₀ hL₀X))
  omega

theorem nineThreeListGroup_d1KBar_of_escape (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR2 : KFactNineThreeRankTwo) (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B)
    (hBN : B ≤ N) (hNtop : N ≠ ⊤) (hK : d1KBar p M N ≠ ⊥) :
    NineThreeListGroup p (d1KBar p M N) := by
  have hp := he.prime
  obtain ⟨L₀, hL₀, hL₀X, h | ⟨L₁, hL₁, hL₁X, hne, hK₀₁, hr₀, hr₁⟩⟩ :=
    d1KBar_eq_or_eq_sup_of_escape he hB hBN hK
  · rw [h]
    exact Or.inl (exists_nineThreeIndex_of_component h31 h75 hS hKP he hB hBN hNtop hL₀ hL₀X)
  obtain ⟨d₀, hd₀, ⟨e₀⟩⟩ := hR2 p _ L₀ hp
    (exists_nineThreeIndex_of_component h31 h75 hS hKP he hB hBN hNtop hL₀ hL₀X) hr₀
  obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := hR2 p _ L₁ hp
    (exists_nineThreeIndex_of_component h31 h75 hS hKP he hB hBN hNtop hL₁ hL₁X) hr₁
  have hd : d₁ = d₀ := eq_of_isNineThreeProductIndex hd₁ hd₀
  subst hd
  rw [hK₀₁]
  exact nineThreeListGroup_sup_of_components hL₀ hL₁ hne hd₁ e₀ e₁

theorem center_d1KBar_eq_bot_of_escape (h31 : KFactThreeOne) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G}
    (hB : IsAGLQ p M B) (hBN : B ≤ N) (hNtop : N ≠ ⊤) (hK : d1KBar p M N ≠ ⊥) :
    Subgroup.center (d1KBar p M N) = ⊥ := by
  obtain ⟨L₀, hL₀, hL₀X, h | ⟨L₁, hL₁, hL₁X, hne, hK₀₁, -, -⟩⟩ :=
    d1KBar_eq_or_eq_sup_of_escape he hB hBN hK
  · have hZ := (exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL₀ hL₀X).2
    rw [h]
    exact hZ
  have hZ₀ := (exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL₀ hL₀X).2
  have hZ₁ := (exists_threeOneIndex_of_component h31 hKP he hB hBN hNtop hL₁ hL₁X).2
  rw [hK₀₁]
  exact center_sup_eq_bot_of_le_centralizer (le_centralizer_of_component_ne hL₁ hL₀ (Ne.symm hne))
    hZ₀ hZ₁

theorem factor_of_escape (hOut : KFactNineThreeOutPClosed) {p : ℕ} {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B)
    (hBN : B ≤ N) (hK : d1KBar p M N ≠ ⊥) (hlist : NineThreeListGroup p (d1KBar p M N)) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ k : N,
      QuotientGroup.mk' (primeComplementCore (G := N) p) k ∈ d1KBar p M N ∧ x = m * k := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hKn : (d1KBar p M N).Normal := d1KBar_normal_of_escape he hB hBN hK
  obtain ⟨Rb, hRbX, hNRb, -, -⟩ := exists_sylow_d1X0_of_escape he hB hBN
  haveI := hOut p _ (d1KBar p M N) hp he.ne_two hKn hlist Rb
  have htop := Sylow.normalizer_sup_eq_top' Rb
    (le_sup_left : (Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤
      (Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊔ (d1KBar p M N ⊔
        Subgroup.centralizer ((d1KBar p M N : Subgroup (N ⧸ primeComplementCore (G := N) p)) :
          Set (N ⧸ primeComplementCore (G := N) p))))
  have hCK := centralizer_d1KBar_le_d1X0_of_escape he hB hBN hK
  have htop' : (⊤ : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤
      d1X0 p M N ⊔ d1KBar p M N := by
    rw [← htop]
    exact sup_le (hNRb.trans le_sup_left) (sup_le (hRbX.trans le_sup_left)
      (sup_le le_sup_right (hCK.trans le_sup_left)))
  intro x hx
  have hmem := htop' (Subgroup.mem_top (QuotientGroup.mk' (primeComplementCore (G := N) p)
    ⟨x, hx⟩))
  obtain ⟨ν, hν, k, hk, hνk⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨m, hm, rfl⟩ := hν
  obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := N) p) k
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have h1 : QuotientGroup.mk' (primeComplementCore (G := N) p) (m⁻¹ * ⟨x, hx⟩ * k'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hνk]; group
  have hoM : ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : N) : G) ∈ M :=
    core_le_of_base (muAt_of_escape he) hB hBN
      ⟨m⁻¹ * ⟨x, hx⟩ * k'⁻¹, (QuotientGroup.eq_one_iff (m⁻¹ * (⟨x, hx⟩ : N) * k'⁻¹)).mp h1, rfl⟩
  refine ⟨(m : G) * ((m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : N) : G),
    ⟨N.mul_mem m.2 (m⁻¹ * ⟨x, hx⟩ * k'⁻¹ : N).2, M.mul_mem hmM hoM⟩, k', hk, ?_⟩
  simp [mul_assoc]

theorem hyp93At_of_escape (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR2 : KFactNineThreeRankTwo) (hS : Setting G)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hNtop : N ≠ ⊤) (hK : d1KBar p M N ≠ ⊥) : Hyp93At p M N :=
  ⟨factor_of_escape hOut he hB hBN hK
      (nineThreeListGroup_d1KBar_of_escape h31 h75 hR2 hS hKP he hB hBN hNtop hK),
    core_le_of_base (muAt_of_escape he) hB hBN⟩

theorem agl81NineThreeAt_of_kfacts (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR2 : KFactNineThreeRankTwo) (hS : Setting G) :
    AGL81NineThreeAt G := by
  intro hg p P M hμ B N hB hBN hN _ hK
  obtain ⟨H₁, R₁, he⟩ := hμ.escape
  have hNtop : N ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hg.simple hg.nonab hN.1
  have hlist := nineThreeListGroup_d1KBar_of_escape h31 h75 hR2 hS hg.kProper he hB hBN hNtop hK
  exact ⟨⟨d1KBar_normal_of_escape he hB hBN hK, d1PlusCore_le_of_escape he hB hBN hK,
    factor_of_escape hOut he hB hBN hK hlist⟩, pRank_d1PlusCore_le_one_of_escape he hB hBN hK,
    hlist⟩

theorem agl81NineCompetitorQ_of_kfacts (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR2 : KFactNineThreeRankTwo) (h917 : AGL81NineSeventeenQ G)
    (hS : Setting G) : AGL81NineCompetitorQ G :=
  agl81NineCompetitorQ_of (agl81NineThreeAt_of_kfacts h31 h75 hOut hR2 hS) h917

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
