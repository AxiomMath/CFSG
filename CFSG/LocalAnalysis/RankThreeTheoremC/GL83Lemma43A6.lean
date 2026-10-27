module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6PropSDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowActionKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6ActProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9R
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Case2M
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6Point
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6_exists_rotation {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J) :
    ∃ ρ ∈ centralizer ({x} : Set G),
      ρ ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
      ∀ a ∈ (P : Subgroup G) ⊓ J, ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = a⁻¹ := by
  obtain ⟨S, φ, hinj, hφS, -, hlift⟩ :=
    r1s_normalizer_data hgen hJ.le_centralizer hJ.centralizer_le
  obtain ⟨n', hn'N, hn'rot⟩ := a6SylowRotation_proved _ (r1sBar_isA6 hJ) S
  obtain ⟨n, hnC, hnN, hnact⟩ := hlift n' hn'N
  refine ⟨n, hnC, hnN, fun a ha => ?_⟩
  have hna : n * a * n⁻¹ ∈ (P : Subgroup G) ⊓ J := (mem_normalizer_iff.mp hnN a).mp ha
  have hnna : n * (n * a * n⁻¹) * n⁻¹ ∈ (P : Subgroup G) ⊓ J :=
    (mem_normalizer_iff.mp hnN _).mp hna
  have h1 := hnact ⟨a, ha⟩ ⟨_, hna⟩ rfl
  have h2 := hnact ⟨_, hna⟩ ⟨_, hnna⟩ rfl
  have h3 : φ ⟨_, hnna⟩ = φ ⟨a⁻¹, inv_mem ha⟩ := by
    rw [h2, h1, hn'rot _ (hφS _)]
    exact (map_inv φ ⟨a, ha⟩).symm
  exact congrArg Subtype.val (hinj h3)

theorem a6Lemma43_of_wc (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hA1 : A6SylowData) (hAct : KFactA6SylowAction) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (hK3 : KFactOutCyclic) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (h34S : A6Prop34S 3 P J x)
    (hwcQ : LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    A6PointLemma43 3 P M J x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hS.simple
  have hJC := hJ.le_centralizer
  obtain ⟨⟨hQab, -, -⟩, hShapeI, -⟩ := h34S
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := hShapeI hwcQ
  have hQP : (P : Subgroup G) ⊓ centralizer ({x} : Set G) = (P : Subgroup G) :=
    inf_eq_left.mpr hPC
  have hPab : IsMulCommutative (P : Subgroup G) := by rw [← hQP]; exact hQab
  have hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x := by
    rw [← hQP]; exact hwcQ
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  have hxM : x ∈ M := hgen.2.1.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hK₀el : IsElemAbelian 3 ((P : Subgroup G) ⊓ J) := a6_inf_isElemAbelian hA1 hgen hJ
  have hK₀card : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 :=
    (a6_T_data hS hU0 hA1 hp hM hgen hJ).2.2
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  have hxK₀ : x ∉ (P : Subgroup G) ⊓ J := fun h => hxJ h.2
  obtain ⟨hNM, hOxM, hCM⟩ := a6l43_point_facts hS hU0 hA1 hp hM hgen hJ
  have hSC := a6l43_strongClosed hS hU0 hA1 hp hM hgen hJ hPab hwc
  have hmove : ∀ a ∈ (P : Subgroup G) ⊓ J, a ≠ 1 → ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ∧
      n * a * n⁻¹ ∉ zpowers a := fun a ha ha1 => a6_exists_moving hAct hgen hJ ha ha1
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1.1
  have hK₀P : (P : Subgroup G) ⊓ J ≤ (P : Subgroup G) := inf_le_left
  have hK₀C : (P : Subgroup G) ⊓ J ≤ centralizer ({x} : Set G) := inf_le_right.trans hJC
  have hBnorm := l43_normalizer_sup_of_moving hS.kProper hInn hWC hK3 hPab hMtop hPM hxP hx3 hx1
    hwc hK₀P hK₀C hK₀el (by simpa using hK₀card) hmove hNM hOxM hCM hSC
  have hK₀x : ∀ a ∈ (P : Subgroup G) ⊓ J, a * x = x * a := fun a ha =>
    setLike_mul_comm ha.1 hxP
  have hEle : ((P : Subgroup G) ⊓ J) ⊔ zpowers x ≤ (P : Subgroup G) :=
    sup_le inf_le_left (zpowers_le.mpr hxP)
  have hEel : IsElemAbelian 3 (((P : Subgroup G) ⊓ J) ⊔ zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hEle a.2) (hEle b.2))⟩⟩, fun e he => ?_⟩
    have hTx : ∀ t ∈ (P : Subgroup G) ⊓ J, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc =>
      setLike_mul_comm ht.1 (zpowers_le.mpr hxP hc)
    obtain ⟨t₀, ht₀, c₀, hc₀, rfl⟩ := u3l42_decomp hTx he
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc₀
    rw [Commute.mul_pow (hTx t₀ ht₀ _ hc₀) 3, hK₀el.2 t₀ ht₀, one_mul, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hEcard : Nat.card (((P : Subgroup G) ⊓ J) ⊔ zpowers x : Subgroup G) = 27 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three _ hx3 hxK₀ hK₀x, hK₀card]
    norm_num
  obtain ⟨ρ, -, hρN, hρrot⟩ := a6_exists_rotation hgen hJ
  have hdata : E9Case1DataR G M (GLBPrimeCore 3 M) ((P : Subgroup G) ⊓ J) x :=
    { O_le := glbPrimeCore_le 3 M
      O_norm := le_normalizer_glbPrimeCore 3 M
      O_cop := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
      O₂_le := pCoreOf_le_glbPrimeCore Nat.prime_two (by norm_num) M
      O₂_ne := by
        obtain ⟨S, hSne, hS2, hSM⟩ := hM.1.1
        have hSleM : S ≤ M := by rw [hSM]; exact Subgroup.le_normalizer
        intro hbot
        apply hSne
        rw [eq_bot_iff]
        have := normal_pGroup_le_pCoreOf 2 S M hSleM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hSleM).mpr hSM.le) hS2
        exact this.trans hbot.le
      charTwo := hS.charTwo M hM.1.1
      K₀_le := inf_le_left.trans hPM
      K₀_el := hK₀el
      K₀_card := by simpa using hK₀card
      x_mem := hxM
      E_el := by rw [sup_comm]; exact hEel
      E_card := by rw [sup_comm]; exact hEcard
      B_norm := hBnorm
      rot := ⟨ρ, hNM hρN, hρN, hρrot⟩
      D1 := fun Y₀ hne h2 hr =>
        le_of_three_le_pRank_inf hD1 hp hM ⟨Y₀, hne, h2, rfl⟩ hr }
  obtain ⟨ℓ, hℓ, hℓ1, hℓY⟩ := hdata.exists_normalizer_le
  have hℓ3 : ℓ ^ 3 = 1 := hK₀el.2 ℓ hℓ
  have hℓP : ℓ ∈ (P : Subgroup G) := hℓ.1
  have hxℓ : x ∉ zpowers ℓ := fun h => hxK₀ (zpowers_le.mpr hℓ h)
  have hcomm : ∀ e ∈ zpowers ℓ, e * x = x * e := fun e he =>
    setLike_mul_comm (zpowers_le.mpr hℓP he) hxP
  have hUle : zpowers ℓ ⊔ zpowers x ≤ (P : Subgroup G) :=
    sup_le (zpowers_le.mpr hℓP) (zpowers_le.mpr hxP)
  have hUE : zpowers ℓ ⊔ zpowers x ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x :=
    sup_le_sup_right (zpowers_le.mpr hℓ) _
  refine ⟨zpowers ℓ ⊔ zpowers x, ⟨hUle.trans (le_inf le_rfl hPC), ?_, ?_,
    mem_sup_right (mem_zpowers x), ?_⟩, ?_⟩
  · have := hEel.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hUE a.2) (hUE b.2))⟩⟩,
      fun a ha => hEel.2 a (hUE ha)⟩
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers ℓ) hx3 hxℓ hcomm,
      Nat.card_zpowers, orderOf_eq_prime hℓ3 hℓ1]
    norm_num
  ·
    intro g hg
    have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
      rw [hg]; exact inf_le_left.trans hUle
    have h1 := hwc g hle
    have hxJ' : x ∈ J := by
      have hx : x ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := by rw [h1]; exact mem_zpowers x
      rw [hg] at hx
      exact hx.2
    exact hxJ hxJ'
  · intro Y hY2 hYM hUY hYO
    exact hℓY Y hY2 hYM hYO (hUY (mem_sup_right (mem_zpowers x)))
      (hUY (mem_sup_left (mem_zpowers ℓ)))

@[expose] def GL83GenericPrimeThreeA6Lemma43VI (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P M x J => A6Prop34S p P J x →
    ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) →
    A6PointLemma43 p P M J x

theorem GL83GenericPrimeThreeA6Lemma43S.of_VI (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hA1 : A6SylowData) (hAct : KFactA6SylowAction)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hK3 : KFactOutCyclic)
    (h : GL83GenericPrimeThreeA6Lemma43VI G) : GL83GenericPrimeThreeA6Lemma43S G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  by_cases hwc : LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
  · subst hp3
    exact a6Lemma43_of_wc hS hU0 hD1 hA1 hAct hInn hWC hK3 hp hM hgen
      ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩ h34 hwc
  · exact h p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34 hwc

end CFSG.LocalAnalysis.RankThreeTheoremC
