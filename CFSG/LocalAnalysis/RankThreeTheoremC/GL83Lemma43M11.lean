module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34SDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Case2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43M11Point

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem m11Lemma43S_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hK3 : KFactOutCyclic) : GL83GenericPrimeThreeM11Lemma43S G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34S
  subst hp3
  have hJ : IsM11Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hS.simple
  obtain ⟨⟨hPab, hwc⟩, hEel, hEcard, -⟩ := h34S
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  have hxM : x ∈ M := hgen.2.1.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  obtain ⟨hK₀el, hK₀card, hxK₀⟩ := p34_inf_data hS hU0 hKM hKA hp hM hgen hJ
  obtain ⟨hNM, hOxM, htrans, hCM⟩ := m11_point_facts hS hU0 hKM hKA hKT hp hM hgen hJ
  have hSC := m11_point_strongClosed hS hU0 hKM hKA hp hM hgen hJ hPab hwc
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1.1
  have hK₀P : (P : Subgroup G) ⊓ J ≤ (P : Subgroup G) := inf_le_left
  have hK₀C : (P : Subgroup G) ⊓ J ≤ centralizer ({x} : Set G) := inf_le_right.trans hJC
  have hBnorm := m11_normalizer_sup_of_data hS.kProper hInn hWC hK3 hPab hMtop hPM hxP hx3 hx1 hwc
    hK₀P hK₀C hK₀el (by simpa using hK₀card) htrans hNM hOxM hCM hSC
  have hdata : E9Case1Data G M (GLBPrimeCore 3 M) ((P : Subgroup G) ⊓ J) x :=
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
      E_card := by rw [sup_comm]; simpa using hEcard
      B_norm := hBnorm
      trans := fun a ha b hb ha1 hb1 => by
        obtain ⟨n, -, hnN, hnab⟩ := htrans a ha b hb ha1 hb1
        exact ⟨n, hNM hnN, hnab⟩
      D1 := fun Y₀ hne h2 hr =>
        le_of_three_le_pRank_inf hD1 hp hM ⟨Y₀, hne, h2, rfl⟩ hr }
  obtain ⟨ℓ, hℓ, hℓ1⟩ : ∃ ℓ ∈ (P : Subgroup G) ⊓ J, ℓ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : (P : Subgroup G) ⊓ J = ⊥ := eq_bot_iff.mpr fun g hg => mem_bot.mpr (hcon g hg)
    rw [hbot, Subgroup.card_bot] at hK₀card
    omega
  have hℓ3 : ℓ ^ 3 = 1 := hK₀el.2 ℓ hℓ
  have hℓP : ℓ ∈ (P : Subgroup G) := hℓ.1
  have hxℓ : x ∉ zpowers ℓ := fun h => hxK₀ (zpowers_le.mpr hℓ h)
  have hcomm : ∀ e ∈ zpowers ℓ, e * x = x * e := fun e he => by
    have := hPab
    exact setLike_mul_comm (zpowers_le.mpr hℓP he) hxP
  have hUle : zpowers ℓ ⊔ zpowers x ≤ (P : Subgroup G) :=
    sup_le (zpowers_le.mpr hℓP) (zpowers_le.mpr hxP)
  have hUE : zpowers ℓ ⊔ zpowers x ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x :=
    sup_le_sup_right (zpowers_le.mpr hℓ) _
  refine ⟨zpowers ℓ ⊔ zpowers x, hUle, ?_, ?_, mem_sup_right (mem_zpowers x), ?_⟩
  · have := hEel.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hUE a.2) (hUE b.2))⟩⟩,
      fun a ha => hEel.2 a (hUE ha)⟩
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers ℓ) hx3 hxℓ hcomm,
      Nat.card_zpowers, orderOf_eq_prime hℓ3 hℓ1]
    norm_num
  · intro Y hY2 hYM hUY hYO
    exact hdata.normalizer_le hℓ hℓ1 hY2 hYM hYO (hUY (mem_sup_right (mem_zpowers x)))
      (hUY (mem_sup_left (mem_zpowers ℓ)))

end CFSG.LocalAnalysis.RankThreeTheoremC
