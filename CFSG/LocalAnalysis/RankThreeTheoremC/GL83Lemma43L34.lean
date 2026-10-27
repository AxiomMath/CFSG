module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Residues
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1K0
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34Lemma43_of_remark (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK7 : KFactL34SylowTransitive)
    (hrem : GL83GenericPrimeThreeL34Remark G) : GL83GenericPrimeThreeL34Lemma43 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  subst hp3
  have hJ : IsL34Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have hBnorm : M ≤ normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 M : Subgroup G) :
      Set G) :=
    hrem 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hEel, hEcard, -, -⟩ := h34
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  have hxM : x ∈ M := hgen.2.1.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hK₀card : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 :=
    l34Sign_card_inf hS hU0 hK1 hK2 hp hM hgen hJ
  have hK₀E : (P : Subgroup G) ⊓ J ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x := le_sup_left
  have hK₀el : IsElemAbelian 3 ((P : Subgroup G) ⊓ J) := by
    have := hEel.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hK₀E a.2) (hK₀E b.2))⟩⟩,
      fun a ha => hEel.2 a (hK₀E ha)⟩
  have hxK₀ : x ∉ (P : Subgroup G) ⊓ J := by
    intro hx
    have hle : zpowers x ≤ (P : Subgroup G) ⊓ J := zpowers_le.mpr hx
    rw [sup_eq_left.mpr hle, hK₀card] at hEcard
    omega
  have hD2 : 2 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ J) :=
    le_pRank_of_elemAbelian_card (p := 3) (k := 2) le_rfl hK₀el hK₀card
  have hNM : normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤ M := by
    refine le_trans ?_ (hU0 3 hp P M hM)
    unfold rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨(P : Subgroup G) ⊓ J, inf_le_left, hD2, rfl⟩
  have htrans := l34_transitive hK7 hgen hJ
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
  have hxE : x ∈ ((P : Subgroup G) ⊓ J) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hcomm : ∀ e ∈ zpowers ℓ, e * x = x * e := fun e he => by
    have := hEel.1
    exact setLike_mul_comm (hK₀E (zpowers_le.mpr hℓ he)) hxE
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
