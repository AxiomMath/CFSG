module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.PerfectCommutator
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_commutator' {H P Q : Subgroup G}
    (hP : H ≤ Subgroup.normalizer (P : Set G)) (hQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ hh)]

theorem commutator_commutator_le {Q L : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) : ⁅⁅Q, L⁆, L⁆ ≤ ⁅Q, L⁆ := by
  have hn : L ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hLQ Subgroup.le_normalizer
  rw [Subgroup.commutator_le]
  intro x hx l hl
  have h1 : l * x⁻¹ * l⁻¹ ∈ (⁅Q, L⁆ : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp (hn hl) x⁻¹).mp ((⁅Q, L⁆ : Subgroup G).inv_mem hx)
  have : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
    rw [commutatorElement_def]; group
  rw [this]
  exact (⁅Q, L⁆ : Subgroup G).mul_mem hx h1

theorem commutator_commutator_eq_of_perfect' {Q L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hQL : Q ≤ Subgroup.normalizer (L : Set G)) :
    ⁅⁅Q, L⁆, L⁆ = ⁅Q, L⁆ := by
  refine le_antisymm (commutator_commutator_le hLQ) ?_
  set Y : Subgroup G := Q ⊔ L with hY
  have hQY : Q ≤ Y := le_sup_left
  have hLY : L ≤ Y := le_sup_right
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hLQ
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) := sup_le hQL Subgroup.le_normalizer
  have hYQL : Y ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hYQ hYL
  have hYK : Y ≤ Subgroup.normalizer ((⁅⁅Q, L⁆, L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hYQL hYL
  have hQLL : (⁅Q, L⁆ : Subgroup G) ≤ L := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    have h1 : q * l * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hQL hq) l).mp hl
    have : ⁅q, l⁆ = (q * l * q⁻¹) * l⁻¹ := by rw [commutatorElement_def]
    rw [this]; exact L.mul_mem h1 (L.inv_mem hl)
  have hKY : (⁅⁅Q, L⁆, L⁆ : Subgroup G) ≤ Y :=
    (commutator_commutator_le hLQ).trans (hQLL.trans hLY)
  have hKn : ((⁅⁅Q, L⁆, L⁆ : Subgroup G).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr hYK
  have key : ∀ A B : Subgroup G, A ≤ Y → B ≤ Y →
      (⁅A.subgroupOf Y, B.subgroupOf Y⁆).map Y.subtype = ⁅A, B⁆ := by
    intro A B hA hB
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB]
  have key2 : ∀ A B C : Subgroup G, A ≤ Y → B ≤ Y → C ≤ Y →
      (⁅⁅A.subgroupOf Y, B.subgroupOf Y⁆, C.subgroupOf Y⁆).map Y.subtype = ⁅⁅A, B⁆, C⁆ := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, key A B hA hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have hLQ' : (⁅L, Q⁆ : Subgroup G) = ⁅Q, L⁆ := Subgroup.commutator_comm L Q
  have hAB : ⁅⁅L.subgroupOf Y, Q.subgroupOf Y⁆, L.subgroupOf Y⁆ ≤
      (⁅⁅Q, L⁆, L⁆ : Subgroup G).subgroupOf Y := by
    refine Subgroup.map_le_iff_le_comap.mp ?_
    rw [key2 L Q L hLY hQY hLY, hLQ']
  have hBC : ⁅⁅Q.subgroupOf Y, L.subgroupOf Y⁆, L.subgroupOf Y⁆ ≤
      (⁅⁅Q, L⁆, L⁆ : Subgroup G).subgroupOf Y := by
    refine Subgroup.map_le_iff_le_comap.mp ?_
    rw [key2 Q L L hQY hLY hLY]
  have h3 := CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.three_subgroups_mod_normal
    (A := L.subgroupOf Y) (B := Q.subgroupOf Y) (C := L.subgroupOf Y) hAB hBC
  have h4 := Subgroup.map_le_iff_le_comap.mpr h3
  rw [key2 L L Q hLY hLY hQY, hL] at h4
  rwa [hLQ'] at h4

theorem commutator_eq_of_short {Q V L₁ : Subgroup G} (hS : IsShort2 L₁) (hperf : ⁅L₁, L₁⁆ = L₁)
    (hQL : Q ≤ Subgroup.normalizer (L₁ : Set G)) (hLQ : L₁ ≤ Subgroup.normalizer (Q : Set G))
    (hcore : L₁ ⊓ Q = pCoreOf 2 L₁) (hVQ : V ≤ Q)
    (hLV : L₁ ≤ Subgroup.normalizer (V : Set G)) (hne : ⁅V, L₁⁆ ≠ ⊥) :
    ⁅Q, L₁⁆ = ⁅V, L₁⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono hVQ le_rfl)
  set Q₁ : Subgroup G := pCoreOf 2 L₁ with hQ₁
  set U₁ : Subgroup G := blockU L₁ with hU₁
  set Z₁ : Subgroup G := blockZ L₁ with hZ₁
  set W₁ : Subgroup G := ⁅V, L₁⁆ with hW₁
  have hQ₁L : Q₁ ≤ L₁ := by rw [← hcore]; exact inf_le_left
  have ha : (⁅Q, L₁⁆ : Subgroup G) ≤ Q₁ := by
    rw [← hcore, Subgroup.commutator_le]
    intro q hq l hl
    refine ⟨?_, ?_⟩
    · have h1 : q * l * q⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp (hQL hq) l).mp hl
      have : ⁅q, l⁆ = (q * l * q⁻¹) * l⁻¹ := by rw [commutatorElement_def]
      rw [this]; exact L₁.mul_mem h1 (L₁.inv_mem hl)
    · have h1 : l * q⁻¹ * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hl) q⁻¹).mp (Q.inv_mem hq)
      have : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
      rw [this]; exact Q.mul_mem hq h1
  have hb : (⁅Q, L₁⁆ : Subgroup G) ≤ U₁ := by
    have h := commutator_commutator_eq_of_perfect' hperf hLQ hQL
    calc (⁅Q, L₁⁆ : Subgroup G) = ⁅⁅Q, L₁⁆, L₁⁆ := h.symm
      _ ≤ ⁅Q₁, L₁⁆ := Subgroup.commutator_mono ha le_rfl
  obtain ⟨-, -, ⟨hUQ, -⟩, -, hZlt, hmin⟩ := hS
  have hUabel : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y = y * x := by
    intro x hx y hy
    have := Subgroup.mem_centralizer_iff.mp (hUQ hx).2 y (hUQ hy).1
    exact this.symm
  have hVL : V ≤ Subgroup.normalizer (L₁ : Set G) := hVQ.trans hQL
  have hW₁U : W₁ ≤ U₁ := (Subgroup.commutator_mono hVQ le_rfl).trans hb
  have hZU : Z₁ ≤ U₁ := inf_le_left
  have hZC : ∀ z ∈ Z₁, ∀ g ∈ L₁, g * z * g⁻¹ = z := by
    intro z hz g hg
    have hzC : z ∈ Subgroup.centralizer (L₁ : Set G) :=
      (show z ∈ blockU L₁ ⊓ Subgroup.centralizer (L₁ : Set G) from hz).2
    have := Subgroup.mem_centralizer_iff.mp hzC g hg
    rw [this]; group
  have hWnorm : L₁ ≤ Subgroup.normalizer (W₁ : Set G) :=
    le_normalizer_commutator' hLV Subgroup.le_normalizer
  have hZnorm : L₁ ≤ Subgroup.normalizer (Z₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hZC h hh g hg]; exact hh, fun hh => ?_⟩
    have := hZC _ hh g⁻¹ (L₁.inv_mem hg)
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e] at this
    rw [this]; exact hh
  have hWZnorm : L₁ ≤ Subgroup.normalizer ((W₁ ⊔ Z₁ : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWnorm hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZnorm hg)]
  have hWZ : W₁ ⊔ Z₁ = U₁ := by
    rcases hmin (W₁ ⊔ Z₁) le_sup_right (sup_le hW₁U hZU) hWZnorm with h | h
    · exfalso
      apply hne
      have hWC : W₁ ≤ Subgroup.centralizer (L₁ : Set G) := by
        intro w hw
        have hwZ : w ∈ blockZ L₁ := by rw [← h]; exact Subgroup.mem_sup_left hw
        exact (show w ∈ blockU L₁ ⊓ Subgroup.centralizer (L₁ : Set G) from hwZ).2
      have h0 : ⁅W₁, L₁⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWC
      have := commutator_commutator_eq_of_perfect' hperf hLV hVL
      rw [← hW₁, h0] at this
      exact this.symm
    · exact h
  have hUW : U₁ ≤ W₁ := by
    have h1 : ⁅U₁, L₁⁆ = U₁ :=
      CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.commutator_blockU_eq hperf
    rw [← h1, Subgroup.commutator_le]
    intro x hx l hl
    rw [← hWZ] at hx
    have hUnorm : L₁ ≤ Subgroup.normalizer (U₁ : Set G) :=
      le_normalizer_commutator'
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L₁)
        Subgroup.le_normalizer
    have hmain : ∀ x ∈ W₁ ⊔ Z₁, x ∈ U₁ ∧ ∀ l ∈ L₁, ⁅x, l⁆ ∈ W₁ := by
      intro x hx
      rw [Subgroup.sup_eq_closure] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hw | hz
        · refine ⟨hW₁U hw, fun l hl => ?_⟩
          have h1 : l * x⁻¹ * l⁻¹ ∈ W₁ :=
            (Subgroup.mem_normalizer_iff.mp (hWnorm hl) x⁻¹).mp (W₁.inv_mem hw)
          have : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
          rw [this]; exact W₁.mul_mem hw h1
        · refine ⟨hZU hz, fun l hl => ?_⟩
          have h2 := hZC x hz l hl
          have h3 : x * l = l * x := by
            have := congrArg (· * l) h2; simpa [mul_assoc] using this.symm
          have e : ⁅x, l⁆ = 1 := by rw [commutatorElement_def, h3]; group
          rw [e]; exact W₁.one_mem
      | one => exact ⟨U₁.one_mem, fun l hl => by rw [commutatorElement_one_left]; exact W₁.one_mem⟩
      | mul x y hx hy ihx ihy =>
        obtain ⟨hxU, hx'⟩ := ihx
        obtain ⟨hyU, hy'⟩ := ihy
        refine ⟨U₁.mul_mem hxU hyU, fun l hl => ?_⟩
        have e : ⁅x * y, l⁆ = (x * ⁅y, l⁆ * x⁻¹) * ⁅x, l⁆ := by
          simp only [commutatorElement_def]; group
        have hyl : ⁅y, l⁆ ∈ U₁ := hW₁U (hy' l hl)
        have hc : x * ⁅y, l⁆ * x⁻¹ = ⁅y, l⁆ := by
          have := hUabel x hxU _ hyl
          rw [this]; group
        rw [e, hc]
        exact W₁.mul_mem (hy' l hl) (hx' l hl)
      | inv x hx ih =>
        obtain ⟨hxU, hx'⟩ := ih
        refine ⟨U₁.inv_mem hxU, fun l hl => ?_⟩
        have h1 := W₁.inv_mem (hx' l hl)
        have hlx : l * x * l⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hUnorm hl) x).mp hxU
        have hc := hUabel x⁻¹ (U₁.inv_mem hxU) _ hlx
        have e : ⁅x⁻¹, l⁆ = (⁅x, l⁆)⁻¹ := by
          have : (⁅x, l⁆)⁻¹ = (l * x * l⁻¹) * x⁻¹ := by rw [commutatorElement_def]; group
          rw [this, ← hc, commutatorElement_def]; group
        rw [e]; exact h1
    exact (hmain x hx).2 l hl
  exact hb.trans hUW

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
