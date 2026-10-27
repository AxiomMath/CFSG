module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowR2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowUMoves
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelRow

public section

namespace CFSG.EvenSporadicStandard.Solomon78.Fi24Row

open CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.FischerOddCore
open CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime (zR)
open CFSG.Sporadic.Fi24 (R J JR tR xb tJ jR jR_mem_JR J_le_R normal_JR index_JR conjJ coe_conjJ
  jR_conjJ conjJ_injective jR_injective D24)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi24_autModel : AutModel (JR : Subgroup R) (⊤ : Subgroup R) where
  le := le_top
  conj_mem := fun x _ p hp => normal_JR.conj_mem p hp x
  surj := by
    intro α
    let e : J ≃* JR := (Subgroup.subgroupOfEquivOfLe J_le_R).symm
    let α' : MulAut J := (e.trans α).trans e.symm
    obtain ⟨r, hr⟩ := CFSG.Sporadic.FischerOddCore.conjJ_surjective α'
    refine ⟨r, Subgroup.mem_top r, fun p => ?_⟩
    obtain ⟨g, rfl⟩ := e.surjective p
    have h1 : ((α (e g) : JR) : R) = jR (α' g) := by
      have : e (α' g) = α (e g) := by
        show e (e.symm (α (e g))) = α (e g)
        exact e.apply_symm_apply _
      rw [← this]
      rfl
    rw [h1, ← hr, jR_conjJ]
    rfl
  inj := by
    intro x _ hx
    apply conjJ_injective
    rw [map_one]
    refine MulEquiv.ext fun g => jR_injective ?_
    rw [jR_conjJ, MulAut.one_apply]
    calc x * jR g * x⁻¹ = jR g * x * x⁻¹ := by rw [hx (jR g) (jR_mem_JR g)]
      _ = jR g := by group

theorem not_mem_JR_conj {w c : R} (hw : w ∉ JR) : c⁻¹ * w * c ∉ JR := fun h' => hw (by
  have h0 := normal_JR.conj_mem _ h' c
  rwa [show c * (c⁻¹ * w * c) * c⁻¹ = w by group] at h0)

theorem fi24_index : ∀ x ∈ (⊤ : Subgroup R), x ∉ (JR : Subgroup R) →
    ∀ y ∈ (⊤ : Subgroup R), y ∉ (JR : Subgroup R) → x⁻¹ * y ∈ (JR : Subgroup R) := by
  intro x _ hx y _ hy
  exact mul_mem_JR_of_not_mem (fun h => hx (by have h0 := JR.inv_mem h; rwa [inv_inv] at h0)) hy

theorem fi24_cases_JR (hPF : CFSG.Fischer.PolarFacts) {a : R} (ha : a ∈ JR) (ha2 : orderOf a = 2) :
    ∃ c ∈ JR, a = c * (tR * xb) * c⁻¹ ∨ a = c * zR * c⁻¹ := by
  obtain ⟨a', ha'⟩ : ∃ a' : J, jR a' = a := by
    have : a ∈ jR.range := by rw [CFSG.Sporadic.Fi24.range_jR]; exact ha
    exact this
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  have ha'2 : a' * a' = 1 := jR_injective (by rw [map_mul, ha', map_one]; exact haa)
  have ha'1 : a' ≠ 1 := by
    rintro rfl
    rw [map_one] at ha'
    rw [← ha', orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  rcases fi24_isConj_cases hPF ha'2 ha'1 with h | h
  · obtain ⟨d, hd⟩ := isConj_iff.1 h
    refine ⟨jR d⁻¹, jR_mem_JR _, Or.inl ?_⟩
    rw [← CFSG.Sporadic.Fi24.jR_tJ, ← hd, ← ha']
    simp only [map_mul, map_inv, inv_inv]
    group
  · obtain ⟨d, hd⟩ := isConj_iff.1 h
    refine ⟨jR d⁻¹, jR_mem_JR _, Or.inr ?_⟩
    show a = _ * jR fi24R2 * _
    rw [← hd, ← ha']
    simp only [map_mul, map_inv, inv_inv]
    group

section Fields

variable (hPF : CFSG.Fischer.PolarFacts)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈
      ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : Fi24.EdgeSwap e)

include hPF hfix22 he in
theorem fi24_centerInv : ∀ a ∈ (JR : Subgroup R), orderOf a = 2 → ∀ z ∈ (JR : Subgroup R),
    z * z = 1 → z * a = a * z → (∀ y ∈ (JR : Subgroup R), y * a = a * y → z * y = y * z) →
    z = 1 ∨ z = a := by
  intro a ha ha2
  obtain ⟨c, hc, h | h⟩ := fi24_cases_JR hPF ha ha2
  · exact centerInv_conj hc h fun z hz hzz hza hall => fi24_ci_tJ hPF hfix22 he hz hza hall
  · exact centerInv_conj hc h fun z hz hzz hza hall => fi24_ci_r2 hzz hall

include hPF hfix22 he in
theorem fi24_outerLe : ∀ a ∈ (JR : Subgroup R), orderOf a = 2 → ∀ w ∈ (⊤ : Subgroup R),
    w ∉ (JR : Subgroup R) → w * w = 1 →
    ¬ ∀ y ∈ (JR : Subgroup R), y * a = a * y → y * w = w * y := by
  intro a ha ha2 w _ hwJ hww hall
  obtain ⟨c, hc, h | h⟩ := fi24_cases_JR hPF ha ha2
  · have key : ∀ y ∈ (JR : Subgroup R), y * (tR * xb) = tR * xb * y →
        y * (c⁻¹ * w * c) = c⁻¹ * w * c * y := by
      intro y hy hyr
      have hy' : c * y * c⁻¹ ∈ JR := normal_JR.conj_mem y hy c
      have hya : c * y * c⁻¹ * a = a * (c * y * c⁻¹) := by
        rw [h]
        calc c * y * c⁻¹ * (c * (tR * xb) * c⁻¹) = c * (y * (tR * xb)) * c⁻¹ := by group
          _ = c * ((tR * xb) * y) * c⁻¹ := by rw [hyr]
          _ = c * (tR * xb) * c⁻¹ * (c * y * c⁻¹) := by group
      have h2 := hall _ hy' hya
      calc y * (c⁻¹ * w * c) = c⁻¹ * (c * y * c⁻¹ * w) * c := by group
        _ = c⁻¹ * (w * (c * y * c⁻¹)) * c := by rw [h2]
        _ = c⁻¹ * w * c * y := by group
    refine fi24_ol_tJ hPF hfix22 he (w := c⁻¹ * w * c) ?_ key
    exact not_mem_JR_conj hwJ
  · have key : ∀ y ∈ (JR : Subgroup R), y * zR = zR * y →
        y * (c⁻¹ * w * c) = c⁻¹ * w * c * y := by
      intro y hy hyr
      have hy' : c * y * c⁻¹ ∈ JR := normal_JR.conj_mem y hy c
      have hya : c * y * c⁻¹ * a = a * (c * y * c⁻¹) := by
        rw [h]
        calc c * y * c⁻¹ * (c * zR * c⁻¹) = c * (y * zR) * c⁻¹ := by group
          _ = c * (zR * y) * c⁻¹ := by rw [hyr]
          _ = c * zR * c⁻¹ * (c * y * c⁻¹) := by group
      have h2 := hall _ hy' hya
      calc y * (c⁻¹ * w * c) = c⁻¹ * (c * y * c⁻¹ * w) * c := by group
        _ = c⁻¹ * (w * (c * y * c⁻¹)) * c := by rw [h2]
        _ = c⁻¹ * w * c * y := by group
    refine fi24_ol_r2 (not_mem_JR_conj hwJ) ?_ key
    calc c⁻¹ * w * c * (c⁻¹ * w * c) = c⁻¹ * (w * w) * c := by group
      _ = 1 := by rw [hww]; group

include hPF hfix22 he in
theorem fi24_autRowData : AutRowData (JR : Subgroup R) (⊤ : Subgroup R) where
  model := fi24_autModel
  index := fi24_index
  centerInv := fi24_centerInv hPF hfix22 he
  outerLe := fi24_outerLe hPF hfix22 he

include hPF hfix22 hcent22 he in
theorem fi24_autCenterCond_P : AutCenterCond ↥(JR : Subgroup R) :=
  AutCenterCondExc.toCond ((fi24_autRowData hPF hfix22 he).autCenterCondExc
    fun _ _ _ hwP _ hww _ hz hz2 hzw hall =>
      (fi24_houter hPF hfix22 hcent22 he hww hwP hz hz2 hzw hall).elim)

include hPF in
theorem fi24_umovesCond_P : UMovesCond ↥(JR : Subgroup R) :=
  AutModel.umovesCond fi24_autModel fun _ hu hu2 _ _ hww => fi24_umoves hPF hu hu2 hww

end Fields

theorem fi24_equiv_P {Y : Type} [Group Y]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic Y .Fi24Prime) :
    Nonempty (Y ≃* ↥(JR : Subgroup R)) := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.Fi24prime := e
  exact ⟨(e'.trans CFSG.Sporadic.Fi24.fi24EquivJ).trans
    (Subgroup.subgroupOfEquivOfLe J_le_R).symm⟩

end CFSG.EvenSporadicStandard.Solomon78.Fi24Row
