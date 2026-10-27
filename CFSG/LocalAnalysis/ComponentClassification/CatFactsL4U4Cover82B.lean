module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover82A
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZ
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCover

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

@[expose] def A10CoverComponents : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → center Y ≠ ⊥ →
    Nonempty (Y ⧸ center Y ≃* alternatingGroup (Fin 10)) →
    ∀ y₀ : Y, y₀ ∉ center Y → y₀ ^ 2 ∈ center Y →
    ∀ M : Subgroup Y, M ≤ centralizer ({y₀} : Set Y) →
      IsPComponent 2 (M.subgroupOf (centralizer ({y₀} : Set Y))) →
      center (↥M ⧸ pPrimeCore 2 ↥M) ≠ ⊥

theorem cf82Cover_of (hMult : MultiplierL4U4) (hA10 : A10CoverComponents) : CF82Cover := by
  intro G _ _ p f hp hp2 hf Y hYq hYZ htype t ht2 htN hinner M hMC hMcomp hMtype
  classical
  obtain ⟨y₀, hy₀Y, hy₀⟩ := hinner
  have hMY : M ≤ Y := hMC.trans inf_le_left
  have hcomm : ∀ w ∈ Y, (w * t = t * w ↔ w * y₀ = y₀ * w) := by
    intro w hw
    have h := hy₀ w hw
    constructor
    · intro h1
      have h2 : y₀ * w * y₀⁻¹ = w := by rw [← h, ← h1, mul_inv_cancel_right]
      calc w * y₀ = (y₀ * w * y₀⁻¹) * y₀ := by rw [h2]
        _ = y₀ * w := by group
    · intro h1
      have h2 : t * w * t⁻¹ = w := by rw [h, ← h1, mul_inv_cancel_right]
      calc w * t = (t * w * t⁻¹) * t := by rw [h2]
        _ = t * w := by group
  have hCeq : Y ⊓ centralizer ({t} : Set G) = Y ⊓ centralizer ({y₀} : Set G) := by
    ext w
    simp only [mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun ⟨hw, h⟩ => ⟨hw, (hcomm w hw).mp h⟩, fun ⟨hw, h⟩ => ⟨hw, (hcomm w hw).mpr h⟩⟩
  rw [hCeq] at hMC hMcomp
  have : Group.IsPerfect ↥Y := hYq.1
  set ℓ : ↥Y := ⟨y₀, hy₀Y⟩ with hℓ
  have hℓ2 : ℓ ^ 2 ∈ center ↥Y := by
    rw [mem_center_iff]
    intro w
    apply Subtype.ext
    have htw : t * (w : G) * t⁻¹ ∈ Y := (mem_normalizer_iff.mp htN (w : G)).mp w.2
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h3 : t * (t * (w : G) * t⁻¹) * t⁻¹ = w := by
      rw [ht']
      calc t * (t * (w : G) * t) * t = (t * t) * (w : G) * (t * t) := by group
        _ = w := by rw [ht2, one_mul, mul_one]
    rw [hy₀ _ htw, hy₀ _ w.2] at h3
    show (w : G) * y₀ ^ 2 = y₀ ^ 2 * w
    rw [sq]
    calc (w : G) * (y₀ * y₀) = (y₀ * (y₀ * (w : G) * y₀⁻¹) * y₀⁻¹) * (y₀ * y₀) := by rw [h3]
      _ = y₀ * y₀ * w := by group
  set J : Subgroup ↥Y := M.subgroupOf Y with hJdef
  have hJC : J ≤ centralizer {ℓ} := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hMC (mem_subgroupOf.mp hx)).2)
  have eJM : ↥J ≃* ↥M := subgroupOfEquivOfLe hMY
  have hJtype : IsSec8JType (↥J ⧸ pPrimeCore 2 ↥J) p f :=
    isSec8JType_of_mulEquiv
      (QuotientGroup.congr (pPrimeCore 2 ↥J) (pPrimeCore 2 ↥M) eJM (pPrimeCore_map_iso 2 eJM)).symm
      hMtype
  have hZJ := center_eq_bot_of_isSec8JType hp hp2 hf hJtype
  obtain ⟨hJc, ⟨s, hs, hs2, hsq, hsQ, hsJ⟩, hnc⟩ := jdata hp hp2 hf hJtype
  have hJp : ⁅J, J⁆ = J :=
    AZ.subgroupOf_perfect hMY (commutator_eq_self_of_isPComponent hMC hMcomp)
  by_cases hℓZ : ℓ ∈ center ↥Y
  ·
    have hCY : Y ⊓ centralizer ({y₀} : Set G) = Y := by
      refine le_antisymm inf_le_left fun w hw => mem_inf.mpr ⟨hw, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_center_iff.mp hℓZ ⟨w, hw⟩)
    rw [hCY] at hMcomp
    obtain ⟨-, -, hJsub, -, -⟩ := hMcomp
    have hq := le_sq_mul (three_le_pow hp hp2 hf)
    rcases hJsub.lt_normal with htop | ⟨K, hKn, hJK, hKlt⟩
    · have hMeq : M = Y := by
        refine le_antisymm hMY fun w hw => ?_
        have hw' : (⟨w, hw⟩ : ↥Y) ∈ J := by
          rw [hJdef, htop]
          exact mem_top _
        exact mem_subgroupOf.mp hw'
      rw [hMeq] at hMtype
      exact false_of_central hp hp2 hf hYq htype hMtype
    · have : K.Normal := hKn
      rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hYq K with hK | hK
      · have hJb : J = ⊥ := by
          rw [← hJp, commutator_eq_bot_iff_le_centralizer]
          exact (hJK.trans hK).trans (center_le_centralizer _)
        have h1 : Nat.card J = 1 := by rw [hJb, card_bot]
        omega
      · exact absurd hK hKlt.ne
  rcases htype with hL | hU | hA
  ·
    have hZ2 := hMult ↥Y hYq p f hp hp2 hf (Or.inl hL)
    obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
    let : Fintype F := Fintype.ofFinite F
    have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
    have hqF : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
    exact hYZ (center_eq_bot_of_inner_L4 hZ2 hqF eL hℓZ hℓ2 hJC hJp (by rw [hFq]; exact hJc) hs
      hs2 (by rw [hFq]; exact hsq) hsJ hnc)
  ·
    obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
    have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
      ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
    have : IsSimpleGroup (↥Y ⧸ center ↥Y) := hYq.2.1
    have hZbar : center (↥Y ⧸ center ↥Y) = ⊥ := center_eq_bot_of_simple hYq.2.2
    have hZ2bar : IsPGroup 2 (center (↥Y ⧸ center ↥Y)) := by
      rw [hZbar]
      exact IsPGroup.of_card (n := 0) (by rw [card_bot, pow_zero])
    have eZ : (↥Y ⧸ center ↥Y) ⧸ center (↥Y ⧸ center ↥Y) ≃* ↥Y ⧸ center ↥Y :=
      (QuotientGroup.quotientMulEquivOfEq hZbar).trans QuotientGroup.quotientBot
    have hℓbar : (QuotientGroup.mk ℓ : ↥Y ⧸ center ↥Y) ∉ center (↥Y ⧸ center ↥Y) := by
      rw [hZbar, mem_bot, QuotientGroup.eq_one_iff]
      exact hℓZ
    have hℓbar2 : (QuotientGroup.mk ℓ : ↥Y ⧸ center ↥Y) ^ 2 ∈ center (↥Y ⧸ center ↥Y) := by
      rw [hZbar, mem_bot, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hℓ2
    obtain ⟨u, huJ, hus⟩ := exists_orderOf_mk_eq hZJ hs hsQ
    have huℓ : (QuotientGroup.mk u : ↥Y ⧸ center ↥Y) * QuotientGroup.mk ℓ =
        QuotientGroup.mk ℓ * QuotientGroup.mk u := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        mem_centralizer_singleton_iff.mp (hJC huJ)]
    have hq1 := card_mod_four_of_inner_U4 hUF hZ2bar hp2 (eZ.trans eU) hℓbar hℓbar2 hs hs2 hsq
      hus huℓ
    have hZ2 := hMult ↥Y hYq p f hp hp2 hf (Or.inr ⟨hU, by omega⟩)
    exact hYZ (center_eq_bot_of_inner_U4 hUF hZ2 hp2 eU hℓZ hℓ2 hJC hJp hJc hs hs2 hsq hsJ hnc)
  ·
    exact hA10 ↥Y hYq hYZ hA ℓ hℓZ hℓ2 J hJC
      (isPComponent_subgroupOf_centralizer hy₀Y hMC hMcomp) hZJ

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4
