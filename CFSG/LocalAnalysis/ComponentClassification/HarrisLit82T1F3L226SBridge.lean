module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226SCrit
public import CFSG.GH74.GLS.Balance.Lift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3L226S

open CFSG Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem isSolvTwoCompSL23In_of_isSolvableTwoComponentIn {A L : Subgroup X}
    (hL : IsSolvableTwoComponentIn L A) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) :
    GH74.GLS.Balance.IsSolvTwoCompSL23In A L := by
  let eL : ↥(L.subgroupOf A) ≃* ↥L := subgroupOfEquivOfLe hL.1
  set χ : ↥(L.subgroupOf A) →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp eL.toMonoidHom) with hχ
  have hχs : Function.Surjective χ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eL.surjective)
  have hO := hL.2.2.1
  have hker : ∀ n : ↥(L.subgroupOf A), χ n = 1 → (n : ↥A) ∈ pPrimeCore 2 ↥A := by
    intro n hn
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥L) (eL n)) = 1 :=
      e.injective (by rw [map_one]; exact hn)
    have h2 : eL n ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((eL n : ↥L) : X) ∈ (pPrimeCore 2 ↥A).map A.subtype := by
      rw [← hO]
      exact ⟨eL n, h2, rfl⟩
    obtain ⟨a, ha, hae⟩ := h3
    have h4 : a = (n : ↥A) := Subtype.ext hae
    rw [← h4]
    exact ha
  have hOL : pPrimeCore 2 ↥A ≤ L.subgroupOf A := by
    intro a ha
    have h1 : (a : X) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      rw [hO]
      exact ⟨a, ha, rfl⟩
    obtain ⟨l, -, hl⟩ := h1
    show (a : X) ∈ L
    rw [← hl]
    exact l.2
  have h := GH74.GLS.Balance.isSolvTwoCompSL23_of_subnormal (L.subgroupOf A) hL.2.1 χ hχs hker
  rw [sup_eq_left.mpr hOL] at h
  exact ⟨hL.1, h⟩

theorem oPrimeResidualOf_map_le {H H' : Type} [Group H] [Finite H] [Group H'] (φ : H →* H')
    (V : Subgroup H) :
    GH74.GLS.oPrimeResidualOf 2 (V.map φ) ≤ (GH74.GLS.oPrimeResidualOf 2 V).map φ := by
  rintro _ ⟨y, hy, rfl⟩
  have hle : GH74.GLS.oPrimeResidual 2 ↥(V.map φ) ≤
      ((GH74.GLS.oPrimeResidualOf 2 V).map φ).comap (V.map φ).subtype := by
    rw [GH74.GLS.oPrimeResidual, closure_le]
    rintro ⟨w, hw⟩ ⟨k, hk⟩
    obtain ⟨v, hv, rfl⟩ := hw
    have hk' : (φ.comp V.subtype) ⟨v, hv⟩ ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    obtain ⟨u, -, ⟨m, hm⟩, hu⟩ := exists_two_element_map (φ.comp V.subtype) ⟨v, hv⟩ hk'
    exact ⟨u, mem_oPrimeResidualOf_of_pow hm, hu⟩
  exact hle hy

omit [Finite X] in
theorem oPrimeResidualOf_le_map_subgroupOf {L C : Subgroup X} (hLC : L ≤ C) :
    GH74.GLS.oPrimeResidualOf 2 L ≤
      (GH74.GLS.oPrimeResidualOf 2 (L.subgroupOf C)).map C.subtype := by
  rintro _ ⟨u, hu, rfl⟩
  have hle : GH74.GLS.oPrimeResidual 2 ↥L ≤
      ((GH74.GLS.oPrimeResidualOf 2 (L.subgroupOf C)).map C.subtype).comap L.subtype := by
    rw [GH74.GLS.oPrimeResidual, closure_le]
    rintro ⟨y, hy⟩ ⟨k, hk⟩
    have hk' : (⟨⟨y, hLC hy⟩, hy⟩ : ↥(L.subgroupOf C)) ^ 2 ^ k = 1 :=
      Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))
    exact ⟨_, mem_oPrimeResidualOf_of_pow hk', rfl⟩
  exact hle hu

end CFSG.ComponentClassification.HarrisLit.T1.F3L226S
