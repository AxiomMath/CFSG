module

public import CFSG.LargeExtraspecial.S14SMFDefs
public import CFSG.LargeExtraspecial.S14SMFOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

theorem smithE34a_of_smithE33Conj (h33 : SmithE33Conj) (hQ : SmithE34Q) : SmithE34a := by
  intro G _ _ _ S hw hU x hx hxM hxQ hxz
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  obtain ⟨v, hv, hvQ, hvQx⟩ := h33 G S hw hU g hxM hxQ hxz
  obtain ⟨k, rfl⟩ := isConj_iff.mp hv
  have hvQx' : g⁻¹ * (k * S.z * k⁻¹) * g ∈ S.QG := (SME.mem_Qa_iff S g _).mp hvQx
  have hvz : k * S.z * k⁻¹ ≠ S.z := by
    intro h
    apply SMF.conj_z_not_mem_QG S hxQ
    rw [← h]
    exact hvQx'
  have hvx : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ := fun h => hxQ (h ▸ hvQ)
  have hzQv : k⁻¹ * S.z * k ∈ S.QG :=
    (SME.mem_Qa_iff S k S.z).mp (S.z_mem_Qa_of_mem_QG rfl hvQ hvz)
  have hxQv : k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.QG := SME.mem_Qa_symm S hvQx' hvx
  have hzx : Commute S.z (g * S.z * g⁻¹) :=
    (show Commute (g * S.z * g⁻¹) S.z from mem_centralizer_singleton_iff.mp hxM).symm
  refine hQ G S hw hU k⁻¹ (k⁻¹ * (g * S.z * g⁻¹) * k) (by rw [inv_inv]; exact hzQv)
    (SmithGraph.isConj_conj hx k) hxQv ?_ ?_ ?_
  · rw [inv_inv]
    exact (SmithGraph.commute_conj_iff k S.z _).mpr hzx
  · intro h
    have h' := (SME.mem_Qa_iff S k⁻¹ _).mp h
    rw [show k⁻¹⁻¹ * (k⁻¹ * (g * S.z * g⁻¹) * k) * k⁻¹ = g * S.z * g⁻¹ by group] at h'
    exact hxQ h'
  · have e : k⁻¹ * S.z * k⁻¹⁻¹ * (k⁻¹ * (g * S.z * g⁻¹) * k) =
        k⁻¹ * (g * S.z * g⁻¹ * S.z) * k := by
      calc k⁻¹ * S.z * k⁻¹⁻¹ * (k⁻¹ * (g * S.z * g⁻¹) * k) =
          k⁻¹ * (S.z * (g * S.z * g⁻¹)) * k := by group
        _ = k⁻¹ * (g * S.z * g⁻¹ * S.z) * k := by rw [hzx.eq]
    rw [e]
    exact SmithGraph.isConj_conj hxz k

theorem smithE34b_of (h34a : SmithE34a) : SmithE34b := by
  intro G _ _ _ S hw hU x x' hx hx' hxM hxQ hQ
  have hfix : ∀ {α : G}, IsConj S.z α → α ∈ S.M → α ∉ S.QG →
      S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G)) := by
    intro α hα hαM hαQ
    by_contra hne
    obtain ⟨y, -, hy⟩ := S.lemma_3_2_1 hαM hne
    apply h34a G S hw hU α hα hαM hαQ
    rw [← hy]
    exact hα.trans (isConj_iff.mpr ⟨y, rfl⟩)
  have hhQ : x' * x⁻¹ ∈ S.QG := by
    have e : x' * x⁻¹ = x * (x⁻¹ * x') * x⁻¹ := by group
    rw [e]
    exact S.conj_mem_QG hxM hQ
  set h := x' * x⁻¹ with hh
  have hx'eq : x' = h * x := by rw [hh]; group
  have hhM : h ∈ S.M := S.QG_le_M hhQ
  have hx'M : x' ∈ S.M := by
    rw [hx'eq]
    exact S.M.mul_mem hhM hxM
  have hx'Q : x' ∉ S.QG := by
    intro h'
    apply hxQ
    have e : x = h⁻¹ * x' := by rw [hx'eq]; group
    rw [e]
    exact S.QG.mul_mem (S.QG.inv_mem hhQ) h'
  have hfx := hfix hx hxM hxQ
  have hfx' := hfix hx' hx'M hx'Q
  have hρ : S.fixQt x' = S.fixQt x := by
    rw [S.fixQt_of_mem hx'M, S.fixQt_of_mem hxM]
    have e : S.ρ ⟨x', hx'M⟩ = S.ρ ⟨x, hxM⟩ := by
      rw [show (⟨x', hx'M⟩ : S.M) = ⟨h, hhM⟩ * ⟨x, hxM⟩ from Subtype.ext hx'eq, map_mul,
        (S.ρ_eq_one_iff _).mpr hhQ, one_mul]
    rw [e]
  set C := S.QG ⊓ centralizer ({x} : Set G) with hC
  set C' := S.QG ⊓ centralizer ({x'} : Set G) with hC'
  have hzC : S.z ∈ C := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm⟩
  have hzC' : S.z ∈ C' := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hx'M).symm⟩
  have hCC : C' = C := by
    have e1 : S.clPre (S.clSub C') = C' := S.clPre_clSub inf_le_left hzC'
    have e2 : S.clPre (S.clSub C) = C := S.clPre_clSub inf_le_left hzC
    calc C' = S.clPre (S.clSub C') := e1.symm
      _ = S.clPre (S.clSub C) := by rw [← hfx', hρ, hfx]
      _ = C := e2
  have hhC : h ∈ S.QG ⊓ centralizer (C : Set G) := by
    refine ⟨hhQ, mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs1 : s * x = x * s := mem_centralizer_singleton_iff.mp hs.2
    have hs' : s ∈ C' := by
      rw [hCC]
      exact hs
    have hs2 : s * x' = x' * s := mem_centralizer_singleton_iff.mp hs'.2
    rw [hx'eq] at hs2
    calc s * h = s * (h * x) * x⁻¹ := by group
      _ = h * x * s * x⁻¹ := by rw [hs2]
      _ = h * (x * s) * x⁻¹ := by group
      _ = h * (s * x) * x⁻¹ := by rw [hs1]
      _ = h * s := by group
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    exact SmithQ.mul_self_eq_one_of_isConj S hx
  rw [S.centralizer_inf_QG_eq_clPre inf_le_left, ← hfx, ← S.commQt_eq_orthogonal hxM hx2] at hhC
  obtain ⟨y, hy, hyh⟩ := (S.mem_commQt_iff' hxM).mp hhC.2
  rcases (S.cl_eq_cl_iff (S.commutator_mem_QG' hxM hy) hhQ).mp hyh with h1 | h1
  · refine ⟨y⁻¹, S.QG.inv_mem hy, ?_⟩
    rw [hx'eq, h1]
    group
  · exfalso
    apply h34a G S hw hU x hx hxM hxQ
    have hzx : S.z * x = x * S.z := (S.z_comm hxM).symm
    have hzy : y⁻¹ * S.z = S.z * y⁻¹ := S.z_comm_QG (S.QG.inv_mem hy)
    have e : x' = y * (x * S.z) * y⁻¹ := by
      calc x' = h * x := hx'eq
        _ = y * x * y⁻¹ * x⁻¹ * S.z * x := by rw [h1]
        _ = y * x * y⁻¹ * x⁻¹ * (S.z * x) := by group
        _ = y * x * y⁻¹ * x⁻¹ * (x * S.z) := by rw [hzx]
        _ = y * x * (y⁻¹ * S.z) := by group
        _ = y * x * (S.z * y⁻¹) := by rw [hzy]
        _ = y * (x * S.z) * y⁻¹ := by group
    exact hx'.trans (isConj_iff.mpr ⟨y⁻¹, by rw [e]; group⟩)

end CFSG.LargeExtraspecial.S14
