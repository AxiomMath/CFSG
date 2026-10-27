module

public import CFSG.ClassicalInvolution.Asc77.AscC22G2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem rLayer_le_rLayer_of_le_centralizer {c d : G}
    (h : rLayer Ω c ≤ Subgroup.centralizer ({d} : Set G)) : rLayer Ω c ≤ rLayer Ω d := by
  unfold rLayer
  refine iSup₂_le fun R hR => iSup_le fun hRC => ?_
  have hRc : R ≤ rLayer Ω c := C22G.le_rLayer_of_le_centralizer hR hRC
  exact C22G.le_rLayer_of_le_centralizer hR (hRc.trans h)

theorem rLayer_conj (hΩ : ConjInvariant Ω) (g c : G) :
    rLayer Ω (g * c * g⁻¹) = conjSub g (rLayer Ω c) := by
  refine le_antisymm ?_ ?_
  · unfold rLayer
    refine iSup₂_le fun R hR => iSup_le fun hRC => ?_
    have hR' : conjSub g⁻¹ R ∈ RSet Ω := RSet.conj hΩ hR g⁻¹
    have hC' : conjSub g⁻¹ R ≤ Subgroup.centralizer ({c} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxR : g * x * g⁻¹ ∈ R := by
        have h := mem_conjSub_iff.mp hx
        simpa using h
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hRC hxR)
      calc x * c = g⁻¹ * (g * x * g⁻¹ * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hcomm]
        _ = c * x := by group
    calc R = conjSub g (conjSub g⁻¹ R) := (conjSub_conjSub_inv g R).symm
      _ ≤ conjSub g (rLayer Ω c) :=
        conjSub_mono (le_iSup₂_of_le (conjSub g⁻¹ R) hR' (le_iSup_of_le hC' le_rfl))
  · rw [conjSub, Subgroup.map_le_iff_le_comap]
    unfold rLayer
    refine iSup₂_le fun R hR => iSup_le fun hRC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (conjSub g R) (RSet.conj hΩ hR g) (le_iSup_of_le ?_ le_rfl)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxR : g⁻¹ * x * g ∈ R := mem_conjSub_iff.mp hx
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hRC hxR)
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * c * g⁻¹) * x := by group

theorem rLayer_conj_eq_of_le_centralizer [Finite G] (hΩ : ConjInvariant Ω) {c y : G}
    (h : rLayer Ω c ≤ Subgroup.centralizer ({y * c * y⁻¹} : Set G)) :
    rLayer Ω (y * c * y⁻¹) = rLayer Ω c := by
  have h1 : rLayer Ω c ≤ rLayer Ω (y * c * y⁻¹) := rLayer_le_rLayer_of_le_centralizer h
  rw [rLayer_conj hΩ] at h1 ⊢
  have hcard : Nat.card ↥(conjSub y (rLayer Ω c)) = Nat.card ↥(rLayer Ω c) :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  exact (Subgroup.eq_of_le_of_card_ge h1 hcard.le).symm

end CFSG.ClassicalInvolution.Asc77
