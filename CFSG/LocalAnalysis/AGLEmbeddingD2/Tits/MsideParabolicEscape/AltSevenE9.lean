module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AltSevenCC

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC

theorem kFactAltSevenE9 : KFactAltSevenE9 := by
  intro W _ _ L E N _ ⟨φ⟩ hEL hE3 hE9 hNL hNE htrans
  set E' : Subgroup (alternatingGroup (Fin 7)) := (E.subgroupOf L).map φ.toMonoidHom with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  obtain ⟨x, hx, y, hy, hx1, hy1, hne⟩ := AltSeven.exists_cc_ne E' hE'9
  obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
  have hx0' : (x0 : W) ∈ E := hx0
  have hy0' : (y0 : W) ∈ E := hy0
  have hx01 : (x0 : W) ≠ 1 := fun h => hx1 (by
    have : x0 = 1 := Subtype.ext h
    simp [this])
  have hy01 : (y0 : W) ≠ 1 := fun h => hy1 (by
    have : y0 = 1 := Subtype.ext h
    simp [this])
  obtain ⟨n, hn, hxy⟩ := htrans _ hx0' _ hy0' hx01 hy01
  have hnL : ∀ l ∈ L, n * l * n⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp (hNL hn) l).mp hl
  have hnL' : ∀ l ∈ L, n⁻¹ * l * n⁻¹⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp (hNL (N.inv_mem hn)) l).mp hl
  let c : ↥L ≃* ↥L :=
    { toFun := fun l => ⟨n * l * n⁻¹, hnL l l.2⟩
      invFun := fun l => ⟨n⁻¹ * l * n⁻¹⁻¹, hnL' l l.2⟩
      left_inv := fun l => by ext; simp [mul_assoc]
      right_inv := fun l => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  let β : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := φ.symm.trans (c.trans φ)
  have hβ : β (φ x0) = φ y0 := by
    simp only [β, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    ext
    simpa [c] using hxy
  have := AltSeven.cc_mulEquiv β (φ x0)
  rw [hβ] at this
  exact hne this.symm

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
