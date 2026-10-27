module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRFu
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fzrAux_index_PT (h : Ctx t L S x₁ x₂ lam rho tau) :
    (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex S = 2 := h.index_PT

theorem fzr_elem_le_S (h : Ctx t L S x₁ x₂ lam rho tau) {E : Subgroup G} (hE : E ≤ S)
    (hEel : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 16 := by
  set PT : Subgroup G := twoCore t ⊔ wreathGrp x₁ x₂ lam with hPT
  have hsub : E ⊓ PT ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
    rw [← hPT]; exact inf_le_right
  have hcardPT : Nat.card (E ⊓ PT : Subgroup G) ≤ 8 :=
    h.m2_PT (E ⊓ PT) hsub (CFSG.Open.IsElemAbelian.mono hEel inf_le_left)
  have hrel : (E ⊓ PT).relIndex E ≤ 2 := by
    have h1 : (E ⊓ PT).relIndex E = PT.relIndex E := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    have h2 := Subgroup.relIndex_le_of_le_right (H := PT) (K := E) (L := S) hE
      (by rw [hPT, fzrAux_index_PT h]; norm_num)
    rwa [hPT, fzrAux_index_PT h] at h2
  have hcard : Nat.card E = (E ⊓ PT).relIndex E * Nat.card (E ⊓ PT : Subgroup G) := by
    have h3 := Subgroup.relIndex_mul_card (H := E ⊓ PT) (K := E)
    have h4 : (E ⊓ PT) ⊓ E = E ⊓ PT := by
      ext y; simp only [Subgroup.mem_inf]; tauto
    rw [h4] at h3
    exact h3.symm
  calc Nat.card E = (E ⊓ PT).relIndex E * Nat.card (E ⊓ PT : Subgroup G) := hcard
    _ ≤ 2 * 8 := Nat.mul_le_mul hrel hcardPT
    _ = 16 := by norm_num

theorem fzr_elem_le_cent_of_conj (h : Ctx t L S x₁ x₂ lam rho tau) {T₂ : Subgroup G}
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) {u : G} (hu : ∃ g : G, g⁻¹ * t * g = u)
    {E : Subgroup G} (hE : E ≤ T₂ ⊓ invCent u) (hEel : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 16 := by
  have hS : IsSylowOf 2 S (invCent t) := fzr_isSylowOf_S h.toCtx0
  obtain ⟨g, -, hgS⟩ := fzr_transport hS hT₂ hST hu
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hE'map : E.map (φ : G →* G) ≤ S := by
    rintro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [φ] using hgS c (hE hc)
  have hE'el : CFSG.Open.IsElemAbelian 2 (E.map (φ : G →* G)) :=
    CFSG.Open.IsElemAbelian.map hEel (φ : G →* G)
  have h1 : Nat.card (E.map (φ : G →* G)) ≤ 16 := fzr_elem_le_S h hE'map hE'el
  have h2 : Nat.card (E.map (φ : G →* G)) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := (φ : G →* G)) φ.injective
  omega

theorem fzr_not_conj_of_elem_gt (h : Ctx t L S x₁ x₂ lam rho tau) {T₂ : Subgroup G}
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) {u : G} {E : Subgroup G} (hE : E ≤ T₂ ⊓ invCent u)
    (hEel : CFSG.Open.IsElemAbelian 2 E) (hcard : 16 < Nat.card E) :
    ¬ ∃ g : G, g⁻¹ * t * g = u := by
  rintro ⟨g, hg⟩
  have := fzr_elem_le_cent_of_conj h hT₂ hST ⟨g, hg⟩ hE hEel
  omega

end CFSG.OddStandard.SmallF3.FritzII
