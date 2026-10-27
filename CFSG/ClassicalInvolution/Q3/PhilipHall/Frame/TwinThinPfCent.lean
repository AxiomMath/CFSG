module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinHyps

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.AE

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem conj_inv_mem : conjSub g⁻¹ K ∈ π := by
  obtain ⟨M, hM, hMK⟩ := S.hos.mem_conj_image_of_mem S.hπ S.hg
  rw [← hMK, conjSub_inv_conjSub]
  exact hM

theorem conj_mem_image : conjSub g K ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
  obtain ⟨a, ha, hKa⟩ := transitive_of_maxOrb S.hos.graph S.hπ _ S.conj_inv_mem _ S.hg
  refine ⟨conjSub (g * a * g⁻¹) K, mem_fam ?_, ?_⟩
  · have ha' : a ∈ piGen π := ha
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using ha'
  · rw [← conjSub_mul, show g⁻¹ * (g * a * g⁻¹) = a * g⁻¹ by group, conjSub_mul]
    exact hKa

theorem pSpan_conj_fam : pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) = piGen π := by
  rw [pSpan_image_conjSub, S.fam_gen]
  exact conjSub_inv_conjSub g _

theorem trans_conj_fam : ∀ L ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)),
    ∀ L' ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)),
      ∃ x ∈ pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))), conjSub x L = L' := by
  rintro _ ⟨L₁, hL₁, rfl⟩ _ ⟨L₂, hL₂, rfl⟩
  obtain ⟨x, hx, hxL⟩ := fam_trans L₁ hL₁ L₂ hL₂
  refine ⟨g⁻¹ * x * g, ?_, ?_⟩
  · rw [S.pSpan_conj_fam]
    have := mem_conjSub_iff.mp hx
    exact this
  · rw [show g⁻¹ * x * g = g⁻¹ * (x * g) by group, conjSub_mul, conjSub_mul]
    have := conjSub_inv_conjSub g⁻¹ L₁
    rw [inv_inv] at this
    rw [this, hxL]

theorem centralizes_of_three {m : ℕ} {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AEQ m)}
    (I : AEIdentOn (fam K (conjSub g (piGen π))) m 𝒜 H)
    (h37 : ∀ Q : Set (Subgroup G), AEIdentOn Q m 𝒜 H → ∀ {y : G},
      y ∈ Subgroup.normalizer (pSpan Q : Set G) → (∃ a : ℕ, y ^ 3 ^ a = 1) → ∀ {L : Subgroup G},
        L ∈ Q → (∀ l ∈ L, y * l = l * y) → (∀ L' ∈ Q, ∃ x ∈ pSpan Q, conjSub x L = L') →
          ∀ x ∈ pSpan Q, y * x = x * y)
    {y : G} (hyX' : y ∈ conjSub g (piGen π)) (hyz : y * z = z * y)
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1) : ∀ x ∈ piGen π, y * x = x * y := by
  have hyN : y ∈ Subgroup.normalizer (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) :
      Set G) := by
    rw [S.pSpan_conj_fam]
    exact S.hos.centralizer_le_normalizer_piGen S.hK S.hπ S.hH1 S.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  have hyL : ∀ l ∈ conjSub g K, y * l = l * y := by
    intro l hl
    have := (S.hos.conj_le_inf_centralizer S.hπ S.hg hl).2
    exact (Subgroup.mem_centralizer_iff.mp this) y hyX'
  have := h37 _ (I.conj g⁻¹) hyN hy3 S.conj_mem_image hyL (S.trans_conj_fam _ S.conj_mem_image)
  rw [S.pSpan_conj_fam] at this
  exact this

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
