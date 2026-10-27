module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Cfg

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.short (h : Lin2Cfg G T M H S L n D) : IsShort2 L := h.cs.block.1.1

theorem Lin2Cfg.charTwo_L (h : Lin2Cfg G T M H S L n D) : CharTwo L := h.short.2.1

theorem Lin2Cfg.S_le_normalizer (h : Lin2Cfg G T M H S L n D) :
    S ≤ Subgroup.normalizer (L : Set G) := by
  intro s hs
  have hle : ∀ t ∈ S, ∀ x ∈ L, t * x * t⁻¹ ∈ L := by
    intro t ht x hx
    have h1 : L.map (MulAut.conj t).toMonoidHom ≤ conjJoin S L :=
      le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩
    rw [h.single] at h1
    exact h1 ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hle s hs x hx, fun hx => ?_⟩
  have := hle s⁻¹ (S.inv_mem hs) _ hx
  have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem Lin2Cfg.H_eq (h : Lin2Cfg G T M H S L n D) : H = L ⊔ S := by
  have := h.cs.eq_join
  rwa [h.single] at this

theorem Lin2Cfg.L_le_H (h : Lin2Cfg G T M H S L n D) : L ≤ H := h.H_eq ▸ le_sup_left

theorem Lin2Cfg.H_le_normalizer_L (h : Lin2Cfg G T M H S L n D) :
    H ≤ Subgroup.normalizer (L : Set G) := by
  rw [h.H_eq]
  exact sup_le Subgroup.le_normalizer h.S_le_normalizer

theorem Lin2Cfg.H_le_normalizer_Q (_h : Lin2Cfg G T M H S L n D) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H

theorem Lin2Cfg.Q_le_S (h : Lin2Cfg G T M H S L n D) : pCoreOf 2 H ≤ S :=
  h.cs.sylow.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
    h.H_le_normalizer_Q (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)

theorem Lin2Cfg.S_isPGroup (h : Lin2Cfg G T M H S L n D) : IsPGroup 2 S := h.cs.sylow.isPGroup

end Cfg

section Block

variable {G : Type*} [Group G]

theorem blockU_le_pCoreOf (L : Subgroup G) : blockU L ≤ pCoreOf 2 L := by
  unfold blockU blockQ
  rw [Subgroup.commutator_le]
  intro q hq ℓ hℓ
  have hn : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have h1 : ℓ * q⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.1 (hn hℓ) q⁻¹).1
    (inv_mem hq)
  have : ⁅q, ℓ⁆ = q * (ℓ * q⁻¹ * ℓ⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact mul_mem hq h1

theorem blockU_le (L : Subgroup G) : blockU L ≤ L :=
  (blockU_le_pCoreOf L).trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L)

theorem blockZ_le_blockU (L : Subgroup G) : blockZ L ≤ blockU L := inf_le_left

theorem blockZ_eq_centerOf {L : Subgroup G} (hc : CharTwo L) (hOL : pCoreOf 2 L = blockU L) :
    blockZ L = centerOf L := by
  apply le_antisymm
  · exact le_inf ((blockZ_le_blockU L).trans (blockU_le L)) inf_le_right
  · refine le_inf ?_ inf_le_right
    have h1 : centerOf L ≤ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      refine le_inf inf_le_left ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have : g ∈ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L hg
      exact (Subgroup.mem_centralizer_iff.1 hz.2 g this).symm ▸ rfl
    intro z hz
    have := hc (h1 hz)
    rwa [hOL] at this

end Block

end CFSG.QuasithinUnique.Lin2
