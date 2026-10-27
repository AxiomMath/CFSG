module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem map_conj_eq_conjR (X : Subgroup G) (g : G) :
    X.map (MulAut.conj g).toMonoidHom = conjR X g⁻¹ := by
  simp [conjR]

omit [Finite G] in
theorem conjJoin_conjR (X : Subgroup G) {t : G} (ht : t ∈ S) :
    conjJoin S (conjR X t) = conjJoin S X := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    have e : (conjR X t).map (MulAut.conj (s : G)).toMonoidHom = conjR X (t * (s : G)⁻¹) := by
      rw [map_conj_eq_conjR]
      exact conjSubgroup_conjSubgroup X t (s : G)⁻¹
    rw [e]
    exact conjR_le_conjJoin' (S.mul_mem ht (S.inv_mem s.2))
  · refine iSup_le fun s => ?_
    have e : X.map (MulAut.conj (s : G)).toMonoidHom =
        conjR (conjR X t) (t⁻¹ * (s : G)⁻¹) := by
      rw [map_conj_eq_conjR]
      show conjSubgroup X (s : G)⁻¹ = conjSubgroup (conjSubgroup X t) (t⁻¹ * (s : G)⁻¹)
      rw [conjSubgroup_conjSubgroup]
      simp
    rw [e]
    exact conjR_le_conjJoin' (S.mul_mem (S.inv_mem ht) (S.inv_mem s.2))

omit [Finite G] in
theorem conjR_thompsonJ {g : G} (hg : g ∈ S) : conjR (thompsonJ S) g = thompsonJ S :=
  C5.conjSubgroup_eq_self
    (GammaExtra.normalizer_le_normalizer_thompsonJ S (Subgroup.le_normalizer hg))

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem S_le_M : S ≤ M := D.hcs.le_T.trans D.hcs.setting.le

theorem conjR_M {g : G} (hg : g ∈ S) : conjR M g = M :=
  C5.conjSubgroup_eq_self (Subgroup.le_normalizer (D.S_le_M hg))

theorem conjJoin_L₂ : conjJoin S (conjR L t) = conjJoin S L := conjJoin_conjR L D.ht

theorem swap_cs : ConstrainedSetting G T M H S (conjR L t) where
  setting := D.hcs.setting
  notBender := D.hcs.notBender
  notSmall := D.hcs.notSmall
  gamma0 := D.hcs.gamma0
  charTwo := D.hcs.charTwo
  sylow := D.hcs.sylow
  sylow_inf := D.hcs.sylow_inf
  le_T := D.hcs.le_T
  center_le := D.hcs.center_le
  ne_T := D.hcs.ne_T
  witness := D.hcs.witness
  block := ⟨CFSG.Quasithin.IsBlock2.conjByElt_of_mem D.hcs.block.1
    (H.inv_mem (D.hcs.sylow.le D.ht)), Or.inr (Or.inr D.h5₂)⟩
  not_le := by
    intro hle
    apply D.hcs.not_le
    have h1 : conjR (conjR L t) t⁻¹ ≤ conjR M t⁻¹ := C5.conjSubgroup_mono hle t⁻¹
    rw [conjR_conjR_inv, D.conjR_M (S.inv_mem D.ht)] at h1
    exact h1
  thompson := by
    have h1 : conjSubgroup (thompsonJ S) t = thompsonJ S := conjR_thompsonJ D.ht
    have h2 := C5.conjSubgroup_commutator L (thompsonJ S) t
    rw [h1, D.hcs.thompson] at h2
    exact h2.symm
  eq_join := by
    rw [D.conjJoin_L₂]
    exact D.hcs.eq_join
  blocks := by
    refine Or.inr ⟨t, D.ht, ?_, ?_, ?_⟩
    · rw [map_conj_eq_conjR, conjR_conjR_inv]
      exact D.hne.symm
    · rw [D.conjJoin_L₂, D.hjoin, map_conj_eq_conjR, conjR_conjR_inv, sup_comm]
    · rw [map_conj_eq_conjR, conjR_conjR_inv, Subgroup.commutator_comm]
      exact D.hcomm
  minParabolic := D.hcs.minParabolic
  maxInf := D.hcs.maxInf

theorem swap : Dbl T M H S (conjR L t) t⁻¹ where
  hcs := D.swap_cs
  h5 := D.h5₂
  ht := S.inv_mem D.ht
  hne := by rw [conjR_conjR_inv]; exact D.hne.symm
  hjoin := by rw [D.conjJoin_L₂, D.hjoin, conjR_conjR_inv, sup_comm]
  hcomm := by rw [conjR_conjR_inv, Subgroup.commutator_comm]; exact D.hcomm

theorem conjR_blockU_cases {g : G} (hg : g ∈ S) :
    conjR (blockU L) g = blockU L ∨ conjR (blockU L) g = blockU2 L t := by
  rcases D.conjR_cases hg with h | h
  · left; rw [← blockU_conjR, h]
  · right
    show conjR (blockU L) g = conjR (blockU L) t
    rw [← blockU_conjR, ← blockU_conjR, h]

theorem conjR_blockU_of_mem {g : G} (hg : g ∈ s2SI S L) :
    conjR (blockU L) g = blockU L ∧ conjR (blockU2 L t) g = blockU2 L t := by
  have h1 : conjR L g = L := mem_normalizer_iff_conjR.1 hg.2
  have h2 : conjR (conjR L t) g = conjR L t :=
    mem_normalizer_iff_conjR.1 (D.s2SI_le_normalizer_L₂ hg)
  refine ⟨?_, ?_⟩
  · rw [← blockU_conjR, h1]
  · show conjR (conjR (blockU L) t) g = conjR (blockU L) t
    rw [← blockU_conjR, ← blockU_conjR, h2]

theorem conjR_blockU_of_not_mem {g : G} (hg : g ∈ S) (hn : g ∉ normalizer (L : Set G)) :
    conjR (blockU L) g = blockU2 L t ∧ conjR (blockU2 L t) g = blockU L := by
  rcases D.conjR_L₂_cases hg with h | h
  · exact absurd (mem_normalizer_iff_conjR.2 h.1) hn
  · refine ⟨?_, ?_⟩
    · show conjR (blockU L) g = conjR (blockU L) t
      rw [← blockU_conjR, ← blockU_conjR, h.1]
    · show conjR (conjR (blockU L) t) g = blockU L
      rw [← blockU_conjR, ← blockU_conjR, h.2]

end Dbl

end CFSG.QuasithinUnique.AppCS2
