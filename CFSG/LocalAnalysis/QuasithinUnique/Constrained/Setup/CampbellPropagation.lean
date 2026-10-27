module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCommuting

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

section CommutatorSubgroup

variable {G : Type*} [Group G]

def commutatorSubgroup (G₀ Q : Subgroup G) (hQn : G₀ ≤ normalizer (Q : Set G)) :
    Subgroup G where
  carrier := {k | k ∈ G₀ ∧ ∀ q ∈ Q, ⁅q, k⁆ ∈ centerTorsion 2 Q}
  one_mem' := ⟨one_mem _, fun q _ => by
    rw [commutatorElement_one_right]
    exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, hag⟩ ⟨hb, hbg⟩
    refine ⟨mul_mem ha hb, fun q hq => ?_⟩
    have e : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hag q hq) (conj_mem_centerTorsion (hQn ha) (hbg q hq))
  inv_mem' := by
    rintro a ⟨ha, hag⟩
    refine ⟨inv_mem ha, fun q hq => ?_⟩
    have e : ⁅q, a⁻¹⁆ = a⁻¹ * (⁅q, a⁆)⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have := conj_mem_centerTorsion (hQn (inv_mem ha)) (inv_mem (hag q hq))
    simpa using this

theorem mem_commutatorSubgroup {G₀ Q : Subgroup G} {hQn : G₀ ≤ normalizer (Q : Set G)} {k : G} :
    k ∈ commutatorSubgroup G₀ Q hQn ↔ k ∈ G₀ ∧ ∀ q ∈ Q, ⁅q, k⁆ ∈ centerTorsion 2 Q :=
  Iff.rfl

end CommutatorSubgroup

section Propagation

variable {G : Type*} [Group G] [Finite G]

theorem full_Sylow_short_core_propagation {G₀ H S Y : Subgroup G} (hG₀ : CharTwo G₀)
    (hS : IsSylowTwoOf S G₀) (hSH : S ≤ H) (hHG : H ≤ G₀) (hY : IsBlock2 H Y) :
    blockU Y ≤ centerTorsion 2 (blockQ G₀) ∧ ⁅blockQ G₀, Y⁆ = blockU Y ∧
      ⁅blockQ G₀, conjJoin G₀ Y⁆ ≤ centerTorsion 2 (blockQ G₀) := by
  classical
  set Q : Subgroup G := blockQ G₀ with hQ
  have hYH : Y ≤ H := hY.2.1
  have hYsub : (Y.subgroupOf H).IsSubnormal := hY.2.2
  have hYshort : IsShort2 Y := hY.1
  have hYG : Y ≤ G₀ := hYH.trans hHG
  have hQ2 : IsPGroup 2 Q := C1.blockQ_isPGroup G₀
  have hQn : G₀ ≤ normalizer (Q : Set G) := C1.le_normalizer_blockQ G₀
  have hQH : Q ≤ H := (hS.pCoreOf_le : Q ≤ S).trans hSH
  obtain ⟨hQY, hYQ⟩ := signalizer_action_ambient hYH hYsub hYshort.1 hQ2 hQH (hYG.trans hQn)
  have hcommQ : ∀ y ∈ Q, ∀ l ∈ Y, y * l * y⁻¹ * l⁻¹ ∈ blockQ Y := by
    intro y hy l hl
    have hmem : ⁅y, l⁆ ∈ ⁅Q, Y⁆ := Subgroup.commutator_mem_commutator hy hl
    rw [Subgroup.commutator_comm] at hmem
    exact hYQ hmem
  have hQcU : ∀ y ∈ Q, ∀ u ∈ blockU Y, u * y = y * u := fun y hy =>
    C1.commute_blockU_of_mem hYshort (hQY hy) (C1.exists_pow_eq_one_of_isPGroup hQ2 hy)
      (hcommQ y hy)
  have hUQ : blockU Y ≤ Q := by
    intro u hu
    refine hG₀ (Subgroup.mem_inf.mpr ⟨hYG (blockU_le_self_of_isShort2 hYshort hu), ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hQcU y hy u hu).symm
  have hUW : blockU Y ≤ centerTorsion 2 Q := by
    intro u hu
    exact mem_centerTorsion_iff.mpr ⟨hUQ hu, fun k hk => (hQcU k hk u hu).symm,
      C1.blockU_sq hYshort u hu⟩
  have hQYU : ⁅Q, Y⁆ = blockU Y := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro y hy l hl
      exact C1.commutator_mem_blockU_of_mem_blockQ hYshort (hcommQ y hy) l hl
    · calc blockU Y = ⁅blockU Y, Y⁆ := (C1.commutator_blockU hYshort).symm
        _ ≤ ⁅Q, Y⁆ := Subgroup.commutator_mono hUQ le_rfl
  have hconj : ∀ s : G₀, Y.map (MulAut.conj (s : G)).toMonoidHom ≤
      commutatorSubgroup G₀ Q hQn := by
    intro s x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨?_, fun q hq => ?_⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem s.2 (hYG hy)) (inv_mem s.2)
    · have hq' : (s : G)⁻¹ * q * (s : G) ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hQn (inv_mem s.2)) q).mp hq
        simpa using this
      have hw : ⁅(s : G)⁻¹ * q * (s : G), y⁆ ∈ centerTorsion 2 Q :=
        hUW (hQYU ▸ Subgroup.commutator_mem_commutator hq' hy)
      have hw' := conj_mem_centerTorsion (hQn s.2) hw
      have e : ⁅q, (MulAut.conj (s : G)).toMonoidHom y⁆ =
          (s : G) * ⁅(s : G)⁻¹ * q * (s : G), y⁆ * (s : G)⁻¹ := by
        simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hw'
  have hK : conjJoin G₀ Y ≤ commutatorSubgroup G₀ Q hQn := iSup_le hconj
  refine ⟨hUW, hQYU, ?_⟩
  rw [Subgroup.commutator_le]
  intro q hq k hk
  exact (hK hk).2 q hq

end Propagation

end CFSG.QuasithinUnique.Setup.Campbell
