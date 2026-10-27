module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.HardMathSupport.Dickson.I271

theorem normal_of_isSimple_of_index {H : Type*} [Group H] [Finite H] (K : Subgroup H)
    [IsSimpleGroup K] {m : ℕ} (hidx : K.index = m) (hm : m ≠ 0) (hcard : m.factorial < Nat.card H) :
    K.Normal := by
  haveI : K.FiniteIndex := ⟨by omega⟩
  have h1 : K.normalCore.index ∣ K.index.factorial :=
    Subgroup.index_normalCore_dvd_factorial_index K
  have hle : K.normalCore ≤ K := Subgroup.normalCore_le K
  have hne : K.normalCore ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.index_bot, hidx] at h1
    exact absurd (Nat.le_of_dvd (Nat.factorial_pos m) h1) (by omega)
  have hn : (K.normalCore.subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.normalCore.subgroupOf K) with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hle hx
    have hmem : (⟨x, hxK⟩ : K) ∈ K.normalCore.subgroupOf K := hx
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  · have hK : K ≤ K.normalCore := by
      intro x hx
      have : (⟨x, hx⟩ : K) ∈ K.normalCore.subgroupOf K := h ▸ Subgroup.mem_top _
      exact this
    have : K = K.normalCore := le_antisymm hK hle
    rw [this]
    infer_instance

end CFSG.HardMathSupport.Dickson.I271
