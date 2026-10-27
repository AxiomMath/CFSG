module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5LetterSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def yOne (k : Nat) : Equiv.Perm (Fin 1408) := elemW (yWord k 0)

@[expose] noncomputable def yTwo (k : Nat) : Equiv.Perm (Fin 1408) := elemW (yWord k 1)

@[expose] noncomputable def tSub (k : Nat) : Subgroup (Equiv.Perm (Fin 1408)) := wSub (tWords k)

@[expose] noncomputable def mSub (k : Nat) : Subgroup (Equiv.Perm (Fin 1408)) := wSub (mWords k)

@[expose] noncomputable def uElt (k : Nat) : Equiv.Perm (Fin 1408) := elemW (uWord k)

theorem yOne_mem {k : Nat} (hk : k < 2) : yOne k ∈ yK k := by
  have h : yWord k 0 ∈ ykWords.getD k [] := by
    interval_cases k <;> decide
  exact Subgroup.subset_closure ⟨_, h, rfl⟩

theorem yTwo_mem {k : Nat} (hk : k < 2) : yTwo k ∈ yK k := by
  have h : yWord k 1 ∈ ykWords.getD k [] := by
    interval_cases k <;> decide
  exact Subgroup.subset_closure ⟨_, h, rfl⟩

theorem tSub_le_yK (k : Nat) : tSub k ≤ yK k := by
  rw [tSub, wSub, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
  exact elemW_expandL_mem (S := yK k) (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩) l

theorem mSub_le_yK (k : Nat) : mSub k ≤ yK k := by
  rw [mSub, wSub, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
  exact elemW_expandL_mem (S := yK k) (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩) l

theorem uElt_mem_yK (k : Nat) : uElt k ∈ yK k :=
  elemW_expandL_mem (S := yK k) (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩) _

structure TFacts (k : Nat) : Prop where
  card_T : Nat.card ↥(tSub k) = 16
  t₀_mem : elemA * elemZ ∈ tSub k
  cen : ∀ x ∈ tSub k, (∀ y ∈ tSub k, x * y = y * x) → x = 1 ∨ x = elemA * elemZ
  M_le : mSub k ≤ tSub k
  relIndex_M : (mSub k).relIndex (tSub k) = 2
  inv_M : ∀ x ∈ mSub k, orderOf x = 2 → x = elemA * elemZ
  u_mem : uElt k ∈ tSub k
  u_not_M : uElt k ∉ mSub k
  u_ord : orderOf (uElt k) = 2
  u_ne : uElt k ≠ elemA * elemZ
  nonab : yOne k * yTwo k ≠ yTwo k * yOne k

structure TMUFacts : Prop where
  k0 : TFacts 0
  k1 : TFacts 1
  c8 : ∀ v ∈ tSub 0, orderOf v = 2 → v ≠ elemA * elemZ →
    ∃ x ∈ tSub 0, x * v * x⁻¹ = uElt 0 ∨ x * v * x⁻¹ = elemA * elemZ * uElt 0
  fpf : ∀ p : Fin 1408, uElt 1 p ≠ p
  fix : ∃ p : Fin 1408, (elemA * elemZ) p = p

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
