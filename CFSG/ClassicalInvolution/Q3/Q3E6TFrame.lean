module

public import CFSG.ClassicalInvolution.Q3.Q3TWWFrameD

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3TW
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.WeakCT
  (blk blockSL LinearBlockStandardPair map_blk map_map_symm map_symm_map)
open scoped MatrixGroups

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))

set_option linter.unusedSectionVars false

section Frame

variable {F : Type} [Field F] [Finite F] {H : Type} [Group H]

theorem exists_frameOfLayer (e : ZMod 3 ≃+* F) (L : TwistedLayer H) (lb : SL(2, F) →* H)
    (S₀ : Subgroup H)
    (hL1 : L.lbZ = lb.comp (Matrix.SpecialLinearGroup.map e.toRingHom))
    (hL2 : L.S = S₀) {n : ℕ} (hn : 4 ≤ n) {X : Type} [Group X]
    (U : Fin (n - 1) → Subgroup X)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC : TD4Collapse)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (θ0 : H →* X) (hθl : Function.Injective (θ0.comp lb))
    (hθU : lb.range.map θ0 = U ⟨n - 3, by omega⟩)
    (hθV : S₀.map θ0 = U ⟨n - 2, by omega⟩) :
    ∃ (θ' : H →* X) (ρ' : Fin (n - 2) → (SL(2, F) →* X)),
      S₀.map θ' = U ⟨n - 2, by omega⟩ ∧
      ρ' ⟨n - 2 - 1, by omega⟩ = θ'.comp lb ∧
      (∀ k, Function.Injective (ρ' k) ∧ (ρ' k).range = U ⟨k.val, by omega⟩) ∧
      ∀ i j : Fin (n - 2), i.val + 1 = j.val →
        ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  obtain ⟨FA, hFA⟩ := Q3W.exists_ctFamily_of_pairs3 (by omega : 2 ≤ m + 2)
    (U := fun i : Fin (m + 2) => U ⟨i.val, by omega⟩)
    (fun i j hij x hx y hy => hcomm ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij x hx y hy)
    (fun i j hij => (hpair ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij.symm
      (by simp only; omega)).imp fun W hW => hW.of_ringEquiv e.symm)
  have hleft : (FA.θ ⟨m, by omega⟩).comp (blockSL (ZMod 3) 3 2 0 (by omega)) =
      FA.ι ⟨m, by omega⟩ := FA.left ⟨m, by omega⟩ (by simp)
  have hright : (FA.θ ⟨m, by omega⟩).comp (blockSL (ZMod 3) 3 2 1 (by omega)) =
      FA.ι ⟨m + 1, by omega⟩ := FA.right ⟨m, by omega⟩ (by simp)
  have hιL : Function.Injective (θ0.comp L.lbZ) := by
    rw [hL1, ← MonoidHom.comp_assoc]
    exact hθl.comp (slMap_injective e 2)
  have hB1 : L.lbZ.range.map θ0 = U ⟨m + 1, by omega⟩ := by
    rw [← MonoidHom.range_comp, hL1, ← MonoidHom.comp_assoc,
      range_comp_of_surjective _ (slMap_surjective e 2), MonoidHom.range_comp]
    exact hθU
  have hB2 : L.S.map θ0 = U ⟨m + 2, by omega⟩ := by
    rw [hL2]
    exact hθV
  obtain ⟨θA', θ', hA'0, hθ'L, hιA', hA'1, hS'⟩ := exists_adjust_td4 L (U ⟨m, by omega⟩)
    (U ⟨m + 1, by omega⟩) (U ⟨m + 2, by omega⟩)
    (hcomm ⟨m, by omega⟩ ⟨m + 2, by omega⟩ (by simp)) hC (FA.θ ⟨m, by omega⟩)
    (by rw [hright]; exact (hFA _).2)
    (by rw [← MonoidHom.range_comp, hleft]; exact (hFA _).1)
    (by rw [← MonoidHom.range_comp, hright]; exact (hFA _).1) θ0 hιL hB1 hB2
  let ρZ : Fin (m + 4 - 2) → (SL(2, ZMod 3) →* X) := fun k =>
    if h : k.val < m + 1 then FA.ι ⟨k.val, by omega⟩ else θA'.comp bA1
  have hρZ0 : ∀ (k : Fin (m + 4 - 2)) (h : k.val < m + 1), ρZ k = FA.ι ⟨k.val, by omega⟩ :=
    fun k h => dite_eq_left h
  have hρZ1 : ∀ k : Fin (m + 4 - 2), ¬ k.val < m + 1 → ρZ k = θA'.comp bA1 :=
    fun k h => dite_eq_right h
  refine ⟨θ', fun k => (ρZ k).comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom), ?_, ?_, ?_,
    ?_⟩
  · rw [← hL2]
    exact hS'
  · show (ρZ ⟨m + 4 - 2 - 1, by omega⟩).comp _ = _
    rw [hρZ1 _ (by simp only; omega)]
    refine MonoidHom.ext fun A => ?_
    show θA' (bA1 (Matrix.SpecialLinearGroup.map e.symm.toRingHom A)) = θ' (lb A)
    rw [← hθ'L, hL1]
    show θ' (lb (Matrix.SpecialLinearGroup.map e.toRingHom
      (Matrix.SpecialLinearGroup.map e.symm.toRingHom A))) = _
    rw [map_symm_map]
  · intro k
    by_cases hk : k.val < m + 1
    · show Function.Injective ((ρZ k).comp _) ∧ ((ρZ k).comp _).range = _
      rw [hρZ0 k hk]
      exact ⟨(hFA ⟨k.val, by omega⟩).2.comp (slMap_injective e.symm 2), by
        rw [range_comp_of_surjective _ (slMap_surjective e.symm 2)]
        exact (hFA ⟨k.val, by omega⟩).1⟩
    · show Function.Injective ((ρZ k).comp _) ∧ ((ρZ k).comp _).range = _
      rw [hρZ1 k hk]
      refine ⟨hιA'.comp (slMap_injective e.symm 2), ?_⟩
      rw [range_comp_of_surjective _ (slMap_surjective e.symm 2), MonoidHom.range_comp]
      have hk' : (⟨k.val, by omega⟩ : Fin (m + 4 - 1)) = ⟨m + 1, by omega⟩ :=
        Fin.ext (by have := k.2; simp only; omega)
      rw [hk']
      exact hA'1
  · intro i j hij
    by_cases hi : i.val < m
    · refine ⟨(FA.θ ⟨i.val, by omega⟩).comp
        (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(3, F) →* SL(3, ZMod 3)), ?_, ?_⟩
      · show _ = (ρZ i).comp _
        rw [hρZ0 i (by omega)]
        exact comp_map_blk_eq e.symm.toRingHom 0 _ _
          (FA.left ⟨i.val, by omega⟩ (by show i.val + 1 < m + 2; omega))
      · show _ = (ρZ j).comp _
        rw [hρZ0 j (by omega)]
        refine (comp_map_blk_eq e.symm.toRingHom 1 _ _
          (FA.right ⟨i.val, by omega⟩ (by show i.val + 1 < m + 2; omega))).trans ?_
        have hjj : (⟨i.val + 1, by omega⟩ : Fin (m + 2)) = ⟨j.val, by omega⟩ :=
          Fin.ext (by show i.val + 1 = j.val; omega)
        rw [hjj]
    · have him : i.val = m := by have := i.2; have := j.2; omega
      refine ⟨θA'.comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(3, F) →*
        SL(3, ZMod 3)), ?_, ?_⟩
      · show _ = (ρZ i).comp _
        rw [hρZ0 i (by omega)]
        refine comp_map_blk_eq e.symm.toRingHom 0 _ _ ?_
        refine hA'0.trans (hleft.trans ?_)
        exact congrArg FA.ι (Fin.ext him.symm)
      · show _ = (ρZ j).comp _
        rw [hρZ1 j (by omega)]
        exact comp_map_blk_eq e.symm.toRingHom 1 _ _ rfl

end Frame

section Injective

theorem injective_of_range_eq {A B : Type} [Group A] [Finite A] [Group B] {f f' : A →* B}
    (hf : Function.Injective f) (h : f.range = f'.range) : Function.Injective f' := by
  have hset : (fun x : B => x ∈ Set.range f) = (fun x : B => x ∈ f'.range) := by
    funext x
    apply propext
    rw [← h]
    exact Iff.rfl
  let e : A ≃ f'.range := (Equiv.ofInjective f hf).trans (Equiv.subtypeEquivProp hset)
  have hinj : Function.Injective f'.rangeRestrict :=
    (Finite.injective_iff_surjective_of_equiv e).2 f'.rangeRestrict_surjective
  intro a b hab
  exact hinj (Subtype.ext hab)

end Injective

end CFSG.ClassicalInvolution.Q3.Q3E6T
