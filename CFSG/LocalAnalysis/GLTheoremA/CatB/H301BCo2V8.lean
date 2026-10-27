module

public import CFSG.Sporadic.Co2I301.Spec
public import Certificates.Certificate101707

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2V8

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2I301
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed
  CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative
open CFSG.RankThree.Native
open scoped Matrix

section Cert


section BitSpan

variable {P : ℕ → Prop} (hxor : ∀ a b, P a → P b → P (a ^^^ b))
include hxor

theorem bitsIn_spanStepL {Ts : List (Array ℕ)}
    (hT : ∀ T ∈ Ts, ∀ a, P a → P (vecMulN 8 T a)) {S : ℕ} (hS : BitsIn P S) :
    BitsIn P (spanStepL Ts S) := by
  unfold spanStepL
  refine foldl_invariant (BitsIn P) _ (fun acc a hacc => ?_) _ S hS
  split_ifs with ha
  · exact List.foldlRecOn Ts _ hacc (fun acc' hacc' T hTm =>
      bitsIn_spanIns hxor hacc' (hT T hTm a (hS a ha)))
  · exact hacc

theorem bitsIn_spanIterL {Ts : List (Array ℕ)} (hT : ∀ T ∈ Ts, ∀ a, P a → P (vecMulN 8 T a)) :
    ∀ (n : ℕ) {S : ℕ}, BitsIn P S → BitsIn P (spanIterL Ts n S)
  | 0, _, hS => hS
  | n + 1, _, hS => bitsIn_spanIterL hT n (bitsIn_spanStepL hxor hT hS)

end BitSpan

section Cols

theorem conjEnd_qVec_cols {g : locC} {arr cols : Array ℕ}
    (hg : Rep 2300 arr (g : Equiv.Perm (Fin 2300)))
    (hgi : Rep 2300 (invCand 2300 arr) (g : Equiv.Perm (Fin 2300))⁻¹) {l : ℕ} (hl : l < 8)
    (h : isProdOrZ (compA 2300 (compA 2300 arr qArrs[l]!) (invCand 2300 arr)) cols[l]! = true) :
    conjEnd (Q := locQ.subgroupOf locC) g (qπ (qcGen l)) = qcCoord (toVecD 8 cols[l]!) := by
  rw [conjEnd_qπ, ← qπ_prod_bits8]
  have hrep : Rep 2300 (compA 2300 (compA 2300 arr qArrs[l]!) (invCand 2300 arr))
      (((MulAut.conjNormal g (qcGen l) : locQ.subgroupOf locC) : locC) :
        Equiv.Perm (Fin 2300)) := by
    rw [coe_conjNormal_qc]
    exact rep_compA (rep_compA hg (rep_qcGen hl)) hgi
  have hp := rep_prodArr repTuple_q (l := bits8 cols[l]!) (fun k hk => by
    rw [qTuple_length]
    exact List.mem_range.1 (List.mem_filter.1 hk).1)
  rw [isProdOrZ, qProdArr, Bool.or_eq_true] at h
  rcases h with h | h
  · congr 1
    exact Subtype.ext (Subtype.ext (eq_of_eqA hrep hp h))
  · have he : MulAut.conjNormal g (qcGen l) =
        toQc (prodList qTuple (bits8 cols[l]!)) (prodList_mem_Q _) * zQc :=
      Subtype.ext (Subtype.ext (eq_of_eqA hrep (rep_compA hp rep_z) h))
    rw [he, qπ_mul, qπ_zQc, add_zero]

private theorem getD_zero_eq (cols : Array ℕ) (i : ℕ) : cols[i]?.getD 0 = cols[i]! := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rfl

@[expose] def v8ColsMat (cols : Array ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun j k => toVecD 8 (cols[(k : ℕ)]?.getD 0) j

theorem toVecD_vecMulN_cols (cols : Array ℕ) (a : ℕ) :
    toVecD 8 (vecMulN 8 cols a) = v8ColsMat cols *ᵥ toVecD 8 a := by
  rw [toVecD_vecMulN, ← Matrix.mulVec_transpose]
  congr 1

theorem qcCoord_v8ColsMat (g : locC) (cols : Array ℕ)
    (hcol : ∀ l : Fin 8, conjEnd (Q := locQ.subgroupOf locC) g (qπ (qcGen l)) =
      qcCoord (toVecD 8 (cols[(l : ℕ)]?.getD 0))) (f : Fin 8 → ZMod 2) :
    qcCoord (v8ColsMat cols *ᵥ f) = conjEnd (Q := locQ.subgroupOf locC) g (qcCoord f) := by
  have key : qcCoord ∘ₗ (v8ColsMat cols).mulVecLin =
      conjEnd (Q := locQ.subgroupOf locC) g ∘ₗ qcCoord := by
    refine (Pi.basisFun (ZMod 2) (Fin 8)).ext fun l => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, qcCoord_single, hcol l]
    rfl
  exact LinearMap.congr_fun key f

theorem conjEnd_vecMulN_of_check {g : locC} {arr cols : Array ℕ}
    (hg : Rep 2300 arr (g : Equiv.Perm (Fin 2300)))
    (hinv : isInvA 2300 arr (invCand 2300 arr) = true)
    (hall : allLt 8 (fun l => decide (cols[l]! < 256) &&
      isProdOrZ (compA 2300 (compA 2300 arr qArrs[l]!) (invCand 2300 arr)) cols[l]!) = true)
    (a : ℕ) :
    qcCoord (toVecD 8 (vecMulN 8 cols a)) =
      conjEnd (Q := locQ.subgroupOf locC) g (qcCoord (toVecD 8 a)) := by
  rw [toVecD_vecMulN_cols, qcCoord_v8ColsMat g cols _]
  intro l
  have h := allLt_spec hall l.2
  rw [Bool.and_eq_true] at h
  rw [getD_zero_eq]
  exact conjEnd_qVec_cols hg (rep_inv_of_isInvA hg hinv) l.2 h.2

theorem conjEnd_vecMulN_of_conjColsOK {g : locC} {arr cols : Array ℕ}
    (hg : (g : Equiv.Perm (Fin 2300)) = permOfArr 2300 arr) (h : conjColsOK arr cols = true)
    (a : ℕ) :
    qcCoord (toVecD 8 (vecMulN 8 cols a)) =
      conjEnd (Q := locQ.subgroupOf locC) g (qcCoord (toVecD 8 a)) := by
  simp only [conjColsOK, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hi⟩, hall⟩ := h
  refine conjEnd_vecMulN_of_check ?_ hi hall a
  rw [hg]
  exact rep_of_validA hv

end Cols

theorem v8_irreducible (c₁ c₂ c₃ : locC)
    (h₁ : (c₁ : Equiv.Perm (Fin 2300)) = k1P) (h₂ : (c₂ : Equiv.Perm (Fin 2300)) = k2P)
    (h₃ : (c₃ : Equiv.Perm (Fin 2300)) = CFSG.Sporadic.Co2I301.dP) (W : Submodule (ZMod 2) QV)
    (hW₁ : ∀ w ∈ W, conjEnd (Q := locQ.subgroupOf locC) c₁ w ∈ W)
    (hW₂ : ∀ w ∈ W, conjEnd (Q := locQ.subgroupOf locC) c₂ w ∈ W)
    (hW₃ : ∀ w ∈ W, conjEnd (Q := locQ.subgroupOf locC) c₃ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have h := Certificates.certificate101707
  simp only [co2RowCheck, v8Check, Bool.and_eq_true] at h
  obtain ⟨-, ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩⟩ := h
  have e₁ := conjEnd_vecMulN_of_conjColsOK (g := c₁) h₁ hA
  have e₂ := conjEnd_vecMulN_of_conjColsOK (g := c₂) h₂ hB
  have e₃ := conjEnd_vecMulN_of_conjColsOK (g := c₃) h₃ hC
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨a, ha, rfl⟩ := exists_qcCoord w
  set P : ℕ → Prop := fun b => qcCoord (toVecD 8 b) ∈ W with hP
  have hxor : ∀ b c, P b → P c → P (b ^^^ c) := fun b c hb hc => by
    simp only [hP, toVecD_xor, map_add] at hb hc ⊢
    exact W.add_mem hb hc
  have hT : ∀ T ∈ [co2K1Cols, co2K2Cols, co2DCols], ∀ b, P b → P (vecMulN 8 T b) := by
    intro T hTm b hb
    simp only [hP] at hb ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTm
    rcases hTm with rfl | rfl | rfl
    · rw [e₁ b]
      exact hW₁ _ hb
    · rw [e₂ b]
      exact hW₂ _ hb
    · rw [e₃ b]
      exact hW₃ _ hb
  have h0 : P 0 := by
    simp only [hP, toVecD_zero, map_zero]
    exact W.zero_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [toVecD_zero, map_zero])
  obtain ⟨v, rfl⟩ : ∃ v, a = v + 1 := ⟨a - 1, by omega⟩
  have hfull := bitsIn_spanIterL hxor hT 5 (bitsIn_spanIns hxor (bitsIn_one h0) hwW)
  rw [beq_iff_eq.1 (allLt_spec hD (i := v) (by omega))] at hfull
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨b, hb, rfl⟩ := exists_qcCoord u
  exact bitsIn_full hfull hb

end Cert

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2V8

end
