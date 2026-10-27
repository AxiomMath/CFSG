
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModelBase

@[expose] public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight (matApp matMulM idCode matApp_lt matApp_matMulM matApp_idCode
  eq_of_cols matApp_pow matApp_xor)

theorem saMat_lt (i : ℕ) : saMat i < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem eq_of_span {M M' : ℕ} (hM : M < 2 ^ 64) (hM' : M' < 2 ^ 64)
    (hs : ∀ c < 8, spanA.getD c 0 ^^^ spanB.getD c 0 = 2 ^ c)
    (h : ∀ c < 8, matApp M (spanA.getD c 0) = matApp M' (spanA.getD c 0) ∧
      matApp M (spanB.getD c 0) = matApp M' (spanB.getD c 0)) : M = M' := by
  refine eq_of_cols hM hM' fun c hc => ?_
  rw [← matApp_pow M hc, ← matApp_pow M' hc, ← hs c hc, matApp_xor, matApp_xor, (h c hc).1,
    (h c hc).2]

@[expose] def Acts (g : Equiv.Perm (Fin 136)) (M : ℕ) : Prop :=
  ∀ p (hp : p < 136), ((g ⟨p, hp⟩ : Fin 136) : ℕ) = nsIdx[matApp M nsArr[p]!]!

theorem acts_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 136)} {M : ℕ} (ht : Rep 136 t g)
    (h : ActsOn t M) : Acts g M := fun p hp => by
  rw [← ht.apply hp]
  exact (h p hp).2

@[expose] def saElt (i : ℕ) : Equiv.Perm (Fin 136) :=
  if _h : 0 < i ∧ saPar i < i then gen (sylowIdx.getD (saLab i) 0) * saElt (saPar i) else 1
termination_by i
decreasing_by exact _h.2

theorem gen_mem_sylowT {l : ℕ} (hl : l < 6) : gen (sylowIdx.getD l 0) ∈ sylowT := by
  rw [sylowT_eq]
  exact Subgroup.subset_closure ⟨l, hl, rfl⟩

theorem sylowIdx_lt {l : ℕ} (hl : l < 6) : sylowIdx.getD l 0 < 11 := by
  interval_cases l <;> decide

end CFSG.EvenSmallLie.OmegaEightMinus

end
