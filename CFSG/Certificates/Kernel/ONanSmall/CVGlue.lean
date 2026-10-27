module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import CFSG.Certificates.Kernel.ONanSmall.PickRunSound
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.ONanSmall

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkEnum CFSG.Certificates
  CFSG.ClassicalInvolution.Q3.TA3.Check

variable {n : ℕ} [Small n]

theorem invC_eq (t : CV n) : invC t = decide (t * t = 1 ∧ t ≠ 1) := by
  rw [invC, ← sq_fast]
  by_cases h : t * t = 1 <;> by_cases h' : t = 1 <;> simp [h, h']

theorem conjC_eq (g t r : CV n) : conjC g t r = decide (g * t * g⁻¹ = r) := (conj_fast g t r).symm

theorem centB_eq_centC (L : List (CV n)) (t : CV n) : centB L t = centC L t := by
  unfold centB centC
  congr 1
  funext c
  exact comm_fast c t

theorem pairsVKF_eq (B : ℕ) (LN K : List (CV n)) (e3b : Bool) (t : CV n) (C : List (CV n)) :
    pairsVKF B LN K e3b t C = pairsVK B LN K e3b t C := by
  simp only [pairsVKF, pairsVK, ← comm_fast, ← pow_fast, Bool.decide_and]

theorem map_centB_eq(R L : List (CV n)) : R.map (centB L) = R.map (centC L) := by
  rw [show centB L = centC L from funext fun t => centB_eq_centC L t]

theorem productsC_eq : ∀ Ts : List (List (CV n)), productsC Ts = productsOf Ts
  | [] => rfl
  | T :: Ts => by rw [productsC, productsOf, productsC_eq Ts]

theorem elemsC_eq (Q : RawSchreierDatum n) :
    elemsC Q = productsOf (TsC Q) := by
  rw [← productsC_eq]
  rfl

theorem genC_mem (Q : RawSchreierDatum n) (d : List ℕ) (g : CV n)
    (h : genC Q d = some g) : g ∈ elemsC Q := by
  rw [elemsC_eq]
  exact mem_genP _ d g h

theorem elemsT_append_map (Q : RawSchreierDatum n) (σ : Equiv.Perm (Fin n)) :
    CFSG.GH74.KGroups.elemsT Q ++ (CFSG.GH74.KGroups.elemsT Q).map (fun d => σ * d) =
      (elemsC Q ++ (elemsC Q).map (cOf σ * ·)).map (evHom n) := by
  have hf : ((fun d => σ * d) ∘ ev) = (evHom n) ∘ (cOf σ * ·) := funext fun x => by
    change σ * ev x = ev (cOf σ * x)
    rw [ev_mul, ev_cOf]
  rw [elemsT_eq_elemsC, List.map_map, hf, List.map_append, ← List.map_map]
  rfl

theorem genA_mem(Q : RawSchreierDatum n) (σ : CV n) (d : List ℕ)
    (g : CV n) (h : genA Q σ d = some g) : g ∈ elemsC Q ++ (elemsC Q).map (σ * ·) := by
  rw [elemsC_eq]
  match d, h with
  | 0 :: d, h => exact List.mem_append_left _ (mem_genP _ d g h)
  | 1 :: d, h =>
    simp only [genA, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact List.mem_append_right _ (List.mem_map.2 ⟨x, mem_genP _ d x hx, rfl⟩)
  | [], h => simp [genA] at h
  | (k + 2) :: d, h => simp [genA] at h

end CFSG.KC.ONanSmall
