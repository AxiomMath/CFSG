
module

public import CFSG.Fischer.Polar.HyperovalBase
import all CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  deltaTab

local notation "PT" => perpTab ()
local notation "DT" => deltaTab ()

@[expose] def deltaM : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.diagonal fun i => if i = 0 then F4.ω else 1

@[expose] noncomputable def deltaGU : GU0 := ⟨diagGL (unitOf F4.ω F4.ω_ne_zero), diagGL_isom _⟩

theorem delta_eq : delta = piGU deltaGU := rfl

theorem deltaGU_val : ((deltaGU : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = deltaM := by
  rw [deltaGU, deltaM]
  exact diagGL_val _

private theorem code_lt4 (x : F4) : x.code.val < 4 := x.code.isLt

theorem deltaC_codeOf (v : Fin 6 → F4) : deltaC (codeOf v) = codeOf (deltaM.mulVec v) := by
  have h0 := code_lt4 (v 0); have h1 := code_lt4 (v 1); have h2 := code_lt4 (v 2)
  have h3 := code_lt4 (v 3); have h4 := code_lt4 (v 4); have h5 := code_lt4 (v 5)
  have hω : (F4.ω * v 0).code.val = f4mul 2 (v 0).code.val := code_mul F4.ω (v 0)
  have hmod : codeOf v % 4 = (v 0).code.val := by unfold codeOf; omega
  have hdiv : codeOf v / 4 * 4 = codeOf v - (v 0).code.val := by unfold codeOf; omega
  have hM : (Matrix.diagonal fun i : Fin 6 => if i = 0 then F4.ω else 1).mulVec v =
      fun i => (if i = 0 then F4.ω else 1) * v i :=
    funext fun i => Matrix.mulVec_diagonal _ _ _
  unfold deltaC
  rw [hmod, hdiv]
  unfold deltaM
  rw [hM]
  simp only [codeOf, Fin.isValue, ite_true, show (1 : Fin 6) ≠ 0 by decide,
    show (2 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 0 by decide,
    show (4 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 0 by decide, ite_false, one_mul, hω]
  omega

theorem rep_deltaTab : Rep 693 DT delta := by
  intro i hi
  rw [idx_of_lt _ hi, delta_eq]
  show ap DT i = (deltaGU • (⟨i, hi⟩ : Fin 693)).val
  rw [smul_val, deltaGU_val]
  unfold deltaTab ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp only
  have hu : uPts[i]! = codeOf (uVec i) := (codeOf_uVec ptsFacts hi).symm
  rw [hu, deltaC_codeOf, uPos_normC, UInt32.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hw := mulVec_ne_zero (deltaGU : GL (Fin 6) F4) (uVec_ne_zero ptsFacts hi)
  have hiso : hermStd ((((deltaGU : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).mulVec (uVec i))
      ((((deltaGU : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).mulVec (uVec i)) = 0 := by
    rw [hermStd_mulVec]
    exact uVec_iso ptsFacts hi
  rw [deltaGU_val] at hw hiso
  exact lt_trans (ptIdx_lt ptsFacts hw hiso) (by norm_num)

structure DeltaFacts : Prop where
  inv : invOK 693 DT (invT 693 DT) = true
  perp : ∀ a < 693, ap DT a < 693 ∧ ∀ b < 693, (PT[ap DT a]!)[ap DT b]! = (PT[a]!)[b]!
  conj : ∀ p < 693, ∀ q < 693, ap DT (ap tvTabs[p]! q) = ap tvTabs[ap DT p]! (ap DT q)
  root₁ : rootFlags 2 = imgFlags (invT 693 DT) (rootFlags 1)
  root₂ : rootFlags 3 = imgFlags (invT 693 DT) (rootFlags 2)
  root₃ : rootFlags 1 = imgFlags (invT 693 DT) (rootFlags 3)

theorem delta_val (a : Fin 693) : (delta a).val = ap DT a.val := by
  rw [rep_deltaTab a.val a.2, idx_of_lt _ a.2]
  rfl

theorem conj_mem_T46
    {d : Equiv.Perm (Fin 693)} (hd : IsPolarAut d) {g : Equiv.Perm (Fin 693)}
    (hg : g ∈ T46) : d * g * d⁻¹ ∈ T46 := by
  rw [T46_eq_closure] at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [hd.mul_tvP_mul_inv]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

end CFSG.Fischer
