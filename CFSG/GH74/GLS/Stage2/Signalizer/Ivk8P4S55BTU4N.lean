module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

@[expose] def preGL (h : UnitaryFieldData p f K) (W : Subgroup (hypPSU h 2 0)) :
    Subgroup (GL (HypIndex 2 0) K) :=
  (W.comap (hypProj h 2 0)).map (hypSU h 2 0).subtype

@[expose] def IsPElt (h : UnitaryFieldData p f K) (n₀ : ℕ) (W : Subgroup (hypPSU h 2 0))
    (x : GL (HypIndex 2 0) K) : Prop :=
  x ∈ preGL h W ∧ ∃ n : ℕ, x ^ n₀ ^ n = 1

@[expose] def fixSp (h : UnitaryFieldData p f K) (n₀ : ℕ) (W : Subgroup (hypPSU h 2 0)) :
    Submodule K (HypIndex 2 0 → K) where
  carrier := {v | ∀ x, IsPElt h n₀ W x → (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = v}
  zero_mem' := fun x _ => mulVec_zero _
  add_mem' := fun ha hb x hx => by rw [mulVec_add, ha x hx, hb x hx]
  smul_mem' := fun c v hv x hx => by rw [mulVec_smul, hv x hx]

@[expose] def comSp (h : UnitaryFieldData p f K) (n₀ : ℕ) (W : Subgroup (hypPSU h 2 0)) :
    Submodule K (HypIndex 2 0 → K) :=
  Submodule.span K {w | ∃ x v, IsPElt h n₀ W x ∧
    w = (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v - v}

variable {n₀ : ℕ} {W : Subgroup (hypPSU h 2 0)}

theorem isPElt_conj {A : GL (HypIndex 2 0) K}
    (hA : A ∈ normalizer ((preGL h W : Subgroup (GL (HypIndex 2 0) K)) : Set _))
    {x : GL (HypIndex 2 0) K} (hx : IsPElt h n₀ W x) : IsPElt h n₀ W (A * x * A⁻¹) := by
  obtain ⟨hxW, n, hn⟩ := hx
  exact ⟨(Subgroup.mem_normalizer_iff.mp hA x).mp hxW, n, by rw [conj_pow, hn]; group⟩

theorem mulVec_mem_fixSp {A : GL (HypIndex 2 0) K}
    (hA : A ∈ normalizer ((preGL h W : Subgroup (GL (HypIndex 2 0) K)) : Set _))
    {v : HypIndex 2 0 → K} (hv : v ∈ fixSp h n₀ W) :
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v ∈ fixSp h n₀ W := by
  intro x hx
  have h1 := hv _ (isPElt_conj (inv_mem hA) hx)
  rw [inv_inv] at h1
  have e : (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (A : Matrix _ _ K) =
      (A : Matrix _ _ K) * ((A⁻¹ * x * A : GL (HypIndex 2 0) K) : Matrix _ _ K) := by
    rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [mulVec_mulVec, e, ← mulVec_mulVec, h1]

theorem mulVec_mem_comSp {A : GL (HypIndex 2 0) K}
    (hA : A ∈ normalizer ((preGL h W : Subgroup (GL (HypIndex 2 0) K)) : Set _))
    {v : HypIndex 2 0 → K} (hv : v ∈ comSp h n₀ W) :
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v ∈ comSp h n₀ W := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, u, hx, rfl⟩ := hw
    refine Submodule.subset_span ⟨A * x * A⁻¹, (A : Matrix _ _ K) *ᵥ u, isPElt_conj hA hx, ?_⟩
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem hypForm_fixSp_comSp {u v : HypIndex 2 0 → K} (hu : u ∈ fixSp h n₀ W)
    (hv : v ∈ comSp h n₀ W) : hypForm h 2 0 u v = 0 := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, rfl⟩ := hw
    have hux := hu x hx
    obtain ⟨s, -, rfl⟩ := hx.1
    have hux' : (((s : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ u = u := hux
    have hs := (mem_hypSU.mp s.2).1
    have e := gramForm_mulVec h (hypGram 2 0 K)
      (((s : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) u y
    rw [hs, hux'] at e
    show hypForm h 2 0 u ((((s : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ y - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr e
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
