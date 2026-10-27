module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4N
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenB
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowHom

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {n₀ : ℕ}
  {W : Subgroup (hypPSU h 2 0)}

theorem isPElt_semilin {A : GL (HypIndex 2 0) K} {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hW : ∀ w ∈ W, semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ w ∈ W) :
    ∀ x, IsPElt h n₀ W x → ∃ y, IsPElt h n₀ W y ∧
      (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar *
          ((A⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  rintro _ ⟨⟨s, hs, rfl⟩, n, hn⟩
  have hsW : hypProj h 2 0 s ∈ W := hs
  refine ⟨A * glAut σ (s : GL (HypIndex 2 0) K) * A⁻¹,
    ⟨⟨⟨_, conj_mem_hypSU hx s⟩, ?_, rfl⟩, n, ?_⟩, ?_⟩
  · show hypProj h 2 0 ⟨_, conj_mem_hypSU hx s⟩ ∈ W
    rw [← semilinearAutHom_apply h (by norm_num) (by norm_num) ⟨_, hx⟩ s]
    exact hW _ hsW
  · have hs1 : (s : GL (HypIndex 2 0) K) ^ n₀ ^ n = 1 := hn
    rw [conj_pow, ← map_pow, hs1, map_one, mul_one, mul_inv_cancel]
  · rw [Units.val_mul, Units.val_mul, coe_glAut_of_bar h hσ]
    rfl

theorem mem_normalizer_preGL_of_lin [Finite K] {A : GL (HypIndex 2 0) K}
    (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hW : ∀ w ∈ W, semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ w ∈ W) :
    A ∈ normalizer ((preGL h W : Subgroup (GL (HypIndex 2 0) K)) : Set _) := by
  refine mem_normalizer_of_conj_le fun x hxW => ?_
  obtain ⟨s, hs, rfl⟩ := hxW
  refine ⟨⟨_, conj_mem_hypSU hx s⟩, ?_, ?_⟩
  · show hypProj h 2 0 ⟨_, conj_mem_hypSU hx s⟩ ∈ W
    rw [← semilinearAutHom_apply h (by norm_num) (by norm_num) ⟨_, hx⟩ s]
    exact hW _ hs
  · show A * glAut (RingEquiv.refl K) (s : GL (HypIndex 2 0) K) * A⁻¹ = A * s * A⁻¹
    rw [show RingEquiv.refl K = 1 from rfl, map_one, MulAut.one_apply]

theorem mem_normalizer_preGL_of_proj [Finite K] {g : hypSU h 2 0}
    (hg : ∀ w ∈ W, hypProj h 2 0 g * w * (hypProj h 2 0 g)⁻¹ ∈ W) :
    (g : GL (HypIndex 2 0) K) ∈ normalizer ((preGL h W : Subgroup (GL (HypIndex 2 0) K)) :
      Set _) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨g * s * g⁻¹, ?_, rfl⟩
  show hypProj h 2 0 (g * s * g⁻¹) ∈ W
  rw [map_mul, map_mul, map_inv]
  exact hg _ hs

theorem pow_four_of_mem_hypScalars {s : hypSU h 2 0} (hs : s ∈ hypScalars h 2 0) :
    s ^ 4 = 1 := by
  obtain ⟨c, -, hc4, hsc⟩ := mem_normOneScalars.mp hs
  have hc4' : c ^ 4 = 1 := hc4
  apply Subtype.ext
  rw [Subgroup.coe_pow, hsc, ← map_pow, hc4', map_one, Subgroup.coe_one]

theorem isNilpotent_comap [Finite K] [Fact n₀.Prime] (hWp : IsPGroup n₀ ↥W) :
    Group.IsNilpotent ↥(W.comap (hypProj h 2 0)) := by
  have : Group.IsNilpotent ↥W := hWp.isNilpotent
  let φ : ↥(W.comap (hypProj h 2 0)) →* ↥W :=
    ((hypProj h 2 0).comp (W.comap (hypProj h 2 0)).subtype).codRestrict W fun x => x.2
  refine Subgroup.isNilpotent_of_ker_le_center φ fun x hx => ?_
  have hx1 : hypProj h 2 0 (x : hypSU h 2 0) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hxs : (x : hypSU h 2 0) ∈ hypScalars h 2 0 := by
    have := MonoidHom.mem_ker.mpr hx1
    rwa [ker_hypProj] at this
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hxs
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hc]
  exact (GeneralLinearGroup.scalar_commute c _).symm

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
