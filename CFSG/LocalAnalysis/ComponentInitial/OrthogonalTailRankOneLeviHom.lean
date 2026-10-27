module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviABlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviParabolic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

@[expose] def tailPair {i : Fin r} (hi : i.val + 1 < r) (t : Fin 2) : Fin r :=
  ⟨i.val + t.val, by have := t.isLt; omega⟩

theorem tailPair_val {i : Fin r} (hi : i.val + 1 < r) (t : Fin 2) :
    (tailPair hi t).val = i.val + t.val := rfl

theorem tailPair_injective {i : Fin r} (hi : i.val + 1 < r) : Function.Injective (tailPair hi) := by
  intro s t h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [tailPair_val] at this
  omega

theorem mem_range_tailPair_iff {i : Fin r} (hi : i.val + 1 < r) (j : Fin r) :
    j ∈ Set.range (tailPair hi) ↔ j.val = i.val ∨ j.val = i.val + 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    fin_cases t <;> simp [tailPair_val]
  · rintro (h | h)
    · exact ⟨0, by apply Fin.ext; simp [tailPair_val]; omega⟩
    · exact ⟨1, by apply Fin.ext; simp [tailPair_val]; omega⟩

abbrev TailLeviTarget (K : Type) [Field K] (A : Type) [AddCommGroup A] [Module K A] (r : ℕ)
    (i : Fin r) : Type :=
  GL (Fin 2) K ×
    (({j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1} → Kˣ) × LinearMap.GeneralLinearGroup K A)

@[expose] def tailLeviBlk {i : Fin r} (hi : i.val + 1 < r) (g : TailModel K A r) :
    Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun s t => tailCoeff g (tailPair hi s) (tailPair hi t)

theorem tailLeviBlk_apply {i : Fin r} (hi : i.val + 1 < r) (g : TailModel K A r) (s t : Fin 2) :
    tailLeviBlk hi g s t = tailCoeff g (tailPair hi s) (tailPair hi t) := rfl

theorem tailLeviBlk_one {i : Fin r} (hi : i.val + 1 < r) :
    tailLeviBlk hi (1 : TailModel K A r) = 1 := by
  ext s t
  rw [tailLeviBlk_apply, tailCoeff_one, Matrix.one_apply]
  by_cases h : s = t
  · subst h
    simp
  · have h' : tailPair hi s ≠ tailPair hi t := fun hh => h (tailPair_injective hi hh)
    simp [h, h']

private theorem tailLeviBlk_mul_aux_H04 {i : Fin r} (hi : i.val + 1 < r)
    {g h : TailModel K A r} (hg : g ∈ tailLeviDom r qA i) (hh : h ∈ tailLeviDom r qA i)
    (s t : Fin 2) :
    ∀ k ∉ Set.range (tailPair hi),
      tailCoeff g (tailPair hi s) k * tailCoeff h k (tailPair hi t) = 0 := by
  intro k hk
  rw [mem_range_tailPair_iff hi k, not_or] at hk
  rcases lt_trichotomy k.val i.val with hlt | heq | hgt
  · have hlt' : k.val < (tailPair hi s).val := by rw [tailPair_val]; omega
    rw [tailCoeff_eq_zero_of_mem_tailLeviDom hi hg hlt' (fun ⟨h1, _⟩ => hk.1 h1), zero_mul]
  · exact absurd heq hk.1
  · have hk2 : i.val + 1 < k.val := by
      have : i.val + 1 ≤ k.val := by omega
      exact lt_of_le_of_ne this (Ne.symm hk.2)
    have hlt' : (tailPair hi t).val < k.val := by
      rw [tailPair_val]
      have := t.isLt
      omega
    rw [tailCoeff_eq_zero_of_mem_tailLeviDom hi hh hlt' (fun ⟨_, h2⟩ => hk.2 h2), mul_zero]

theorem tailLeviBlk_mul {i : Fin r} (hi : i.val + 1 < r) {g h : TailModel K A r}
    (hg : g ∈ tailLeviDom r qA i) (hh : h ∈ tailLeviDom r qA i) :
    tailLeviBlk hi (g * h) = tailLeviBlk hi g * tailLeviBlk hi h := by
  ext s t
  rw [tailLeviBlk_apply, tailCoeff_mul hi hh, Matrix.mul_apply]
  simp only [tailLeviBlk_apply]
  exact (Fintype.sum_of_injective (tailPair hi) (tailPair_injective hi)
    (fun l : Fin 2 => tailCoeff g (tailPair hi s) (tailPair hi l) *
      tailCoeff h (tailPair hi l) (tailPair hi t))
    (fun k : Fin r => tailCoeff g (tailPair hi s) k * tailCoeff h k (tailPair hi t))
    (tailLeviBlk_mul_aux_H04 hi hg hh s t) (fun _ => rfl)).symm

theorem tailCoeff_diag_mul {i : Fin r} (hi : i.val + 1 < r) {g h : TailModel K A r}
    (hg : g ∈ tailLeviDom r qA i) (hh : h ∈ tailLeviDom r qA i) {j : Fin r}
    (hj : j.val ≠ i.val ∧ j.val ≠ i.val + 1) :
    tailCoeff (g * h) j j = tailCoeff g j j * tailCoeff h j j := by
  rw [tailCoeff_mul hi hh]
  refine Finset.sum_eq_single j (fun k _ hkj => ?_)
    (fun h => absurd (Finset.mem_univ j) h)
  rcases lt_trichotomy k.val j.val with hlt | heq | hgt
  · rw [tailCoeff_eq_zero_of_mem_tailLeviDom hi hg hlt (fun ⟨_, h2⟩ => hj.2 h2), zero_mul]
  · exact absurd (Fin.ext heq) hkj
  · rw [tailCoeff_eq_zero_of_mem_tailLeviDom hi hh hgt (fun ⟨h1, _⟩ => hj.1 h1), mul_zero]

variable (qA) in
@[expose] noncomputable def tailLeviBlkHom {i : Fin r} (hi : i.val + 1 < r) :
    ↥(tailLeviDom r qA i) →* GL (Fin 2) K :=
  MonoidHom.toHomUnits (G := ↥(tailLeviDom r qA i)) (M := Matrix (Fin 2) (Fin 2) K)
    { toFun := fun g => tailLeviBlk hi (g : TailModel K A r)
      map_one' := tailLeviBlk_one hi
      map_mul' := fun g h => tailLeviBlk_mul hi g.2 h.2 }

variable (qA) in
@[expose] noncomputable def tailLeviMidHom {i : Fin r} (hi : i.val + 1 < r) :
    ↥(tailLeviDom r qA i) →* ({j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1} → Kˣ) :=
  Pi.monoidHom fun j => MonoidHom.toHomUnits (G := ↥(tailLeviDom r qA i)) (M := K)
    { toFun := fun g => tailCoeff (g : TailModel K A r) j.1 j.1
      map_one' := (tailCoeff_one j.1 j.1).trans (if_pos rfl)
      map_mul' := fun g h => tailCoeff_diag_mul hi g.2 h.2 j.2 }

variable (qA) in
@[expose] noncomputable def tailLeviAutHom {i : Fin r} (hi : i.val + 1 < r) :
    ↥(tailLeviDom r qA i) →* LinearMap.GeneralLinearGroup K A :=
  MonoidHom.toHomUnits (G := ↥(tailLeviDom r qA i)) (M := Module.End K A)
    { toFun := fun g => tailABlock (g : TailModel K A r)
      map_one' := tailABlock_one
      map_mul' := fun g h => tailABlock_mul hi g.2 h.2 }

variable (qA) in
@[expose] noncomputable def tailLeviHom {i : Fin r} (hi : i.val + 1 < r) :
    ↥(tailLeviDom r qA i) →* TailLeviTarget K A r i :=
  (tailLeviBlkHom qA hi).prod ((tailLeviMidHom qA hi).prod (tailLeviAutHom qA hi))

theorem coe_tailLeviBlkHom {i : Fin r} (hi : i.val + 1 < r) (g : ↥(tailLeviDom r qA i)) :
    ((tailLeviBlkHom qA hi g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      tailLeviBlk hi (g : TailModel K A r) := rfl

theorem coe_tailLeviMidHom {i : Fin r} (hi : i.val + 1 < r) (g : ↥(tailLeviDom r qA i))
    (j : {j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1}) :
    ((tailLeviMidHom qA hi g j : Kˣ) : K) = tailCoeff (g : TailModel K A r) j.1 j.1 := rfl

theorem coe_tailLeviAutHom {i : Fin r} (hi : i.val + 1 < r) (g : ↥(tailLeviDom r qA i)) :
    ((tailLeviAutHom qA hi g : LinearMap.GeneralLinearGroup K A) : Module.End K A) =
      tailABlock (g : TailModel K A r) := rfl

theorem tailLeviHom_apply {i : Fin r} (hi : i.val + 1 < r) (g : ↥(tailLeviDom r qA i)) :
    tailLeviHom qA hi g =
      (tailLeviBlkHom qA hi g, tailLeviMidHom qA hi g, tailLeviAutHom qA hi g) := rfl

@[expose] noncomputable def tailRankOneLeviHom {i : Fin r} (hi : i.val + 1 < r)
    (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) :
    ↥(tailRankOneParabolic qA a₀ i) →* TailLeviTarget K A r i :=
  (tailLeviHom qA hi).comp
    (Subgroup.inclusion (tailRankOneParabolic_le_tailLeviDom hi hani ha₀))

theorem tailRankOneLeviHom_apply {i : Fin r} (hi : i.val + 1 < r) (hani : qA.Anisotropic)
    (ha₀ : a₀ ≠ 0) (g : ↥(tailRankOneParabolic qA a₀ i)) :
    tailRankOneLeviHom hi hani ha₀ g =
      tailLeviHom qA hi ⟨g.1, tailRankOneParabolic_le_tailLeviDom hi hani ha₀ g.2⟩ := rfl

variable (K A r) (i : Fin r) in
@[expose] noncomputable def tailLeviSL2Embed :
    SpecialLinearGroup (Fin 2) K →* TailLeviTarget K A r i :=
  (Matrix.SpecialLinearGroup.toGL).prod 1

theorem tailLeviSL2Embed_apply (i : Fin r) (M : SpecialLinearGroup (Fin 2) K) :
    tailLeviSL2Embed K A r i M = (Matrix.SpecialLinearGroup.toGL M, 1, 1) := rfl

theorem tailLeviSL2Embed_injective (i : Fin r) : Function.Injective (tailLeviSL2Embed K A r i) := by
  intro M N h
  rw [tailLeviSL2Embed_apply, tailLeviSL2Embed_apply] at h
  have h1 : Matrix.SpecialLinearGroup.toGL M = Matrix.SpecialLinearGroup.toGL N := by
    simpa using congrArg Prod.fst h
  exact Matrix.SpecialLinearGroup.toGL_injective h1

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
