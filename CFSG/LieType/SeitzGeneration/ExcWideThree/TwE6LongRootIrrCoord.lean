module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrrComb

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace CoreIrr

variable {K : Type} [Field K]

theorem eop_apply (j : Fin TwistTag.E6.tag.rank) (v : Rv K) (γ : Dr) :
    eop K j v γ =
      if h : γ.1 - Pi.single j 1 ∈ degOneRoots then v ⟨γ.1 - Pi.single j 1, h⟩ else 0 := by
  simp [eop]

theorem fop_apply (j : Fin TwistTag.E6.tag.rank) (v : Rv K) (γ : Dr) :
    fop K j v γ =
      if h : γ.1 + Pi.single j 1 ∈ degOneRoots then v ⟨γ.1 + Pi.single j 1, h⟩ else 0 := by
  simp [fop]

theorem xop_apply (j : Fin TwistTag.E6.tag.rank) (c : K) (v : Rv K) :
    xop K j c v = v + c • eop K j v := rfl

theorem yop_apply (j : Fin TwistTag.E6.tag.rank) (c : K) (v : Rv K) :
    yop K j c v = v + c • fop K j v := rfl

theorem eop_apply_of_eq (j : Fin TwistTag.E6.tag.rank) (v : Rv K) {γ γ' : Dr}
    (h : γ.1 - Pi.single j 1 = γ'.1) : eop K j v γ = v γ' := by
  have hm : γ.1 - Pi.single j 1 ∈ degOneRoots := h ▸ γ'.2
  rw [eop_apply, dif_pos hm]
  exact congrArg v (Subtype.ext h)

theorem fop_single (j : Fin TwistTag.E6.tag.rank) {γ δ : Dr} (h : δ.1 + Pi.single j 1 = γ.1)
    (s : K) : fop K j (Pi.single γ s : Rv K) = Pi.single δ s := by
  funext x
  rw [fop_apply]
  by_cases hx : x = δ
  · subst hx
    have hm : x.1 + Pi.single j 1 ∈ degOneRoots := h ▸ γ.2
    rw [dif_pos hm]
    have : (⟨x.1 + Pi.single j 1, hm⟩ : Dr) = γ := Subtype.ext h
    rw [this]
    simp
  · rw [Pi.single_eq_of_ne hx]
    split_ifs with hm
    · refine Pi.single_eq_of_ne (fun h' => hx (Subtype.ext ?_)) _
      have h'' := congrArg Subtype.val h'
      simp only at h''
      exact add_right_cancel (h''.trans h.symm)
    · rfl

@[expose] def VanishLE (m : ℤ) (v : Rv K) : Prop := ∀ γ : Dr, ht γ ≤ m → v γ = 0

theorem VanishLE.mono {m m' : ℤ} {v : Rv K} (h : VanishLE m v) (hm : m' ≤ m) : VanishLE m' v :=
  fun γ hγ => h γ (hγ.trans hm)

theorem VanishLE.add {m : ℤ} {v w : Rv K} (hv : VanishLE m v) (hw : VanishLE m w) :
    VanishLE m (v + w) := fun γ hγ => by simp [hv γ hγ, hw γ hγ]

theorem VanishLE.smul {m : ℤ} {v : Rv K} (hv : VanishLE m v) (c : K) : VanishLE m (c • v) :=
  fun γ hγ => by simp [hv γ hγ]

theorem ht_of_add {γ γ' : Dr} (j : Fin TwistTag.E6.tag.rank)
    (h : γ'.1 = γ.1 + Pi.single j 1) : ht γ' = ht γ + 1 := by
  simp [ht, h, Finset.sum_add_distrib]

theorem VanishLE.eop {m : ℤ} {v : Rv K} (hv : VanishLE m v) (j : Fin TwistTag.E6.tag.rank) :
    VanishLE (m + 1) (eop K j v) := by
  intro γ hγ
  rw [eop_apply]
  split_ifs with h
  · refine hv _ ?_
    have := ht_of_add (γ := (⟨γ.1 - Pi.single j 1, h⟩ : Dr)) (γ' := γ) j (by simp)
    omega
  · rfl

theorem xop_comp_sub (i₀ i₁ : Fin TwistTag.E6.tag.rank) (c d : K) (n : Rv K) :
    xop K i₀ c (xop K i₁ d n) - n =
      c • eop K i₀ n + d • eop K i₁ n + (c * d) • eop K i₀ (eop K i₁ n) := by
  simp only [xop_apply, map_add, map_smul, smul_add, mul_smul]
  module

theorem yop_comp_single (i₀ i₁ : Fin TwistTag.E6.tag.rank) (c d s : K)
    {γ δ δ' γ'' : Dr} (h₁ : δ.1 + Pi.single i₀ 1 = γ.1) (h₂ : δ'.1 + Pi.single i₁ 1 = γ.1)
    (h₃ : γ''.1 + Pi.single i₀ 1 = δ'.1) :
    yop K i₀ c (yop K i₁ d (Pi.single γ s : Rv K)) =
      Pi.single γ s + c • Pi.single δ s + d • Pi.single δ' s + (c * d) • Pi.single γ'' s := by
  simp only [yop_apply, map_add, map_smul, smul_add, mul_smul, fop_single i₀ h₁,
    fop_single i₁ h₂, fop_single i₀ h₃]
  module

end CoreIrr

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
