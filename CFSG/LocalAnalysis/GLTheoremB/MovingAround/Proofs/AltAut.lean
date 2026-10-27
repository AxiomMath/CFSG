module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118R

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

namespace AltAut

variable {X : Type} [Group X]

@[expose] def conjOn {K : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)) :
    K ≃* K where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) x).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply {K : Subgroup X} {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)) (x : K) :
    ((conjOn hg x : K) : X) = g * x * g⁻¹ :=
  rfl

end AltAut

theorem Lemma118R.inputAutAltOdd_holds : Lemma118R.InputAutAltOdd := by
  intro n X _ _ K h7 hn6 hK g hg k hk hgk
  obtain ⟨e⟩ := hK
  have h5 : 5 ≤ n := by omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 hn6
  let f : MulAut (alternatingGroup (Fin n)) := e.symm.trans ((AltAut.conjOn hg).trans e)
  obtain ⟨σ, hσ⟩ := hbij.2 f
  have hβ : ∀ z : K, ((e (AltAut.conjOn hg z) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
      σ * ((e z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ⁻¹ := by
    intro z
    have h := congrArg (fun θ : MulAut (alternatingGroup (Fin n)) =>
      ((θ (e z) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) hσ
    simp only [MulAut.conjNormal_apply, f, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
    exact h.symm
  have hpow : ∀ j : ℕ, ∀ x : K, ∃ y : K, (y : X) = g ^ j * (x : X) * (g ^ j)⁻¹ ∧
      ((e y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ ^ j * ((e x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * (σ ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; exact ⟨x, by simp, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨z, hz1, hz2⟩ := ih x
      refine ⟨AltAut.conjOn hg z, ?_, ?_⟩
      · rw [AltAut.conjOn_apply, hz1]; group
      · rw [hβ z, hz2]; group
  have hσk : σ ^ k = 1 := by
    apply hbij.1
    rw [map_one]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    obtain ⟨y, hy1, hy2⟩ := hpow k (e.symm a)
    have hyx : y = e.symm a := Subtype.ext (hy1.trans (hgk _ (e.symm a).2))
    rw [hyx, MulEquiv.apply_symm_apply] at hy2
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    exact hy2.symm
  have hs : Equiv.Perm.sign σ = 1 := by
    have h1 : (Equiv.Perm.sign σ) ^ k = 1 := by
      rw [← map_pow, hσk, map_one]
    obtain ⟨m, hm⟩ := hk
    rw [hm, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
    exact h1
  have hmem : σ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hs
  let τ : alternatingGroup (Fin n) := ⟨σ, hmem⟩
  refine ⟨((e.symm τ : K) : X), (e.symm τ).2, fun x hx => ?_⟩
  have key : AltAut.conjOn hg ⟨x, hx⟩ = e.symm τ * ⟨x, hx⟩ * (e.symm τ)⁻¹ := by
    apply e.injective
    apply Subtype.ext
    rw [hβ ⟨x, hx⟩]
    simp [τ]
  have hx' := congrArg (fun z : K => (z : X)) key
  simpa [AltAut.conjOn_apply] using hx'

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
