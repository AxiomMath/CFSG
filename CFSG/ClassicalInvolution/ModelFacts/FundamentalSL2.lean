module

public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal
open scoped MatrixGroups

@[expose] def FundamentalSL2 (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ (g : (Generic.modelUniv t n p e Fact.out).K)
    (γ : Fin (Generic.modelUniv t n p e Fact.out).D.rank → ℤ),
    Generic.IsLongestRoot (Generic.modelUniv t n p e Fact.out).D γ →
      Nonempty (((Generic.modelUniv t n p e Fact.out).D.rootGroup γ ⊔
        (Generic.modelUniv t n p e Fact.out).D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom ≃*
          SL(2, GaloisField p e))

section Transport

def slMapEquiv {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') : SL(2, K) ≃* SL(2, K') where
  toFun := Matrix.SpecialLinearGroup.map (e : K →+* K')
  invFun := Matrix.SpecialLinearGroup.map (e.symm : K' →+* K)
  left_inv := map_map_symm e
  right_inv := map_symm_map e
  map_mul' := map_mul _

theorem nonempty_equiv_sl2_of_ringEquiv {K K' R : Type} [Field K] [Field K'] [Group R]
    (e : K ≃+* K') (h : Nonempty (R ≃* SL(2, K))) : Nonempty (R ≃* SL(2, K')) :=
  h.map fun φ => φ.trans (slMapEquiv e)

noncomputable def subgroupMapConjEquiv {X : Type} [Group X] (U : Subgroup X) (g : X) :
    U.map (MulAut.conj g).toMonoidHom ≃* U :=
  (Subgroup.equivMapOfInjective U (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

end Transport

section StandardPair

variable {F : Type} [Field F] {X : Type} [Group X]

theorem linearBlockStandardPair_equiv {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) :
    Nonempty (U ≃* SL(2, F)) ∧ Nonempty (V ≃* SL(2, F)) := by
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  let θ' : SL(3, F) →* X := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hker' : θ'.ker ≤ Subgroup.center SL(3, F) := by
    intro x hx
    have h1 : (MulAut.conj c⁻¹).toMonoidHom x ∈ θ.ker := hx
    have h2 := hker h1
    have h3 := (inferInstance : (Subgroup.center SL(3, F)).Normal).conj_mem _ h2 c
    simpa [mul_assoc] using h3
  have hB : ∀ B : Subgroup SL(3, F),
      B.map θ' = (B.map (MulAut.conj c⁻¹).toMonoidHom).map θ := fun B => by
    rw [Subgroup.map_map]
  have key : ∀ (i : ℕ) (hi : i + 2 ≤ 3),
      Nonempty (((blockSL F 3 2 i hi).range.map θ') ≃* SL(2, F)) := by
    intro i hi
    have hinj := comp_blockSL_injective hker' hi (by omega)
    rw [← MonoidHom.range_comp]
    exact ⟨(MonoidHom.ofInjective hinj).symm⟩
  have h12 : Nonempty (((B12 F).map θ') ≃* SL(2, F)) := key 0 (by omega)
  have h23 : Nonempty (((B23 F).map θ') ≃* SL(2, F)) := key 1 (by omega)
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨?_, ?_⟩
    · rw [← h1, ← hB]
      exact h12
    · rw [← h2, ← hB]
      exact h23
  · refine ⟨?_, ?_⟩
    · rw [← h2, ← hB]
      exact h23
    · rw [← h1, ← hB]
      exact h12

end StandardPair

section Reduction

variable (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]

theorem fundamentalSL2_of_partner
    (hpart : ∀ γ, Generic.IsLongestRoot (Generic.modelUniv t n p e Fact.out).D γ → ∃ δ, ∃ W,
      LinearBlockStandardPair (GaloisField p e) W
        ((Generic.modelUniv t n p e Fact.out).D.rootGroup γ ⊔
          (Generic.modelUniv t n p e Fact.out).D.rootGroup (-γ))
        ((Generic.modelUniv t n p e Fact.out).D.rootGroup δ ⊔
          (Generic.modelUniv t n p e Fact.out).D.rootGroup (-δ))) :
    FundamentalSL2 p t n e := by
  intro g γ hγ
  obtain ⟨δ, W, hW⟩ := hpart γ hγ
  obtain ⟨⟨eU⟩, -⟩ := linearBlockStandardPair_equiv hW
  exact ⟨(subgroupMapConjEquiv _ g).trans eU⟩

theorem fundamentalSL2_of_longest_root (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {γ₀ : Fin (Generic.modelUniv t n p e Fact.out).D.rank → ℤ}
    (h₀ : Generic.IsLongestRoot (Generic.modelUniv t n p e Fact.out).D γ₀)
    (hSL : Nonempty (((Generic.modelUniv t n p e Fact.out).D.rootGroup γ₀ ⊔
      (Generic.modelUniv t n p e Fact.out).D.rootGroup (-γ₀) :
        Subgroup (Generic.modelUniv t n p e Fact.out).K) ≃* SL(2, GaloisField p e))) :
    FundamentalSL2 p t n e := by
  intro g γ hγ
  obtain ⟨h, hh⟩ := exists_conj_of_isLongestRoot t n p e hp.out hfund hadm hγ h₀
  obtain ⟨e₀⟩ := hSL
  exact ⟨(subgroupMapConjEquiv _ g).trans
    ((Subgroup.equivMapOfInjective _ (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective).trans ((MulEquiv.subgroupCongr hh).trans e₀))⟩

end Reduction

end CFSG.ClassicalInvolution.ModelFacts
