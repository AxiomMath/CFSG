module

public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.HardMathSupport.Solomon.Proving.LBBalanceUp
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transfer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def NoL2Sub {G : Type} [Group G] (D : Subgroup G) : Prop :=
  ∀ A : Subgroup G, GLAPComponent 3 D A → ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r (barOf 3 A)

theorem noL2Layer_iff_noL2Sub {P : Type} [Group P] (ψ : MulAut P) :
    NoL2Layer ψ ↔ NoL2Sub (fixSubgroup ψ) := Iff.rfl

theorem map_gLAPPrimeCore_equiv {A B : Type*} [Group A] [Finite A] [Group B] (p : ℕ) (e : A ≃* B) :
    (GLAPPrimeCore p A).map e.toMonoidHom = GLAPPrimeCore p B := by
  haveI : Finite B := Finite.of_equiv A e.toEquiv
  refine le_antisymm (map_gLAPPrimeCore_le' p e.toMonoidHom e.surjective) ?_
  have h := map_gLAPPrimeCore_le' p e.symm.toMonoidHom e.symm.surjective
  intro y hy
  have hy' : e.symm y ∈ GLAPPrimeCore p A := h ⟨y, hy, rfl⟩
  exact ⟨e.symm y, hy', e.apply_symm_apply y⟩

noncomputable def barOfEquiv {G G' : Type*} [Group G] [Group G'] (p : ℕ) {A : Subgroup G}
    {A' : Subgroup G'} [Finite ↥A] (e : ↥A ≃* ↥A') : barOf p A ≃* barOf p A' :=
  QuotientGroup.congr (GLAPPrimeCore p ↥A) (GLAPPrimeCore p ↥A') e (map_gLAPPrimeCore_equiv p e)

theorem noL2Sub_of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {D : Subgroup G} {D' : Subgroup G'} (e : ↥D ≃* ↥D') (h : NoL2Sub D') : NoL2Sub D := by
  intro A hA r hr hT
  have h1 := glaPComponent_subgroupOf Nat.prime_three (le_refl D) hA
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := glaPComponent_map_mulEquiv Nat.prime_three e h1
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h2
  have h3 := CFSG.HardMathSupport.Solomon.Proving.lbUp_component_top_map Nat.prime_three D' h2
  let eA : ↥A ≃* ↥(((A.subgroupOf D).map e.toMonoidHom).map D'.subtype) :=
    (Subgroup.subgroupOfEquivOfLe hA.1).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (Subgroup.equivMapOfInjective _ D'.subtype D'.subtype_injective))
  exact h _ h3 r hr (l2fld_isTypeL2_of_mulEquiv (barOfEquiv 3 eA) hT)

theorem noL2Layer_of_fixEquiv {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P']
    {ψ : MulAut P} {ψ' : MulAut P'} (e : ↥(fixSubgroup ψ) ≃* ↥(fixSubgroup ψ'))
    (h : NoL2Layer ψ') : NoL2Layer ψ :=
  noL2Sub_of_equiv e h

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
