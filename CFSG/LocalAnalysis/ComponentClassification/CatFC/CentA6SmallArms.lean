module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.A6LieSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SmallEven
public import CFSG.LieType.Multipliers.U43

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a6InnerLieSmall_of_classify (hshape : ∀ t, OddA6Shape t) (hsmall : ∀ t, OddA6Small t) :
    A6InnerLieSmall := by
  intro S _ _ _ hodd z hz hC D hDn ⟨eD⟩
  have hna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := a6sq_nonab
    refine ⟨((eD.symm a : ↥D) : ↥(centralizer ({z} : Set S))),
      ((eD.symm b : ↥D) : ↥(centralizer ({z} : Set S))), fun h => hab ?_⟩
    have h1 : (eD.symm a) * (eD.symm b) = (eD.symm b) * (eD.symm a) :=
      Subtype.ext (Subtype.ext h)
    simpa using congrArg eD h1
  have hσ : orderOf (MulAut.conj z : MulAut S) = 2 :=
    (orderOf_injective (MulAut.conj : S →* MulAut S) (mulAut_conj_injective_of_simple hna) z).trans hz
  have hfix : fixedSubgroup (MulAut.conj z : MulAut S) = centralizer ({z} : Set S) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    change z * x * z⁻¹ = x ↔ x * z = z * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  let φ : ↥(centralizer ({z} : Set S)) ≃* ↥(fixedSubgroup (MulAut.conj z : MulAut S)) :=
    MulEquiv.subgroupCongr hfix.symm
  have hDn' : (D.map φ.toMonoidHom).Normal := Subgroup.Normal.map hDn φ.toMonoidHom φ.surjective
  have hDA' : Nonempty (↥(D.map φ.toMonoidHom) ≃* alternatingGroup (Fin 6)) :=
    ⟨(D.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eD⟩
  have hC' : Nat.card (fixedSubgroup (MulAut.conj z : MulAut S)) ≤ 1440 := by rw [hfix]; exact hC
  have hyp := a6Hyp_of_small (D.map φ.toMonoidHom) hDn' hDA' hC'
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  obtain ⟨hp3, hs, -⟩ := hshape t S n p f hp hp2 hadm hm _ hσ _ hyp
  have hsm := hsmall t S n p f hp hp2 hadm hm hp3 hs _ hσ _ hyp
  have h1 := hsm.1 ⟨z, rfl⟩
  omega


theorem a6OuterLieSmall_of_classify (hO : LieOrderFormulasInput) (hshape : ∀ t, OddA6Shape t)
    (hsmall : ∀ t, OddA6Small t) : A6OuterLieSmall := by
  intro S _ _ _ hL σ hσ hout hC D hDn hDA hinv
  rcases hL with hodd | heven
  · have hyp := a6Hyp_of_small D hDn hDA (by omega)
    obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hodd
    obtain ⟨hp3, hs, -⟩ := hshape t S n p f hp hp2 hadm hm σ hσ D hyp
    have hsm := hsmall t S n p f hp hp2 hadm hm hp3 hs σ hσ D hyp
    obtain ⟨h720, hx⟩ := hsm.2 hout hC
    refine ⟨?_, h720⟩
    rcases hx with ⟨x, hx2, hxD⟩ | ⟨ht, hn4, hf1⟩
    · exact absurd (hinv x hx2) hxD
    · subst ht
      subst hn4
      subst hf1
      subst hp3
      exact CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hm
  · exact (a6small_even_false hO heven hσ hout D hDn hDA hC hinv).elim

end CFSG.ComponentClassification.CatFC
