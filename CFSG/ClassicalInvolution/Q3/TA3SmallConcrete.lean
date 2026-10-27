module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTransportEx
public import CFSG.ClassicalInvolution.SmallCases.NobqSmall
public import CFSG.GH74.KGroups.Generic
public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.GH74.KGroups (AutModel)

@[expose] def ConcreteLeaf (G : Type) [Group G] (P A : Subgroup G) : Prop :=
  ∀ X : Subgroup G, P ≤ X → X ≤ A → ∀ (R : Subgroup ↥X) (S : Sylow 2 R) (t : ↥X),
    TightDatum R S t → TightCls ↥X R S t → ¬ TightInO2 t →
      TightEx ↥X R S t ∨ GoodThreeElement R t

theorem autModel_Φ_conj_eq {K G : Type} [Group K] [Group G] (M : AutModel K G)
    (hPA : M.P ≤ M.A) (k : K) : (M.Φ (MulAut.conj k) : G) = (M.e k : G) := by
  set a : M.A := ⟨(M.e k : G), hPA (M.e k).2⟩ with ha
  have hΦψ : M.Φ (M.Φ.symm a) = a := M.Φ.apply_symm_apply a
  have hψ : M.Φ.symm a = MulAut.conj k := by
    ext x
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec _ x, hΦψ]
    simp [ha, MulAut.conj_apply]
  rw [← hψ, hΦψ]

section Realize

variable {Y K G : Type} [Group Y] [Group K] [Group G] (N : Subgroup Y) [N.Normal]
  (eK : ↥N ≃* K) (M : AutModel K G)

noncomputable def realize : Y →* G :=
  M.ι.comp ((MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal)

theorem realize_injective (hC : Subgroup.centralizer (N : Set Y) = ⊥) :
    Function.Injective (realize N eK M) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h2 : (MulAut.congr eK) (MulAut.conjNormal y) = 1 :=
    M.ι_injective (by rw [map_one]; exact hy)
  have h3 : (MulAut.conjNormal y : MulAut ↥N) = 1 := by
    rw [← map_one (MulAut.congr eK)] at h2
    exact (MulAut.congr eK).injective h2
  have hyC : y ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h4 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : Y)) h3
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc x * y = (y * x * y⁻¹) * y := by rw [h4]
      _ = y * x := by group
  rw [hC] at hyC
  exact hyC

theorem realize_range_le : (realize N eK M).range ≤ M.A := by
  rintro _ ⟨y, rfl⟩
  exact M.ι_mem _

theorem le_realize_range (hPA : M.P ≤ M.A) : M.P ≤ (realize N eK M).range := by
  intro p hp
  set k : K := M.e.symm ⟨p, hp⟩ with hk
  refine ⟨(eK.symm k : Y), ?_⟩
  have hconj : (MulAut.congr eK) (MulAut.conjNormal (eK.symm k : Y)) = MulAut.conj k := by
    ext k'
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
    apply eK.symm.injective
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv]
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
  show (M.Φ ((MulAut.congr eK) (MulAut.conjNormal (eK.symm k : Y))) : G) = p
  rw [hconj, autModel_Φ_conj_eq M hPA k, hk]
  simp

end Realize


theorem smallSimpleLeaf_of_concrete {K G : Type} [Group K] [Group G] (M : AutModel K G)
    (hPA : M.P ≤ M.A) (hC : ConcreteLeaf G M.P M.A) :
    SmallSimpleLeaf fun F _ => Nonempty (F ≃* K) := by
  intro Y _ _ _ _ hnab _ ⟨eK⟩ R S t hd hc hE2
  have := genFittingFStar_normal Y
  have hinj := realize_injective (genFittingFStar Y) eK M
    (Nobq.centralizer_genFittingFStar_eq_bot hnab)
  exact tightExOrGood_of_map_equiv (MonoidHom.ofInjective hinj) hd hc hE2
    fun S' hd' hc' hE2' => hC _ (le_realize_range _ eK M hPA)
      (realize_range_le _ eK M) _ S' _ hd' hc' hE2'

theorem SmallSimpleLeaf.mono {P Q : ∀ (F : Type) [Group F], Prop}
    (hPQ : ∀ (F : Type) [Group F], P F → Q F) (h : SmallSimpleLeaf Q) : SmallSimpleLeaf P :=
  fun Y _ _ _ hA hnab hG hPF => h Y hA hnab hG (hPQ _ hPF)

theorem SmallSimpleLeaf.of_or {P Q : ∀ (F : Type) [Group F], Prop}
    (hP : SmallSimpleLeaf P) (hQ : SmallSimpleLeaf Q) : SmallSimpleLeaf fun F _ => P F ∨ Q F :=
  fun Y _ _ _ hA hnab hG hPQ => hPQ.elim (hP Y hA hnab hG) (hQ Y hA hnab hG)

end CFSG.ClassicalInvolution.Q3.TA3
