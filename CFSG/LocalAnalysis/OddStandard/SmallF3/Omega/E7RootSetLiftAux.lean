module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRoots
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
public import CFSG.LocalAnalysis.StandardType.GGFamOuterEField
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.OddStandard.SmallF3.Omega.E7RootSet
open Certificates.OmegaSevenMax CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Timmesfeld.RootAut

private theorem e7LiftP11_polarV_redV_aux (x y : Fin Tag.E7.rank → ℤ) :
    QuadraticMap.polar qForm (redV x) (redV y) = ((iform x y : ℤ) : ZMod 3) := by
  have hsym : Tag.symmetrizedCartan Tag.E7 = Tag.cartan Tag.E7 := by
    rw [Tag.symmetrizedCartan, Tag.symmetrizer]
    exact one_mul _
  rw [polar_qForm, iform, hsym]
  change polarV (redV x) (redV y) =
    ((∑ i : Fin 7, ∑ j : Fin 7, x i * Tag.cartan Tag.E7 i j * y j : ℤ) : ZMod 3)
  simp only [polarV, redV, Tag.cartan, Tag.cartanE, Matrix.mul_apply, Fin.sum_univ_seven,
    Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.val_one', Finset.sum_apply, Pi.smul_apply,
    Matrix.of_apply]
  norm_num
  push_cast
  rw [show (2 : ZMod 3) = -1 by decide]
  ring

theorem e7LiftP11_polarV_redV (x y : Fin Tag.E7.rank → ℤ) :
    QuadraticMap.polar qForm (redV x) (redV y) = ((iform x y : ℤ) : ZMod 3) :=
  e7LiftP11_polarV_redV_aux x y

theorem e7LiftP11_isRootComponent :
    IsRootComponent ({γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}) := by
  let χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Multiplicative (ZMod 2) := 1
  have hχ : ∀ γ : Fin Tag.E7.rank → ℤ, χ (Multiplicative.ofAdd γ) = 1 := fun γ => rfl
  let i : KernelComponent χ :=
    Quotient.mk _ ⟨(Pi.single 0 1 : Fin Tag.E7.rank → ℤ),
      ⟨isRoot_single Tag.E7 0, hχ _⟩⟩
  rw [← CFSG.StandardType.TableCRes.famTrivial_componentRoots_eq_univ
    (τ := Tag.E7) (Or.inr (Or.inl rfl)) χ hχ i]
  exact isRootComponent_componentRoots i

theorem e7LiftP11_ncard :
    ({γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}).ncard = 126 := by
  classical
  have hinj : Set.InjOn redV {α : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 α} :=
    redV_injOn_roots
  have himg : (↑rootSet : Set _) = redV '' {α : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 α} :=
    rootSet_eq_image
  rw [← hinj.ncard_image, ← himg, Set.ncard_coe_finset, card_rootSet]

theorem e7LiftP11_sepB_E7 : sepB (TauCeti.DynkinType.E7).cartanMatrix 14 = true := by
  rw [TauCeti.DynkinType.cartanMatrix_E7]
  decide +kernel

theorem e7LiftP11_rigidity (σ : Equiv.Perm (Fin 7))
    (h : ∀ i j, CartanMatrix.E 7 (σ i) (σ j) = CartanMatrix.E 7 i j) : σ = 1 := by
  refine eq_one_of_sepB (M := CartanMatrix.E 7) (K := 14) ?_ h
  rw [← TauCeti.DynkinType.cartanMatrix_E7]
  exact e7LiftP11_sepB_E7

theorem e7LiftP11_dynkinType_E7 (t : TauCeti.DynkinType) (ht : t.Valid) (hs : t.IsSimplyLaced)
    (h : t.numRoots = 126) : t = .E7 := by
  cases t with
  | A n =>
    exfalso
    simp only [TauCeti.DynkinType.numRoots] at h
    have hn : n ≤ 11 := by nlinarith
    interval_cases n <;> norm_num at h
  | B n => exact absurd hs (TauCeti.DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hs (TauCeti.DynkinType.not_isSimplyLaced_C n)
  | D n =>
    exfalso
    simp only [TauCeti.DynkinType.numRoots] at h
    have ht4 : 4 ≤ n := (TauCeti.DynkinType.valid_D).1 ht
    have hn1 : 1 ≤ n := by omega
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    have hn : n ≤ 8 := by nlinarith
    interval_cases n <;> norm_num at h
  | E6 => norm_num [TauCeti.DynkinType.numRoots] at h
  | E7 => rfl
  | E8 => norm_num [TauCeti.DynkinType.numRoots] at h
  | F4 => exact absurd hs (TauCeti.DynkinType.not_isSimplyLaced_F4)
  | G2 => exact absurd hs (TauCeti.DynkinType.not_isSimplyLaced_G2)

end CFSG.StandardType

end
