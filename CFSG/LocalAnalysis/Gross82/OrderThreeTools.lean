module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent

public section

namespace CFSG.LocalAnalysis.Gross82.OrderThree

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearField
  (pglFieldAut fixedField fixedPGL subfieldPGLEquivFixed mem_fixedField)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (card_SL_eq)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (u42_card_PGL_mul)

theorem exists_sylow_fix_congr {K M : Type*} [Group K] [Group M] [Finite K] {p : ℕ}
    [Fact p.Prime] (θ : K ≃* M) (P : Sylow p K) {α : MulAut K}
    (hfix : ∀ x ∈ (P : Subgroup K), α x = x) :
    ∃ P' : Sylow p M, ∀ y ∈ (P' : Subgroup M), MulAut.congr θ α y = y := by
  refine ⟨P.mapSurjective (f := (θ : K →* M)) θ.surjective, fun y hy => ?_⟩
  rw [Sylow.coe_mapSurjective (f := (θ : K →* M)) (hf := θ.surjective) (P := P)] at hy
  obtain ⟨x, hx, hxy⟩ := (Subgroup.mem_map.mp hy)
  rw [← hxy]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    show θ.symm ((θ : K →* M) x) = x from θ.symm_apply_apply x]
  rw [hfix x hx]
  rfl

theorem card_fixedSubgroup_dvd_of_injective_intertwine {G H : Type*} [Group G] [Group H]
    (ι : G →* H) (hι : Function.Injective ι) (α : MulAut G) (β : MulAut H)
    (h : ∀ x, ι (α x) = β (ι x)) :
    Nat.card (fixedSubgroup α) ∣ Nat.card (fixedSubgroup β) := by
  have hle : (fixedSubgroup α).map ι ≤ fixedSubgroup β := by
    rintro _ ⟨x, hx, rfl⟩
    change α x = x at hx
    change β (ι x) = ι x
    rw [← h x, hx]
  rw [← Subgroup.card_map_of_injective hι]
  exact Subgroup.card_dvd_of_le hle

theorem card_fixedSubgroup_pglFieldAut {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (σ : F ≃+* F) :
    Nat.card (fixedSubgroup
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldAut (Fin n) F σ)) =
      lieOrderNumerator .PSL n
        (Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField F σ)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Finite (fixedField F σ) :=
    Finite.of_injective (fixedField F σ).subtype (fixedField F σ).subtype_injective
  have hq : 0 < Nat.card (fixedField F σ) - 1 := by
    have h2 : 1 < Nat.card (fixedField F σ) := Finite.one_lt_card
    omega
  have hPGL := u42_card_PGL_mul (n := n) hn (F := fixedField F σ)
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin n) (fixedField F σ)) *
      (Nat.card (fixedField F σ) - 1) = Nat.card (GL (Fin n) (fixedField F σ)) := by
    rw [← Nat.card_units (fixedField F σ), Matrix.card_SL_mul_card_units]
  have heq : Nat.card (Matrix.ProjGenLinGroup (Fin n) (fixedField F σ)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (fixedField F σ)) :=
    Nat.eq_of_mul_eq_mul_right hq (hPGL.trans hSL.symm)
  have hfix : fixedSubgroup (pglFieldAut (Fin n) F σ) = fixedPGL (Fin n) F σ := rfl
  rw [hfix]
  calc Nat.card (fixedPGL (Fin n) F σ)
      = Nat.card (Matrix.ProjGenLinGroup (Fin n) (fixedField F σ)) :=
        (Nat.card_congr (subfieldPGLEquivFixed (Fin n) F σ).toEquiv).symm
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin n) (fixedField F σ)) := heq
    _ = lieOrderNumerator .PSL n (Nat.card (fixedField F σ)) := by
        rw [card_SL_eq hn, lieOrderNumerator]

theorem card_fixedField_eq_card_semilinearFixedSubfield {F : Type} [Field F] (σ : F ≃+* F) :
    Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField F σ) =
      Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) := by
  have h : CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField F σ =
      CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ := by
    ext x
    rw [mem_fixedField, RingHom.mem_eqLocusField]
    rfl
  rw [h]

end CFSG.LocalAnalysis.Gross82.OrderThree
