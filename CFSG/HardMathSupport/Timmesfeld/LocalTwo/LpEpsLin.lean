module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsUpper
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearOuter
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.GorensteinWalter
open CFSG.HardMathSupport.Timmesfeld.CrossChar

section Model

variable {F : Type} [Field F] [Finite F] {p : ℕ}

omit [Finite F] in
theorem conjAut_scalar_eq_one {n : ℕ} (u : Fˣ) :
    conjAut n F (GeneralLinearGroup.scalar (Fin n) u) = 1 :=
  LinearFlag.conjAut_scalar u

theorem exists_cyclic_quotient_linear {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (A : Subgroup (MulAut (projectiveSL n F))) (hA : IsElemAbelian p A) :
    ∃ (C : Type) (_ : Group C) (_ : IsCyclic C) (α : A →* C),
      ∀ x : A, α x = 1 → (x : MulAut (projectiveSL n F)) ∈ (conjAut n F).range := by
  classical
  set Dl := linearAutGroup n F with hDl
  set Es := semilinearAutGroup n F with hEs
  have hgen := (automorphism_generation (K := F) hn).1
  obtain ⟨hID, -, hDnorm, -, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := F)
  rw [hgen] at hDnorm
  have hDlN : Dl.Normal := linearAutGroup_normal_of_three_le hn
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg,
      inv_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hAE : A ≤ Es := fun x hx => by
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hA.2 x hx)
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  refine ⟨Es ⧸ Dl.subgroupOf Es, inferInstance, hcyc,
    (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hAE), fun x hx => ?_⟩
  have hxDl : (x : MulAut (projectiveSL n F)) ∈ Dl := by
    change QuotientGroup.mk (Subgroup.inclusion hAE x) = (1 : Es ⧸ Dl.subgroupOf Es) at hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    exact hx
  exact MonoidHom.mem_range.2 (mem_linearAutGroup_iff.1 hxDl)

noncomputable def linUpperModel (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ p)
    (hpF : p ∣ Nat.card F - 1) : UpperModel p (projectiveSL p F) F where
  M := GL (Fin p) F
  ι := MonoidHom.id _
  ι_inj := fun _ _ h => h
  ρ := conjAut p F
  ker_ρ := fun g hg => by
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn g 1 (by
      rw [map_one, mul_one]; exact hg)
    exact ⟨c, hc.symm⟩
  scalar_ρ := fun g c hg => by
    have : g = GeneralLinearGroup.scalar (Fin p) c := hg
    rw [this]
    exact conjAut_scalar_eq_one c
  plane := fun A B hAB hAp hBp hA1 hBA H hH hnorm =>
    diagAbelianPlaneBalance_holds p F hn p hp hp2 hpF dvd_rfl A B hAB hAp hBp hA1 hBA H hH hnorm
  outer_bal := fun D hD hDl H hH =>
    localDeltaIn_eq_bot_of_not_le_linearAutGroup hn hp hp2 hpF hD
      (fun h => hDl fun x hx => MonoidHom.mem_range.2 (mem_linearAutGroup_iff.1 (h hx))) hH
  cyc := fun A hA _ => exists_cyclic_quotient_linear hn hp hp2 A hA

theorem linLowerData (hp : p.Prime) (hn : 7 ≤ p) (hpF : p ∣ Nat.card F - 1) :
    Nonempty (LowerData p (projectiveSL p F)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζ : IsPrimitiveRoot z p := hz ▸ IsPrimitiveRoot.orderOf z
  have hdet : ∀ g : GL (Fin p) F, (g : Matrix (Fin p) (Fin p) F).det = 1 →
      g ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin p) F →* GL (Fin p) F).range := by
    intro g hg
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, hg]; rfl)
  refine Torus.lowerDataOfModel hζ hn (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin p) F →*
    GL (Fin p) F) SpecialLinearGroup.toGL_injective (proj p F) ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg)
    exact ⟨c, Units.ext hc⟩
  · exact fun k => hdet _ (Torus.det_Xg z hn k)
  · exact fun k => hdet _ (Torus.det_Swg hn k)
  · exact hdet _ (Torus.det_Tg hn)

end Model

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
