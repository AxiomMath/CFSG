module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.BenderSuzuki.PFAppendixIII
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem properHull_fixedPointFree_inverts [Finite G]
    (Q : Subgroup G) (s : G) (hs : s * s = 1)
    (hsQ : s ∈ Subgroup.normalizer (Q : Set G))
    (hfixed : Q ⊓ Subgroup.centralizer ({s} : Set G) = ⊥) :
    ∀ x ∈ Q, rightConjugateElem x s = x⁻¹ := by
  let sN : Subgroup.normalizer (Q : Set G) := ⟨s, hsQ⟩
  let tau : MulAut Q := Q.normalizerMonoidHom sN
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have hinvol : Function.Involutive tau := by
    intro x
    apply Subtype.ext
    change s * (s * (x : G) * s⁻¹) * s⁻¹ = (x : G)
    rw [hsinv]
    calc
      s * (s * (x : G) * s) * s = (s * s) * (x : G) * (s * s) := by group
      _ = (x : G) := by rw [hs]; simp only [one_mul, mul_one]
  have hfree : MonoidHom.FixedPointFree tau := by
    intro x hx
    apply Subtype.ext
    have hxconj : s * (x : G) * s⁻¹ = (x : G) := congrArg Subtype.val hx
    have hxcomm : (x : G) ∈ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hxconj).symm
    exact Subgroup.mem_bot.mp (hfixed ▸ (show (x : G) ∈
      Q ⊓ Subgroup.centralizer ({s} : Set G) from ⟨x.property, hxcomm⟩))
  have hinv := hfree.coe_eq_inv_of_involutive hinvol
  intro x hx
  have hh := congrArg Subtype.val (congrFun hinv (⟨x, hx⟩ : Q))
  simpa only [tau, sN, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inv, rightConjugateElem, hsinv] using hh

theorem properHull_inversion_automorphism_commutes
    {Q : Type*} [Group Q] (tau rho : MulAut Q)
    (hinv : ∀ x : Q, tau x = x⁻¹) : Commute tau rho := by
  apply MulEquiv.ext
  intro x
  change tau (rho x) = rho (tau x)
  rw [hinv, hinv, map_inv]

theorem properHull_actor_commutator_centralizes_inverted [Finite G]
    (X Q : Subgroup G) (s : G) (hs : s * s = 1)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hsQ : s ∈ Subgroup.normalizer (Q : Set G))
    (hfixed : Q ⊓ Subgroup.centralizer ({s} : Set G) = ⊥) :
    ⁅X, Subgroup.zpowers s⁆ ≤ Subgroup.centralizer (Q : Set G) := by
  let N := Subgroup.normalizer (Q : Set G)
  let rho := Q.normalizerMonoidHom
  let sN : N := ⟨s, hsQ⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have hinv : ∀ x : Q, rho sN x = x⁻¹ := by
    intro x
    apply Subtype.ext
    have hh := properHull_fixedPointFree_inverts Q s hs hsQ hfixed x x.property
    simpa only [rho, sN, Subgroup.normalizerMonoidHom_apply_apply_coe,
      rightConjugateElem, hsinv, Subgroup.coe_inv] using hh
  apply Subgroup.commutator_le.mpr
  intro x hx a ha
  have hxN : x ∈ N := hXQ hx
  have haN : a ∈ N := (Subgroup.zpowers_le.mpr hsQ) ha
  let xN : N := ⟨x, hxN⟩
  let aN : N := ⟨a, haN⟩
  have haPow : aN ∈ Subgroup.zpowers sN := by
    obtain ⟨n, hn⟩ := ha
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  obtain ⟨n, hn⟩ := haPow
  have hcomm : Commute (rho xN) (rho aN) := by
    have hh := (properHull_inversion_automorphism_commutes (rho sN) (rho xN) hinv).symm
    rw [← hn, map_zpow]
    exact hh.zpow_right n
  have hker : ⁅xN, aN⁆ ∈ rho.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hcomm
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact hker

theorem properHull_self_commutator_centralizes_inverted [Finite G]
    (X Q : Subgroup G) (s : G) (hs : s * s = 1)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hsQ : s ∈ Subgroup.normalizer (Q : Set G))
    (hfixed : Q ⊓ Subgroup.centralizer ({s} : Set G) = ⊥)
    (hself : ⁅X, Subgroup.zpowers s⁆ = X) :
    X ≤ Subgroup.centralizer (Q : Set G) := by
  rw [← hself]
  exact properHull_actor_commutator_centralizes_inverted X Q s hs hXQ hsQ hfixed

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
