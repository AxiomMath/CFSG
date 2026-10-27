module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

section Root

structure FrobRoot {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) (p : ℕ) where
  q0 : ℕ
  Fr0 : L →+* L
  Fr0_apply : ∀ c, Fr0 c = c ^ q0
  z0 : ModGL τ L
  q_eq : D.q = q0 ^ p
  pow_eq : ∀ g : ModGL τ L,
    (fun h => z0 * Units.map (entrywiseHom Fr0) h * z0⁻¹)^[p] g = D.step g

namespace FrobRoot

variable {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L} {p : ℕ} (R : FrobRoot D p)

@[expose] noncomputable def step0 : ModGL τ L →* ModGL τ L :=
  (MulAut.conj R.z0).toMonoidHom.comp (Units.map (entrywiseHom R.Fr0))

theorem step0_apply (g : ModGL τ L) :
    R.step0 g = R.z0 * Units.map (entrywiseHom R.Fr0) g * R.z0⁻¹ :=
  rfl

theorem step0_iterate (g : ModGL τ L) : R.step0^[p] g = D.step g := by
  have h : ⇑R.step0 = fun h => R.z0 * Units.map (entrywiseHom R.Fr0) h * R.z0⁻¹ :=
    funext R.step0_apply
  rw [h]
  exact R.pow_eq g

theorem mem_torus_of_step0_eq {y : ModGL τ L} (hy : y ∈ torusGroup τ L) (h : R.step0 y = y) :
    y ∈ D.torus := by
  refine mem_twistedTorusOf.2 ⟨hy, ?_⟩
  have h1 : R.step0^[p] y = y := Function.iterate_fixed h p
  rw [R.step0_iterate] at h1
  exact h1

end FrobRoot

end Root

section Rigidity

variable {τ : Tag} {L : Type} [Field L]

theorem FrobRoot.not_conj [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ}
    (R : FrobRoot S.D p) (hτ : τ ≠ .G2) {r j : ℕ} [ExpChar L r] (hr : r.Prime)
    (hq0 : R.q0 = r ^ j) (hj : 0 < j) (hp : 2 ≤ p) (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (z : ModGL τ L)
    (hz : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, R.step0 x = z * x * z⁻¹) :
    False := by
  have hFr : R.Fr0 = iterateFrobenius L r j :=
    RingHom.ext fun c => by rw [R.Fr0_apply, hq0, iterateFrobenius_def]
  have hq : S.D.q = r ^ (j * p) := by rw [R.q_eq, hq0, ← pow_mul]
  have hjf : j < j * p := lt_mul_of_one_lt_right hj hp
  refine outer_false_of_component_fixed_by_twist S hτ hT i hr hq hq4 hj hjf (z⁻¹ * R.z0)
    fun x hx => ?_
  have h := hz x hx
  rw [R.step0_apply, hFr] at h
  calc z⁻¹ * R.z0 * Units.map (entrywiseHom (iterateFrobenius L r j)) x * (z⁻¹ * R.z0)⁻¹
      = z⁻¹ * (R.z0 * Units.map (entrywiseHom (iterateFrobenius L r j)) x * R.z0⁻¹) * z := by
        group
    _ = x := by rw [h]; group

end Rigidity

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
