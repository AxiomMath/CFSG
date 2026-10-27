module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Char

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

omit [Finite K] in
theorem a2Char_eq_rootChar (d : Kˣ) (β : Fin d4.rank → ℤ) :
    a2Char d β = ((rootChar (τ := TwistTag.D4.tag) ![1, 1, d, 1] β : Kˣ) : K) := by
  unfold a2Char rootChar
  have e : ∀ f : Fin d4.rank → Kˣ, ∏ x, f x = f 0 * f 1 * f 2 * f 3 := fun f =>
    Fin.prod_univ_four f
  rw [e]
  simp [nd]
  rfl

omit [Finite K] in
theorem a2Char_rho (d : Kˣ) (β : Fin d4.rank → ℤ) : a2Char d (rho β) = a2Char d β := by
  unfold a2Char
  congr 2

theorem A2Core.a2_map_char (h : A2Core σ d q) (β : Fin d4.rank → ℤ) :
    σ (a2Char d β) = a2Char d β := by
  have h1 : Units.map σ.toRingHom.toMonoidHom (d ^ β (nd 2)) = d ^ β (nd 2) := by
    rw [map_zpow, h.fixed]
  have h2 := congrArg (fun u : Kˣ => (u : K)) h1
  exact h2

end Char

section Sign

variable {K : Type} [Field K]

@[expose] def a2Sign (K : Type) [Field K] (β : Fin d4.rank → ℤ) : K :=
  (((rootOperatorFamily d4).pinnedFamilySign β : ℤ) : K)

theorem a2Sign_mul_self (β : Fin d4.rank → ℤ) : a2Sign K β * a2Sign K β = 1 :=
  (rootOperatorFamily d4).pinnedFamilySign_mul_self K β

theorem a2_map_sign (σ : K ≃+* K) (β : Fin d4.rank → ℤ) : σ (a2Sign K β) = a2Sign K β := by
  unfold a2Sign
  exact map_intCast σ _

end Sign

section Root

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

omit [Finite K] in
theorem coe_xPar_a2 {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (c : K) :
    ((xPar (rootOperatorFamily d4) β c : adjointGroup d4 K) : ModGL d4 K) =
      pinnedX d4 K β (a2Sign K β * c) := by
  have h2 : pinnedX d4 K β (a2Sign K β * c) =
      (rootOperatorFamily d4).eltUnit K ⟨β, hβ⟩ c := by
    rw [a2Sign, (rootOperatorFamily d4).pinnedX_eq_eltUnit K hβ, ← mul_assoc,
      (rootOperatorFamily d4).pinnedFamilySign_mul_self, one_mul]
  rw [xPar_of_isRoot hβ]
  exact h2.symm

theorem A2Core.a2Conj_xPar (_h : A2Core σ d q) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (c : K) :
    a2Conj σ d ((xPar (rootOperatorFamily d4) β c : adjointGroup d4 K) : ModGL d4 K) =
      ((xPar (rootOperatorFamily d4) β (a2Char d β * σ c) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [coe_xPar_a2 hβ, coe_xPar_a2 hβ]
  have h1 : Units.map (entrywiseHom σ.toRingHom) (pinnedX d4 K β (a2Sign K β * c)) =
      pinnedX d4 K β (σ (a2Sign K β * c)) :=
    Units.ext (entrywise_pinnedX σ.toRingHom β _)
  unfold a2Conj
  rw [h1]
  have key : a2S d * pinnedX d4 K β (σ (a2Sign K β * c)) * (a2S d)⁻¹ =
      pinnedX d4 K β (a2Char d β * σ (a2Sign K β * c)) := by
    rw [a2Char_eq_rootChar]
    exact rootDiagUnit_conj_pinnedX _ hβ _
  rw [key, map_mul, a2_map_sign]
  congr 1
  ring

end Root

section Orbit

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2Conj_xOrbit (h : A2Core σ d q) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β)
    (_hne : rho β ≠ β) (c : K) :
    a2Conj σ d ((xOrbit σ.toRingHom β c : adjointGroup d4 K) : ModGL d4 K) =
      ((xOrbit σ.toRingHom β (a2Char d β * σ c) : adjointGroup d4 K) : ModGL d4 K) := by
  have h1 := isRoot_rho hβ
  have h2 := isRoot_rho h1
  have e1 := map_sign σ.toRingHom (twistSign_eq_one_or σ.toRingHom β)
  have e2 := map_sign σ.toRingHom (twistSign_eq_one_or σ.toRingHom (rho β))
  have ec := a2_map_char h β
  have er1 := a2Char_rho d β
  have er2 := a2Char_rho d (rho β)
  simp only [xOrbit, Subgroup.coe_mul]
  rw [a2Conj_mul, a2Conj_mul, a2Conj_xPar h hβ, a2Conj_xPar h h1, a2Conj_xPar h h2]
  congr 3
  · congr 1
    show a2Char d (rho β) * σ (twistSign σ.toRingHom β * σ c) =
      twistSign σ.toRingHom β * σ (a2Char d β * σ c)
    change σ (twistSign σ.toRingHom β) = _ at e1
    simp only [map_mul, e1, ec, er1]
    ring
  · show a2Char d (rho (rho β)) *
        σ (twistSign σ.toRingHom β * twistSign σ.toRingHom (rho β) * σ (σ c)) =
      twistSign σ.toRingHom β * twistSign σ.toRingHom (rho β) * σ (σ (a2Char d β * σ c))
    change σ (twistSign σ.toRingHom β) = _ at e1
    change σ (twistSign σ.toRingHom (rho β)) = _ at e2
    simp only [map_mul, e1, e2, ec, er1, er2]
    ring

end Orbit

end CFSG.GH74.GLS.Stage2.Bender.Thm1
