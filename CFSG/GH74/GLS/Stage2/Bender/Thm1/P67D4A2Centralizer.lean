module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Central

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Lift

theorem a2cen_lift_one : d43Lift (hexPos 1) = Pi.single (nd 0) 1 := by
  decide

theorem a2cen_lift_five : d43Lift (hexPos 5) = Pi.single (nd 0) 1 + Pi.single (nd 2) 1 := by
  decide

end Lift

section Char

variable {K : Type} [Field K]

theorem a2cen_rootChar_rho {c : Fin d4.rank → Kˣ} (hρ : ∀ i, c (rhoPerm i) = c i)
    (β : Fin d4.rank → ℤ) :
    rootChar (τ := TwistTag.D4.tag) c (rho β) = rootChar (τ := TwistTag.D4.tag) c β := by
  unfold rootChar
  refine Fintype.prod_equiv rhoPerm.symm _ _ fun j => ?_
  have h1 := hρ (rhoPerm.symm j)
  rw [Equiv.apply_symm_apply] at h1
  simp only [permLattice, Function.comp_apply]
  rw [h1]

theorem a2cen_map_rootChar {σ : K ≃+* K} {c : Fin d4.rank → Kˣ}
    (hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (c i) = c i) (β : Fin d4.rank → ℤ) :
    σ.toRingHom ((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) =
      ((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) := by
  have h1 : Units.map σ.toRingHom.toMonoidHom (rootChar (τ := TwistTag.D4.tag) c β) =
      rootChar (τ := TwistTag.D4.tag) c β := by
    unfold rootChar
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, hfix]
  exact congrArg (fun u : Kˣ => (u : K)) h1

end Char

section Orbit

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem a2cen_torus_conj_xOrbit {g : adjointGroup d4 K} {c : Fin d4.rank → Kˣ}
    (hg : (g : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag c)
    (hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (c i) = c i)
    (hρ : ∀ i, c (rhoPerm i) = c i) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (u : K) :
    g * xOrbit σ.toRingHom β u * g⁻¹ =
      xOrbit σ.toRingHom β (((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) * u) := by
  have h1 := isRoot_rho hβ
  have h2 := isRoot_rho h1
  have e1 : ((rootChar (τ := TwistTag.D4.tag) c (rho β) : Kˣ) : K) =
      ((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) := by
    rw [a2cen_rootChar_rho hρ]
  have e2 : ((rootChar (τ := TwistTag.D4.tag) c (rho (rho β)) : Kˣ) : K) =
      ((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) := by
    rw [a2cen_rootChar_rho hρ, a2cen_rootChar_rho hρ]
  have hσχ := a2cen_map_rootChar (σ := σ) hfix β
  have key : ∀ x y z : adjointGroup d4 K,
      g * (x * y * z) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) := fun x y z => by
    group
  simp only [xOrbit]
  rw [key, a2_torus_conj_xPar hg hβ, a2_torus_conj_xPar hg h1, a2_torus_conj_xPar hg h2, e1, e2]
  have p1 : ((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) *
      (twistSign σ.toRingHom β * σ.toRingHom u) =
      twistSign σ.toRingHom β *
        σ.toRingHom (((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) * u) := by
    rw [map_mul, hσχ]
    ring
  have p2 : ((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) *
      (twistSign σ.toRingHom β * twistSign σ.toRingHom (rho β) *
        σ.toRingHom (σ.toRingHom u)) =
      twistSign σ.toRingHom β * twistSign σ.toRingHom (rho β) *
        σ.toRingHom (σ.toRingHom (((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) * u)) := by
    rw [map_mul, map_mul, hσχ, hσχ]
    ring
  rw [p1, p2]

end Orbit

section Weight

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2cen_weight_eq_one (h : A2Core σ d q) {t : adjointGroup d4 K} {c : Fin d4.rank → Kˣ}
    (hct : (t : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag c)
    (hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (c i) = c i)
    (hρ : ∀ i, c (rhoPerm i) = c i) {k : ℤ} (hk : k = 1 ∨ k = 5) {g : adjointGroup d4 K}
    (hg : g ∈ twistedRootSubgroupD4 σ.toRingHom (hexPos k)) (hg1 : g ≠ 1)
    (hcomm : t * g = g * t) :
    rootChar (τ := TwistTag.D4.tag) c (d43Lift (hexPos k)) = 1 := by
  have hσ3 : ∀ x, σ.toRingHom (σ.toRingHom (σ.toRingHom x)) = x :=
    sigma_three_of_card (σ := σ.toRingHom) h.card (fun x => h.frob x)
  have hγ : IsRoot Tag.G2 (hexPos k) :=
    isRoot_hexPos (by rcases hk with rfl | rfl <;> norm_num)
      (by rcases hk with rfl | rfl <;> norm_num)
  have hs : ¬ d43Long (hexPos k) := by
    rcases hk with rfl | rfl <;> (unfold d43Long; decide)
  have hα := isRoot_d43Lift hγ
  have hne := rho_d43Lift_ne hγ hs
  obtain ⟨u, rfl⟩ := (mem_iff_d43XSh hσ3 hγ hs g).1 hg
  have e := a2cen_torus_conj_xOrbit (σ := σ) hct hfix hρ hα u
  have e2 : t * xOrbit σ.toRingHom (d43Lift (hexPos k)) u * t⁻¹ =
      xOrbit σ.toRingHom (d43Lift (hexPos k)) u := by
    have hcomm' : t * xOrbit σ.toRingHom (d43Lift (hexPos k)) u =
        xOrbit σ.toRingHom (d43Lift (hexPos k)) u * t := hcomm
    rw [hcomm']
    group
  rw [e2] at e
  have e3 := xOrbit_injective σ.toRingHom hα hne e
  have hu : u ≠ 0 := by
    rintro rfl
    exact hg1 (xOrbit_zero σ.toRingHom (d43Lift (hexPos k)))
  refine Units.ext ?_
  rw [Units.val_one]
  exact mul_right_cancel₀ hu (by rw [one_mul]; exact e3.symm)

end Weight

section Main

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_torus_centralizer (h : A2Core σ d q) {t : adjointGroup d4 K}
    (ht : t ∈ ⨆ i, hHatE σ.toRingHom i)
    (htfix : a2Conj σ d (t : ModGL TwistTag.D4.tag K) = (t : ModGL TwistTag.D4.tag K))
    (hc : ∀ k : ℤ, (k = 1 ∨ k = 5) → ∃ g ∈ twistedRootSubgroupD4 σ.toRingHom (hexPos k),
      g ≠ 1 ∧ a2Conj σ d (g : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K) ∧
        t * g = g * t) :
    t = 1 := by
  obtain ⟨c, hct, c1, c3, c30, -⟩ := a2_torus_coord h ht
  have hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (c i) = c i := by
    have h1 := htfix
    rw [hct, a2tor_conj_rootDiagUnit] at h1
    exact fun i => congrFun (rootDiagUnit_injective h1) i
  have hρ0 : c (nd 1) = c (nd 0) := c1.trans (hfix _)
  have hρ1 : c (nd 3) = c (nd 1) := c3.trans (hfix _)
  have hρ3 : c (nd 0) = c (nd 3) := ((hfix (nd 3)).symm.trans c30).symm
  have hρ : ∀ i, c (rhoPerm i) = c i := by
    intro i
    fin_cases i
    · exact hρ0
    · exact hρ1
    · rfl
    · exact hρ3
  obtain ⟨g1, hg1, hg1ne, -, hcomm1⟩ := hc 1 (Or.inl rfl)
  obtain ⟨g5, hg5, hg5ne, -, hcomm5⟩ := hc 5 (Or.inr rfl)
  have w1 := a2cen_weight_eq_one h hct hfix hρ (Or.inl rfl) hg1 hg1ne hcomm1
  have w5 := a2cen_weight_eq_one h hct hfix hρ (Or.inr rfl) hg5 hg5ne hcomm5
  rw [a2cen_lift_one, a2_rootChar_single] at w1
  rw [a2cen_lift_five, rootChar_add, a2_rootChar_single, a2_rootChar_single, w1, one_mul] at w5
  have hc1 : c = 1 := by
    funext i
    fin_cases i
    · exact w1
    · exact hρ0.trans w1
    · exact w5
    · exact hρ1.trans (hρ0.trans w1)
  apply Subtype.ext
  rw [hct, hc1, rootDiagUnit_one]
  rfl

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
