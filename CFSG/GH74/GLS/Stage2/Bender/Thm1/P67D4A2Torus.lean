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

theorem a2tor_cartan_two :
    d4.cartan (nd 2) (nd 0) = -1 ∧ d4.cartan (nd 2) (nd 1) = -1 ∧ d4.cartan (nd 2) (nd 2) = 2 ∧
      d4.cartan (nd 2) (nd 3) = -1 := by
  decide

section Diagonal

variable {K : Type} [Field K] {σ : K ≃+* K} {d : Kˣ}

theorem a2tor_a2S_eq (d : Kˣ) :
    a2S d = rootDiagUnit d4 (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) :=
  congrArg (rootDiagUnit d4) (funext fun j => by fin_cases j <;> rfl)

theorem a2tor_conj_rootDiagUnit (b : Fin d4.rank → Kˣ) :
    a2Conj σ d (rootDiagUnit d4 b) =
      rootDiagUnit d4 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) := by
  unfold a2Conj
  rw [a2tor_a2S_eq, units_map_entrywiseHom_rootDiagUnit (t := TwistTag.D4),
    mul_inv_eq_iff_eq_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

end Diagonal

section Torus

variable
  {K : Type} [Field K] {σ : K ≃+* K} {d : Kˣ}

theorem a2tor_coe_torusElement (i : Fin d4.rank) (t : Kˣ) :
    ((torusElement d4 K i t : adjointGroup d4 K) : ModGL d4 K) = torusElt d4 K i t := rfl

theorem a2tor_coe_weylElement (i : Fin d4.rank) :
    ((CFSG.LieType.Chevalley.weylElement d4 K i : adjointGroup d4 K) : ModGL d4 K) =
      weylElt d4 K i 1 := rfl

theorem a2tor_conj_torusElt (i : Fin d4.rank) (t : Kˣ) :
    a2Conj σ d (torusElt d4 K i t) =
      torusElt d4 K i (Units.map σ.toRingHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, a2tor_conj_rootDiagUnit, torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  simp [map_zpow]

end Torus

section Weyl

variable
  {K : Type} [Field K] {σ : K ≃+* K} {d : Kˣ}

theorem a2tor_conj_weylElt_outer {i : Fin d4.rank} (hi : i ≠ nd 2) :
    a2Conj σ d (weylElt d4 K i 1) = weylElt d4 K i 1 := by
  have h := weylElt_conj_rootDiagUnit (K := K) (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) i
  rw [Pi.mulSingle_eq_of_ne hi] at h
  simp only [one_zpow, mul_one] at h
  unfold a2Conj
  rw [entrywise_weylElt_one σ i, a2tor_a2S_eq, mul_inv_eq_iff_eq_mul]
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem a2tor_conj_weylElt_central :
    a2Conj σ d (weylElt d4 K (nd 2) 1) =
      weylElt d4 K (nd 2) 1 * torusElt d4 K (nd 2) d⁻¹ := by
  obtain ⟨c0, c1, c2, c3⟩ := a2tor_cartan_two
  have hX : torusElt d4 K (nd 2) d⁻¹ * a2S d =
      rootDiagUnit d4 (fun j => d⁻¹ ^ d4.cartan (nd 2) j *
        (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) j) := by
    rw [torusElt_eq_rootDiagUnit, a2tor_a2S_eq, ← rootDiagUnit_mul]
    rfl
  have hw := weylElt_conj_rootDiagUnit (K := K)
    (fun j => d⁻¹ ^ d4.cartan (nd 2) j * (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) j) (nd 2)
  have hfun : (fun j => (d⁻¹ ^ d4.cartan (nd 2) j *
        (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) j) *
      (d⁻¹ ^ d4.cartan (nd 2) (nd 2) *
        (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) (nd 2)) ^ (-d4.cartan (nd 2) j)) =
      (Pi.mulSingle (nd 2) d : Fin d4.rank → Kˣ) := by
    funext j
    have hj : j = nd 0 ∨ j = nd 1 ∨ j = nd 2 ∨ j = nd 3 := by
      revert j; decide
    rcases hj with rfl | rfl | rfl | rfl
    · simp only [c0, c2, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (show nd 0 ≠ nd 2 by decide)]
      group
    · simp only [c1, c2, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (show nd 1 ≠ nd 2 by decide)]
      group
    · simp only [c2, Pi.mulSingle_eq_same]
      group
    · simp only [c3, c2, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (show nd 3 ≠ nd 2 by decide)]
      group
  rw [hfun, ← hX, ← a2tor_a2S_eq] at hw
  unfold a2Conj
  rw [entrywise_weylElt_one σ (nd 2)]
  calc a2S d * weylElt d4 K (nd 2) 1 * (a2S d)⁻¹ =
      (weylElt d4 K (nd 2) 1 * (torusElt d4 K (nd 2) d⁻¹ * a2S d) * (weylElt d4 K (nd 2) 1)⁻¹) *
        weylElt d4 K (nd 2) 1 * (a2S d)⁻¹ := by rw [hw]
    _ = weylElt d4 K (nd 2) 1 * torusElt d4 K (nd 2) d⁻¹ := by group

theorem a2tor_mem_hHatE_zero {σ' : K →+* K} {t : Kˣ} (ht : σ' t = t) :
    torusElement d4 K (nd 2) t ∈ hHatE σ' (ng 0) :=
  ⟨⟨t, (mem_fixedUnits σ').2 ht⟩, rfl⟩

theorem a2tor_mem_hHatE_one {σ' : K →+* K} (t : Kˣ) : hShortHom σ' t ∈ hHatE σ' (ng 1) :=
  ⟨t, rfl⟩

theorem a2tor_exists_of_mem_hHatE_zero {σ' : K →+* K} {g : adjointGroup d4 K}
    (hg : g ∈ hHatE σ' (ng 0)) : ∃ t : Kˣ, σ' t = t ∧ g = torusElement d4 K (nd 2) t := by
  obtain ⟨⟨t, ht⟩, rfl⟩ := hg
  exact ⟨t, (mem_fixedUnits σ').1 ht, rfl⟩

theorem a2tor_exists_of_mem_hHatE_one {σ' : K →+* K} {g : adjointGroup d4 K}
    (hg : g ∈ hHatE σ' (ng 1)) : ∃ t : Kˣ, g = hShortHom σ' t := by
  obtain ⟨t, rfl⟩ := hg
  exact ⟨t, rfl⟩

end Weyl

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_torus_stable (h : A2Core σ d q) (i : Fin (Tag.rank .G2)) {g : adjointGroup d4 K}
    (hg : g ∈ hHatE σ.toRingHom i) :
    ∃ g' ∈ hHatE σ.toRingHom i,
      (g' : ModGL TwistTag.D4.tag K) = a2Conj σ d (g : ModGL TwistTag.D4.tag K) := by
  have _ := h
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨t, ht, rfl⟩ := a2tor_exists_of_mem_hHatE_zero hg
    refine ⟨_, hg, ?_⟩
    change torusElt d4 K (nd 2) t = a2Conj σ d (torusElt d4 K (nd 2) t)
    rw [a2tor_conj_torusElt]
    congr 1
    exact Units.ext ht.symm
  | ⟨1, _⟩ =>
    obtain ⟨t, rfl⟩ := a2tor_exists_of_mem_hHatE_one hg
    refine ⟨hShortHom σ.toRingHom (Units.map σ.toRingHom.toMonoidHom t),
      a2tor_mem_hHatE_one _, ?_⟩
    rw [hShortHom_apply, hShortHom_apply]
    simp only [Subgroup.coe_mul, a2tor_coe_torusElement]
    rw [a2Conj_mul, a2Conj_mul, a2tor_conj_torusElt, a2tor_conj_torusElt, a2tor_conj_torusElt]

theorem A2Core.a2_weyl_one (h : A2Core σ d q) :
    a2Conj σ d ((nHatE K (ng 1) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((nHatE K (ng 1) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  have _ := h
  rw [nHatE_one]
  simp only [Subgroup.coe_mul, a2tor_coe_weylElement]
  rw [a2Conj_mul, a2Conj_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (a2tor_conj_weylElt_outer (by decide))
    (a2tor_conj_weylElt_outer (by decide))) (a2tor_conj_weylElt_outer (by decide))

theorem A2Core.a2_weyl_zero (h : A2Core σ d q) :
    ∃ t ∈ hHatE σ.toRingHom (ng 0),
      a2Conj σ d ((nHatE K (ng 0) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
        ((nHatE K (ng 0) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) *
          (t : ModGL TwistTag.D4.tag K) := by
  refine ⟨torusElement d4 K (nd 2) d⁻¹, a2tor_mem_hHatE_zero ?_, ?_⟩
  · have hd : σ.toRingHom (d : K) = d := congrArg Units.val h.fixed
    rw [Units.val_inv_eq_inv_val, map_inv₀, hd]
  · rw [nHatE_zero]
    exact a2tor_conj_weylElt_central

end CFSG.GH74.GLS.Stage2.Bender.Thm1
