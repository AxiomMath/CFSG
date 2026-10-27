module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Duals
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix


@[expose] noncomputable def baseFlag : Flags Vec3 :=
  ⟨(⟨Pi.single 0 1, by decide⟩, ⟨LinearMap.proj 2, fun h => by
      have := LinearMap.congr_fun h (Pi.single 2 1)
      simp at this⟩), by simp⟩

theorem baseFlag_fst : (baseFlag.1.1 : Vec3) = Pi.single 0 1 := rfl

theorem baseFlag_snd : (baseFlag.1.2 : Module.Dual (ZMod 2) Vec3) = LinearMap.proj 2 := rfl

@[expose] noncomputable def flagActG (g : GL32) (f : Flags Vec3) : Flags Vec3 := flagAct (repV g) f

theorem flagActG_fst (g : GL32) (f : Flags Vec3) :
    ((flagActG g f).1.1 : Vec3) = repV g (f.1.1 : Vec3) := rfl

theorem flagActG_snd (g : GL32) (f : Flags Vec3) :
    ((flagActG g f).1.2 : Module.Dual (ZMod 2) Vec3) =
      (f.1.2 : Module.Dual (ZMod 2) Vec3) ∘ₗ ((repV g).symm : Vec3 →ₗ[ZMod 2] Vec3) := rfl

theorem flagActG_mul (g h : GL32) (f : Flags Vec3) :
    flagActG (g * h) f = flagActG g (flagActG h f) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [flagActG_fst, flagActG_fst, flagActG_fst, map_mul]
    rfl
  · apply Subtype.ext
    rw [flagActG_snd, flagActG_snd, flagActG_snd, map_mul]
    rfl

theorem flagActG_one (f : Flags Vec3) : flagActG 1 f = f := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [flagActG_fst, map_one]
    rfl
  · apply Subtype.ext
    rw [flagActG_snd, map_one]
    rfl


theorem flag_complete : ∀ p0 p1 p2 w0 w1 w2 : ZMod 2,
    (p0 ≠ 0 ∨ p1 ≠ 0 ∨ p2 ≠ 0) → (w0 ≠ 0 ∨ w1 ≠ 0 ∨ w2 ≠ 0) →
    p0 * w0 + p1 * w1 + p2 * w2 = 0 →
    ∃ q0 q1 q2 r0 r1 r2 : ZMod 2, q0 * w0 + q1 * w1 + q2 * w2 = 0 ∧
      r0 * w0 + r1 * w1 + r2 * w2 = 1 ∧
      p0 * q1 * r2 - p0 * r1 * q2 - q0 * p1 * r2 + q0 * r1 * p2 + r0 * p1 * q2 -
        r0 * q1 * p2 = 1 := by
  decide +kernel

theorem dual_eq_zero_of_coord (φ : Module.Dual (ZMod 2) Vec3) (h : ∀ i, φ (Pi.single i 1) = 0) :
    φ = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [dual_apply_eq_sum]
  simp [h]

theorem flagActG_transitive (f : Flags Vec3) : ∃ g : GL32, flagActG g baseFlag = f := by
  obtain ⟨⟨⟨p, hp⟩, ⟨φ, hφ⟩⟩, hf⟩ := f
  have hf' : φ p = 0 := hf
  have hp' : p 0 ≠ 0 ∨ p 1 ≠ 0 ∨ p 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    funext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  have hφ' : φ (Pi.single 0 1) ≠ 0 ∨ φ (Pi.single 1 1) ≠ 0 ∨ φ (Pi.single 2 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    exact dual_eq_zero_of_coord φ (fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])
  have hsum : p 0 * φ (Pi.single 0 1) + p 1 * φ (Pi.single 1 1) + p 2 * φ (Pi.single 2 1) = 0 := by
    have := dual_apply_eq_sum φ p
    rw [hf', Fin.sum_univ_three] at this
    exact this.symm
  obtain ⟨q0, q1, q2, r0, r1, r2, hq, hr, hdet⟩ := flag_complete _ _ _ _ _ _ hp' hφ' hsum
  let M : Mat3 := !![p 0, q0, r0; p 1, q1, r1; p 2, q2, r2]
  have hM : IsUnit M.det := by
    have h1 : M.det = 1 := by
      rw [Matrix.det_fin_three]
      simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.head_fin_const]
      linear_combination hdet
    rw [h1]
    exact isUnit_one
  let g : GL32 := Matrix.GeneralLinearGroup.mk'' M hM
  have hg : (g : Mat3) = M := rfl
  have hφg : φ ∘ₗ (repV g : Vec3 →ₗ[ZMod 2] Vec3) = LinearMap.proj 2 := by
    refine LinearMap.ext fun u => ?_
    change φ ((g : Mat3) *ᵥ u) = u 2
    rw [dual_apply_eq_sum, hg]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, M, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const]
    linear_combination u 0 * hsum + u 1 * hq + u 2 * hr
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [flagActG_fst, baseFlag_fst, repV_apply, hg]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, M]
  · apply Subtype.ext
    rw [flagActG_snd, baseFlag_snd]
    refine LinearMap.ext fun v => ?_
    have hv : v = repV g ((repV g).symm v) := ((repV g).apply_symm_apply v).symm
    change (LinearMap.proj 2 : Module.Dual (ZMod 2) Vec3) ((repV g).symm v) = φ v
    rw [← LinearMap.congr_fun hφg ((repV g).symm v)]
    change φ (repV g ((repV g).symm v)) = φ v
    rw [(repV g).apply_symm_apply]


theorem eq_one_of_isUnit_zmod_two {x : ZMod 2} (h : IsUnit x) : x = 1 := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
  · exact absurd h not_isUnit_zero
  · rfl

theorem mem_sylowT_of_flagActG {g : GL32} (h : flagActG g baseFlag = baseFlag) : g ∈ sylowT := by
  have h1 : ((flagActG g baseFlag).1.1 : Vec3) = (baseFlag.1.1 : Vec3) :=
    congrArg (fun f : Flags Vec3 => ((f.1.1 : Points Vec3) : Vec3)) h
  have h2 : ((flagActG g baseFlag).1.2 : Module.Dual (ZMod 2) Vec3) =
      (baseFlag.1.2 : Module.Dual (ZMod 2) Vec3) :=
    congrArg (fun f : Flags Vec3 => ((f.1.2 : Points (Module.Dual (ZMod 2) Vec3)) :
      Module.Dual (ZMod 2) Vec3)) h
  rw [flagActG_fst, baseFlag_fst] at h1
  rw [flagActG_snd, baseFlag_snd] at h2
  have hcol : ∀ i, (g : Mat3) i 0 = (Pi.single 0 1 : Vec3) i := by
    intro i
    have := congrFun h1 i
    simpa [repV_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Fin.sum_univ_three] using this
  have hrow : ∀ j, (g : Mat3) 2 j = (Pi.single 2 1 : Vec3) j := by
    intro j
    have := LinearMap.congr_fun h2 (repV g (Pi.single j 1))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_proj, Function.eval,
      LinearEquiv.symm_apply_apply] at this
    have h3 : (repV g (Pi.single j 1) : Vec3) 2 = (g : Mat3) 2 j := by
      simp [repV_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3] at this
    rw [← this]
    simp [Pi.single_apply, eq_comm]
  have c0 : (g : Mat3) 0 0 = 1 := by simpa using hcol 0
  have c1 : (g : Mat3) 1 0 = 0 := by simpa using hcol 1
  have c2 : (g : Mat3) 2 0 = 0 := by simpa using hcol 2
  have r1 : (g : Mat3) 2 1 = 0 := by simpa using hrow 1
  have r2 : (g : Mat3) 2 2 = 1 := by simpa using hrow 2
  have hdet : (g : Mat3).det = 1 := eq_one_of_isUnit_zmod_two (Matrix.isUnits_det_units g)
  rw [Matrix.det_fin_three, c0, c1, c2, r1, r2] at hdet
  have d11 : (g : Mat3) 1 1 = 1 := by simpa using hdet
  refine ⟨(g : Mat3) 0 1, (g : Mat3) 0 2, (g : Mat3) 1 2, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [unitriGL, unitri, c0, c1, c2, r1, r2, d11]


theorem finite_dual_vec3 : Finite (Module.Dual (ZMod 2) Vec3) :=
  Module.finite_of_finite (ZMod 2)

theorem exists_flagMap {E : Type*} [AddCommMonoid E] [Module (ZMod 2) E] [Finite E]
    (ρ : GL32 →* (E ≃ₗ[ZMod 2] E)) (hρ : IsIrrRep ρ) :
    ∃ π : (Flags Vec3 → ZMod 2) →ₗ[ZMod 2] E,
      IsEquivAct (fun (g : GL32) (z : Flags Vec3 → ZMod 2) => flagPermAct (repV g) z)
        (fun g x => ρ g x) π ∧ π ≠ 0 := by
  classical
  have : Nontrivial E := hρ.1
  obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
  have hbot : (⊤ : Submodule (ZMod 2) E) ≠ ⊥ := fun h => hx0 (by
    have : x0 ∈ (⊥ : Submodule (ZMod 2) E) := h ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨e, -, he0, hefix⟩ := exists_ne_zero_fixed ρ sylowT isPGroup_sylowT ⊤ hbot
    (fun g _ x _ => Submodule.mem_top)
  have hT : ∀ g : GL32, flagActG g baseFlag = baseFlag → ρ g e = e := fun g hg =>
    hefix g (mem_sylowT_of_flagActG hg)
  have := finite_dual_vec3
  let _ : Fintype (Module.Dual (ZMod 2) Vec3) := Fintype.ofFinite _
  choose s hs using flagActG_transitive
  have hkey : ∀ (g : GL32) (f : Flags Vec3), ρ (s (flagActG g f)) e = ρ g (ρ (s f) e) := by
    intro g f
    have hh : flagActG ((s (flagActG g f))⁻¹ * (g * s f)) baseFlag = baseFlag := by
      have e1 : flagActG g (flagActG (s f) baseFlag) = flagActG (s (flagActG g f)) baseFlag := by
        rw [hs f, hs (flagActG g f)]
      rw [flagActG_mul, flagActG_mul, e1, ← flagActG_mul, inv_mul_cancel, flagActG_one]
    have h3 := hT _ hh
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_inv] at h3
    calc ρ (s (flagActG g f)) e
        = ρ (s (flagActG g f)) ((ρ (s (flagActG g f)))⁻¹ (ρ g (ρ (s f) e))) := by rw [h3]
      _ = ρ g (ρ (s f) e) := by
        change (ρ (s (flagActG g f)) * (ρ (s (flagActG g f)))⁻¹) (ρ g (ρ (s f) e)) = _
        rw [mul_inv_cancel]
        rfl
  refine ⟨Fintype.linearCombination (ZMod 2) (fun f => ρ (s f) e), fun g z => ?_, ?_⟩
  · change Fintype.linearCombination (ZMod 2) (fun f => ρ (s f) e) (flagPermAct (repV g) z) =
      ρ g (Fintype.linearCombination (ZMod 2) (fun f => ρ (s f) e) z)
    simp only [Fintype.linearCombination_apply]
    rw [map_sum, ← Equiv.sum_comp (flagPerm (repV g))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul]
    change z (flagAct (repV g).symm (flagAct (repV g) f)) • ρ (s (flagActG g f)) e = _
    rw [flagAct_symm_flagAct, hkey]
  · intro h0
    have h1 := LinearMap.congr_fun h0 (Pi.single baseFlag 1)
    rw [Fintype.linearCombination_apply_single, one_smul, LinearMap.zero_apply,
      hT _ (hs baseFlag)] at h1
    exact he0 h1

end CFSG.QuasithinUnique.Setup.Family
