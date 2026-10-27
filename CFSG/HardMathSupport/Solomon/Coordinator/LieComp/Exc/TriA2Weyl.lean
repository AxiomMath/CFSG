module

public import CFSG.LieType.Steinberg.TwistedD4.Weyl
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Chevalley.BraidWalk
public import CFSG.LieType.Chevalley.RootOps.Instance

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily d4)

noncomputable abbrev w4 (j : Fin 4) (t : Kˣ) : adjointGroup d4 K :=
  CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily d4)) j t

theorem len_d4_roots : (Tag.rootCertificate d4).roots.length = 24 := by decide +kernel

theorem w4_conj_X (j : Fin 4) (a : ℕ) (ha : a < 24) (t : Kˣ) (u : K) :
    w4 j t * 𝕩 (d4Root a) u * (w4 j t)⁻¹ =
      𝕩 (d4Root ((Tag.rootCertificate d4).image a j))
        (((RootOps.signOf d4 a j : ℤ) : K) *
          ((t ^ (∑ k, d4.cartan j k * d4Root ((Tag.rootCertificate d4).image a j) k) : Kˣ) : K) *
            u) := by
  classical
  have hr : IsRoot d4 (d4Root a) := isRoot_d4Root ha
  have himg : (Tag.rootCertificate d4).image a j < 24 := by
    have := rootCertificate_image_lt (τ := d4) (k := a) (by rw [len_d4_roots]; exact ha) j
    rwa [len_d4_roots] at this
  have hr' : IsRoot d4 (d4Root ((Tag.rootCertificate d4).image a j)) := isRoot_d4Root himg
  have e1 := (rootOperatorFamily d4).weylElement_mul_eltElement_mul_inv (K := K) j ⟨d4Root a, hr⟩ u
  have hS : simple d4 j • (⟨d4Root a, hr⟩ : Root d4) =
      ⟨d4Root ((Tag.rootCertificate d4).image a j), hr'⟩ := by
    apply Subtype.ext
    have h1 := rootCertificate_root_image (τ := d4) (k := a) (by rw [len_d4_roots]; exact ha) j
    have h2 := simple_smul (τ := d4) j (d4Root a)
    have h3 := coe_smul_root (simple d4 j) (⟨d4Root a, hr⟩ : Root d4)
    exact h3.trans (h2.trans h1.symm)
  rw [hS] at e1
  have e2 := (rootOperatorFamily d4).torusElement_mul_eltElement_mul_inv (K := K) j t
    ⟨d4Root ((Tag.rootCertificate d4).image a j), hr'⟩
    (((rootOperatorFamily d4).sign j ⟨d4Root a, hr⟩ : ℤ) * u)
  have e3 : w4 j t = torusElement d4 K j t * CFSG.LieType.Chevalley.weylElement d4 K j :=
    weylElement_xPar (F := rootOperatorFamily d4) j t
  have e4 : (rootOperatorFamily d4).sign j ⟨d4Root a, hr⟩ = RootOps.signOf d4 a j := by
    have := RootOps.rootPos_eq (τ := d4) (α := ⟨d4Root a, hr⟩) (a := a)
      (by rw [len_d4_roots]; exact ha) rfl
    exact congrArg (fun p => RootOps.signOf d4 p j) this
  rw [e3, xPar_of_isRoot hr, xPar_of_isRoot hr']
  have e5 : torusElement d4 K j t * CFSG.LieType.Chevalley.weylElement d4 K j *
        (rootOperatorFamily d4).eltElement ⟨d4Root a, hr⟩ u *
        (torusElement d4 K j t * CFSG.LieType.Chevalley.weylElement d4 K j)⁻¹ =
      torusElement d4 K j t * (CFSG.LieType.Chevalley.weylElement d4 K j *
        (rootOperatorFamily d4).eltElement ⟨d4Root a, hr⟩ u *
        (CFSG.LieType.Chevalley.weylElement d4 K j)⁻¹) * (torusElement d4 K j t)⁻¹ := by group
  rw [e5, e1, e2, e4]
  congr 1
  ring

theorem w4_inv (j : Fin 4) (t : Kˣ) : (w4 j t)⁻¹ = w4 j (-t) := by
  have hne : (-(t⁻¹ : Kˣ) : Kˣ) = (-t)⁻¹ := by
    rw [inv_neg]
  unfold w4 CFSG.LieType.Steinberg.weylElement
  simp only [mul_inv_rev, xPar_neg, Units.val_neg, ← hne, neg_neg, mul_assoc]

theorem w4_one (j : Fin 4) : w4 j (1 : Kˣ) = CFSG.LieType.Chevalley.weylElement d4 K j := by
  have h := weylElement_xPar (F := rootOperatorFamily d4) (K := K) j (1 : Kˣ)
  have h1 := torusElement_one_eq (τ := d4) (K := K) j
  rw [h1, one_mul] at h
  exact h

theorem conj_triple {G : Type*} [Group G] (g a b c : G) :
    g * (a * b * c) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by
  group

theorem w4_conj_X' (j : Fin 4) (a a' : ℕ) (s e : ℤ) (ha : a < 24) (t : Kˣ) (u : K)
    (h1 : (Tag.rootCertificate d4).image a j = a') (h2 : RootOps.signOf d4 a j = s)
    (h3 : ∑ k, d4.cartan j k * d4Root a' k = e) :
    w4 j t * 𝕩 (d4Root a) u * (w4 j t)⁻¹ = 𝕩 (d4Root a') ((s : K) * (t : K) ^ e * u) := by
  have := w4_conj_X j a ha t u
  rw [h1, h2, h3] at this
  rw [this]
  congr 2
  rw [Units.val_zpow_eq_zpow_val]

theorem w4c_0_0 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 0) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 4) (-(((t : K) ^ 2)⁻¹ * u)) := by
  rw [w4_conj_X' 0 0 4 (-1) (-2) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_1 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 1) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 1) (u) := by
  rw [w4_conj_X' 0 1 1 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_2 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 2) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 5) (-((t : K) * u)) := by
  rw [w4_conj_X' 0 2 5 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_3 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 3) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 3) (u) := by
  rw [w4_conj_X' 0 3 3 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_4 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 4) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 0) (-((t : K) ^ 2 * u)) := by
  rw [w4_conj_X' 0 4 0 (-1) (2) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_5 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 5) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 2) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 0 5 2 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_6 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 6) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 6) (u) := by
  rw [w4_conj_X' 0 6 6 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_7 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 7) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 12) ((t : K) * u) := by
  rw [w4_conj_X' 0 7 12 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_8 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 8) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 11) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 0 8 11 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_9 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 9) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 13) (-((t : K) * u)) := by
  rw [w4_conj_X' 0 9 13 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_10 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 10) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 10) (u) := by
  rw [w4_conj_X' 0 10 10 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_11 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 11) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 8) ((t : K) * u) := by
  rw [w4_conj_X' 0 11 8 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_12 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 12) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 7) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 0 12 7 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_13 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 13) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 9) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 0 13 9 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_14 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 14) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 17) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 0 14 17 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_15 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 15) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 19) ((t : K) * u) := by
  rw [w4_conj_X' 0 15 19 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_16 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 16) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 18) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 0 16 18 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_17 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 17) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 14) (-((t : K) * u)) := by
  rw [w4_conj_X' 0 17 14 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_18 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 18) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 16) ((t : K) * u) := by
  rw [w4_conj_X' 0 18 16 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_19 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 19) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 15) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 0 19 15 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_20 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 20) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 21) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 0 20 21 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_0_21 (t : Kˣ) (u : K) :
    w4 0 t * 𝕩 (d4Root 21) u * (w4 0 t)⁻¹ = 𝕩 (d4Root 20) (-((t : K) * u)) := by
  rw [w4_conj_X' 0 21 20 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_0 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 0) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 0) (u) := by
  rw [w4_conj_X' 1 0 0 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_1 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 1) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 6) (-(((t : K) ^ 2)⁻¹ * u)) := by
  rw [w4_conj_X' 1 1 6 (-1) (-2) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_2 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 2) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 7) (-((t : K) * u)) := by
  rw [w4_conj_X' 1 2 7 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_3 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 3) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 3) (u) := by
  rw [w4_conj_X' 1 3 3 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_4 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 4) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 4) (u) := by
  rw [w4_conj_X' 1 4 4 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_5 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 5) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 12) ((t : K) * u) := by
  rw [w4_conj_X' 1 5 12 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_6 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 6) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 1) (-((t : K) ^ 2 * u)) := by
  rw [w4_conj_X' 1 6 1 (-1) (2) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_7 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 7) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 2) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 1 7 2 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_8 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 8) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 14) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 1 8 14 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_9 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 9) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 15) (-((t : K) * u)) := by
  rw [w4_conj_X' 1 9 15 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_10 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 10) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 10) (u) := by
  rw [w4_conj_X' 1 10 10 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_11 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 11) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 17) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 1 11 17 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_12 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 12) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 5) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 1 12 5 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_13 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 13) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 19) ((t : K) * u) := by
  rw [w4_conj_X' 1 13 19 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_14 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 14) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 8) ((t : K) * u) := by
  rw [w4_conj_X' 1 14 8 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_15 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 15) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 9) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 1 15 9 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_16 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 16) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 20) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 1 16 20 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_17 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 17) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 11) (-((t : K) * u)) := by
  rw [w4_conj_X' 1 17 11 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_18 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 18) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 21) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 1 18 21 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_19 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 19) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 13) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 1 19 13 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_20 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 20) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 16) ((t : K) * u) := by
  rw [w4_conj_X' 1 20 16 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_1_21 (t : Kˣ) (u : K) :
    w4 1 t * 𝕩 (d4Root 21) u * (w4 1 t)⁻¹ = 𝕩 (d4Root 18) (-((t : K) * u)) := by
  rw [w4_conj_X' 1 21 18 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_0 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 0) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 5) ((t : K) * u) := by
  rw [w4_conj_X' 2 0 5 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_1 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 1) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 7) ((t : K) * u) := by
  rw [w4_conj_X' 2 1 7 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_3 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 3) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 9) (-((t : K) * u)) := by
  rw [w4_conj_X' 2 3 9 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_4 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 4) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 11) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 2 4 11 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_5 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 5) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 0) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 2 5 0 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_6 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 6) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 14) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 2 6 14 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_7 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 7) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 1) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 2 7 1 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_9 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 9) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 3) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 2 9 3 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_10 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 10) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 16) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 2 10 16 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_11 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 11) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 4) (-((t : K) * u)) := by
  rw [w4_conj_X' 2 11 4 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_12 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 12) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 12) (u) := by
  rw [w4_conj_X' 2 12 12 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_13 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 13) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 13) (u) := by
  rw [w4_conj_X' 2 13 13 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_14 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 14) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 6) (-((t : K) * u)) := by
  rw [w4_conj_X' 2 14 6 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_15 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 15) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 15) (u) := by
  rw [w4_conj_X' 2 15 15 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_16 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 16) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 10) ((t : K) * u) := by
  rw [w4_conj_X' 2 16 10 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_17 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 17) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 17) (u) := by
  rw [w4_conj_X' 2 17 17 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_18 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 18) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 18) (u) := by
  rw [w4_conj_X' 2 18 18 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_2_20 (t : Kˣ) (u : K) :
    w4 2 t * 𝕩 (d4Root 20) u * (w4 2 t)⁻¹ = 𝕩 (d4Root 20) (u) := by
  rw [w4_conj_X' 2 20 20 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_0 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 0) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 0) (u) := by
  rw [w4_conj_X' 3 0 0 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_1 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 1) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 1) (u) := by
  rw [w4_conj_X' 3 1 1 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_2 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 2) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 9) ((t : K) * u) := by
  rw [w4_conj_X' 3 2 9 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_3 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 3) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 10) (-(((t : K) ^ 2)⁻¹ * u)) := by
  rw [w4_conj_X' 3 3 10 (-1) (-2) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_4 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 4) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 4) (u) := by
  rw [w4_conj_X' 3 4 4 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_5 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 5) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 13) ((t : K) * u) := by
  rw [w4_conj_X' 3 5 13 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_6 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 6) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 6) (u) := by
  rw [w4_conj_X' 3 6 6 (1) (0) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_7 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 7) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 15) ((t : K) * u) := by
  rw [w4_conj_X' 3 7 15 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_8 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 8) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 16) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 3 8 16 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_9 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 9) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 2) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 3 9 2 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_10 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 10) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 3) (-((t : K) ^ 2 * u)) := by
  rw [w4_conj_X' 3 10 3 (-1) (2) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_11 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 11) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 18) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 3 11 18 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_12 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 12) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 19) ((t : K) * u) := by
  rw [w4_conj_X' 3 12 19 (1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_13 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 13) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 5) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 3 13 5 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_14 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 14) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 20) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 3 14 20 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_15 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 15) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 7) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 3 15 7 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_16 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 16) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 8) (-((t : K) * u)) := by
  rw [w4_conj_X' 3 16 8 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_17 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 17) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 21) ((t : K)⁻¹ * u) := by
  rw [w4_conj_X' 3 17 21 (1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_18 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 18) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 11) (-((t : K) * u)) := by
  rw [w4_conj_X' 3 18 11 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_19 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 19) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 12) (-((t : K)⁻¹ * u)) := by
  rw [w4_conj_X' 3 19 12 (-1) (-1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_20 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 20) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 14) (-((t : K) * u)) := by
  rw [w4_conj_X' 3 20 14 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

theorem w4c_3_21 (t : Kˣ) (u : K) :
    w4 3 t * 𝕩 (d4Root 21) u * (w4 3 t)⁻¹ = 𝕩 (d4Root 17) (-((t : K) * u)) := by
  rw [w4_conj_X' 3 21 17 (-1) (1) (by decide) t u (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  norm_num

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
