module

public import CFSG.ClassicalInvolution.Phan.PhanS9O2Fix
public import CFSG.ClassicalInvolution.Phan.PhanH8Gen
import CFSG.ClassicalInvolution.Phan.PhanS9O3Num
import CFSG.ClassicalInvolution.Phan.PhanP17Ell

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
open CFSG.Assembly.LowTwoRank (StatedSp)

section Plane

variable {F : Type} [Field F]

@[expose] noncomputable def plMap : (F × F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Unit → F) where
  toFun p := mk7 p.1 0 0 p.1 0 0 p.2
  map_add' p q := by
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · simp
  map_smul' c p := by
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · simp

theorem plMap_apply (p : F × F) : plMap p = mk7 p.1 0 0 p.1 0 0 p.2 := rfl

theorem plMap_injective : Function.Injective (plMap (F := F)) := by
  intro p q h
  have e1 := congrFun h (.inl 0)
  have e2 := congrFun h (.inr (.inr ()))
  simp only [plMap_apply, mk7_x0, mk7_z] at e1 e2
  exact Prod.ext e1 e2

noncomputable abbrev plSpan (F : Type) [Field F] : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Unit → F) :=
  LinearMap.range plMap

noncomputable abbrev plPerp (F : Type) [Field F] : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Unit → F) :=
  LinearMap.BilinForm.orthogonal (quadOdd 3 F).polarBilin (plSpan F)

theorem mem_plPerp_iff (x : Fin 3 ⊕ Fin 3 ⊕ Unit → F) :
    x ∈ plPerp F ↔ ∀ s z : F, polar (quadOdd 3 F) (mk7 s 0 0 s 0 0 z) x = 0 := by
  rw [plPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h s z
    have h' := h (plMap (s, z)) ⟨(s, z), rfl⟩
    rw [QuadraticMap.polarBilin_apply_apply] at h'
    exact h'
  · rintro h _ ⟨⟨s, z⟩, rfl⟩
    rw [QuadraticMap.polarBilin_apply_apply]
    exact h s z

theorem plSpan_regular (h2 : (2 : F) ≠ 0) :
    ((quadOdd 3 F).restrict (plSpan F)).Nondegenerate := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  refine PhanP.nondegenerate_restrict_of_forall (plSpan F) ?_
  rintro _ ⟨⟨s, z⟩, rfl⟩ hx
  have h1 := hx (plMap (1, 0)) ⟨(1, 0), rfl⟩
  have h3 := hx (plMap (0, 1)) ⟨(0, 1), rfl⟩
  simp only [plMap_apply, polar_mk7] at h1 h3
  have hs : s = 0 := by
    have : (2 : F) * s = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hz : z = 0 := by
    have : (2 : F) * z = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [show ((s, z) : F × F) = 0 from Prod.ext hs hz, map_zero]

theorem kappa_mem_plPerp (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) : kappa v ∈ plPerp F := by
  rw [mem_plPerp_iff]
  intro s z
  exact polar_pP_kappa s z v

theorem finrank_plSpan : Module.finrank F (plSpan F) = 2 := by
  rw [plSpan, LinearMap.finrank_range_of_inj plMap_injective]
  simp

theorem finrank_plPerp (h2 : (2 : F) ≠ 0) : Module.finrank F (plPerp F) = 5 := by
  rw [plPerp, LinearMap.BilinForm.finrank_orthogonal (nondegenerate_polarBilin_quadOdd 3 F h2),
    finrank_plSpan]
  simp [Module.finrank_fintype_fun_eq_card]

theorem kappa_codRestrict_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (kappa.codRestrict (plPerp F) kappa_mem_plPerp) :=
  fun _ _ h => kappa_injective h2 (congrArg Subtype.val h)

noncomputable def plKappa (h2 : (2 : F) ≠ 0) :
    (Fin 2 ⊕ Fin 2 ⊕ Unit → F) ≃ₗ[F] plPerp F :=
  LinearMap.linearEquivOfInjective (kappa.codRestrict (plPerp F) kappa_mem_plPerp)
    (kappa_codRestrict_injective h2)
    (by rw [finrank_plPerp h2]; simp [Module.finrank_fintype_fun_eq_card])

theorem plKappa_coe (h2 : (2 : F) ≠ 0) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    ((plKappa h2 v : plPerp F) : Fin 3 ⊕ Fin 3 ⊕ Unit → F) = kappa v := by
  simp only [plKappa, LinearMap.linearEquivOfInjective_apply, LinearMap.codRestrict_apply]

theorem plKappa_quad (h2 : (2 : F) ≠ 0) (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    ((quadOdd 3 F).restrict (plPerp F)) (plKappa h2 v) = (-1 : F) * quadOdd 2 F v := by
  rw [QuadraticMap.restrict_apply, plKappa_coe, quad_kappa h2, neg_one_mul]

theorem card_fixSub_plSpan_le [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (fixSub (quadOdd 3 F) (plSpan F : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F))) ≤
      Nat.card (StatedSp 2 F) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hQ : (quadOdd 3 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 3 F h2)
  obtain ⟨ν, hν⟩ := exists_nonsquare_of_two_ne_zero h2
  have : Nontrivial (plPerp F) := (plKappa h2).injective.nontrivial
  have hreg := plSpan_regular h2
  have h1 : Nat.card (fixSub (quadOdd 3 F) (plSpan F : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F))) ≤
      Nat.card (spinGroup ((quadOdd 3 F).restrict (plPerp F))) := card_fixSub_le hQ hreg
  have hQ' : ((quadOdd 3 F).restrict (plPerp F)).Nondegenerate :=
    hQ.nondegenerate_restrict_orthogonal hreg
  obtain ⟨va, hva⟩ : ∃ v : Fin 2 ⊕ Fin 2 ⊕ Unit → F, quadOdd 2 F v = -1 :=
    ⟨mk5 (-1) 0 1 0 0, by rw [quad5_mk5]; ring⟩
  obtain ⟨vb, hvb⟩ : ∃ v : Fin 2 ⊕ Fin 2 ⊕ Unit → F, quadOdd 2 F v = -ν :=
    ⟨mk5 (-ν) 0 1 0 0, by rw [quad5_mk5]; ring⟩
  have h2' := two_mul_card_spinGroup_le hQ' hν (a := plKappa h2 va) (b := plKappa h2 vb)
    (by rw [plKappa_quad, hva]; ring) (by rw [plKappa_quad, hvb]; ring)
  have h3 := card_orthogonalGroup_le_of_similar (quadOdd 2 F)
    ((quadOdd 3 F).restrict (plPerp F)) (plKappa h2) (c := -1) (neg_ne_zero.mpr one_ne_zero)
    (plKappa_quad h2)
  have h4 := card_orthogonalGroup_quadOdd_two h2
  omega

end Plane

section Final

variable {F : Type} [Field F] [Finite F]

theorem fixP_le_theta_of_two_ne_zero (h2 : (2 : F) ≠ 0) (Dθ : ThetaData F h2)
    (g : spinGroup (quadOdd 3 F))
    (hg : ∀ s z : F, spinAction (quadOdd 3 F) g (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z) :
    g ∈ Dθ.θ.range := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hQ : (quadOdd 3 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 3 F h2)
  have := finite_spinGroup hQ
  have hle : Dθ.θ.range ≤
      fixSub (quadOdd 3 F) (plSpan F : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F)) := by
    rintro _ ⟨t, rfl⟩
    refine mem_fixSub.2 ?_
    rintro x ⟨⟨s, z⟩, rfl⟩
    exact theta_fix_P Dθ.fix t s z
  have hcard : Nat.card (fixSub (quadOdd 3 F) (plSpan F : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F))) ≤
      Nat.card Dθ.θ.range := by
    rw [card_range_eq_of_injective Dθ.θ_inj]
    exact card_fixSub_plSpan_le h2
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hmem : g ∈ fixSub (quadOdd 3 F) (plSpan F : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F)) := by
    refine mem_fixSub.2 ?_
    rintro x ⟨⟨s, z⟩, rfl⟩
    exact hg s z
  rw [heq]
  exact hmem

theorem fixP_le_theta (h2 : (2 : F) ≠ 0) (hn1 : ¬ IsSquare (-1 : F)) (Dθ : ThetaData F h2)
    (g : spinGroup (quadOdd 3 F))
    (hg : ∀ s z : F, spinAction (quadOdd 3 F) g (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z) :
    g ∈ Dθ.θ.range := by
  have _ := hn1
  exact fixP_le_theta_of_two_ne_zero h2 Dθ g hg

end Final

end CFSG.ClassicalInvolution.PhanB3.S
