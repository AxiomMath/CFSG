module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.LieType.Chevalley.AllRootWeylSignsDefs
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.RootOps.Groups
public import CFSG.LieType.Chevalley.BraidWalk

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.RankTwo
open scoped MatrixGroups commutatorElement

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

local notation "F2" => rootOperatorFamily Tag.G2

section Pure

variable {K : Type} [Field K]

theorem diag_eq_wSL_prod (d : Matrix.SpecialLinearGroup (Fin (2 + 1)) K)
    (hd : ∀ i j : Fin 3, i ≠ j → (d : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ∃ t s : Kˣ, d = (wSL (show (0 : Fin 3) ≠ 1 by decide) (t : K) *
        wSL (show (0 : Fin 3) ≠ 1 by decide) (-1)) *
      (wSL (show (1 : Fin 3) ≠ 2 by decide) (s : K) *
        wSL (show (1 : Fin 3) ≠ 2 by decide) (-1)) := by
  have hdiag : (d : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i => (d : Matrix (Fin 3) (Fin 3) K) i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [hd i j h, Matrix.diagonal_apply_ne _ h]
  have hdet : (d : Matrix (Fin 3) (Fin 3) K) 0 0 * (d : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (d : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have := d.2
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at this
    exact this
  have ha : (d : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hb : (d : Matrix (Fin 3) (Fin 3) K) 0 0 * (d : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  refine ⟨Units.mk0 _ ha, Units.mk0 _ hb, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Units.val_mk0, Units.val_mk0,
    coe_wSL_mul_neg_one _ ha, coe_wSL_mul_neg_one _ hb, Matrix.diagonal_mul_diagonal, hdiag]
  ext i j
  by_cases h : i = j
  · subst h
    fin_cases i
    · simp
    · simp
      field_simp
    · simp
      have hc : (d : Matrix (Fin 3) (Fin 3) K) 2 2 =
          ((d : Matrix (Fin 3) (Fin 3) K) 0 0 * (d : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ :=
        eq_inv_of_mul_eq_one_right hdet
      rw [hc]
      exact mul_inv_rev _ _
  · simp [Matrix.diagonal_apply_ne _ h]

end Pure

section Basic

variable {K : Type} [Field K]

theorem root_isRoot (g : ℕ) (hg : g < 12) : IsRoot .G2 (g2CommRoot g) :=
  CFSG.LieType.Chevalley.RootWalk.isRoot_rootCertificate_root
    (τ := .G2) (k := g) (by rw [g2CommRoot_length]; exact hg)

theorem n1_conj_mem_torus (d : ↥(adjointGroup .G2 K))
    (hd : (d : ModGL .G2 K) ∈ torusGroup .G2 K) :
    ((CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)) * d *
        (CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)))⁻¹ :
        ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ torusGroup .G2 K := by
  have hn := weylElt_mem_normalizer_torus (τ := .G2) K (⟨1, by decide⟩ : Fin (Tag.rank .G2)) 1
  exact (Subgroup.mem_normalizer_iff.1 hn (d : ModGL .G2 K)).1 hd

end Basic

section Torus


variable {K : Type} [Field K]

theorem n_conj_pos (i : Fin (Tag.rank .G2)) (g : ℕ) (hg : g < 12) (c : K) :
    CFSG.LieType.Chevalley.weylElement .G2 K i * xPar F2 (g2CommRoot g) c *
        (CFSG.LieType.Chevalley.weylElement .G2 K i)⁻¹ =
      xPar F2 (g2CommRoot ((Tag.rootCertificate .G2).image g i))
        ((CFSG.LieType.Chevalley.RootOps.signOf .G2 g i : K) * c) := by
  have hlen : g < (Tag.rootCertificate .G2).roots.length := by
    rw [g2CommRoot_length]
    exact hg
  have hr := root_isRoot g hg
  have himg := CFSG.LieType.Chevalley.RootWalk.rootCertificate_image_lt (τ := .G2) hlen i
  have hr' : IsRoot .G2 (g2CommRoot ((Tag.rootCertificate .G2).image g i)) :=
    CFSG.LieType.Chevalley.RootWalk.isRoot_rootCertificate_root himg
  set α : Root .G2 := ⟨g2CommRoot g, hr⟩ with hα
  have h1 := (rootOperatorFamily .G2).weylElement_mul_eltElement_mul_inv (K := K) i α c
  have hsign : (rootOperatorFamily .G2).sign i α =
      CFSG.LieType.Chevalley.RootOps.signOf .G2 g i := by
    rw [sign_rootOperatorFamily, CFSG.LieType.Chevalley.RootOps.rootPos_eq hlen rfl]
  have hs : simple .G2 i • α = ⟨g2CommRoot ((Tag.rootCertificate .G2).image g i), hr'⟩ := by
    apply Subtype.ext
    show simple .G2 i • g2CommRoot g = _
    rw [simple_smul]
    exact (CFSG.LieType.Chevalley.RootWalk.rootCertificate_root_image hlen i).symm
  rw [xPar_of_isRoot hr, xPar_of_isRoot hr', ← hsign]
  rw [← hs]
  exact h1

theorem n1_conj_e0 (c : K) :
    CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)) *
        xPar F2 (g2CommRoot 0) c *
        (CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)))⁻¹ =
      xPar F2 (g2CommRoot 3) c := by
  rw [n_conj_pos ⟨1, by decide⟩ 0 (by norm_num) c]
  have h : (Tag.rootCertificate .G2).image 0 (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = 3 := by
    decide +kernel
  have hs : CFSG.LieType.Chevalley.RootOps.signOf .G2 0 (⟨1, by decide⟩ : Fin (Tag.rank .G2)) =
      1 := by decide +kernel
  rw [h, hs]
  simp

theorem n1_conj_ne0 (c : K) :
    CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)) *
        xPar F2 (g2CommRoot 2) c *
        (CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)))⁻¹ =
      xPar F2 (g2CommRoot 6) c := by
  rw [n_conj_pos ⟨1, by decide⟩ 2 (by norm_num) c]
  have h : (Tag.rootCertificate .G2).image 2 (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = 6 := by
    decide +kernel
  have hs : CFSG.LieType.Chevalley.RootOps.signOf .G2 2 (⟨1, by decide⟩ : Fin (Tag.rank .G2)) =
      1 := by decide +kernel
  rw [h, hs]
  simp

section Phi2

variable (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* ↥(adjointGroup .G2 K))
  (hφ : ∀ γ ∈ RA2, ∀ c : K, φ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c)

include hφ

theorem phi_T12 (c : K) :
    φ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) =
      xPar F2 (g2CommRoot 3) c := by
  rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (γ := ![0, 1]) (show (1 : Fin 3) ≠ 2 by decide)
    (by decide) c, hφ _ (mem_rootsA2.2 (Or.inr (Or.inl rfl))) c]
  have : a2pos ((0 : ℤ), (1 : ℤ)) = 3 := by decide
  simp [a2y, this]

theorem phi_T21 (c : K) :
    φ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) =
      xPar F2 (g2CommRoot 6) c := by
  rw [← CFSG.LieType.Steinberg.SL.x_eq (m := 2) (γ := ![0, -1]) (show (2 : Fin 3) ≠ 1 by decide)
    (by decide) c, hφ _ (mem_rootsA2.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) c]
  have : a2pos ((0 : ℤ), (-1 : ℤ)) = 6 := by decide
  simp [a2y, this]

theorem phi_wSL12 (t : K) :
    φ (wSL (show (1 : Fin 3) ≠ 2 by decide) t) =
      CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)) *
        φ (wSL (show (0 : Fin 3) ≠ 1 by decide) t) *
        (CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)))⁻¹ := by
  simp only [wSL, map_mul]
  rw [phi_T12 φ hφ, phi_T21 φ hφ, phi_T01 φ hφ, phi_T10 φ hφ, ← root2, ← root0]
  set n := CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2))
  have e1 := n1_conj_e0 (K := K) t
  have e2 := n1_conj_ne0 (K := K) (-t⁻¹)
  have e3 : n * (xPar F2 (g2CommRoot 0) t * xPar F2 (g2CommRoot 2) (-t⁻¹) *
      xPar F2 (g2CommRoot 0) t) * n⁻¹ =
      (n * xPar F2 (g2CommRoot 0) t * n⁻¹) * (n * xPar F2 (g2CommRoot 2) (-t⁻¹) * n⁻¹) *
        (n * xPar F2 (g2CommRoot 0) t * n⁻¹) := by group
  rw [e3, e1, e2]

theorem phi_D12 (t : Kˣ) :
    φ (wSL (show (1 : Fin 3) ≠ 2 by decide) (t : K) *
        wSL (show (1 : Fin 3) ≠ 2 by decide) (-1)) =
      CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)) *
        torusElement .G2 K (⟨0, by decide⟩ : Fin (Tag.rank .G2)) t *
        (CFSG.LieType.Chevalley.weylElement .G2 K (⟨1, by decide⟩ : Fin (Tag.rank .G2)))⁻¹ := by
  rw [map_mul, phi_wSL12 φ hφ, phi_wSL12 φ hφ, ← phi_D01 φ hφ t, map_mul]
  group

theorem phi_diag_mem_torusGroup (d : Matrix.SpecialLinearGroup (Fin (2 + 1)) K)
    (hd : ∀ i j : Fin 3, i ≠ j → (d : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ((φ d : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ torusGroup .G2 K := by
  obtain ⟨t, s, rfl⟩ := diag_eq_wSL_prod d hd
  rw [map_mul, phi_D01 φ hφ t, phi_D12 φ hφ s, Subgroup.coe_mul]
  exact mul_mem (torusElt_mem_torusGroup _ _) (n1_conj_mem_torus _ (torusElt_mem_torusGroup _ _))

end Phi2

end Torus

end CFSG.GH74.GLS.Stage2.Bender.Thm1
