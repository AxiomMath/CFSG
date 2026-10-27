module

public import CFSG.CharacterTheory.Semidihedral.MatrixCoverData
public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient

public section

namespace CFSG.Semidihedral.ProjectiveNonsquareInvolutions

noncomputable section

open Matrix
open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.MatrixCoverData
open CFSG.Semidihedral.SemilinearOuterQuotient

universe u

variable (F : Type u) [Field F]

theorem projective_mem_G_iff [Finite F] (V : GL2 F) :
    (glProjective F V : Equiv.Perm (Omega F)) ∈ coordinateG F ↔
      IsSquare (GeneralLinearGroup.det V) := by
  have hm (g : PGL2 F) :
      (pglEquivCoordinateD F g : Equiv.Perm (Omega F)) ∈ coordinateG F ↔
        g ∈ Matrix.ProjectiveSpecialLinearGroup.toPGL.range := by
    change pglEquivCoordinateD F g ∈ (coordinateG F).subgroupOf (coordinateD F) ↔ _
    rw [← pglPSLRange_map_coordinateD]
    constructor
    · rintro ⟨x, hx, he⟩
      exact (pglEquivCoordinateD F).injective he ▸ hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  change (pglEquivCoordinateD F (Matrix.ProjGenLinGroup.mk V) :
    Equiv.Perm (Omega F)) ∈ coordinateG F ↔ _
  rw [hm, ← pglDet_ker]
  change pglDet F (Matrix.ProjGenLinGroup.mk V) = 1 ↔ _
  rw [pglDet_mk, squareClassMap_eq_one]

theorem nonsquare_quotient_square [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (a b : Fˣ)
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) : IsSquare (b / a) := by
  have hab : squareClassMap F b = squareClassMap F a :=
    eq_of_nonone_of_card_two (squareClass_card_two F hF)
      (fun h => hb ((squareClassMap_eq_one F b).mp h))
      (fun h => ha ((squareClassMap_eq_one F a).mp h))
  apply (squareClassMap_eq_one F _).mp
  rw [map_div, hab]
  exact div_self' _

theorem cayley_hamilton_two (V : Matrix (Fin 2) (Fin 2) F) :
    V ^ 2 - V.trace • V + Matrix.scalar (Fin 2) V.det = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

theorem trace_zero_of_projective_involution [Finite F] (V : GL2 F)
    (hV : orderOf (glProjective F V) = 2) :
    Matrix.trace (V : Matrix (Fin 2) (Fin 2) F) = 0 := by
  have hs : Matrix.ProjGenLinGroup.mk (V ^ 2) = 1 := by
    apply coordinatePGLAction_injective F
    change ((glProjective F (V ^ 2) : coordinateD F) : Equiv.Perm (Omega F)) = _
    have hp : (glProjective F V) ^ 2 = 1 := by
      simpa only [hV] using pow_orderOf_eq_one (glProjective F V)
    rw [map_pow, hp]
    simp
  have hc : V ^ 2 ∈ Subgroup.center (GL2 F) := Matrix.ProjGenLinGroup.mk_eq_one.mp hs
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨l, hl⟩ := hc
  have hm : (V : Matrix (Fin 2) (Fin 2) F) ^ 2 =
      Matrix.scalar (Fin 2) (l : F) := congrArg Units.val hl.symm
  have hch := cayley_hamilton_two F (V : Matrix (Fin 2) (Fin 2) F)
  rw [hm] at hch
  by_contra ht
  let t := Matrix.trace (V : Matrix (Fin 2) (Fin 2) F)
  let c := ((l : F) + Matrix.det (V : Matrix (Fin 2) (Fin 2) F)) / t
  have he : (V : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := by
    ext i j
    have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) hch
    fin_cases i <;> fin_cases j
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      dsimp [c, t]
      field_simp [ht]
      linear_combination -h
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      exact h.resolve_left ht
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      exact h.resolve_left ht
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      dsimp [c, t]
      field_simp [ht]
      linear_combination -h
  have hc0 : c ≠ 0 := by
    intro hz
    have hd := (GeneralLinearGroup.det V).ne_zero
    have hdet : (GeneralLinearGroup.det V : F) = 0 := by
      change Matrix.det (V : Matrix (Fin 2) (Fin 2) F) = 0
      rw [he, hz]
      simp
    exact hd hdet
  have hv : V = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) := Units.ext he
  have h1 : glProjective F V = 1 := by rw [hv, glProjective_scalar]
  rw [h1] at hV
  norm_num at hV

theorem companion_conjugator (W : GL2 F) (a : Fˣ)
    (ht : Matrix.trace (W : Matrix (Fin 2) (Fin 2) F) = 0)
    (hd : GeneralLinearGroup.det W = a)
    (hn : ∀ c : Fˣ, W ≠ GeneralLinearGroup.scalar (Fin 2) c) :
    ∃ P : GL2 F, P⁻¹ * W * P = J F a := by
  let b := (W : Matrix (Fin 2) (Fin 2) F) 0 0
  let c := (W : Matrix (Fin 2) (Fin 2) F) 1 0
  let k := (W : Matrix (Fin 2) (Fin 2) F) 0 1
  have htt : (W : Matrix (Fin 2) (Fin 2) F) 1 1 = -b := by
    rw [Matrix.trace_fin_two] at ht
    dsimp [b]
    linear_combination ht
  have hdet : -b * b - k * c = (a : F) := by
    have h := congrArg Units.val hd
    change Matrix.det (W : Matrix (Fin 2) (Fin 2) F) = (a : F) at h
    rw [Matrix.det_fin_two, htt] at h
    dsimp [b, c, k]
    linear_combination h
  have hW : (W : Matrix (Fin 2) (Fin 2) F) = !![b, k; c, -b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [b, c, k, htt]
  have build (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0)
      (he : (W : Matrix (Fin 2) (Fin 2) F) * P =
        P * (J F a : Matrix (Fin 2) (Fin 2) F)) :
      ∃ P : GL2 F, P⁻¹ * W * P = J F a := by
    let g := GeneralLinearGroup.mkOfDetNeZero P hP
    have hg : W * g = g * J F a := Units.ext he
    refine ⟨g, ?_⟩
    calc
      g⁻¹ * W * g = g⁻¹ * (W * g) := by group
      _ = g⁻¹ * (g * J F a) := congrArg (fun x => g⁻¹ * x) hg
      _ = J F a := inv_mul_cancel_left _ _
  by_cases hc : c = 0
  · by_cases hk : k = 0
    · have hb : b ≠ 0 := by
        intro hb
        have h := (GeneralLinearGroup.det W).ne_zero
        have hz : (a : F) = 0 := by simpa [hb, hc, hk] using hdet.symm
        exact a.ne_zero hz
      have hbb : -b - b ≠ 0 := by
        intro h
        have he : -b = b := sub_eq_zero.mp h
        have hs : W = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 b hb) := by
          apply Units.ext
          rw [hW]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [hc, hk, he]
        exact hn _ hs
      apply build !![1, b; 1, -b]
      · simpa [Matrix.det_fin_two] using hbb
      · rw [hW, J_matrix]
        have hd0 : -b * b = (a : F) := by simpa [hc, hk] using hdet
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hk]
        · linear_combination -hd0
        · linear_combination -hd0
    · apply build !![0, k; 1, -b]
      · simpa [Matrix.det_fin_two] using neg_ne_zero.mpr hk
      · rw [hW, J_matrix]
        have hd0 : -b * b = (a : F) := by simpa [hc] using hdet
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
        · ring
        · linear_combination -hd0
  · apply build !![1, b; 0, c]
    · simpa [Matrix.det_fin_two] using hc
    · rw [hW, J_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination -hdet
      · ring

theorem projective_nonsquare_involutions_are_conjugate [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (a : Fˣ) (ha : ¬IsSquare a)
    (v : coordinateD F) (hvG : (v : Equiv.Perm (Omega F)) ∉ coordinateG F)
    (hv : orderOf v = 2) :
    ∃ d : coordinateD F, d * v * d⁻¹ = jProjective F a := by
  obtain ⟨V, hV⟩ := Matrix.ProjGenLinGroup.mk_surjective ((pglEquivCoordinateD F).symm v)
  have hrep : glProjective F V = v := by
    change pglEquivCoordinateD F (Matrix.ProjGenLinGroup.mk V) = v
    rw [hV, MulEquiv.apply_symm_apply]
  have hdet : ¬IsSquare (GeneralLinearGroup.det V) := by
    intro h
    exact hvG (by rw [← hrep]; exact (projective_mem_G_iff F V).mpr h)
  obtain ⟨c, hc⟩ := (nonsquare_quotient_square F hF a (GeneralLinearGroup.det V)
    ha hdet).exists_sq
  let W : GL2 F := GeneralLinearGroup.scalar (Fin 2) c⁻¹ * V
  have hWrep : glProjective F W = v := by
    dsimp [W]
    rw [map_mul, glProjective_scalar, one_mul, hrep]
  have hWd : GeneralLinearGroup.det W = a := by
    dsimp [W]
    rw [map_mul, GeneralLinearGroup.det_scalar]
    have hd : GeneralLinearGroup.det V = c ^ 2 * a := (div_eq_iff_eq_mul).mp hc
    rw [hd]
    norm_num only [Fintype.card_fin]
    group
  have hWt : Matrix.trace (W : Matrix (Fin 2) (Fin 2) F) = 0 :=
    trace_zero_of_projective_involution F W (hWrep ▸ hv)
  have hWn : ∀ b : Fˣ, W ≠ GeneralLinearGroup.scalar (Fin 2) b := by
    intro b hb
    have h1 : v = 1 := by rw [← hWrep, hb, glProjective_scalar]
    rw [h1] at hv
    norm_num at hv
  obtain ⟨P, hP⟩ := companion_conjugator F W a hWt hWd hWn
  refine ⟨glProjective F P⁻¹, ?_⟩
  calc
    glProjective F P⁻¹ * v * (glProjective F P⁻¹)⁻¹ =
        glProjective F (P⁻¹ * W * P) := by
      rw [← hWrep]
      simp only [map_mul, map_inv, inv_inv]
    _ = jProjective F a := congrArg (glProjective F) hP

theorem jProjective_outer_involution [Finite F] (a : Fˣ) (ha : ¬IsSquare a) :
    (jProjective F a : Equiv.Perm (Omega F)) ∉ coordinateG F ∧
      orderOf (jProjective F a) = 2 := by
  have hout : (jProjective F a : Equiv.Perm (Omega F)) ∉ coordinateG F := by
    intro h
    have hs := (projective_mem_G_iff F (J F a)).mp h
    rw [J_det] at hs
    exact ha hs
  refine ⟨hout, orderOf_eq_prime (jProjective_square F a) ?_⟩
  intro h
  have hG := (coordinateG F).one_mem
  exact hout (by simpa only [h, Subgroup.coe_one] using hG)

theorem projective_nonsquare_involutions_single_class [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (a : Fˣ) (ha : ¬IsSquare a) :
    (jProjective F a : Equiv.Perm (Omega F)) ∉ coordinateG F ∧
    orderOf (jProjective F a) = 2 ∧
    ∀ v : coordinateD F, (v : Equiv.Perm (Omega F)) ∉ coordinateG F →
      orderOf v = 2 → ∃ d : coordinateD F, d * v * d⁻¹ = jProjective F a := by
  exact ⟨(jProjective_outer_involution F a ha).1,
    (jProjective_outer_involution F a ha).2,
    projective_nonsquare_involutions_are_conjugate F hF a ha⟩

theorem projective_nonsquare_involutions_original_field
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (a : Fˣ) (ha : ¬IsSquare a)
    (v : Equiv.Perm (Omega F)) (hvD : v ∈ coordinateD F)
    (hvG : v ∉ coordinateG F) (hv : orderOf v = 2) :
    (jProjective F a : Equiv.Perm (Omega F)) ∉ coordinateG F ∧
    orderOf (jProjective F a) = 2 ∧
    ∃ d : Equiv.Perm (Omega F), d ∈ coordinateD F ∧
      d * v * d⁻¹ = (jProjective F a : Equiv.Perm (Omega F)) := by
  let : Finite F := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hp.ne_zero)
  have hF : IsOddPrimePower (Nat.card F) := by
    exact ⟨p, f, hp, hpodd, hf, hcard⟩
  obtain ⟨d, hd⟩ := projective_nonsquare_involutions_are_conjugate F hF a ha
    ⟨v, hvD⟩ hvG (by simpa only [Subgroup.orderOf_mk] using hv)
  exact ⟨(jProjective_outer_involution F a ha).1,
    (jProjective_outer_involution F a ha).2, d, d.property,
    congrArg Subtype.val hd⟩

end

end CFSG.Semidihedral.ProjectiveNonsquareInvolutions
