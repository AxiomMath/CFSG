module

public import CFSG.ClassicalInvolution.Phan.PhanS9O2Fix
public import CFSG.ClassicalInvolution.Phan.PhanH8Gen
import CFSG.ClassicalInvolution.Phan.PhanS9O3Num
import CFSG.ClassicalInvolution.Phan.PhanP17Ell
import CFSG.ClassicalInvolution.Phan.PhanB21Exists

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section Span

variable {F : Type} [Field F]

theorem fr0_span_mk7_mem (h2 : (2 : F) ≠ 0) (s a b z : F) :
    mk7 s a b s (-a) (-b) z ∈ (fr0 h2).span := by
  rw [Frame.mem_span_iff_inv _ h2, La0_neg_one, neg_mk7]
  simp

theorem polar_span_span (s a b z s' a' b' z' : F) :
    polar (quadOdd 3 F) (mk7 s a b s (-a) (-b) z) (mk7 s' a' b' s' (-a') (-b') z') =
      2 * (s * s' - a * a' - b * b' + z * z') := by
  rw [polar_mk7]
  ring

theorem fr0_span_regular (h2 : (2 : F) ≠ 0) :
    ((quadOdd 3 F).restrict (fr0 h2).span).Nondegenerate := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  refine PhanP.nondegenerate_restrict_of_forall _ ?_
  intro x hx hort
  obtain ⟨s, a, b, z, rfl⟩ := mem_span_fr0 h2 hx
  have h1 := hort _ (fr0_span_mk7_mem h2 1 0 0 0)
  have h3 := hort _ (fr0_span_mk7_mem h2 0 1 0 0)
  have h4 := hort _ (fr0_span_mk7_mem h2 0 0 1 0)
  have h5 := hort _ (fr0_span_mk7_mem h2 0 0 0 1)
  rw [polar_span_span] at h1 h3 h4 h5
  have key : ∀ t : F, 2 * t = 0 → t = 0 := fun t ht => (mul_eq_zero.mp ht).resolve_left h2
  have hs : s = 0 := key s (by linear_combination h1)
  have ha : a = 0 := key a (by linear_combination -h3)
  have hb : b = 0 := key b (by linear_combination -h4)
  have hz : z = 0 := key z (by linear_combination h5)
  subst hs ha hb hz
  simp only [neg_zero]
  exact mk7_zero

noncomputable abbrev w0Perp (h2 : (2 : F) ≠ 0) : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Unit → F) :=
  LinearMap.BilinForm.orthogonal (quadOdd 3 F).polarBilin (fr0 h2).span

theorem mem_w0Perp_iff (h2 : (2 : F) ≠ 0) (x : Fin 3 ⊕ Fin 3 ⊕ Unit → F) :
    x ∈ w0Perp h2 ↔
      ∀ s a b z : F, polar (quadOdd 3 F) (mk7 s a b s (-a) (-b) z) x = 0 := by
  rw [w0Perp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h s a b z
    have h' := h _ (fr0_span_mk7_mem h2 s a b z)
    rw [QuadraticMap.polarBilin_apply_apply] at h'
    exact h'
  · intro h w hw
    obtain ⟨s, a, b, z, rfl⟩ := mem_span_fr0 h2 hw
    rw [QuadraticMap.polarBilin_apply_apply]
    exact h s a b z

@[expose] noncomputable def w0Psi :
    (Fin 1 ⊕ Fin 1 ⊕ Unit → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Unit → F) where
  toFun v := mk7 (v (.inr (.inl 0)) - v (.inl 0)) (v (.inl 0) + v (.inr (.inl 0)))
    (2 * v (.inr (.inr ()))) (-(v (.inr (.inl 0)) - v (.inl 0)))
    (v (.inl 0) + v (.inr (.inl 0))) (2 * v (.inr (.inr ()))) 0
  map_add' v w := by
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp <;> ring
    · fin_cases i <;> simp <;> ring
    · simp
  map_smul' c v := by
    funext t
    rcases t with i | i | u
    · fin_cases i <;> simp <;> ring
    · fin_cases i <;> simp <;> ring
    · simp

theorem w0Psi_apply (v : Fin 1 ⊕ Fin 1 ⊕ Unit → F) :
    w0Psi v = mk7 (v (.inr (.inl 0)) - v (.inl 0)) (v (.inl 0) + v (.inr (.inl 0)))
      (2 * v (.inr (.inr ()))) (-(v (.inr (.inl 0)) - v (.inl 0)))
      (v (.inl 0) + v (.inr (.inl 0))) (2 * v (.inr (.inr ()))) 0 := rfl

theorem w0Psi_quad (v : Fin 1 ⊕ Fin 1 ⊕ Unit → F) :
    quadOdd 3 F (w0Psi v) = 4 * quadOdd 1 F v := by
  rw [w0Psi_apply, quad_mk7, quadOdd_apply, Fin.sum_univ_one]
  ring

theorem w0Psi_mem (h2 : (2 : F) ≠ 0) (v : Fin 1 ⊕ Fin 1 ⊕ Unit → F) : w0Psi v ∈ w0Perp h2 := by
  rw [mem_w0Perp_iff]
  intro s a b z
  rw [w0Psi_apply, polar_mk7]
  ring

omit [Field F] in
theorem ext3 {v w : Fin 1 ⊕ Fin 1 ⊕ Unit → F} (h0 : v (.inl 0) = w (.inl 0))
    (h1 : v (.inr (.inl 0)) = w (.inr (.inl 0)))
    (h2 : v (.inr (.inr ())) = w (.inr (.inr ()))) : v = w := by
  funext t
  rcases t with i | i | ⟨⟩
  · rw [Subsingleton.elim i 0]
    exact h0
  · rw [Subsingleton.elim i 0]
    exact h1
  · exact h2

theorem w0Psi_injective (h2 : (2 : F) ≠ 0) : Function.Injective (w0Psi (F := F)) := by
  intro v w h
  have e1 := congrFun h (.inl 0)
  have e2 := congrFun h (.inl 1)
  have e3 := congrFun h (.inl 2)
  simp only [w0Psi_apply, mk7_x0, mk7_x1, mk7_x2] at e1 e2 e3
  refine ext3 ?_ ?_ ?_
  · exact mul_left_cancel₀ h2 (by linear_combination e2 - e1)
  · exact mul_left_cancel₀ h2 (by linear_combination e1 + e2)
  · exact mul_left_cancel₀ h2 e3

theorem finrank_fr0_span (h2 : (2 : F) ≠ 0) : Module.finrank F (fr0 h2).span = 4 := by
  have hinj : Function.Injective (fr0 h2).incl := fun X Y h => by
    have := congrArg (fr0 h2).coords h
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  have hspan : (fr0 h2).span = LinearMap.range (fr0 h2).incl := rfl
  rw [hspan, LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix]
  simp

theorem finrank_w0Perp (h2 : (2 : F) ≠ 0) : Module.finrank F (w0Perp h2) = 3 := by
  rw [w0Perp, LinearMap.BilinForm.finrank_orthogonal (nondegenerate_polarBilin_quadOdd 3 F h2),
    finrank_fr0_span h2]
  simp [Module.finrank_fintype_fun_eq_card]

theorem w0Psi_codRestrict_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (w0Psi.codRestrict (w0Perp h2) (w0Psi_mem h2)) :=
  fun _ _ h => w0Psi_injective h2 (congrArg Subtype.val h)

noncomputable def w0Equiv (h2 : (2 : F) ≠ 0) :
    (Fin 1 ⊕ Fin 1 ⊕ Unit → F) ≃ₗ[F] w0Perp h2 :=
  LinearMap.linearEquivOfInjective (w0Psi.codRestrict (w0Perp h2) (w0Psi_mem h2))
    (w0Psi_codRestrict_injective h2)
    (by rw [finrank_w0Perp h2]; simp [Module.finrank_fintype_fun_eq_card])

theorem w0Equiv_coe (h2 : (2 : F) ≠ 0) (v : Fin 1 ⊕ Fin 1 ⊕ Unit → F) :
    ((w0Equiv h2 v : w0Perp h2) : Fin 3 ⊕ Fin 3 ⊕ Unit → F) = w0Psi v := by
  simp only [w0Equiv, LinearMap.linearEquivOfInjective_apply, LinearMap.codRestrict_apply]

theorem w0Equiv_quad (h2 : (2 : F) ≠ 0) (v : Fin 1 ⊕ Fin 1 ⊕ Unit → F) :
    ((quadOdd 3 F).restrict (w0Perp h2)) (w0Equiv h2 v) = 4 * quadOdd 1 F v := by
  rw [QuadraticMap.restrict_apply, w0Equiv_coe, w0Psi_quad]

theorem exists_quadOdd_one_eq (c : F) :
    ∃ v : Fin 1 ⊕ Fin 1 ⊕ Unit → F, quadOdd 1 F v = c :=
  ⟨Sum.elim (fun _ => c) (Sum.elim (fun _ => 1) (fun _ => 0)), by
    rw [quadOdd_apply, Fin.sum_univ_one]
    simp⟩

theorem card_fixSub_fr0_span_le [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (fixSub (quadOdd 3 F) ((fr0 h2).span : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F))) ≤
      Nat.card SL(2, F) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hQ : (quadOdd 3 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 3 F h2)
  obtain ⟨ν, hν⟩ := exists_nonsquare_of_two_ne_zero h2
  have : Nontrivial (w0Perp h2) := (w0Equiv h2).injective.nontrivial
  have hreg := fr0_span_regular h2
  have h1 : Nat.card (fixSub (quadOdd 3 F) ((fr0 h2).span : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F))) ≤
      Nat.card (spinGroup ((quadOdd 3 F).restrict (w0Perp h2))) := card_fixSub_le hQ hreg
  have hQ' : ((quadOdd 3 F).restrict (w0Perp h2)).Nondegenerate :=
    hQ.nondegenerate_restrict_orthogonal hreg
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  obtain ⟨va, hva⟩ := exists_quadOdd_one_eq (F := F) (1 / 4)
  obtain ⟨vb, hvb⟩ := exists_quadOdd_one_eq (F := F) (ν / 4)
  have h2' := two_mul_card_spinGroup_le hQ' hν (a := w0Equiv h2 va) (b := w0Equiv h2 vb)
    (by rw [w0Equiv_quad, hva]; field_simp) (by rw [w0Equiv_quad, hvb]; field_simp)
  have h3 := card_orthogonalGroup_le_of_similar (quadOdd 1 F)
    ((quadOdd 3 F).restrict (w0Perp h2)) (w0Equiv h2) (c := 4) h4 (w0Equiv_quad h2)
  have h5 := card_orthogonalGroup_quadOdd_one h2
  omega

end Span

section Final

variable {F : Type} [Field F] [Finite F]

theorem fixW0_le_U2_of_two_ne_zero (h2 : (2 : F) ≠ 0) (Dθ : ThetaData F h2)
    (g : spinGroup (quadOdd 3 F))
    (hg : ∀ x ∈ (fr0 h2).span, spinAction (quadOdd 3 F) g x = x) :
    g ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map Dθ.θ := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hQ : (quadOdd 3 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 3 F h2)
  have := finite_spinGroup hQ
  have hle : (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map Dθ.θ ≤
      fixSub (quadOdd 3 F) ((fr0 h2).span : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F)) := by
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    refine mem_fixSub.2 ?_
    intro x hx
    exact theta_twShort_fix_span Dθ.isLevi Dθ.nat Dθ.fix h2 A hx
  have hcard : Nat.card (fixSub (quadOdd 3 F)
      ((fr0 h2).span : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → F))) ≤
      Nat.card ((CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map Dθ.θ) := by
    rw [Subgroup.card_map_of_injective Dθ.θ_inj,
      card_range_eq_of_injective (CFSG.ClassicalInvolution.PhanB3.twShort_injective h2)]
    exact card_fixSub_fr0_span_le h2
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact mem_fixSub.2 hg

theorem fixW0_le_U2 (h2 : (2 : F) ≠ 0) (hn1 : ¬ IsSquare (-1 : F)) (Dθ : ThetaData F h2)
    (g : spinGroup (quadOdd 3 F))
    (hg : ∀ x ∈ (fr0 h2).span, spinAction (quadOdd 3 F) g x = x) :
    g ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map Dθ.θ := by
  have _ := hn1
  exact fixW0_le_U2_of_two_ne_zero h2 Dθ g hg

end Final

end CFSG.ClassicalInvolution.PhanB3.S
