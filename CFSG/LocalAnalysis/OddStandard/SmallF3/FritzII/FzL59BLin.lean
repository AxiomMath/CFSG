module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BCl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinHom

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup FzL59BLin CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}

theorem fzl59bFn_mem (hg : Fz59Grid t s lam rho b) {T : Subgroup G} (hb : ∀ i k, b i k ∈ T)
    (n : N) : fzl59bFn hg n ∈ T := by
  have hq : ∀ (i : Fin 3) (q : Q), q8Hom (hg.quat i) q ∈ T := by
    intro i q
    have h1 : q8Hom (hg.quat i) (QuaternionGroup.a 1) = b i 0 := fzl_q8Hom_a_one _
    have h2 : q8Hom (hg.quat i) (QuaternionGroup.xa 0) = b i 1 := fzl_q8Hom_xa_zero _
    rcases q with j | j
    · have hj : (QuaternionGroup.a j : Q) = (QuaternionGroup.a 1) ^ j.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [hj, map_pow, h1]
      exact pow_mem (hb i 0) _
    · have hj : (QuaternionGroup.xa j : Q) =
          QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ j.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add]
      rw [hj, map_mul, map_pow, h1, h2]
      exact mul_mem (hb i 1) (pow_mem (hb i 0) _)
  obtain ⟨n0, n1, n2⟩ := n
  rw [fzl59bFn_apply]
  exact mul_mem (hq 0 n0) (mul_mem (hq 1 n1) (hq 2 n2))

theorem fzl59b_lam_mem [Finite G] (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) :
    lam ∈ T₃ := by
  rw [h.hT₃]
  refine Subgroup.mem_sup_left ?_
  rw [h.hT₂]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)

theorem fzl59b_u_mem [Finite G] (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) :
    u ∈ T₃ := by
  rw [h.hT₃]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem fzl59b_phi_mem [Finite G] (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (x : X) : phi (fzl59bFn h.grid) lam u x ∈ T₃ := by
  have hy : ∀ e : Bool, yp lam e ∈ T₃ := by
    intro e
    cases e
    · exact T₃.one_mem
    · exact fzl59b_lam_mem h
  have hu : ∀ f : Bool, up u f ∈ T₃ := by
    intro f
    cases f
    · exact T₃.one_mem
    · exact fzl59b_u_mem h
  exact mul_mem (mul_mem (fzl59bFn_mem h.grid (fzl59b_b_mem h) x.1) (hy _)) (hu _)

theorem fzl59b_phi_cov [Finite G] (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) {ε : Bool}
    (D : LinData ε (fzl59bFn h.grid) lam u) (g : G) (hg : g ∈ T₃) :
    ∃ x : X, phi (fzl59bFn h.grid) lam u x = g := by
  have hRle : closure (Set.range fun p : Fin 3 × Fin 2 => b p.1 p.2) ≤ D.rangeSubgroup := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨⟨i, k⟩, rfl⟩
    exact ⟨(gen3 i k, false, false), by simp [phi, yp, up, fzl59bFn_gen]⟩
  have hlam : lam ∈ D.rangeSubgroup := ⟨(1, true, false), by simp [phi, yp, up]⟩
  have hu : u ∈ D.rangeSubgroup := ⟨(1, false, true), by simp [phi, yp, up]⟩
  have hT2le : T₂ ≤ D.rangeSubgroup :=
    h.hT₂.le.trans (sup_le (h.hR.le.trans hRle) (Subgroup.zpowers_le.mpr hlam))
  have hle : T₃ ≤ D.rangeSubgroup :=
    h.hT₃.le.trans (sup_le hT2le (Subgroup.zpowers_le.mpr hu))
  exact D.mem_rangeSubgroup.mp (hle hg)

theorem fz59_linear [Finite G] (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃) :
    Fz59Linear T₃ := by
  rcases h.u_cases with hu | hu
  · have D := fzl59b_linData_good h.grid hu
    exact fz59_linear_aux D (fzl59b_phi_mem h) (fzl59b_phi_cov h D) h.card_T₃
  · have D := fzl59b_linData_bad h.grid hu
    exact fz59_linear_aux D (fzl59b_phi_mem h) (fzl59b_phi_cov h D) h.card_T₃

end CFSG.OddStandard.SmallF3.FritzII
