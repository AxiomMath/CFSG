module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bUni
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bAbs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bPtsProof

open Matrix Projectivization KFactsSmall K21bUniProof K21bAbsProof
open scoped LinearAlgebra.Projectivization

variable {F : Type} [Field F]

@[expose] def pP : ℙ F (Fin 3 → F) := mk F ![1, 0, 0] (fun h => by simpa using congrFun h 0)

@[expose] def pL (a : F) : ℙ F (Fin 3 → F) := mk F ![a, 1, 0] (fun h => by simpa using congrFun h 1)

@[expose] def pA (a b : F) : ℙ F (Fin 3 → F) :=
  mk F ![a, b, 1] (fun h => by simpa using congrFun h 2)

theorem cover (y : ℙ F (Fin 3 → F)) :
    y = pP ∨ (∃ a, y = pL a) ∨ ∃ a b, y = pA a b := by
  induction y using Projectivization.ind with
  | h v hv =>
    by_cases h2 : v 2 = 0
    · by_cases h1 : v 1 = 0
      · left
        have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv
          funext i
          fin_cases i <;> simp [h0, h1, h2]
        rw [pP, mk_eq_mk_iff' F]
        exact ⟨v 0, by funext i; fin_cases i <;> simp [h1, h2]⟩
      · right
        left
        refine ⟨v 0 / v 1, ?_⟩
        rw [pL, mk_eq_mk_iff' F]
        refine ⟨v 1, ?_⟩
        funext i
        fin_cases i <;> simp [h1, h2] <;> field_simp
    · right
      right
      refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
      rw [pA, mk_eq_mk_iff' F]
      refine ⟨v 2, ?_⟩
      funext i
      fin_cases i <;> simp [h2] <;> field_simp

theorem pL_injective : Function.Injective (pL : F → ℙ F (Fin 3 → F)) := by
  intro a a' h
  rw [pL, pL, mk_eq_mk_iff' F] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrFun hc 1
  have h0 := congrFun hc 0
  simp at h1 h0
  rw [h1] at h0
  simpa using h0.symm

theorem pA_injective : Function.Injective fun p : F × F => (pA p.1 p.2 : ℙ F (Fin 3 → F)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [pA, mk_eq_mk_iff' F] at h
  obtain ⟨c, hc⟩ := h
  have h2 := congrFun hc 2
  have h1 := congrFun hc 1
  have h0 := congrFun hc 0
  simp at h2 h1 h0
  rw [h2] at h1 h0
  simp at h1 h0
  rw [h1, h0]

theorem pP_ne_pL (a : F) : (pP : ℙ F (Fin 3 → F)) ≠ pL a := by
  intro h
  rw [pP, pL, mk_eq_mk_iff' F] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrFun hc 1
  have h0 := congrFun hc 0
  simp at h1 h0
  rw [h1] at h0
  simp at h0

theorem smul_mk_coord (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F) (hv : v ≠ 0)
    (w : Fin 3 → F) (hw : w ≠ 0) (c : F) (hgw : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • w) :
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • mk F v hv = mk F w hw := by
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk]
  have h : g • v = c • w := hgw
  exact (mk_eq_mk_iff' F _ _ _ _).2 ⟨c, h.symm⟩

theorem uSL_smul_pP (α β γ : F) :
    (uSL α β γ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pP : ℙ F (Fin 3 → F)) = pP := by
  rw [pP]
  refine smul_mk_coord _ _ _ _ _ 1 ?_
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, coe_uSL, uMat]

theorem uSL_smul_pL (α β γ a : F) :
    (uSL α β γ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pL a : ℙ F (Fin 3 → F)) =
      pL (a + α) := by
  rw [pL, pL]
  refine smul_mk_coord _ _ _ _ _ 1 ?_
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, coe_uSL, uMat]

theorem uSL_smul_pA (α β γ a b : F) :
    (uSL α β γ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pA a b : ℙ F (Fin 3 → F)) =
      pA (a + α * b + β) (b + γ) := by
  rw [pA, pA]
  refine smul_mk_coord _ _ _ _ _ 1 ?_
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, coe_uSL, uMat]

variable (F) in
abbrev U0P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
  (U0 F).map (QuotientGroup.mk' _)

theorem point_lemma [Finite F] (hq4 : 4 ≤ Nat.card F) (hq8 : Nat.card F ≠ 8)
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)} (hE : Nat.card E = 9)
    (hperm : Permutable E (U0P F)) :
    ∀ e ∈ E, e • (pP : ℙ F (Fin 3 → F)) = pP := by
  have hAc : 9 < (Set.range fun p : F × F => (pA p.1 p.2 : ℙ F (Fin 3 → F))).ncard := by
    rw [Set.ncard_range_of_injective pA_injective, Nat.card_prod]
    have := Nat.mul_le_mul hq4 hq4
    omega
  refine fixed_of_orbits (L := Set.range (pL : F → ℙ F (Fin 3 → F)))
    (A := Set.range fun p : F × F => (pA p.1 p.2 : ℙ F (Fin 3 → F))) (q := Nat.card F)
    hperm hE ?_ ?_ (Set.ncard_range_of_injective pL_injective) ?_ ?_ hAc ?_ hq4 hq8
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨⟨α, β, γ⟩, rfl⟩ := hg
    exact uSL_smul_pP α β γ
  · rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    refine ⟨((uSL (a' - a) 0 0 : SpecialLinearGroup (Fin 3) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F), ⟨_, uSL_mem_U0 _ _ _, rfl⟩, ?_⟩
    rw [uSL_smul_pL, add_sub_cancel]
  · rintro ⟨a, ha⟩
    exact pP_ne_pL a ha.symm
  · rintro _ ⟨⟨a, b⟩, rfl⟩ _ ⟨⟨a', b'⟩, rfl⟩
    refine ⟨((uSL 0 (a' - a) (b' - b) : SpecialLinearGroup (Fin 3) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F), ⟨_, uSL_mem_U0 _ _ _, rfl⟩, ?_⟩
    simp only [uSL_smul_pA, zero_mul, add_zero, add_sub_cancel]
  · intro y
    rcases cover y with h | ⟨a, h⟩ | ⟨a, b, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, h.symm⟩)
    · exact Or.inr (Or.inr ⟨(a, b), h.symm⟩)

theorem fix_pP_iff (g : SpecialLinearGroup (Fin 3) F) :
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pP : ℙ F (Fin 3 → F)) = pP ↔
      (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  constructor
  · intro h
    rw [pP, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk,
      mk_eq_mk_iff' F] at h
    obtain ⟨c, hc⟩ := h
    have hc' : c • (![1, 0, 0] : Fin 3 → F) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] := hc
    have h1 := congrFun hc' 1
    have h2 := congrFun hc' 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    rw [pP]
    refine smul_mk_coord g _ _ _ _ ((g : Matrix (Fin 3) (Fin 3) F) 0 0) ?_
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

theorem tauFun_10 (A : SpecialLinearGroup (Fin 3) F) :
    (tauFun A : Matrix (Fin 3) (Fin 3) F) 1 0 =
      -((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 := by
  simp [coe_tauFun, wMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem upper_of_fixes (A : SpecialLinearGroup (Fin 3) F)
    (h1 : (A : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pP : ℙ F (Fin 3 → F)) = pP)
    (h2 : ((tauFun A : SpecialLinearGroup (Fin 3) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pP : ℙ F (Fin 3 → F)) = pP) :
    (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨h10, h20⟩ := (fix_pP_iff A).mp h1
  obtain ⟨t10, -⟩ := (fix_pP_iff (tauFun A)).mp h2
  rw [tauFun_10] at t10
  have hdet := A.2
  rw [Matrix.det_fin_three] at hdet
  refine ⟨h10, h20, ?_⟩
  have hinv : ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 =
      -((A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 2 1) +
        (A : Matrix (Fin 3) (Fin 3) F) 0 1 * (A : Matrix (Fin 3) (Fin 3) F) 2 0 := by
    simp [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
  have h21 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    rw [hinv, h20] at t10
    linear_combination t10
  have hA00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro h0
    rw [h0, h10, h20] at hdet
    simp at hdet
  exact (mul_eq_zero.mp h21).resolve_left hA00

variable (F) in
@[expose] noncomputable def tauP :
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
  QuotientGroup.congr _ _ (tau F) (Subgroup.map_center_eq (tau F))

theorem tauP_mk (g : SpecialLinearGroup (Fin 3) F) :
    tauP F (g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) =
      ((tauFun g : SpecialLinearGroup (Fin 3) F) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
  QuotientGroup.congr_mk _ _ (tau F) _ g

theorem tauP_map_U0P : (U0P F).map (tauP F).toMonoidHom = U0P F := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨tauFun g, ?_, (tauP_mk g).symm⟩
    have h : tau F g ∈ (U0 F).map (tau F).toMonoidHom := Subgroup.mem_map_of_mem _ hg
    rwa [tau_map_U0] at h
  · rintro ⟨g, hg, rfl⟩
    rw [← tau_map_U0] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨_, ⟨y, hy, rfl⟩, tauP_mk y⟩

theorem normalizes_of_fixes {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)}
    (h1 : ∀ e ∈ E, e • (pP : ℙ F (Fin 3 → F)) = pP)
    (h2 : ∀ e ∈ E.map (tauP F).toMonoidHom, e • (pP : ℙ F (Fin 3 → F)) = pP) :
    E ≤ Subgroup.normalizer ((U0P F : Subgroup _) : Set _) := by
  refine le_normalizer_of_forward _ _ ?_
  intro e he u hu
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective e
  obtain ⟨g, hg, rfl⟩ := hu
  have hA1 := h1 _ he
  have hA2 : ((tauFun A : SpecialLinearGroup (Fin 3) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) • (pP : ℙ F (Fin 3 → F)) = pP := by
    rw [← tauP_mk]
    exact h2 _ ⟨_, he, rfl⟩
  obtain ⟨h10, h20, h21⟩ := upper_of_fixes A hA1 hA2
  exact ⟨A * g * A⁻¹, conj_mem_U0 h10 h20 h21 hg, rfl⟩

theorem geom_psl_upper [Finite F] (hq4 : 4 ≤ Nat.card F) (hq8 : Nat.card F ≠ 8)
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)} (hE : Nat.card E = 9)
    (hperm : Permutable E (U0P F)) :
    E ≤ Subgroup.normalizer ((U0P F : Subgroup _) : Set _) := by
  have h1 := point_lemma hq4 hq8 hE hperm
  have hE' : Nat.card (E.map (tauP F).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := (tauP F).toMonoidHom) (tauP F).injective]
    exact hE
  have hperm' : Permutable (E.map (tauP F).toMonoidHom) (U0P F) := by
    have h := permutable_map (tauP F).toMonoidHom hperm
    rwa [tauP_map_U0P] at h
  exact normalizes_of_fixes h1 (point_lemma hq4 hq8 hE' hperm')

end K21bPtsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
