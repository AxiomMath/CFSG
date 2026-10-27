module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section SL2

variable {F : Type*} [Field F]

theorem uSL_mul_WSL (u : Fˣ) :
    (uSL (u : F) * WSL : SL2 F) = vSL ((u⁻¹ : Fˣ) : F) * HSL (-u) * uSL (-((u⁻¹ : Fˣ) : F)) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_HSL, coe_WSL,
    Units.val_neg, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hu]

theorem WSL_mul_uSL_mul_WSL (u : Fˣ) :
    (WSL * uSL (u : F) * WSL : SL2 F) =
      uSL (-((u⁻¹ : Fˣ) : F)) * WSL * HSL (-u) * uSL (-((u⁻¹ : Fˣ) : F)) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_HSL, coe_WSL,
    Units.val_neg, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hu]

theorem vSL_eq (u : Fˣ) :
    (vSL (u : F) : SL2 F) =
      uSL ((u⁻¹ : Fˣ) : F) * (HSL (-u⁻¹) * WSL) * uSL ((u⁻¹ : Fˣ) : F) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_HSL, coe_WSL,
    Units.val_neg, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hu]

end SL2

section Rank1


variable {t : TwistTag} {K : Type} [Field K] (σ : K →+* K) (a : Fin t.foldedTag.rank)

theorem orbitX_mul_n (u : (orbitField t K σ a)ˣ) :
    (orbitX t K σ a (u : orbitField t K σ a) : ModGL t.tag K) *
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      (orbitY t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) : ModGL t.tag K) *
        (orbitH t K σ a (-u) : ModGL t.tag K) *
        (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :
          ModGL t.tag K) := by
  have h := congrArg (orbitRankOneHom t K σ a) (uSL_mul_WSL u)
  simp only [map_mul, orbitRankOneHom_uSL, orbitRankOneHom_vSL, orbitRankOneHom_HSL,
    orbitRankOneHom_WSL] at h
  rw [canonicalRep_orbitReflection_eq_orbitN (σ := σ)]
  exact h

theorem n_mul_orbitX_mul_n (u : (orbitField t K σ a)ˣ) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
        (orbitX t K σ a (u : orbitField t K σ a) : ModGL t.tag K) *
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :
          ModGL t.tag K) *
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
        (orbitH t K σ a (-u) : ModGL t.tag K) *
        (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :
          ModGL t.tag K) := by
  have h := congrArg (orbitRankOneHom t K σ a) (WSL_mul_uSL_mul_WSL u)
  simp only [map_mul, orbitRankOneHom_uSL, orbitRankOneHom_HSL, orbitRankOneHom_WSL] at h
  rw [canonicalRep_orbitReflection_eq_orbitN (σ := σ)]
  exact h

theorem orbitY_eq (u : (orbitField t K σ a)ˣ) :
    (orbitY t K σ a (u : orbitField t K σ a) : ModGL t.tag K) =
      (orbitX t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) : ModGL t.tag K) *
        ((orbitH t K σ a (-u⁻¹) : ModGL t.tag K) *
          canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) *
        (orbitX t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) : ModGL t.tag K) := by
  have h := congrArg (orbitRankOneHom t K σ a) (vSL_eq u)
  simp only [map_mul, orbitRankOneHom_uSL, orbitRankOneHom_vSL, orbitRankOneHom_HSL,
    orbitRankOneHom_WSL] at h
  rw [canonicalRep_orbitReflection_eq_orbitN (σ := σ)]
  exact h

end Rank1

section Transport


variable {t : TwistTag} {K : Type} [Field K] (σ : K →+* K)

theorem conj_mem_rootSpan_inf_iff {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α) (g : ModGL t.tag K) :
    canonicalRep (coxeterSystem t.tag) K w * g * (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
        rootSpan t.tag K ((fun α => w • α) '' S) ⊓ twistedFixedGroup t K σ ↔
      g ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ := by
  set n := canonicalRep (coxeterSystem t.tag) K w with hn_def
  have hn : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
  have hmap := (canonical_weyl_root_transport t.tag K).1 w S hS
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    rw [← hmap] at h1
    obtain ⟨y, hy, hyg⟩ := h1
    have e : y = g := by
      have hyg' : n * y * n⁻¹ = n * g * n⁻¹ := hyg
      rwa [mul_left_inj, mul_right_inj] at hyg'
    refine Subgroup.mem_inf.2 ⟨e ▸ hy, ?_⟩
    have e' : g = n⁻¹ * (n * g * n⁻¹) * n := by group
    rw [e']
    exact mul_mem (mul_mem (inv_mem hn) h2) hn
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hn h2) (inv_mem hn)⟩
    rw [← hmap]
    exact ⟨g, h1, rfl⟩

theorem torus_conj_mem_rootSpan_inf {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α) {h g : ModGL t.tag K}
    (hh : h ∈ graphFixedRootTorus t K σ) (hg : g ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) :
    h * g * h⁻¹ ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ := by
  obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (graphFixedTorus_le t K σ hh1) hg2)
    (inv_mem (graphFixedTorus_le t K σ hh1))⟩
  exact (Subgroup.mem_normalizer_iff.mp
    (torusGroup_le_normalizer_rootSpan hS (Subgroup.mem_inf.1 hh1).1) g).mp hg1

variable (t) in
theorem orbitReflection_image_simpleOrbitRoots (a : Fin t.foldedTag.rank) :
    (fun α => t.orbitReflection a • α) '' simpleOrbitRoots t a = negOrbitRoots t a := by
  rw [simpleOrbitRoots, negOrbitRoots, Set.image_image]
  exact Set.image_congr fun i hi => t.orbitReflection_smul_single hi

variable (t) in
theorem orbitReflection_image_negOrbitRoots (a : Fin t.foldedTag.rank) :
    (fun α => t.orbitReflection a • α) '' negOrbitRoots t a = simpleOrbitRoots t a := by
  rw [simpleOrbitRoots, negOrbitRoots, Set.image_image]
  exact Set.image_congr fun i hi => by
    simp only [smul_neg, t.orbitReflection_smul_single hi, neg_neg]

variable (t) in
theorem negComplementRoots_eq (a : Fin t.foldedTag.rank) :
    negComplementRoots t a = (fun α => -α) '' simpleComplementRoots t a := by
  ext γ
  constructor
  · rintro ⟨⟨hr, hn⟩, hne⟩
    refine ⟨-γ, ⟨⟨CFSG.LieType.Chevalley.IsRoot.neg hr, ?_⟩, fun h => hne ?_⟩, neg_neg γ⟩
    · rw [height_neg]
      omega
    · obtain ⟨i, hi, hiγ⟩ := h
      exact ⟨i, hi, by simp only [hiγ, neg_neg]⟩
  · rintro ⟨α, ⟨⟨hr, hp⟩, hαE⟩, rfl⟩
    refine ⟨⟨CFSG.LieType.Chevalley.IsRoot.neg hr, ?_⟩, fun h => hαE ?_⟩
    · rw [height_neg]
      omega
    · obtain ⟨i, hi, hiα⟩ := h
      exact ⟨i, hi, by simpa using hiα⟩

variable (t) in
theorem orbitReflection_image_negComplementRoots (a : Fin t.foldedTag.rank) :
    (fun α => t.orbitReflection a • α) '' negComplementRoots t a = negComplementRoots t a := by
  rw [negComplementRoots_eq, Set.image_image]
  conv_rhs => rw [← image_orbitReflection_simpleComplementRoots a, Set.image_image]
  exact Set.image_congr fun α _ => smul_neg _ _

end Transport

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
