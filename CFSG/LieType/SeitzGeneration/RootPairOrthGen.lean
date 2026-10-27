module

public import CFSG.LieType.SeitzGeneration.RootPairOrthModel

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.RankThree.Classical2 (orthDerived)

namespace RootPairOrth

section Rational

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem eichler_entry_mem_gen (hext : IsExtension k Q₀ Q) {u w : Fin d → K} (hu : IsRat k u)
    (hw : IsRat k w) (hQu : Q u = 0) (hp : polar Q u w = 0) (i j : Fin d) :
    eichler Q u w (Pi.single j 1) i ∈ k := by
  rw [eichler_apply hQu hp]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact k.sub_mem (k.add_mem (isRat_single k j i)
    (k.mul_mem (polar_isRat_mem hext (isRat_single k j) hu) (hw i)))
    (k.mul_mem (k.add_mem (polar_isRat_mem hext (isRat_single k j) hw)
      (k.mul_mem (Q_isRat_mem hext hw) (polar_isRat_mem hext (isRat_single k j) hu))) (hu i))

theorem eichlerMat_rational_gen (hext : IsExtension k Q₀ Q) {σ : K ≃+* K}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w)
    (hQu : Q u = 0) (hp : polar Q u w = 0) :
    ∃ B ∈ matrixIsometries Q₀, glIncl k B = (matrixLinearIso (d := d) (K := K)).symm
      (eichler Q u w) := by
  set M : GL (Fin d) K := (matrixLinearIso (d := d) (K := K)).symm (eichler Q u w) with hMdef
  have hMv : ∀ v, M.val *ᵥ v = eichler Q u w v := fun v => by
    have h1 : matrixLinearIso M v = M.val *ᵥ v := rfl
    rw [← h1, hMdef, MulEquiv.apply_symm_apply]
  have hfix : glFieldAut (Fin d) K σ M = M := by
    apply Units.ext
    ext i j
    show σ (M.val i j) = M.val i j
    have hent : M.val i j = eichler Q u w (Pi.single j 1) i := by
      rw [← hMv, Matrix.mulVec_single_one]
      rfl
    rw [hent]
    exact (hσk _).mp (eichler_entry_mem_gen hext hu hw hQu hp i j)
  obtain ⟨B, hB⟩ := exists_glIncl_of_fixed k hσk hfix
  refine ⟨B, ?_, hB⟩
  rw [mem_matrixIsometries_iff]
  intro v
  have h1 : ((Q₀ (matrixLinearEquiv B v) : k) : K) = ((Q₀ v : k) : K) := by
    rw [← hext, ← hext, matrixLinearEquiv_apply, ← mulVec_vecIncl, hB, hMv]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup Q u w)) _
  exact Subtype.ext h1

end Rational

section Members

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)} (hext : IsExtension k Q₀ Q)
  {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x) (hder : elementaryGroup Q = orthDerived Q)

include hext hσk hder in
theorem eichler_mem_lift_gen {H : Subgroup (matrixProjectiveDerived Q)}
    (hN : subfieldFixedGroup k Q₀ Q ≤ H) {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w)
    (hQu : Q u = 0) (hp : polar Q u w = 0) : eichler Q u w ∈ liftSubgroup Q H := by
  obtain ⟨B, hB, hBM⟩ := eichlerMat_rational_gen hext hσk hu hw hQu hp
  have hA : (⟨_, eichlerMat_mem_derived hder u w⟩ : matrixDerived Q) ∈
      subfieldIsometries k Q₀ Q := by
    rw [subfieldIsometries, Subgroup.mem_subgroupOf]
    exact ⟨B, hB, hBM⟩
  refine mem_liftSubgroup.mpr ⟨⟨_, eichlerMat_mem_derived hder u w⟩, hN ⟨_, hA, rfl⟩, ?_⟩
  exact matrixLinearIso_symm_apply_apply _

include hext hσk hder in
theorem conj_eichler_mem_lift_gen {H : Subgroup (matrixProjectiveDerived Q)}
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hN' : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤ H)
    {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w) (hQu : Q u = 0) (hp : polar Q u w = 0) :
    matrixLinearIso gp.val.left * eichler Q u w * (matrixLinearIso gp.val.left)⁻¹ ∈
      liftSubgroup Q H := by
  obtain ⟨B, hB, hBM⟩ := eichlerMat_rational_gen hext hσk hu hw hQu hp
  have hA : (⟨_, eichlerMat_mem_derived hder u w⟩ : matrixDerived Q) ∈
      subfieldIsometries k Q₀ Q := by
    rw [subfieldIsometries, Subgroup.mem_subgroupOf]
    exact ⟨B, hB, hBM⟩
  set A : matrixDerived Q := ⟨_, eichlerMat_mem_derived hder u w⟩ with hAdef
  refine mem_liftSubgroup.mpr ⟨matrixDerivedConjugation Q gp A, ?_, ?_⟩
  · rw [← matrixProjectiveConjugation_mk]
    exact hN' ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  · rw [matrixDerivedConjugation_val, hgp, map_one]
    change matrixLinearIso (gp.val.left * A.val * gp.val.left⁻¹) = _
    rw [map_mul, map_mul, map_inv, hAdef]
    simp only [matrixLinearIso_symm_apply_apply]

end Members

section Assembly

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}

theorem elementaryGroup_le_lift_of_fail_gen
    (Basic : (Fin d → K) → (Fin d → K) → Prop)
    (hB : ∀ x y, Basic x y → IsRat k x ∧ IsRat k y ∧ IsTS Q x y)
    (hP3 : ∀ H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)),
      H ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ u w, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ H) →
      ∀ x y, Basic x y → x ≠ y → (∀ t : K, eichler Q x (t • y) ∈ H) → elementaryGroup Q ≤ H)
    (hext : IsExtension k Q₀ Q) (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (hder : elementaryGroup Q = orthDerived Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    {H : Subgroup (matrixProjectiveDerived Q)} (hN : subfieldFixedGroup k Q₀ Q ≤ H)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hN' : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤ H)
    (hfail : ¬ ∀ x y x₀ y₀, Basic x y → Basic x₀ y₀ →
      Phi Q gp.val.left.val (multiplier Q gp : K) x y x₀ y₀ ∈ k) :
    elementaryGroup Q ≤ liftSubgroup Q H := by
  simp only [not_forall] at hfail
  obtain ⟨x, y, x₀, y₀, hxy, hxy₀, hPhi⟩ := hfail
  set gm : GL (Fin d) K := gp.val.left with hgm
  set μ : K := (multiplier Q gp : K) with hμdef
  have hμ : μ ≠ 0 := Units.ne_zero _
  have hg : ∀ v, Q (matrixLinearIso gm v) = μ * Q v := fun v => by
    have h := multiplier_spec Q gp v
    rw [coordinateSemilinearMap_apply, hgp] at h
    exact h
  have hH := liftSubgroup_le_orthogonalGroup H
  obtain ⟨hxr, hyr, hx, hy, hxy'⟩ := hB x y hxy
  obtain ⟨hx₀r, hy₀r, hx₀, hy₀, hxy₀'⟩ := hB x₀ y₀ hxy₀
  have hne : x ≠ y := fun h => hPhi (by rw [h, phi_self_left]; exact k.zero_mem)
  have hc₁ : Q (gm.val *ᵥ x₀) = 0 := by
    have := hg x₀
    rw [hx₀, mul_zero] at this
    exact this
  have hc₂ : Q (gm.val *ᵥ y₀) = 0 := by
    have := hg y₀
    rw [hy₀, mul_zero] at this
    exact this
  have hc₁₂ : polar Q (gm.val *ᵥ x₀) (gm.val *ᵥ y₀) = 0 := by
    have := polar_similarity hg x₀ y₀
    rw [hxy₀', mul_zero] at this
    exact this
  have hHx : ∀ t ∈ k, eichler Q x (t • y) ∈ liftSubgroup Q H := by
    intro t ht
    have hty : IsRat k (t • y) := fun i => k.mul_mem ht (hyr i)
    have hpt : polar Q x (t • y) = 0 := by rw [polar_smul_right_eq, hxy', mul_zero]
    exact eichler_mem_lift_gen hext hσk hder hN hxr hty hx hpt
  have hHc : ∀ t ∈ k, eichler Q (gm.val *ᵥ x₀) ((μ⁻¹ * t) • (gm.val *ᵥ y₀)) ∈
      liftSubgroup Q H := by
    intro t ht
    have hty : IsRat k (t • y₀) := fun i => k.mul_mem ht (hy₀r i)
    have hpt : polar Q x₀ (t • y₀) = 0 := by rw [polar_smul_right_eq, hxy₀', mul_zero]
    have h := conj_eichler_mem_lift_gen hext hσk hder gp hgp hN' hx₀r hty hx₀ hpt
    rw [eichler_conj_similarity hμ hg] at h
    have e1 : matrixLinearIso gm x₀ = gm.val *ᵥ x₀ := rfl
    have e2 : μ⁻¹ • matrixLinearIso gm (t • y₀) = (μ⁻¹ * t) • (gm.val *ᵥ y₀) := by
      rw [map_smul, smul_smul]
      rfl
    rw [e1, e2] at h
    exact h
  have hline := eichler_line_of_irrational hp hp2 hK hk3 hx hy hxy' hc₁ hc₂ hc₁₂ hHx hHc hPhi
  exact hP3 _ hH (fun u w hu hw hQu hp' => eichler_mem_lift_gen hext hσk hder hN hu hw hQu hp')
    x y hxy hne hline

theorem orthPair_of_basic
    (Basic : (Fin d → K) → (Fin d → K) → Prop)
    (hB : ∀ x y, Basic x y → IsRat k x ∧ IsRat k y ∧ IsTS Q x y)
    (hP2 : ∀ σ : K ≃+* K, (∀ x, x ∈ k ↔ σ x = x) → ∀ (g : Matrix (Fin d) (Fin d) K) (μ : K),
      μ ≠ 0 → g.det ≠ 0 → (∀ v, Q (g *ᵥ v) = μ * Q v) →
      (∀ x y x₀ y₀, Basic x y → Basic x₀ y₀ → Phi Q g μ x y x₀ y₀ ∈ k) →
      ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c)
    (hP3 : ∀ H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)),
      H ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ u w, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ H) →
      ∀ x y, Basic x y → x ≠ y → (∀ t : K, eichler Q x (t • y) ∈ H) → elementaryGroup Q ≤ H)
    (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdeg : Module.finrank k K = p)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ := by
  obtain ⟨σ, hσo, hσk⟩ := exists_gen_aut k hp hdeg
  have hS := hsetup σ hσo hσk
  set gm : GL (Fin d) K := gp.val.left with hgm
  have hg : ∀ v, Q (gm.val *ᵥ v) = (multiplier Q gp : K) * Q v := fun v => by
    have h := multiplier_spec Q gp v
    rw [coordinateSemilinearMap_apply, hgp] at h
    exact h
  by_cases hP : ∀ x y x₀ y₀, Basic x y → Basic x₀ y₀ →
      Phi Q gm.val (multiplier Q gp : K) x y x₀ y₀ ∈ k
  · exfalso
    have hdet : gm.val.det ≠ 0 :=
      (((Matrix.isUnit_iff_isUnit_det _).mp gm.isUnit)).ne_zero
    obtain ⟨a, ha, heig⟩ := hP2 σ hσk gm.val (multiplier Q gp : K) (Units.ne_zero _) hdet hg hP
    have hle := map_le_of_eigen hS gp hgp ha heig
    apply hne
    have hcard : Nat.card ((subfieldFixedGroup k Q₀ Q).map
        (matrixProjectiveConjugationHom Q gp).toMonoidHom) = Nat.card (subfieldFixedGroup k Q₀ Q) :=
      Subgroup.card_map_of_injective (matrixProjectiveConjugationHom Q gp).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  · have hl := elementaryGroup_le_lift_of_fail_gen Basic hB hP3 hext hσk hder hp hp2 hK hk3
      (H := Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
        ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
          Set (matrixProjectiveDerived Q))))
      (fun x hx => Subgroup.subset_closure (Or.inl hx)) gp hgp
      (fun x hx => Subgroup.subset_closure (Or.inr hx)) hP
    exact eq_top_of_elementaryGroup_le hder hl

end Assembly

end RootPairOrth

end CFSG.LieType.SeitzGeneration
