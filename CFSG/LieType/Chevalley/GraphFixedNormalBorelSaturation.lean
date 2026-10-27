module

public import CFSG.LieType.Chevalley.GraphFixedBorelCoreCenter
public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.ConnectedDiagram

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (t) in
theorem orbitLength_list_prod
    (ω : List (Fin t.foldedTag.rank)) :
    t.orbitLength (ω.map t.orbitReflection).prod =
      (coxeterSystem t.foldedTag).length ((coxeterSystem t.foldedTag).wordProd ω) := by
  rw [← foldedWeylEquiv_list_prod t ω]
  exact orbitLength_eq t ⟨_, t.list_prod_orbitReflection_mem ω⟩

theorem canonicalRep_mem_of_mem_graphFixedRootBruhatCell
    {A : Subgroup (ModGL t.tag K)}
    (hB : graphFixedRootBorel t K σ ≤ A) {w : WeylGroup t.tag} {x : ModGL t.tag K}
    (hx : x ∈ graphFixedRootBruhatCell t K σ w) (hxA : x ∈ A) :
    canonicalRep (coxeterSystem t.tag) K w ∈ A := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
  have := mul_mem (mul_mem (inv_mem (hB hb)) hxA) (inv_mem (hB hb'))
  simpa [mul_assoc] using this

theorem canonicalRep_mem_graphFixedRootBruhatCell
    (w : WeylGroup t.tag) :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootBruhatCell t K σ w := by
  have h := mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (K := K) (σ := σ) (w := w)
    (one_mem _) (one_mem _)
  rwa [one_mul, mul_one] at h

theorem fixed_normal_Borel_saturation
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    (M : Subgroup (graphFixedRootGroup t K σ.toRingHom)) [M.Normal] :
    M ≤ Subgroup.center (graphFixedRootGroup t K σ.toRingHom) ∨
      ((M.map (graphFixedRootGroup t K σ.toRingHom).subtype : Set (ModGL t.tag K)) *
          (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
        (graphFixedParabolic t K σ.toRingHom Set.univ : Set (ModGL t.tag K)) ∧
      (graphFixedParabolic t K σ.toRingHom Set.univ : Set (ModGL t.tag K)) =
        graphFixedRootGroup t K σ.toRingHom) := by
  have hσ := σ.surjective
  obtain ⟨-, -, -, -, -, hPuniv⟩ := fixed_standard_parabolic_cells t K σ
  have hBC : graphFixedRootBorel t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootBorel_le t K σ.toRingHom
  by_cases hMZ : M ≤ Subgroup.center (graphFixedRootGroup t K σ.toRingHom)
  · exact Or.inl hMZ
  right
  set M' := M.map (graphFixedRootGroup t K σ.toRingHom).subtype
  have hM'C : M' ≤ graphFixedRootGroup t K σ.toRingHom := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hnorm : ∀ g ∈ graphFixedRootGroup t K σ.toRingHom, ∀ x ∈ M', g * x * g⁻¹ ∈ M' := by
    rintro g hg _ ⟨m, hm, rfl⟩
    exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance m hm ⟨g, hg⟩, rfl⟩
  have hBN : graphFixedRootBorel t K σ.toRingHom ≤
      Subgroup.normalizer (M' : Set (ModGL t.tag K)) := fun b hb =>
    Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hnorm b (hBC hb) x hx, fun hx => by
      have := hnorm b⁻¹ (inv_mem (hBC hb)) _ hx
      simpa [mul_assoc] using this⟩
  have hprod : (M' : Set (ModGL t.tag K)) *
      (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      ((M' ⊔ graphFixedRootBorel t K σ.toRingHom : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left M' _ hBN).symm
  set A := M' ⊔ graphFixedRootBorel t K σ.toRingHom
  have hBA : graphFixedRootBorel t K σ.toRingHom ≤ A := le_sup_right
  have hAC : A ≤ graphFixedRootGroup t K σ.toRingHom := sup_le hM'C hBC
  have hA := eq_graphFixedParabolic_of_le hσ hBA hAC
  set J := {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ A}
  have hM'B : ¬ M' ≤ graphFixedRootBorel t K σ.toRingHom := by
    intro h
    apply hMZ
    rw [← (fixed_Borel_core_center t K σ).1]
    refine Subgroup.normal_le_normalCore.2 fun m hm => ?_
    rw [Subgroup.mem_subgroupOf]
    exact h ⟨m, hm, rfl⟩
  have hJne : J.Nonempty := by
    by_contra hJ
    rw [Set.not_nonempty_iff_eq_empty] at hJ
    apply hM'B
    have h0 : A = graphFixedRootBorel t K σ.toRingHom := by
      rw [hA, hJ, graphFixedParabolic_empty]
    rw [← h0]
    exact le_sup_left
  have hJu : J = Set.univ := by
    by_contra hJu
    obtain ⟨a, ha, b, hb, -, hl2, hl3⟩ := (connected_weyl_diagram t.foldedTag).2.2 J hJne hJu
    have hra := t.orbitReflection_mem a
    have hrb := t.orbitReflection_mem b
    have hrba : t.orbitReflection b * t.orbitReflection a ∈ relWeylTwist t := mul_mem hrb hra
    have hrbab : t.orbitReflection b * t.orbitReflection a * t.orbitReflection b ∈
        relWeylTwist t := mul_mem hrba hrb
    have h1 : t.orbitLength (t.orbitReflection a) = 1 := by
      have := orbitLength_list_prod t [a]
      rwa [List.map_singleton, List.prod_singleton, CoxeterSystem.wordProd_singleton,
        CoxeterSystem.length_simple] at this
    have h2 : t.orbitLength (t.orbitReflection b * t.orbitReflection a) = 2 := by
      have := orbitLength_list_prod t [b, a]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil] at this
      rw [this]
      exact hl2
    have h3 : t.orbitLength (t.orbitReflection b * t.orbitReflection a * t.orbitReflection b) =
        3 := by
      have := orbitLength_list_prod t [b, a, b]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, ← mul_assoc] at this
      rw [this]
      exact hl3
    have haA : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        (M' : Set (ModGL t.tag K)) *
          (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := by
      rw [hprod]
      exact ha
    obtain ⟨m, hm, u, hu, hmu⟩ := haA
    have hmD : m ∈ graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) := by
      have e : m = 1 * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * u⁻¹ := by
        rw [← hmu]
        group
      rw [e]
      exact mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (one_mem _) (inv_mem hu)
    have hbC : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) ∈
        graphFixedRootGroup t K σ.toRingHom := canonicalRep_mem_graphFixedRootGroup hrb
    have hx : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * m *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b))⁻¹ ∈ M' :=
      hnorm _ hbC m hm
    have hbinv : (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b))⁻¹ ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection b) := by
      have h := inv_graphFixedRootBruhatCell (K := K) (σ := σ.toRingHom) hrb
      rw [t.orbitReflection_inv] at h
      rw [← h]
      exact Set.inv_mem_inv.2 (canonicalRep_mem_graphFixedRootBruhatCell _)
    have hD : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) * m *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b))⁻¹ ∈
        graphFixedRootBruhatCell t K σ.toRingHom
          (t.orbitReflection b * t.orbitReflection a * t.orbitReflection b) := by
      rw [← graphFixedRootBruhatCell_mul_of_orbitLength_eq_add_one hσ hrba (by rw [h3, h2]),
        ← mul_graphFixedRootBruhatCell_of_pos hσ hra
          (forall_height_inv_smul_pos_of_orbitLength hra (by rw [h2, h1]))]
      exact Set.mul_mem_mul (Set.mul_mem_mul (canonicalRep_mem_graphFixedRootBruhatCell _) hmD)
        hbinv
    have hn := canonicalRep_mem_of_mem_graphFixedRootBruhatCell hBA hD
      (le_sup_left (b := graphFixedRootBorel t K σ.toRingHom) hx)
    have hω : ([b, a, b].map t.orbitReflection).prod =
        t.orbitReflection b * t.orbitReflection a * t.orbitReflection b := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    exact hb (fixed_reduced_word_Borel_extraction t K σ.toRingHom A hAC hBA _ hrbab
      (fun y hy => mul_mem (mul_mem hn (hBA hy)) (inv_mem hn)) [b, a, b] hω
      (by rw [h3]; rfl) b List.mem_cons_self)
  refine ⟨?_, by rw [hPuniv]⟩
  rw [hprod, hA, hJu]

end CFSG.LieType.Chevalley
