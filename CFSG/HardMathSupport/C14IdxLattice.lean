module

public import CFSG.HardMathSupport.C14IdxDet
public import TauCeti.Algebra.Group.AddSubgroup.RationalSpan

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.C14Idx

namespace CFSG.HardMathSupport.C14IdxDet

private abbrev toRatQ {ι : Type*} (v : ι → ℤ) : ι → ℚ := ((↑) : ℤ → ℚ) ∘ v

private theorem toRatQ_apply {ι : Type*} (v : ι → ℤ) (i : ι) : toRatQ v i = (v i : ℚ) := rfl

private theorem toRatQ_single {ι : Type*} [DecidableEq ι] (i : ι) :
    toRatQ (Pi.single i 1) = (Pi.single i (1 : ℚ) : ι → ℚ) := by
  ext j
  by_cases h : j = i <;> simp [toRatQ, Pi.single_apply, h]

private noncomputable def formQ (τ : Tag) : LinearMap.BilinForm ℚ (Fin τ.rank → ℚ) :=
  Matrix.toBilin' (τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ))

private noncomputable def sharp (τ : Tag) : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ) where
  toFun x := fun i => ∑ j, (τ.symmetrizedCartan j i : ℚ) * x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    change ∑ j, (τ.symmetrizedCartan j i : ℚ) * (c * x j) =
      c * ∑ j, (τ.symmetrizedCartan j i : ℚ) * x j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private noncomputable def spanΨ {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) :
    Submodule ℚ (Fin τ.rank → ℚ) :=
  Submodule.span ℚ (toRatQ '' Ψ)

private theorem sharp_apply (τ : Tag) (x : Fin τ.rank → ℚ) (i : Fin τ.rank) :
    sharp τ x i = ∑ j, (τ.symmetrizedCartan j i : ℚ) * x j := rfl

private theorem formQ_toRat (τ : Tag) (u v : Fin τ.rank → ℤ) :
    formQ τ (toRatQ u) (toRatQ v) = (iform u v : ℚ) := by
  rw [formQ, Matrix.toBilin'_apply]
  simp only [toRatQ, Function.comp_apply, Matrix.map_apply, iform, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem formQ_single (τ : Tag) (x : Fin τ.rank → ℚ) (i : Fin τ.rank) :
    formQ τ x (Pi.single i 1) = sharp τ x i := by
  rw [formQ, Matrix.toBilin'_apply, sharp_apply, Finset.sum_comm]
  simp only [Matrix.map_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp only [Pi.single_eq_same, Int.cast_one, mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem formQ_eq_sum (τ : Tag) (x u : Fin τ.rank → ℚ) :
    formQ τ x u = ∑ i, u i * formQ τ x (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (u i) = u i • (Pi.single i (1 : ℚ) : Fin τ.rank → ℚ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul]

private theorem formQ_self_eq_sum (τ : Tag) (x : Fin τ.rank → ℚ) :
    formQ τ x x = ∑ i, x i * sharp τ x i := by
  rw [formQ_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formQ_single]

private theorem sum_mul_sharp_eq_formQ (τ : Tag) (u v : Fin τ.rank → ℚ) :
    ∑ i, u i * sharp τ v i = formQ τ v u := by
  rw [formQ_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formQ_single]

private theorem formQ_isSymm (τ : Tag) :
    (formQ τ).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [formQ, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
  simp only [Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_symm τ j i]
  ring

private theorem posDef_symmetrizedCartan_int (τ : Tag) :
    τ.symmetrizedCartan.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact (symmetrizedCartan_symm τ i j).symm
  · have hpos := iform_self_pos (τ := τ) hx
    have e : dotProduct (star x) (Matrix.mulVec τ.symmetrizedCartan x) = iform x x := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, iform, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rwa [e]

private theorem posDef_symmetrizedCartan_rat (τ : Tag) :
    (τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ)).PosDef :=
  TauCeti.Matrix.posDef_map_intCast (posDef_symmetrizedCartan_int τ)

private theorem formQ_pos {τ : Tag}
    {x : Fin τ.rank → ℚ} (hx : x ≠ 0) : 0 < formQ τ x x := by
  have hPD := posDef_symmetrizedCartan_rat τ
  have h := hPD.dotProduct_mulVec_pos hx
  simpa [formQ, Matrix.toBilin'_apply', star_trivial] using h

private theorem formQ_self_eq_zero {τ : Tag}
    {x : Fin τ.rank → ℚ} (h : formQ τ x x = 0) : x = 0 := by
  by_contra hx
  have hpos := formQ_pos (τ := τ) hx
  rw [h] at hpos
  exact lt_irrefl 0 hpos

private theorem sharp_injective (τ : Tag) :
    Function.Injective (sharp τ) := by
  intro x y hxy
  have h0 : sharp τ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hself : formQ τ (x - y) (x - y) = 0 := by
    rw [formQ_self_eq_sum]
    simp [h0]
  exact sub_eq_zero.1 (formQ_self_eq_zero hself)

private theorem restrict_nondegenerate (τ : Tag)
    (Ψ : Set (Fin τ.rank → ℤ)) :
    ((formQ τ).restrict (spanΨ Ψ)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply formQ_self_eq_zero
    simpa using hx x
  · apply Subtype.ext
    apply formQ_self_eq_zero
    simpa using hx x

private theorem isCompl_span_orthogonal (τ : Tag)
    (Ψ : Set (Fin τ.rank → ℤ)) :
    IsCompl (spanΨ Ψ) ((formQ τ).orthogonal (spanΨ Ψ)) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (formQ_isSymm τ).isRefl
    (restrict_nondegenerate τ Ψ)

private theorem sharp_toRat_eq_smul_coroot {τ : Tag}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    sharp τ (toRatQ β) = ((iform β β : ℚ) / 2) • toRatQ (C14Idx.corootVec β) := by
  have hpos : (iform β β : ℚ) ≠ 0 := by
    exact_mod_cast (iform_self_pos_of_isRoot hβ).ne'
  ext i
  have hsharp : sharp τ (toRatQ β) i = (iform β (Pi.single i 1) : ℚ) := by
    rw [← formQ_single, ← toRatQ_single, formQ_toRat]
  have hcor : (C14Idx.corootVec β i : ℚ) =
      2 * (iform β (Pi.single i 1) : ℚ) / (iform β β : ℚ) := by
    have hmul : C14Idx.corootVec β i * iform β β = 2 * iform β (Pi.single i 1) := by
      simpa [C14Idx.corootVec] using corootPair_mul hβ (Pi.single i 1)
    rw [eq_div_iff hpos]
    exact_mod_cast hmul
  rw [hsharp, Pi.smul_apply, smul_eq_mul, toRatQ_apply, hcor]
  field_simp

private theorem sharp_mem_span_coroot {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ α ∈ Ψ, IsRoot τ α) {v : Fin τ.rank → ℚ} (hv : v ∈ spanΨ Ψ) :
    sharp τ v ∈ Submodule.span ℚ (toRatQ '' (C14Idx.corootVec '' Ψ)) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨β, hβ, rfl⟩
    rw [sharp_toRat_eq_smul_coroot (hΨ β hβ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨C14Idx.corootVec β, ⟨β, hβ, rfl⟩, rfl⟩)
  · simp
  · intro x y hx hy hx' hy'
    rw [map_add]
    exact Submodule.add_mem _ hx' hy'
  · intro c x hx hx'
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx'

private theorem mem_span_perpOf_of_dot_eq_zero {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {x : Fin τ.rank → ℚ} (hx : ∀ α ∈ Ψ, ∑ i, (α i : ℚ) * x i = 0) :
    x ∈ Submodule.span ℚ (toRatQ '' {lam | PerpOf Ψ lam}) := by
  classical
  have htop : Submodule.span ℚ
      (toRatQ '' ((⊤ : AddSubgroup (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ))) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℚ) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Pi.single i (v i) = v i • (Pi.single i (1 : ℚ) : Fin τ.rank → ℚ) by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨Pi.single i 1, AddSubgroup.mem_top _, by rw [toRatQ_single]⟩
  obtain ⟨N, hN, z, hzmem, hz⟩ := TauCeti.AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span
    (P := ⊤) (x := x) (by rw [htop]; exact Submodule.mem_top)
  have hzperp : PerpOf Ψ z := by
    intro α hα
    have hcast : ((∑ i, α i * z i : ℤ) : ℚ) = 0 := by
      calc ((∑ i, α i * z i : ℤ) : ℚ)
          = ∑ i, (α i : ℚ) * (z i : ℚ) := by push_cast; ring
        _ = ∑ i, (α i : ℚ) * ((N : ℚ) * x i) := by
            refine Finset.sum_congr rfl fun i _ => by rw [hz i]
        _ = (N : ℚ) * ∑ i, (α i : ℚ) * x i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hx α hα, mul_zero]
    exact_mod_cast hcast
  have hzspan : toRatQ z ∈ Submodule.span ℚ (toRatQ '' {lam | PerpOf Ψ lam}) :=
    Submodule.subset_span ⟨z, hzperp, rfl⟩
  have hx_eq : x = (1 / (N : ℚ)) • toRatQ z := by
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    funext i
    rw [Pi.smul_apply, smul_eq_mul, toRatQ_apply, hz i]
    field_simp [hNq]
  rw [hx_eq]
  exact Submodule.smul_mem _ _ hzspan

private theorem sharp_mem_span_perpOf {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} {q : Fin τ.rank → ℚ}
    (hq : q ∈ (formQ τ).orthogonal (spanΨ Ψ)) :
    sharp τ q ∈ Submodule.span ℚ (toRatQ '' {lam | PerpOf Ψ lam}) := by
  refine mem_span_perpOf_of_dot_eq_zero (Ψ := Ψ) fun α hα => ?_
  have hmem : toRatQ α ∈ spanΨ Ψ := Submodule.subset_span ⟨α, hα, rfl⟩
  have h0 : formQ τ (toRatQ α) q = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hq) (toRatQ α) hmem
  rw [sum_mul_sharp_eq_formQ]
  change formQ τ q (toRatQ α) = 0
  rw [← (formQ_isSymm τ).eq (toRatQ α) q]
  exact h0

private theorem span_union_eq_top {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ α ∈ Ψ, IsRoot τ α) :
    Submodule.span ℚ (toRatQ '' ({lam | PerpOf Ψ lam} ∪ C14Idx.corootVec '' Ψ)) = ⊤ := by
  classical
  have hcompl := isCompl_span_orthogonal τ Ψ
  have hsurj : Function.Surjective (sharp τ) :=
    (LinearMap.injective_iff_surjective.1 (sharp_injective τ))
  have hle : (⊤ : Submodule ℚ (Fin τ.rank → ℚ)) ≤
      Submodule.span ℚ (toRatQ '' {lam | PerpOf Ψ lam}) ⊔
        Submodule.span ℚ (toRatQ '' (C14Idx.corootVec '' Ψ)) := by
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    have hy : y ∈ spanΨ Ψ ⊔ (formQ τ).orthogonal (spanΨ Ψ) := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hy
    rw [← hpq, map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (sharp_mem_span_coroot hΨ hp))
      (Submodule.mem_sup_left (sharp_mem_span_perpOf hq))
  rw [Set.image_union, Submodule.span_union]
  exact top_le_iff.1 hle

theorem exists_pos_nsmul_single_mem_closure_perp_coroot {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ α ∈ Ψ, IsRoot τ α) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N • Pi.single i 1 : Fin τ.rank → ℤ) ∈
      AddSubgroup.closure ({lam | PerpOf Ψ lam} ∪ C14Idx.corootVec '' Ψ) := by
  classical
  let S : Set (Fin τ.rank → ℤ) := {lam | PerpOf Ψ lam} ∪ C14Idx.corootVec '' Ψ
  have hspan : Submodule.span ℚ (toRatQ '' S) = ⊤ := span_union_eq_top hΨ
  have hex : ∀ i : Fin τ.rank, ∃ Ni : ℕ, 0 < Ni ∧
      ∃ p ∈ AddSubgroup.closure S, p = (Ni : ℤ) • Pi.single i 1 := by
    intro i
    have hxmem : (Pi.single i 1 : Fin τ.rank → ℚ) ∈
        Submodule.span ℚ (toRatQ '' (AddSubgroup.closure S)) := by
      have hle : Submodule.span ℚ (toRatQ '' S) ≤
          Submodule.span ℚ (toRatQ '' (AddSubgroup.closure S)) :=
        Submodule.span_mono (Set.image_mono AddSubgroup.subset_closure)
      rw [hspan] at hle
      exact hle Submodule.mem_top
    obtain ⟨Ni, hNi, p, hp, hpx⟩ :=
      TauCeti.AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span
        (P := AddSubgroup.closure S) (x := (Pi.single i 1 : Fin τ.rank → ℚ)) hxmem
    refine ⟨Ni, hNi, p, hp, ?_⟩
    ext j
    apply Int.cast_injective (α := ℚ)
    have h := hpx j
    rw [← toRatQ_single] at h
    simpa [Pi.smul_apply, toRatQ] using h
  choose Ni hNi pi hpi hpi_eq using hex
  refine ⟨∏ i, Ni i, Finset.prod_pos fun i _ => hNi i, fun i => ?_⟩
  have hdvd : Ni i ∣ ∏ j, Ni j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hdvd
  have hsingle : ((∏ j, Ni j : ℕ) • Pi.single i 1 : Fin τ.rank → ℤ) = k • pi i := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hk, congrFun (hpi_eq i) j]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hsingle]
  exact AddSubgroup.nsmul_mem _ (hpi i) k

end CFSG.HardMathSupport.C14IdxDet
