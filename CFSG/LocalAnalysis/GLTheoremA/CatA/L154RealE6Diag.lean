module

public import CFSG.RankThree.PartOne.KE6.E6LIso
public import CFSG.RankThree.PartOne.KE6.E6LStd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Isogeny

section Ext

variable {τ : Tag} {k : Type} [Field k]

@[expose] def e6DiagExt (b : Fin Tag.E6.rank → kˣ) : Fin τ.rank → kˣ :=
  fun j => if h : j.val < Tag.E6.rank then b ⟨j.val, h⟩ else 1

theorem e6DiagExt_inv (b : Fin Tag.E6.rank → kˣ) :
    e6DiagExt (τ := τ) b⁻¹ = (e6DiagExt b)⁻¹ := by
  funext j
  by_cases h : j.val < Tag.E6.rank <;> simp [e6DiagExt, h]

theorem rootDiagUnit_inv_eq (d : Fin τ.rank → kˣ) :
    (rootDiagUnit τ d)⁻¹ = rootDiagUnit τ d⁻¹ :=
  Units.ext rfl

variable [E6Sub τ] in
theorem e6DiagExt_e6Idx (b : Fin Tag.E6.rank → kˣ) (i : Fin Tag.E6.rank) :
    e6DiagExt (τ := τ) b (e6Idx i) = b i := by
  simp [e6DiagExt, e6Idx]

end Ext

section Torus

variable
  {τ : Tag} {k : Type} [Field k]

theorem rootDiagUnit_conj_mem_subsystemGroup (J : Set (Fin τ.rank)) (d : Fin τ.rank → kˣ)
    {q : ModGL τ k} (hq : q ∈ subsystemGroup τ k J) :
    rootDiagUnit τ d * q * (rootDiagUnit τ d)⁻¹ ∈ subsystemGroup τ k J := by
  rw [subsystemGroup] at hq ⊢
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [(root_diagonal_conjugation τ k d).1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
    · rw [(root_diagonal_conjugation τ k d).2.1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have e : rootDiagUnit τ d * (x * y) * (rootDiagUnit τ d)⁻¹ =
        (rootDiagUnit τ d * x * (rootDiagUnit τ d)⁻¹) *
          (rootDiagUnit τ d * y * (rootDiagUnit τ d)⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : rootDiagUnit τ d * x⁻¹ * (rootDiagUnit τ d)⁻¹ =
        (rootDiagUnit τ d * x * (rootDiagUnit τ d)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem rootDiagUnit_mem_normalizer_subsystemGroup (J : Set (Fin τ.rank)) (d : Fin τ.rank → kˣ) :
    rootDiagUnit τ d ∈ Subgroup.normalizer (subsystemGroup τ k J : Set (ModGL τ k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact rootDiagUnit_conj_mem_subsystemGroup J d
  · intro hh
    have := rootDiagUnit_conj_mem_subsystemGroup J d⁻¹ hh
    rw [← rootDiagUnit_inv_eq, inv_inv] at this
    have e : (rootDiagUnit τ d)⁻¹ * (rootDiagUnit τ d * h * (rootDiagUnit τ d)⁻¹) *
        rootDiagUnit τ d = h := by group
    rwa [e] at this

variable (τ k) in
@[expose] noncomputable def diagConj (d : Fin τ.rank → kˣ) :
    ↥(subsystemGroup τ k (e6Set τ)) →* ↥(subsystemGroup τ k (e6Set τ)) :=
  ((MulAut.conj (rootDiagUnit τ d)).toMonoidHom.comp
    (subsystemGroup τ k (e6Set τ)).subtype).codRestrict _ fun q =>
      rootDiagUnit_conj_mem_subsystemGroup _ d q.2

theorem coe_diagConj (d : Fin τ.rank → kˣ) (q : ↥(subsystemGroup τ k (e6Set τ))) :
    ((diagConj τ k d q : ↥(subsystemGroup τ k (e6Set τ))) : ModGL τ k) =
      rootDiagUnit τ d * (q : ModGL τ k) * (rootDiagUnit τ d)⁻¹ :=
  rfl

end Torus

section Gen

variable {τ : Tag} [E6Sub τ]
  {k : Type} [Field k]

theorem diagConj_xUnit (b : Fin Tag.E6.rank → kˣ) (i : Fin Tag.E6.rank) (c : k) :
    diagConj τ k (e6DiagExt b)
        ⟨xUnit τ k (e6Idx i) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) c⟩ =
      ⟨xUnit τ k (e6Idx i) ((b i : k) * c), xUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) _⟩ := by
  apply Subtype.ext
  rw [coe_diagConj, (root_diagonal_conjugation τ k _).1, e6DiagExt_e6Idx]

theorem diagConj_yUnit (b : Fin Tag.E6.rank → kˣ) (i : Fin Tag.E6.rank) (c : k) :
    diagConj τ k (e6DiagExt b)
        ⟨yUnit τ k (e6Idx i) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) c⟩ =
      ⟨yUnit τ k (e6Idx i) (((b i)⁻¹ : kˣ) * c),
        yUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) _⟩ := by
  apply Subtype.ext
  rw [coe_diagConj, (root_diagonal_conjugation τ k _).2.1, e6DiagExt_e6Idx]

end Gen

section Ad

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {k : Type} [Field k] [Finite k]

variable (τ k) in
@[expose] noncomputable def e6Ad : ↥(subsystemGroup τ k (e6Set τ)) →* ↥(adjointGroup Tag.E6 k) :=
  (e6Isogeny k).comp (m27Equiv τ k).toMonoidHom

theorem e6Ad_xUnit (i : Fin Tag.E6.rank) (c : k) :
    e6Ad τ k ⟨xUnit τ k (e6Idx i) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) c⟩ =
      xElement i c := by
  haveI := certificate123_of_kernel
  change e6Isogeny k (m27Equiv τ k _) = _
  rw [m27Equiv_apply, m27ResMin_xUnit, e6Isogeny_xm_single, eltElement_simpleRoot_E6]

theorem e6Ad_yUnit (i : Fin Tag.E6.rank) (c : k) :
    e6Ad τ k ⟨yUnit τ k (e6Idx i) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set i) c⟩ =
      yElement i c := by
  haveI := certificate123_of_kernel
  change e6Isogeny k (m27Equiv τ k _) = _
  rw [m27Equiv_apply, m27ResMin_yUnit, e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]

theorem e6Ad_surjective : Function.Surjective (e6Ad τ k) :=
  (e6Isogeny_surjective k).comp (m27Equiv τ k).surjective

theorem e6Ad_ne_one : ∃ q, e6Ad τ k q ≠ 1 := by
  obtain ⟨g, hg⟩ := e6Isogeny_ne_one k
  exact ⟨(m27Equiv τ k).symm g, by simpa [e6Ad] using hg⟩

theorem e6Ad_diagConj (b : Fin Tag.E6.rank → kˣ) (q : ↥(subsystemGroup τ k (e6Set τ))) :
    ((e6Ad τ k (diagConj τ k (e6DiagExt b) q) : ↥(adjointGroup Tag.E6 k)) :
        ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 b * ((e6Ad τ k q : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) *
        (rootDiagUnit Tag.E6 b)⁻¹ := by
  have key : (adjointGroup Tag.E6 k).subtype.comp
      ((e6Ad τ k).comp (diagConj τ k (e6DiagExt (τ := τ) b))) =
      (MulAut.conj (rootDiagUnit Tag.E6 b)).toMonoidHom.comp
        ((adjointGroup Tag.E6 k).subtype.comp (e6Ad τ k)) := by
    refine hom_ext_Q (fun i c => ?_) (fun i c => ?_)
    · simp only [MonoidHom.comp_apply, diagConj_xUnit, e6Ad_xUnit, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, Subgroup.subtype_apply]
      exact ((root_diagonal_conjugation Tag.E6 k b).1 i c).symm
    · simp only [MonoidHom.comp_apply, diagConj_yUnit, e6Ad_yUnit, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, Subgroup.subtype_apply]
      exact ((root_diagonal_conjugation Tag.E6 k b).2.1 i c).symm
  exact DFunLike.congr_fun key q

theorem e6Ad_conj_rel (b : Fin Tag.E6.rank → kˣ) (Y X X' : ↥(subsystemGroup τ k (e6Set τ)))
    (h : (rootDiagUnit τ (e6DiagExt b) * (Y : ModGL τ k)) * (X : ModGL τ k) *
      (rootDiagUnit τ (e6DiagExt b) * (Y : ModGL τ k))⁻¹ = (X' : ModGL τ k)) :
    ((e6Ad τ k X' : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 b * ((e6Ad τ k Y : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) *
        ((e6Ad τ k X : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) *
        ((e6Ad τ k Y : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k)⁻¹ *
          (rootDiagUnit Tag.E6 b)⁻¹ := by
  have hrel : diagConj τ k (e6DiagExt b) (Y * X * Y⁻¹) = X' := by
    apply Subtype.ext
    rw [coe_diagConj, ← h]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h2 := e6Ad_diagConj (τ := τ) b (Y * X * Y⁻¹)
  rw [hrel] at h2
  rw [h2]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Ad

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
