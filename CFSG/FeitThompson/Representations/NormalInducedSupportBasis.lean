module

public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace NormalInducedSupportBasis

variable {L : Type*} [Group L]

def classFunSupportedOn (H : Subgroup L) : Submodule ℂ (L → ℂ) where
  carrier := {f | f ∈ classFun L ∧ ∀ l ∉ H, f l = 0}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun l hl => by simp [hf.2 l hl, hg.2 l hl]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, fun l hl => by simp [hf.2 l hl]⟩

theorem mem_classFunSupportedOn {H : Subgroup L} {f : L → ℂ} :
    f ∈ classFunSupportedOn H ↔ f ∈ classFun L ∧ ∀ l ∉ H, f l = 0 := Iff.rfl

theorem classFunSupportedOn_le_classFun (H : Subgroup L) :
    classFunSupportedOn H ≤ classFun L := fun _ hf => hf.1

theorem mem_classFun_of_mem_classFunSupportedOn {H : Subgroup L} {f : L → ℂ}
    (hf : f ∈ classFunSupportedOn H) : f ∈ classFun L := hf.1

theorem eq_zero_of_mem_classFunSupportedOn_of_notMem {H : Subgroup L} {f : L → ℂ}
    (hf : f ∈ classFunSupportedOn H) {l : L} (hl : l ∉ H) : f l = 0 := hf.2 l hl

variable [Fintype L]

omit [Group L] in
private theorem linearIndependent_of_orthogonal {ι : Type*} {v : ι → L → ℂ}
    (horth : ∀ i j, i ≠ j → cfInner (v i) (v j) = 0)
    (hne : ∀ i, cfInner (v i) (v i) ≠ 0) : LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  have h0 : cfInner (∑ i ∈ s, g i • v i) (v j) = 0 := by rw [hg, cfInner_zero_left]
  rw [cfInner_sum_left] at h0
  rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => by
    rw [cfInner_smul_left, horth i j hij, mul_zero]), cfInner_smul_left] at h0
  exact (mul_eq_zero.1 h0).resolve_right (hne j)

theorem indClassFun_sum (H : Subgroup L) {ι : Type*} (s : Finset ι) (g : ι → H → ℂ) :
    indClassFun H (∑ i ∈ s, g i) = ∑ i ∈ s, indClassFun H (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, indClassFun_add, ih]

theorem indClassFun_resClassFun (H : Subgroup L) [H.Normal] {f : L → ℂ}
    (hf : f ∈ classFun L) (hf0 : ∀ l ∉ H, f l = 0) :
    indClassFun H (resClassFun H f) = (H.index : ℂ) • f := by
  funext y
  by_cases hy : y ∈ H
  · rw [indClassFun_eq_sum_extendByZero]
    have key : ∀ x : L, extendByZero H (resClassFun H f) (x⁻¹ * y * x) = f y := by
      intro x
      have hmem : x⁻¹ * y * x ∈ H := by simpa using ‹H.Normal›.conj_mem y hy x⁻¹
      rw [show x⁻¹ * y * x = ((⟨x⁻¹ * y * x, hmem⟩ : H) : L) from rfl,
        extendByZero_apply_coe, resClassFun_apply]
      exact classFun.apply_eq_of_isConj hf (isConj_iff.2 ⟨x, by group⟩)
    have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Nat.card_eq_fintype_card, Pi.smul_apply, smul_eq_mul,
      ← Subgroup.index_mul_card H]
    push_cast
    field_simp
  · rw [indClassFun_eq_zero_of_notMem H _ hy, Pi.smul_apply, hf0 y hy, smul_zero]

theorem eq_inv_index_smul_indClassFun_resClassFun (H : Subgroup L) [H.Normal] {f : L → ℂ}
    (hf : f ∈ classFunSupportedOn H) :
    f = ((H.index : ℂ)⁻¹) • indClassFun H (resClassFun H f) := by
  rw [indClassFun_resClassFun H hf.1 hf.2, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero), one_smul]

instance finite_indFam_Irr (H : Subgroup L) : Finite (indFam H (Irr H)) :=
  (indFam_finite H finite_Irr).to_subtype

theorem indFam_subset_classFunSupportedOn (H : Subgroup L) [H.Normal] :
    indFam H (Irr H) ⊆ (classFunSupportedOn H : Set (L → ℂ)) := by
  intro f hf
  obtain ⟨θ, -, rfl⟩ := (mem_indFam H).1 hf
  exact ⟨indClassFun_mem_classFun H θ, fun l hl => indClassFun_eq_zero_of_notMem H θ hl⟩

theorem exists_cfInner_self_eq_of_mem_indFam (H : Subgroup L) [H.Normal] {ξ : L → ℂ}
    (hξ : ξ ∈ indFam H (Irr H)) : ∃ n : ℕ, 0 < n ∧ cfInner ξ ξ = (n : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFam H).1 hξ
  exact ⟨H.relIndex (inertiaGroup H θ),
    Nat.pos_of_ne_zero (NormalInducedFamily.relIndex_inertiaGroup_ne_zero H θ),
    cfInner_self_indClassFun H hθ⟩

theorem cfInner_self_ne_zero_of_mem_indFam (H : Subgroup L) [H.Normal] {ξ : L → ℂ}
    (hξ : ξ ∈ indFam H (Irr H)) : cfInner ξ ξ ≠ 0 := by
  obtain ⟨n, hn, hne⟩ := exists_cfInner_self_eq_of_mem_indFam H hξ
  rw [hne]
  exact Nat.cast_ne_zero.2 hn.ne'

theorem span_indFam_eq (H : Subgroup L) [H.Normal] :
    Submodule.span ℂ (indFam H (Irr H)) = classFunSupportedOn H := by
  classical
  have _ : Fintype (H : Type _) := Fintype.ofFinite _
  refine le_antisymm (Submodule.span_le.2 (indFam_subset_classFunSupportedOn H)) ?_
  intro f hfm
  obtain ⟨hf, hf0⟩ := mem_classFunSupportedOn.1 hfm
  have : Fintype (Irr (H : Type _)) := Fintype.ofFinite _
  set c : Irr (H : Type _) → ℂ := fun θ => cfInner (resClassFun H f) (θ : H → ℂ) with hc
  have hres : resClassFun H f = ∑ θ : Irr (H : Type _), c θ • ((θ : Irr _) : H → ℂ) :=
    classFun.coe_eq_sum_cfInner_smul (⟨resClassFun H f, resClassFun_mem_classFun H hf⟩ : classFun H)
  have hind : (H.index : ℂ) • f
      = ∑ θ : Irr (H : Type _), c θ • indClassFun H ((θ : Irr _) : H → ℂ) := by
    rw [← indClassFun_resClassFun H hf hf0, hres, indClassFun_sum]
    exact Finset.sum_congr rfl fun θ _ => indClassFun_smul _ _ _
  have hmem : (H.index : ℂ) • f ∈ Submodule.span ℂ (indFam H (Irr H)) := by
    rw [hind]
    exact Submodule.sum_mem _ fun θ _ => Submodule.smul_mem _ _
      (Submodule.subset_span (indClassFun_mem_indFam H θ.2))
  have hne : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  have h2 := Submodule.smul_mem _ ((H.index : ℂ)⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2

def toClassFunSupportedOn (H : Subgroup L) [H.Normal] (ξ : indFam H (Irr H)) :
    classFunSupportedOn H :=
  ⟨(ξ : L → ℂ), indFam_subset_classFunSupportedOn H ξ.2⟩

@[simp] theorem coe_toClassFunSupportedOn (H : Subgroup L) [H.Normal]
    (ξ : indFam H (Irr H)) : (toClassFunSupportedOn H ξ : L → ℂ) = (ξ : L → ℂ) := (rfl)

theorem linearIndependent_toClassFunSupportedOn (H : Subgroup L) [H.Normal] :
    LinearIndependent ℂ (toClassFunSupportedOn H) := by
  refine LinearIndependent.of_comp (classFunSupportedOn H).subtype ?_
  exact linearIndependent_of_orthogonal
    (fun ξ η hξη => NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H ξ.2 η.2
      fun h => hξη (Subtype.ext h))
    fun ξ => cfInner_self_ne_zero_of_mem_indFam H ξ.2

theorem span_range_toClassFunSupportedOn (H : Subgroup L) [H.Normal] :
    Submodule.span ℂ (Set.range (toClassFunSupportedOn H)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  have himg : (classFunSupportedOn H).subtype '' Set.range (toClassFunSupportedOn H)
      = indFam H (Irr H) := by
    rw [← Set.range_comp]
    exact Subtype.range_coe
  have hmap : (Submodule.span ℂ (Set.range (toClassFunSupportedOn H))).map
      (classFunSupportedOn H).subtype = classFunSupportedOn H := by
    rw [Submodule.map_span, himg, span_indFam_eq]
  have hx : (x : L → ℂ) ∈ (Submodule.span ℂ (Set.range (toClassFunSupportedOn H))).map
      (classFunSupportedOn H).subtype := by rw [hmap]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  exact Subtype.ext hyx ▸ hy

noncomputable def basisIndFam (H : Subgroup L) [H.Normal] :
    Module.Basis (indFam H (Irr H)) ℂ (classFunSupportedOn H) :=
  Module.Basis.mk (linearIndependent_toClassFunSupportedOn H)
    (span_range_toClassFunSupportedOn H).ge

@[simp] theorem basisIndFam_apply (H : Subgroup L) [H.Normal] (ξ : indFam H (Irr H)) :
    basisIndFam H ξ = toClassFunSupportedOn H ξ := by
  rw [basisIndFam, Module.Basis.mk_apply]

theorem cfInner_basisIndFam_eq_zero_of_ne (H : Subgroup L) [H.Normal]
    {ξ η : indFam H (Irr H)} (hne : ξ ≠ η) :
    cfInner (basisIndFam H ξ : L → ℂ) (basisIndFam H η : L → ℂ) = 0 := by
  rw [basisIndFam_apply, basisIndFam_apply, coe_toClassFunSupportedOn,
    coe_toClassFunSupportedOn]
  exact NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H ξ.2 η.2 fun h => hne (Subtype.ext h)

theorem coe_eq_sum_cfInner_div_smul (H : Subgroup L) [H.Normal]
    [Fintype (indFam H (Irr H))] (f : classFunSupportedOn H) :
    (f : L → ℂ) = ∑ ξ : indFam H (Irr H),
      (cfInner (f : L → ℂ) (ξ : L → ℂ) / cfInner (ξ : L → ℂ) (ξ : L → ℂ)) • (ξ : L → ℂ) := by
  classical
  set r : indFam H (Irr H) → ℂ := fun ξ => (basisIndFam H).repr f ξ with hr
  have hf : (f : L → ℂ) = ∑ ξ : indFam H (Irr H), r ξ • (ξ : L → ℂ) := by
    have h := congrArg (fun x : classFunSupportedOn H => (x : L → ℂ))
      ((basisIndFam H).sum_repr f)
    simpa [Submodule.coe_sum] using h.symm
  have key : ∀ ξ : indFam H (Irr H),
      r ξ = cfInner (f : L → ℂ) (ξ : L → ℂ) / cfInner (ξ : L → ℂ) (ξ : L → ℂ) := by
    intro ξ
    have h1 : cfInner (f : L → ℂ) (ξ : L → ℂ) = r ξ * cfInner (ξ : L → ℂ) (ξ : L → ℂ) := by
      rw [hf, cfInner_sum_left, Finset.sum_eq_single_of_mem ξ (Finset.mem_univ ξ)
        (fun η _ hηξ => by
          rw [cfInner_smul_left,
            NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H η.2 ξ.2
              (fun h => hηξ (Subtype.ext h)), mul_zero]),
        cfInner_smul_left]
    rw [h1, mul_div_assoc, div_self (cfInner_self_ne_zero_of_mem_indFam H ξ.2), mul_one]
  exact hf.trans (Finset.sum_congr rfl fun ξ _ => by rw [key ξ])

end NormalInducedSupportBasis

end

end CFSG.FeitThompson
