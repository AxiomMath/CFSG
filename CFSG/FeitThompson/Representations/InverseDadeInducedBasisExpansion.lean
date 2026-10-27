module

public import CFSG.FeitThompson.Representations.DadeReciprocityAveraging
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.RegularCharOrthogonalInducedBasis
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.DadeAveragingClassFunction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate NormalInducedSupportBasis

noncomputable def puncturedDiff {X : Type*} [One X] (ξ₀ ξ : X → ℂ) : X → ℂ :=
  ξ - (ξ 1 / ξ₀ 1) • ξ₀

theorem puncturedDiff_apply {X : Type*} [One X] (ξ₀ ξ : X → ℂ) (x : X) :
    puncturedDiff ξ₀ ξ x = ξ x - (ξ 1 / ξ₀ 1) * ξ₀ x := (rfl)

theorem puncturedDiff_eq {X : Type*} [One X] (ξ₀ ξ : X → ℂ) :
    puncturedDiff ξ₀ ξ = ξ - (ξ 1 / ξ₀ 1) • ξ₀ := (rfl)

theorem puncturedDiff_one {X : Type*} [One X] {ξ₀ ξ : X → ℂ} (h : ξ₀ 1 ≠ 0) :
    puncturedDiff ξ₀ ξ 1 = 0 := by
  rw [puncturedDiff_apply, div_mul_cancel₀ _ h, sub_self]

@[simp]
theorem puncturedDiff_self {X : Type*} [One X] {ξ₀ : X → ℂ} (h : ξ₀ 1 ≠ 0) :
    puncturedDiff ξ₀ ξ₀ = 0 := by
  funext x
  rw [puncturedDiff_apply, div_self h, one_mul, sub_self, Pi.zero_apply]

theorem apply_one_ne_zero_of_mem_indFam {M : Type*} [Group M] [Fintype M] (N : Subgroup M)
    {ξ : M → ℂ} (hξ : ξ ∈ indFam N (Irr ↥N)) : ξ 1 ≠ 0 := by
  obtain ⟨d, hd, -, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_indFam N hξ
  rw [hd1]
  exact Nat.cast_ne_zero.2 hd.ne'

theorem conj_apply_one_of_mem_indFam {M : Type*} [Group M] [Fintype M] (N : Subgroup M)
    {ξ : M → ℂ} (hξ : ξ ∈ indFam N (Irr ↥N)) : conj (ξ 1) = ξ 1 := by
  obtain ⟨d, -, -, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_indFam N hξ
  rw [hd1, Complex.conj_natCast]

private theorem sub_sub_mul_neg_div_cancel {ra sz za nz z1 : ℂ} (hnz : nz ≠ 0) (hz1 : z1 ≠ 0) :
    ra - sz / nz * za - sz / z1 * -(z1 / nz * za) = ra := by
  field_simp
  ring

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {A : Set G} {J : G → Subgroup G} {χ : G → ℂ} {N : Subgroup ↥L}

omit [Fintype G] [Fintype ↥L] in
theorem coe_mem_iff_of_eq_sdiff (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    (x : ↥L) : (x : G) ∈ A ↔ x ∈ N ∧ x ≠ 1 := by
  subst hA
  simp

omit [Fintype G] in
theorem puncturedDiff_mem_dadeDomain [N.Normal]
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    {ξ₀ ξ : ↥L → ℂ} (hξ₀ : ξ₀ ∈ indFam N (Irr ↥N)) (hξ : ξ ∈ indFam N (Irr ↥N)) :
    puncturedDiff ξ₀ ξ ∈ dadeDomain L A := by
  refine mem_dadeDomain.2 ⟨?_, ?_⟩
  · rw [puncturedDiff_eq]
    exact Submodule.sub_mem _
      (mem_classFunSupportedOn.1 (indFam_subset_classFunSupportedOn N hξ)).1
      (Submodule.smul_mem _ _
        (mem_classFunSupportedOn.1 (indFam_subset_classFunSupportedOn N hξ₀)).1)
  · intro x hx
    rw [coe_mem_iff_of_eq_sdiff hA] at hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact puncturedDiff_one (apply_one_ne_zero_of_mem_indFam N hξ₀)
    · have hxN : x ∉ N := fun h => hx ⟨h, hx1⟩
      rw [puncturedDiff_apply, eq_zero_of_mem_indFam_of_notMem N hξ hxN,
        eq_zero_of_mem_indFam_of_notMem N hξ₀ hxN, mul_zero, sub_zero]

omit [Fintype G] in
noncomputable def puncturedDiffDade [N.Normal]
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    (ξ₀ ξ : indFam N (Irr ↥N)) : dadeDomain L A :=
  ⟨puncturedDiff (ξ₀ : ↥L → ℂ) (ξ : ↥L → ℂ), puncturedDiff_mem_dadeDomain hA ξ₀.2 ξ.2⟩

omit [Fintype G] in
@[simp]
theorem coe_puncturedDiffDade [N.Normal]
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    (ξ₀ ξ : indFam N (Irr ↥N)) :
    (puncturedDiffDade hA ξ₀ ξ : ↥L → ℂ) = puncturedDiff (ξ₀ : ↥L → ℂ) (ξ : ↥L → ℂ) := (rfl)

omit [Fintype ↥L] in
theorem dadeAverage_restrict_mem_classFunSupportedOn (hD : IsDadeData L A J)
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1}) (hχ : χ ∈ classFun G) :
    (fun y : ↥L => dadeAverage A J χ (y : G)) ∈ classFunSupportedOn N :=
  mem_classFunSupportedOn.2 ⟨dadeAverage_restrict_mem_classFun hD hχ, fun x hx =>
    dadeAverage_eq_zero_of_notMem fun hcc => hx ((coe_mem_iff_of_eq_sdiff hA x).1 hcc).1⟩

theorem dadeAverage_eq_sum_conj_cfInner_dadeMap_puncturedDiff
    [N.Normal] [Fintype (indFam N (Irr ↥N))] (hD : IsDadeData L A J)
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    (hχ : χ ∈ classFun G) (ξ₀ : indFam N (Irr ↥N)) {a : ↥L} (ha : (a : G) ∈ A) :
    dadeAverage A J χ (a : G)
      = ∑ ξ ∈ Finset.univ.erase ξ₀,
          conj (cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ ξ) : classFun G) : G → ℂ) χ)
            * (ξ : ↥L → ℂ) a / cfInner (ξ : ↥L → ℂ) (ξ : ↥L → ℂ) := by
  classical
  set r : ↥L → ℂ := fun y => dadeAverage A J χ (y : G) with hrdef
  have hrmem : r ∈ classFunSupportedOn N :=
    dadeAverage_restrict_mem_classFunSupportedOn hD hA hχ
  set n : indFam N (Irr ↥N) → ℂ := fun ξ => cfInner (ξ : ↥L → ℂ) (ξ : ↥L → ℂ) with hn
  set s : indFam N (Irr ↥N) → ℂ := fun ξ => cfInner r (ξ : ↥L → ℂ) with hs
  have hnne : ∀ ξ : indFam N (Irr ↥N), n ξ ≠ 0 :=
    fun ξ => cfInner_self_ne_zero_of_mem_indFam N ξ.2
  have hone : ∀ ξ : indFam N (Irr ↥N), (ξ : ↥L → ℂ) 1 ≠ 0 :=
    fun ξ => apply_one_ne_zero_of_mem_indFam N ξ.2
  have honeconj : ∀ ξ : indFam N (Irr ↥N), conj ((ξ : ↥L → ℂ) 1) = (ξ : ↥L → ℂ) 1 :=
    fun ξ => conj_apply_one_of_mem_indFam N ξ.2
  have hexp : r = ∑ ξ : indFam N (Irr ↥N), (s ξ / n ξ) • (ξ : ↥L → ℂ) :=
    coe_eq_sum_cfInner_div_smul N ⟨r, hrmem⟩
  have hra : r a = ∑ ξ : indFam N (Irr ↥N), s ξ / n ξ * (ξ : ↥L → ℂ) a := by
    have h := congrFun hexp a
    simpa using h
  have hcoef : ∀ ξ : indFam N (Irr ↥N),
      conj (cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ ξ) : classFun G) : G → ℂ) χ)
        = s ξ - ((ξ : ↥L → ℂ) 1 / (ξ₀ : ↥L → ℂ) 1) * s ξ₀ := by
    intro ξ
    rw [cfInner_dadeMap_eq_cfInner_dadeAverage hD _ hχ]
    change conj (cfInner ((puncturedDiffDade hA ξ₀ ξ : ↥L → ℂ)) r) = _
    rw [coe_puncturedDiffDade, puncturedDiff_eq, cfInner_sub_left, cfInner_smul_left,
      map_sub, map_mul, conj_cfInner, conj_cfInner, map_div₀, honeconj ξ, honeconj ξ₀]
  have hane : a ≠ 1 := by
    intro h
    exact hD.ne_one ha (by rw [h]; rfl)
  have hreg : ∑ ξ : indFam N (Irr ↥N), ((ξ : ↥L → ℂ) 1 / n ξ) * (ξ : ↥L → ℂ) a = 0 := by
    have h := congrFun (leftRegular_character_eq_sum_indFam (L := ↥L) N) a
    rw [leftRegular_character_of_ne_one hane] at h
    have h2 : (0 : ℂ) = ∑ ξ : indFam N (Irr ↥N), ((ξ : ↥L → ℂ) 1 / n ξ) * (ξ : ↥L → ℂ) a := by
      rw [h]; simp [hn]
    exact h2.symm
  have hterm : ∀ ξ : indFam N (Irr ↥N),
      conj (cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ ξ) : classFun G) : G → ℂ) χ)
          * (ξ : ↥L → ℂ) a / n ξ
        = s ξ / n ξ * (ξ : ↥L → ℂ) a
          - (s ξ₀ / (ξ₀ : ↥L → ℂ) 1) * (((ξ : ↥L → ℂ) 1 / n ξ) * (ξ : ↥L → ℂ) a) := by
    intro ξ
    rw [hcoef ξ]
    field_simp
  rw [Finset.sum_congr rfl fun ξ _ => hterm ξ, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hg : ∑ ξ ∈ Finset.univ.erase ξ₀, s ξ / n ξ * (ξ : ↥L → ℂ) a
      = r a - s ξ₀ / n ξ₀ * (ξ₀ : ↥L → ℂ) a := by
    rw [hra, ← Finset.sum_erase_add _ _ (Finset.mem_univ ξ₀)]
    ring
  have hh : ∑ ξ ∈ Finset.univ.erase ξ₀, ((ξ : ↥L → ℂ) 1 / n ξ) * (ξ : ↥L → ℂ) a
      = -(((ξ₀ : ↥L → ℂ) 1 / n ξ₀) * (ξ₀ : ↥L → ℂ) a) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (indFam N (Irr ↥N)))
      (fun ξ : indFam N (Irr ↥N) => ((ξ : ↥L → ℂ) 1 / n ξ) * (ξ : ↥L → ℂ) a)
      (Finset.mem_univ ξ₀)
    rw [hreg] at h
    linear_combination h
  rw [hg, hh]
  change r a = _
  exact (sub_sub_mul_neg_div_cancel (hnne ξ₀) (hone ξ₀)).symm

theorem dadeAverage_eq_sum_conj_cfInner_dadeMap_puncturedDiff'
    [N.Normal] [Fintype (indFam N (Irr ↥N))] (hD : IsDadeData L A J)
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    (hχ : χ ∈ classFun G) (ξ₀ : indFam N (Irr ↥N)) {a : ↥L} (haN : a ∈ N) (ha1 : a ≠ 1) :
    dadeAverage A J χ (a : G)
      = ∑ ξ ∈ Finset.univ.erase ξ₀,
          conj (cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ ξ) : classFun G) : G → ℂ) χ)
            * (ξ : ↥L → ℂ) a / cfInner (ξ : ↥L → ℂ) (ξ : ↥L → ℂ) :=
  dadeAverage_eq_sum_conj_cfInner_dadeMap_puncturedDiff hD hA hχ ξ₀
    ((coe_mem_iff_of_eq_sdiff hA a).2 ⟨haN, ha1⟩)

end CFSG.FeitThompson
