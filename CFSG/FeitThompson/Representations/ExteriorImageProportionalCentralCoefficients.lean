module

public import CFSG.FeitThompson.Representations.CentralLayerCharacterRegularDifference
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open scoped ComplexConjugate

section Aux

variable {K : Type*} [Fintype K]

theorem cfInner_zsmul_right (d : ℤ) (f h : K → ℂ) :
    cfInner f (d • h) = (d : ℂ) * cfInner f h := by
  rw [← Int.cast_smul_eq_zsmul ℂ d h, cfInner_smul_right]
  simp

variable [Group K]

theorem mul_cfInner_eq_mul_cfInner_of_forall_charSpanZero {S : Set (K → ℂ)} {g : K → ℂ}
    (hzero : ∀ f : charSpanZero S, cfInner g (f : K → ℂ) = 0)
    {ξ ξ' : K → ℂ} (hξ : ξ ∈ S) (hξ' : ξ' ∈ S) {d d' : ℤ}
    (hd : ξ 1 = (d : ℂ)) (hd' : ξ' 1 = (d' : ℂ)) :
    (d' : ℂ) * cfInner g ξ = (d : ℂ) * cfInner g ξ' := by
  have hcast : ((d' : ℤ) • ξ - (d : ℤ) • ξ' : K → ℂ) = (d' : ℂ) • ξ - (d : ℂ) • ξ' := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hmem : ((d' : ℤ) • ξ - (d : ℤ) • ξ' : K → ℂ) ∈ charSpanZero S := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span hξ))
      (Submodule.smul_mem _ _ (Submodule.subset_span hξ')), ?_⟩
    rw [hcast]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd, hd']
    ring
  have h : cfInner g ((d' : ℤ) • ξ - (d : ℤ) • ξ' : K → ℂ) = 0 := hzero ⟨_, hmem⟩
  rw [cfInner_sub_right, cfInner_zsmul_right, cfInner_zsmul_right, sub_eq_zero] at h
  exact h

end Aux

section Layer

variable {G : Type*} [Group G] {L : Subgroup G} {P Z : Subgroup ↥L}

theorem sum_smul_mem_span_irrTrivialOn [Finite ↥L] (b : (↥L → ℂ) → ℤ) :
    (∑ χ ∈ irrTrivialOnFinset Z, (b χ : ℂ) • χ) ∈ Submodule.span ℤ (irrTrivialOn Z) := by
  refine Submodule.sum_mem _ fun χ hχ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_irrTrivialOnFinset.1 hχ))

theorem exists_pos_apply_one_of_mem_indFamDetect [Fintype ↥L] {H : Subgroup ↥P} {ξ : ↥L → ℂ}
    (hξ : ξ ∈ indFamDetect P H) : ∃ d : ℕ, 0 < d ∧ ξ 1 = (d : ℂ) := by
  have h := indFamDetect_subset_indFam_irrChar P H hξ
  rw [← Irr_eq_irrChar] at h
  obtain ⟨d, hd, -, hval⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_indFam P h
  exact ⟨d, hd, hval⟩

theorem cfInner_eq_zero_of_mem_span_of_forall [Fintype G] {S : Set (↥L → ℂ)} {ψ : G → ℂ}
    (ν : Submodule.span ℤ S →+ virtualChars G)
    (horth : ∀ ξ, ∀ hξ : ξ ∈ S, cfInner ψ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0)
    (u : Submodule.span ℤ S) : cfInner ψ (ν u : G → ℂ) = 0 := by
  obtain ⟨u, hu⟩ := u
  induction hu using Submodule.span_induction with
  | mem x hx => exact horth x hx
  | zero =>
      have h0 : (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℤ S) = 0 := rfl
      rw [h0, map_zero]
      simpa using cfInner_zero_right ψ
  | add x y hx hy ihx ihy =>
      have he : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Submodule.span ℤ S)
          = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [he, map_add]
      have hc : ((ν ⟨x, hx⟩ + ν ⟨y, hy⟩ : virtualChars G) : G → ℂ)
          = (ν ⟨x, hx⟩ : G → ℂ) + (ν ⟨y, hy⟩ : G → ℂ) := by simp
      rw [hc, cfInner_add_right, ihx, ihy, add_zero]
  | smul c x hx ih =>
      have he : (⟨c • x, Submodule.smul_mem _ _ hx⟩ : Submodule.span ℤ S) = c • ⟨x, hx⟩ := rfl
      rw [he, map_zsmul]
      have hc : ((c • ν ⟨x, hx⟩ : virtualChars G) : G → ℂ) = c • (ν ⟨x, hx⟩ : G → ℂ) := by simp
      rw [hc, cfInner_zsmul_right, ih, mul_zero]

end Layer

section Main

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {P E Z : Subgroup ↥L} [P.Normal] [Z.Normal]

theorem exists_resClassFun_eq_add_smul_centralLayerWeightedChar
    (hZP : Z ≤ P) (hZc : Z ≤ centralizer (P : Set ↥L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) (hZ : Z ≠ ⊥)
    (ν : Submodule.span ℤ (indFamDetect P (Z.subgroupOf P)) →+ virtualChars G)
    (hν : ∀ f : charSpanZero (indFamDetect P (Z.subgroupOf P)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    {ψ : G → ℂ} (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect P (Z.subgroupOf P),
      cfInner ψ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0) :
    ∃ lam : ℚ, ∃ Ξ ∈ Submodule.span ℤ (irrTrivialOn Z),
      resClassFun L ψ
          = Ξ + (lam : ℂ) • centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) ∧
        ∀ z : ↥L, z ∈ Z → z ≠ 1 →
          ψ (1 : G) - ψ (z : G) = (lam : ℂ) * (Nat.card ↥P : ℂ) := by
  classical
  have hres : resClassFun L ψ ∈ Submodule.span ℤ (Irr ↥L) := by
    have h := comp_mem_span_Irr (X := ↥L) L.subtype hψ
    have he : ψ ∘ L.subtype = resClassFun L ψ := by funext x; simp
    rwa [he] at h
  obtain ⟨m, hmsum, hmcf⟩ := exists_intCast_finsetSum_of_mem_span_Irr hres
  have hψcf : ψ ∈ classFun G := mem_classFun_of_mem_span_Irr hψ
  have hzero : ∀ f : charSpanZero (indFamDetect P (Z.subgroupOf P)),
      cfInner (resClassFun L ψ) (f : ↥L → ℂ) = 0 := by
    intro f
    have h2 : cfInner ψ (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = 0 :=
      cfInner_eq_zero_of_mem_span_of_forall ν horth _
    rw [hν f] at h2
    have h3 : cfInner (indClassFun L (f : ↥L → ℂ)) ψ = 0 := by
      rw [← conj_cfInner, h2, map_zero]
    rw [cfInner_indClassFun L _ hψcf] at h3
    rw [← conj_cfInner, h3, map_zero]
  have hXeq : indFamDetect P (Z.subgroupOf P) = irrDetect ℂ Z :=
    indFamDetect_eq_irrDetect (E := E) hZP hZc hPE hfree
  have hCL : centralLayerFinset P (Z.subgroupOf P) = irrDetectFinset Z :=
    centralLayerFinset_eq_irrDetectFinset (E := E) hZP hZc hPE hfree
  obtain ⟨ξ₀, hξ₀⟩ := indFamDetect_nonempty (E := E) hZP hZc hPE hfree hZ
  obtain ⟨n₀, hn₀pos, hn₀⟩ := exists_pos_apply_one_of_mem_indFamDetect hξ₀
  have hn₀ne : ((n₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn₀pos.ne'
  have hene : ((P.index : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  set lam : ℚ := ((P.index : ℤ) * m ξ₀ : ℤ) / (n₀ : ℚ) with hlam
  have hlamC : (lam : ℂ) = ((P.index : ℂ) * (m ξ₀ : ℂ)) / (n₀ : ℂ) := by
    rw [hlam]; push_cast; ring
  have hdecomp : resClassFun L ψ = (∑ χ ∈ irrTrivialOnFinset Z, (m χ : ℂ) • χ)
      + (lam : ℂ) • centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) := by
    have hprop : ∀ ξ ∈ centralLayerFinset P (Z.subgroupOf P),
        (m ξ : ℂ) = (lam : ℂ) * (ξ 1 / (P.index : ℂ)) := by
      intro ξ hξ
      have hξX : ξ ∈ indFamDetect P (Z.subgroupOf P) := mem_centralLayerFinset.1 hξ
      obtain ⟨d, -, hd⟩ := exists_pos_apply_one_of_mem_indFamDetect hξX
      have hkey := mul_cfInner_eq_mul_cfInner_of_forall_charSpanZero hzero hξX hξ₀
        (d := (d : ℤ)) (d' := (n₀ : ℤ)) (by rw [hd]; push_cast; ring)
        (by rw [hn₀]; push_cast; ring)
      have hmξ : cfInner (resClassFun L ψ) ξ = (m ξ : ℂ) := by
        refine hmcf ξ (mem_irrFinset.2 ?_)
        rw [hXeq] at hξX
        rw [Irr_eq_irrChar]; exact (mem_irrDetect.1 hξX).1
      have hmξ₀ : cfInner (resClassFun L ψ) ξ₀ = (m ξ₀ : ℂ) := by
        refine hmcf ξ₀ (mem_irrFinset.2 ?_)
        have hm : ξ₀ ∈ irrDetect ℂ Z := by rw [← hXeq]; exact hξ₀
        rw [Irr_eq_irrChar]; exact (mem_irrDetect.1 hm).1
      rw [hmξ, hmξ₀] at hkey
      push_cast at hkey
      rw [hlamC, hd]
      have h2 : ((P.index : ℂ) * (m ξ₀ : ℂ)) / (n₀ : ℂ) * ((d : ℂ) / (P.index : ℂ))
          = ((m ξ₀ : ℂ) * (d : ℂ)) / (n₀ : ℂ) := by field_simp
      rw [h2, eq_div_iff hn₀ne]
      linear_combination hkey
    have hsplit : ∑ θ ∈ irrFinset ↥L, (m θ : ℂ) • θ
        = ∑ θ ∈ irrDetectFinset Z, (m θ : ℂ) • θ
          + ∑ θ ∈ irrTrivialOnFinset Z, (m θ : ℂ) • θ := by
      rw [irrFinset_eq_irrDetectFinset_union_irrTrivialOnFinset Z,
        Finset.sum_union (disjoint_irrDetectFinset_irrTrivialOnFinset Z)]
    have hA : (lam : ℂ) • centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ)
        = ∑ ξ ∈ irrDetectFinset Z, (m ξ : ℂ) • ξ := by
      rw [centralLayerWeightedChar_eq_sum_smul, Finset.smul_sum, ← hCL]
      exact Finset.sum_congr rfl fun ξ hξ => by rw [smul_smul, ← hprop ξ hξ]
    rw [hmsum, hsplit, hA]
    exact add_comm _ _
  refine ⟨lam, _, sum_smul_mem_span_irrTrivialOn m, hdecomp, ?_⟩
  intro z hz hz1
  have h1 := congrFun hdecomp z
  have h2 := congrFun hdecomp 1
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    resClassFun_apply] at h1 h2
  have hchi : ∀ χ ∈ irrTrivialOnFinset Z, (m χ : ℂ) * χ z = (m χ : ℂ) * χ 1 := by
    intro χ hχ
    rw [(mem_irrTrivialOn.1 (mem_irrTrivialOnFinset.1 hχ)).2 z hz]
  rw [Finset.sum_congr rfl hchi] at h1
  have hAval : centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) 1
      - centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) z = (Nat.card ↥P : ℂ) :=
    centralLayerWeightedChar_apply_one_sub (E := E) hZP hZc hPE hfree hz hz1
  have hone : ((1 : ↥L) : G) = 1 := rfl
  rw [← hone, h1, h2]
  linear_combination (lam : ℂ) * hAval

theorem apply_eq_apply_of_mem_of_ne_one
    (hZP : Z ≤ P) (hZc : Z ≤ centralizer (P : Set ↥L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) (hZ : Z ≠ ⊥)
    (ν : Submodule.span ℤ (indFamDetect P (Z.subgroupOf P)) →+ virtualChars G)
    (hν : ∀ f : charSpanZero (indFamDetect P (Z.subgroupOf P)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    {ψ : G → ℂ} (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect P (Z.subgroupOf P),
      cfInner ψ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0)
    {z w : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) (hw : w ∈ Z) (hw1 : w ≠ 1) :
    ψ (z : G) = ψ (w : G) := by
  obtain ⟨lam, -, -, -, hval⟩ :=
    exists_resClassFun_eq_add_smul_centralLayerWeightedChar (E := E) hZP hZc hPE hfree hZ ν hν
      hψ horth
  have h1 := hval z hz hz1
  have h2 := hval w hw hw1
  linear_combination h2 - h1

end Main

namespace IsFreeCentralSection

variable {G : Type*} [Group G] [Fintype G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z)

include h

variable [Fintype ↥L] [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem exists_resClassFun_eq_add_smul_centralLayerWeightedChar
    (ν : Submodule.span ℤ (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hν : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    {ψ : G → ℂ} (hψ : ψ ∈ signedIrr G)
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      cfInner ψ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0) :
    ∃ lam : ℚ, ∃ Ξ ∈ Submodule.span ℤ (irrTrivialOn (Z.subgroupOf L)),
      resClassFun L ψ = Ξ + (lam : ℂ) • centralLayerWeightedChar (P.subgroupOf L)
            ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) (Nat.card E : ℂ) ∧
        ∀ z : ↥L, (z : G) ∈ Z → z ≠ 1 →
          ψ (1 : G) - ψ (z : G) = (lam : ℂ) * (Nat.card P : ℂ) := by
  obtain ⟨lam, Ξ, hΞ, hdec, hval⟩ :=
    CFSG.FeitThompson.exists_resClassFun_eq_add_smul_centralLayerWeightedChar
      (E := E.subgroupOf L) (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer
      h.sup_subgroupOf h.free_subgroupOf h.Z_subgroupOf_ne_bot ν hν
      (signedIrr_subset_span_Irr hψ) horth
  refine ⟨lam, Ξ, hΞ, ?_, ?_⟩
  · rw [h.centralLayerWeightedChar_natCard_E_eq]; exact hdec
  · intro z hz hz1
    rw [hval z hz hz1, h.natCard_P_subgroupOf]

end IsFreeCentralSection

end CFSG.FeitThompson
