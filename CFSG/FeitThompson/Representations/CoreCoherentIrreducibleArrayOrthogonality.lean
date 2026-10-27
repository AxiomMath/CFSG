module

public import CFSG.FeitThompson.Representations.SmallCharactersPerpendicularCyclicTIArray
public import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
public import CFSG.FeitThompson.Representations.CoherentExtensionNonrealConjPairs
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

section Pair

variable {X : Type*} {ξ : X → ℂ}

private def starPair (ξ : X → ℂ) : Set (X → ℂ) := {ξ, star ξ}

private theorem self_mem_starPair : ξ ∈ starPair ξ := Set.mem_insert _ _

private theorem star_mem_starPair : ∀ χ ∈ starPair ξ, star χ ∈ starPair ξ := by
  rintro χ (rfl | rfl)
  · exact Or.inr rfl
  · exact Or.inl (star_star _)

private theorem coe_starElem_starPair :
    ((starElem (star_mem_starPair (ξ := ξ)) ⟨ξ, self_mem_starPair⟩ : starPair ξ) : X → ℂ)
      = star ξ := coe_starElem _ _

private theorem starPair_subset {S : Set (X → ℂ)} (hSstar : ∀ χ ∈ S, star χ ∈ S) (hξS : ξ ∈ S) :
    starPair ξ ⊆ S := by
  rintro χ (rfl | rfl)
  · exact hξS
  · exact hSstar _ hξS

private theorem star_ne_self_of_mem_starPair (h : star ξ ≠ ξ) :
    ∀ χ ∈ starPair ξ, star χ ≠ χ := by
  rintro χ (rfl | rfl)
  · exact h
  · rw [star_star]
    exact fun hc => h hc.symm

private theorem two_le_ncard_starPair (h : star ξ ≠ ξ) : 2 ≤ (starPair ξ).ncard :=
  (Set.ncard_pair h.symm).ge

private theorem starPair_subset_Irr [Group X] [Finite X] (hξIrr : ξ ∈ Irr X) :
    starPair ξ ⊆ Irr X := by
  rintro χ (rfl | rfl)
  · exact hξIrr
  · exact star_mem_Irr hξIrr

end Pair

section Family

variable {L : Type*} [Group L] [Fintype L] {K : Subgroup L} {H : Subgroup ↥K}
  {S : Set (L → ℂ)}

theorem ne_one_of_mem_indFamDetect {ξ : L → ℂ} (hξ : ξ ∈ indFamDetect K H) : ξ ≠ 1 := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect K).1 hξ
  rw [mem_irrDetect] at hθ
  have hθIrr : θ ∈ Irr ↥K := by rw [Irr_eq_irrChar]; exact hθ.1
  have hθ1 : θ ≠ 1 := fun h => hθ.2 fun x _ => by simp [mem_charValueKernel, h]
  intro hc
  have h0 : cfInner (indClassFun K θ) (1 : L → ℂ) = 0 :=
    NormalInducedFamily.cfInner_indClassFun_one K hθIrr hθ1
  rw [hc, cfInner_one_one] at h0
  exact one_ne_zero h0

theorem mem_classFun_of_mem_span_indFamDetect (hS : S ⊆ indFamDetect K H) {f : L → ℂ}
    (hf : f ∈ Submodule.span ℤ S) : f ∈ classFun L := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨θ, -, rfl⟩ := (mem_indFamDetect K).1 (hS hx)
      exact indClassFun_mem_classFun K θ
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact Submodule.smul_of_tower_mem _ a hx

theorem apply_eq_zero_of_mem_span_indFamDetect [K.Normal] (hS : S ⊆ indFamDetect K H)
    {f : L → ℂ} (hf : f ∈ Submodule.span ℤ S) {x : L} (hx : x ∉ K) : f x = 0 := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨θ, -, rfl⟩ := (mem_indFamDetect K).1 (hS hy)
      exact indClassFun_eq_zero_of_notMem K θ hx
  | zero => rfl
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

end Family

section Disjoint

open Pointwise

variable {G : Type*} [Group G] {L : Subgroup G} {K : Subgroup ↥L} {W W1 W2 : Subgroup G}

theorem notMem_map_of_mem_cyclicTIDiff (hW : IsCyclicTIPair W W1 W2)
    (hW2 : W2 ≤ K.map L.subtype) (hW1 : W1 ⊓ K.map L.subtype = ⊥) {v : G}
    (hv : v ∈ cyclicTIDiff W W1 W2) : v ∉ K.map L.subtype := by
  intro hvK
  rw [mem_cyclicTIDiff] at hv
  have hmul : v ∈ (W1 : Set G) * (W2 : Set G) := by
    rw [hW.mul_eq]; exact hv.1
  obtain ⟨x, hx, y, hy, rfl⟩ := hmul
  have hxK : x ∈ K.map L.subtype := by
    have hxe : x = x * y * y⁻¹ := by group
    rw [hxe]
    exact mul_mem hvK (inv_mem (hW2 hy))
  have hx1 : x ∈ W1 ⊓ K.map L.subtype := ⟨hx, hxK⟩
  rw [hW1, Subgroup.mem_bot] at hx1
  subst hx1
  exact hv.2.2 (by simpa using hy)

end Disjoint

section Ambient

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G}

omit [Fintype ↥W] in
theorem cfInner_apply_eq_zero_of_forall_prodCharEta (hW : IsCyclicTIPair W W1 W2) {ρ : G → ℂ}
    (h : ∀ (i : Irr ↥W1) (j : Irr ↥W2), cfInner ρ (hW.prodCharEta ω i j) = 0)
    (f : classFun ↥W) : cfInner ρ (ω f : G → ℂ) = 0 := by
  classical
  have hf1 : Finite ↥W1 := hW.finite_left
  have hf2 : Finite ↥W2 := hW.finite_right
  have : Fintype (Irr ↥W1 × Irr ↥W2) := Fintype.ofFinite _
  have hexp : (ω f : G → ℂ) = ∑ p : Irr ↥W1 × Irr ↥W2,
      (hW.basisProdIrr.repr f p) • hW.prodCharEta ω p.1 p.2 := by
    conv_lhs => rw [← hW.basisProdIrr.sum_repr f]
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, SetLike.val_smul, hW.prodCharEta_eq_coe_apply]
  rw [hexp, cfInner_sum_right]
  simp [cfInner_smul_right, h]

theorem apply_eq_zero_of_forall_prodCharEta (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {ρ : G → ℂ} (hρ : ρ ∈ classFun G)
    (h : ∀ (i : Irr ↥W1) (j : Irr ↥W2), cfInner ρ (hW.prodCharEta ω i j) = 0) {v : G}
    (hv : v ∈ cyclicTIDiff W W1 W2) : ρ v = 0 := by
  classical
  have hcomm : IsMulCommutative ↥W := hW.isMulCommutative_coe
  set w : ↥W := ⟨v, cyclicTIDiff_subset hv⟩ with hwdef
  have hvw : (w : G) ∈ cyclicTIDiff W W1 W2 := hv
  set p : ↥W → ℂ := Pi.single w 1 with hp
  set pcf : classFun ↥W := ⟨p, single_mem_classFun w 1⟩ with hpcf
  have hωp : (ω pcf : G → ℂ) = indClassFun W p := by
    refine hω.eq_indClassFun pcf fun x hx => ?_
    change p x = 0
    rw [hp, Pi.single_eq_of_ne']
    intro hxw
    exact hx (hxw ▸ hvw)
  have h0 : cfInner ρ (indClassFun W p) = 0 := by
    rw [← hωp]
    exact cfInner_apply_eq_zero_of_forall_prodCharEta hW h pcf
  have h1 : cfInner (indClassFun W p) ρ = cfInner p (resClassFun W ρ) :=
    cfInner_indClassFun W p hρ
  have h2 : cfInner p (resClassFun W ρ) = 0 := by
    rw [← h1, ← conj_cfInner, h0, map_zero]
  have h3 : cfInner (resClassFun W ρ) p = 0 := by
    rw [← conj_cfInner, h2, map_zero]
  rw [hp, cfInner_single, resClassFun_apply] at h3
  have hne : (Nat.card ↥W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simpa [hwdef] using (mul_eq_zero.1 h3).resolve_left (inv_ne_zero hne)

end Ambient

namespace CoherentCore

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K : Subgroup ↥L} [K.Normal] {H : Subgroup ↥K}
  {W W1 W2 : Subgroup G} [Fintype ↥W] {A0 : Set G} {T : G → Subgroup G}
  {ω : classFun ↥W →ₗ[ℂ] classFun G} {S : Set (↥L → ℂ)}
  {ν : Submodule.span ℤ S →+ virtualChars G} {ξ : ↥L → ℂ}
  (hodd : Odd (Nat.card G))
  (hW : IsCyclicTIPair W W1 W2)
  (hW2 : W2 ≤ K.map L.subtype)
  (hW1 : W1 ⊓ K.map L.subtype = ⊥)
  (hω : IsCyclicTIIsometry W W1 W2 ω)
  (hD : IsDadeData L A0 T)
  (hVA : cyclicTIDiff W W1 W2 ⊆ A0)
  (hS : S ⊆ indFamDetect K H)
  (hSstar : ∀ χ ∈ S, star χ ∈ S)
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))

omit [Fintype G] [K.Normal] in
include hS in
theorem ne_one_of_mem (hξS : ξ ∈ S) : ξ ≠ 1 := ne_one_of_mem_indFamDetect (hS hξS)

omit [Fintype G] [K.Normal] in
include hodd hS in
theorem star_ne_self (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) : star ξ ≠ ξ := by
  have hLodd : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  have h := ne_conj_of_mem_Irr_of_ne_one_of_odd hLodd hξIrr (ne_one_of_mem hS hξS)
  intro hc
  exact h (funext fun x => by simpa using (congrFun hc x).symm)

omit [K.Normal] in
include hodd hD hS hSstar hνiso hS0 hντ in
private theorem exists_sign_nonreal_Irr_aux (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ χ ∈ Irr G, star χ ≠ χ ∧
      (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) = ε • χ ∧
      (ν ⟨star ξ, Submodule.subset_span (hSstar _ hξS)⟩ : G → ℂ) = ε • star χ := by
  set hPS : starPair ξ ⊆ S := starPair_subset hSstar hξS with hPSdef
  have hzero : ∀ f : charSpanZero (starPair ξ), (f : ↥L → ℂ) ∈ charSpanZero S := fun f =>
    mem_charSpanZero.2 ⟨Submodule.span_mono hPS (charSpanZero_le _ f.2), charSpanZero_apply_one f⟩
  have hdom : ∀ f : charSpanZero (starPair ξ), (f : ↥L → ℂ) ∈ dadeDomain L A0 := fun f =>
    mem_dadeDomain.2
      ⟨mem_classFun_of_mem_span_indFamDetect hS (Submodule.span_mono hPS (charSpanZero_le _ f.2)),
        fun x hx => hS0 ⟨(f : ↥L → ℂ), hzero f⟩ x hx⟩
  have hτ : ∀ f : charSpanZero (starPair ξ),
      (NormalInducedFamily.charSpanZeroRestrict
          (NormalInducedFamily.spanRestrict hPS ν) f : G → ℂ)
        = ((dadeMap hD ⟨(f : ↥L → ℂ), hdom f⟩ : classFun G) : G → ℂ) := fun f => by
    rw [NormalInducedFamily.coe_charSpanZeroRestrict_spanRestrict]
    exact hντ _ _ rfl
  have hτ1 : ∀ f : charSpanZero (starPair ξ),
      (NormalInducedFamily.charSpanZeroRestrict
        (NormalInducedFamily.spanRestrict hPS ν) f : G → ℂ) 1 = 0 := fun f => by
    rw [hτ f]
    exact dadeMap_one_eq_zero hD _
  have hτstar : ∀ f : charSpanZero (starPair ξ),
      (NormalInducedFamily.charSpanZeroRestrict (NormalInducedFamily.spanRestrict hPS ν)
          (starCharSpanZero (star_mem_starPair (ξ := ξ)) f) : G → ℂ)
        = star ((NormalInducedFamily.charSpanZeroRestrict
          (NormalInducedFamily.spanRestrict hPS ν) f : G → ℂ)) := fun f => by
    rw [hτ, hτ]
    have hsub : (⟨((starCharSpanZero (star_mem_starPair (ξ := ξ)) f :
            charSpanZero (starPair ξ)) : ↥L → ℂ),
          hdom (starCharSpanZero (star_mem_starPair (ξ := ξ)) f)⟩ : dadeDomain L A0)
        = ⟨star (f : ↥L → ℂ), star_mem_dadeDomain (hdom f)⟩ :=
      Subtype.ext (coe_starCharSpanZero _ f)
    rw [hsub]
    exact dadeMap_star hD (hdom f)
  obtain ⟨ε, hε, η, -, hηIrr, hηeq, hηnr, hηstar⟩ :=
    exists_sign_nonreal_root_of_isCoherentWith (starPair_subset_Irr hξIrr)
      (two_le_ncard_starPair (star_ne_self hodd hS hξS hξIrr))
      (star_mem_starPair (ξ := ξ))
      (star_ne_self_of_mem_starPair (star_ne_self hodd hS hξS hξIrr)) hτ1 hτstar
      (NormalInducedFamily.isCoherentWith_spanRestrict hPS hνiso)
  have hval := hηeq ⟨ξ, self_mem_starPair⟩
  rw [NormalInducedFamily.coherentVal_spanRestrict, coherentVal_apply] at hval
  have hvalstar := hηeq (starElem (star_mem_starPair (ξ := ξ)) ⟨ξ, self_mem_starPair⟩)
  rw [NormalInducedFamily.coherentVal_spanRestrict, coherentVal_apply,
    hηstar ⟨ξ, self_mem_starPair⟩] at hvalstar
  have hsub : (⟨((starElem (star_mem_starPair (ξ := ξ)) ⟨ξ, self_mem_starPair⟩ : starPair ξ) :
        ↥L → ℂ), Submodule.subset_span
          (hPS (starElem (star_mem_starPair (ξ := ξ)) ⟨ξ, self_mem_starPair⟩).2)⟩ :
          Submodule.span ℤ S)
      = ⟨star ξ, Submodule.subset_span (hSstar _ hξS)⟩ :=
    Subtype.ext coe_starElem_starPair
  rw [hsub] at hvalstar
  exact ⟨ε, hε, η ⟨ξ, self_mem_starPair⟩, hηIrr _, hηnr _, hval, hvalstar⟩

omit [K.Normal] in
include hodd hD hS hSstar hνiso hS0 hντ in
theorem nu_mem_signedIrr (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) :
    (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) ∈ signedIrr G := by
  obtain ⟨ε, hε, χ, hχ, -, hval, -⟩ :=
    exists_sign_nonreal_Irr_aux hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr
  rw [hval]
  rcases hε with rfl | rfl
  · simpa using Irr_subset_signedIrr hχ
  · simpa using neg_mem_signedIrr_iff.2 (Irr_subset_signedIrr hχ)

omit [K.Normal] in
include hodd hD hS hSstar hνiso hS0 hντ in
theorem star_nu_ne (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) :
    star (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
      ≠ (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) := by
  obtain ⟨ε, hε, χ, -, hχnr, hval, -⟩ :=
    exists_sign_nonreal_Irr_aux hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
  rw [hval, star_smul, hstarε]
  intro hc
  exact hχnr (smul_right_injective _ hεne hc)

omit [K.Normal] in
include hodd hD hS hSstar hνiso hS0 hντ in
theorem nu_star_eq (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) :
    (ν ⟨star ξ, Submodule.subset_span (hSstar _ hξS)⟩ : G → ℂ)
      = star (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) := by
  obtain ⟨ε, hε, χ, -, -, hval, hvalstar⟩ :=
    exists_sign_nonreal_Irr_aux hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr
  have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
  rw [hval, hvalstar, star_smul, hstarε]

include hodd hW hW2 hW1 hD hVA hS hSstar hνiso hS0 hντ in
theorem sub_star_nu_apply_eq_zero (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) {v : G}
    (hv : v ∈ cyclicTIDiff W W1 W2) :
    ((ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
      - fun y => conj ((ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) y)) v = 0 := by
  have hmem : ξ - star ξ ∈ Submodule.span ℤ S :=
    Submodule.sub_mem _ (Submodule.subset_span hξS) (Submodule.subset_span (hSstar _ hξS))
  have hone : (ξ - star ξ) 1 = 0 := by
    have h := conj_apply_one_of_mem_Irr hξIrr
    simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def]
    rw [h]
    ring
  have hz : ξ - star ξ ∈ charSpanZero S := mem_charSpanZero.2 ⟨hmem, hone⟩
  have hdom : ξ - star ξ ∈ dadeDomain L A0 :=
    mem_dadeDomain.2
      ⟨Submodule.sub_mem _
          (mem_classFun_of_mem_span_indFamDetect hS (Submodule.subset_span hξS))
          (mem_classFun_of_mem_span_indFamDetect hS
            (Submodule.subset_span (hSstar _ hξS))),
        fun x hx => hS0 ⟨ξ - star ξ, hz⟩ x hx⟩
  have hsub : (ν ⟨ξ - star ξ, hmem⟩ : G → ℂ)
      = ((dadeMap hD ⟨ξ - star ξ, hdom⟩ : classFun G) : G → ℂ) := hντ _ _ rfl
  have hvA : v ∈ A0 := hVA hv
  have hvL : v ∈ L := hD.mem_of_mem hvA
  have hvK : (⟨v, hvL⟩ : ↥L) ∉ K := fun hc =>
    notMem_map_of_mem_cyclicTIDiff hW hW2 hW1 hv ⟨⟨v, hvL⟩, hc, rfl⟩
  have hξv : ξ (⟨v, hvL⟩ : ↥L) = 0 :=
    apply_eq_zero_of_mem_span_indFamDetect hS (Submodule.subset_span hξS) hvK
  have hstarv : star ξ (⟨v, hvL⟩ : ↥L) = 0 :=
    apply_eq_zero_of_mem_span_indFamDetect hS (Submodule.subset_span (hSstar _ hξS)) hvK
  have hval : (ν ⟨ξ - star ξ, hmem⟩ : G → ℂ) v = 0 := by
    rw [hsub, dadeMap_apply_mem hD ⟨ξ - star ξ, hdom⟩ hvA]
    simp [hξv, hstarv]
  have hadd : (ν ⟨ξ - star ξ, hmem⟩ : G → ℂ)
      = (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
        - (ν ⟨star ξ, Submodule.subset_span (hSstar _ hξS)⟩ : G → ℂ) := by
    have hsplit : (⟨ξ - star ξ, hmem⟩ : Submodule.span ℤ S)
        = ⟨ξ, Submodule.subset_span hξS⟩
          - ⟨star ξ, Submodule.subset_span (hSstar _ hξS)⟩ := Subtype.ext rfl
    rw [hsplit, map_sub]
    rfl
  rw [hadd, nu_star_eq hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr] at hval
  simpa using hval

include hodd hW hW2 hW1 hω hD hVA hS hSstar hνiso hS0 hντ in
theorem isOrthogonal_nu_prodCharEta (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) (i : Irr ↥W1)
    (j : Irr ↥W2) :
    IsOrthogonal (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) (hW.prodCharEta ω i j) := by
  have hρ : (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) ∈ signedIrr G :=
    nu_mem_signedIrr hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr
  have hρr : (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ)
      ≠ fun x => conj ((ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) x) := fun hc =>
    star_nu_ne hodd hD hS hSstar hνiso hS0 hντ hξS hξIrr
      (funext fun x => by simpa using (congrFun hc x).symm)
  have hχ : ((hW.basisProdIrr (i, j) : classFun ↥W) : ↥W → ℂ) ∈ Irr ↥W := by
    rw [hW.coe_basisProdIrr_apply]
    exact hW.prodChar_mem_Irr i.2 j.2
  have h := hW.isOrthogonal_apply_of_ne_conj hω hρ hρr
    (fun x hx => sub_star_nu_apply_eq_zero hodd hW hW2 hW1 hD hVA hS hSstar hνiso hS0 hντ
      hξS hξIrr hx) hχ
  rwa [← hW.prodCharEta_eq_coe_apply] at h

include hodd hW hW2 hW1 hω hD hVA hS hSstar hνiso hS0 hντ in
theorem nu_apply_eq_zero_of_mem_cyclicTIDiff (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L) {v : G}
    (hv : v ∈ cyclicTIDiff W W1 W2) : (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) v = 0 := by
  have hcf : (ν ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) ∈ classFun G :=
    mem_classFun_of_mem_span_Irr (virtualChars_le_span_Irr (ν _).2)
  refine apply_eq_zero_of_forall_prodCharEta hW hω hcf (fun i j => ?_) hv
  exact isOrthogonal_iff.1 (isOrthogonal_nu_prodCharEta hodd hW hW2 hW1 hω hD hVA hS hSstar
    hνiso hS0 hντ hξS hξIrr i j)

end CoherentCore

end CFSG.FeitThompson

end
