module

public import CFSG.FeitThompson.Representations.CoherentFamilyCommonSignDegreeRatio
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.CoherentExtensionNonrealConjPairs
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.InductionMulRestrictedClassFun
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

section Restriction

variable {L G : Type*} [Group L] [Group G]

def spanRestrict {S P : Set (L → ℂ)} (hPS : P ⊆ S)
    (ν : Submodule.span ℤ S →+ virtualChars G) : Submodule.span ℤ P →+ virtualChars G :=
  ν.comp (Submodule.inclusion (Submodule.span_mono hPS)).toAddMonoidHom

omit [Group L] in
@[simp] theorem coe_spanRestrict_apply {S P : Set (L → ℂ)} (hPS : P ⊆ S)
    (ν : Submodule.span ℤ S →+ virtualChars G) (f : Submodule.span ℤ P) :
    (spanRestrict hPS ν f : G → ℂ)
      = (ν ⟨(f : L → ℂ), Submodule.span_mono hPS f.2⟩ : G → ℂ) := (rfl)

omit [Group L] in
theorem coherentVal_spanRestrict {S P : Set (L → ℂ)} (hPS : P ⊆ S)
    (ν : Submodule.span ℤ S →+ virtualChars G) (χ : P) :
    coherentVal (spanRestrict hPS ν) χ = coherentVal ν ⟨(χ : L → ℂ), hPS χ.2⟩ := by
  rw [coherentVal_apply, coherentVal_apply, coe_spanRestrict_apply]

def charSpanZeroRestrict {P : Set (L → ℂ)} (ν : Submodule.span ℤ P →+ virtualChars G) :
    charSpanZero P →+ virtualChars G :=
  ν.comp (Submodule.inclusion (charSpanZero_le P)).toAddMonoidHom

@[simp] theorem coe_charSpanZeroRestrict_spanRestrict {S P : Set (L → ℂ)} (hPS : P ⊆ S)
    (ν : Submodule.span ℤ S →+ virtualChars G) (f : charSpanZero P) :
    (charSpanZeroRestrict (spanRestrict hPS ν) f : G → ℂ)
      = (ν ⟨(f : L → ℂ), Submodule.span_mono hPS (charSpanZero_le P f.2)⟩ : G → ℂ) := (rfl)

theorem isCoherentWith_spanRestrict [Fintype L] [Fintype G] {S P : Set (L → ℂ)} (hPS : P ⊆ S)
    {ν : Submodule.span ℤ S →+ virtualChars G}
    (hνiso : ∀ f h : Submodule.span ℤ S,
      cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ)) :
    IsCoherentWith P (charSpanZeroRestrict (spanRestrict hPS ν)) (spanRestrict hPS ν) where
  inner_eq f h := by rw [coe_spanRestrict_apply, coe_spanRestrict_apply, hνiso]
  eq_on_zero _ := rfl

end Restriction

section Pair

variable {X : Type*} {ζ : X → ℂ}

private def pairOf (ζ : X → ℂ) : Set (X → ℂ) := {ζ, star ζ}

private theorem mem_pairOf : ζ ∈ pairOf ζ := Set.mem_insert _ _

private theorem star_mem_pairOf : ∀ χ ∈ pairOf ζ, star χ ∈ pairOf ζ := by
  rintro χ (rfl | rfl)
  · exact Or.inr rfl
  · exact Or.inl (star_star _)

private theorem coe_starElem_pairOf :
    ((starElem (star_mem_pairOf (ζ := ζ)) ⟨ζ, mem_pairOf⟩ : pairOf ζ) : X → ℂ) = star ζ :=
  coe_starElem _ _

private theorem pairOf_subset {S : Set (X → ℂ)} (hSstar : ∀ χ ∈ S, star χ ∈ S) (hζS : ζ ∈ S) :
    pairOf ζ ⊆ S := by
  rintro χ (rfl | rfl)
  · exact hζS
  · exact hSstar _ hζS

private theorem star_ne_self_of_mem_pairOf (h : star ζ ≠ ζ) : ∀ χ ∈ pairOf ζ, star χ ≠ χ := by
  rintro χ (rfl | rfl)
  · exact h
  · rw [star_star]
    exact fun hc => h hc.symm

private theorem two_le_ncard_pairOf (h : star ζ ≠ ζ) : 2 ≤ (pairOf ζ).ncard :=
  (Set.ncard_pair h.symm).ge

private theorem pairOf_subset_Irr [Group X] [Finite X] (hζIrr : ζ ∈ Irr X) :
    pairOf ζ ⊆ Irr X := by
  rintro χ (rfl | rfl)
  · exact hζIrr
  · exact star_mem_Irr hζIrr

end Pair

section Ind

variable {X : Type*} [Group X] [Fintype X] {H : Subgroup X}

theorem star_mem_indFam_sdiff {ξ : X → ℂ} (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) :
    star ξ ∈ indFam H (Irr ↥H \ {1}) := by
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hξ
  refine (mem_indFam H).2 ⟨star θ, ⟨star_mem_Irr hθ, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff] at hθ1 ⊢
    intro h
    exact hθ1 (by rw [← star_star θ, h, star_one])
  · rw [← indClassFun_inducedCharacterConstruction_eq,
      InducedCharacterConstruction.indClassFun_star, indClassFun_inducedCharacterConstruction_eq]

theorem ne_one_of_mem_indFam_sdiff [H.Normal] {ξ : X → ℂ}
    (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) : ξ ≠ 1 := by
  intro h
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hξ
  have h0 : cfInner (indClassFun H θ) (1 : X → ℂ) = 0 :=
    cfInner_indClassFun_one H hθ (by simpa using hθ1)
  rw [h, cfInner_one_one] at h0
  exact one_ne_zero h0

theorem star_ne_self_of_odd_natCard_of_mem_indFam_sdiff (hodd : Odd (Nat.card X)) [H.Normal]
    {ξ : X → ℂ} (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) (hξIrr : ξ ∈ Irr X) : star ξ ≠ ξ := by
  have h := ne_conj_of_mem_Irr_of_ne_one_of_odd hodd hξIrr (ne_one_of_mem_indFam_sdiff hξ)
  intro hc
  exact h (funext fun x => by simpa using (congrFun hc x).symm)

end Ind

section Main

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {S : Set (↥L → ℂ)} {ζ : ↥L → ℂ}
  {ν : Submodule.span ℤ S →+ virtualChars G}
  (hodd : Odd (Nat.card G))
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))

omit [Fintype G] [H.Normal] in
include hS in
theorem star_mem_of_mem (hζS : ζ ∈ S) : star ζ ∈ S :=
  hS ▸ star_mem_indFam_sdiff (hS ▸ hζS)

omit [Fintype G] in
include hodd hS in
theorem star_ne_self_of_odd (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) : star ζ ≠ ζ :=
  star_ne_self_of_odd_natCard_of_mem_indFam_sdiff
    (hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)) (hS ▸ hζS) hζIrr

include hodd hD hA hS hνiso hντ in
private theorem exists_sign_nonreal_Irr_aux (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ χ ∈ Irr G, star χ ≠ χ ∧
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) = ε • χ ∧
      (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ) = ε • star χ := by
  set hPS : pairOf ζ ⊆ S := pairOf_subset (fun _ h => star_mem_of_mem hS h) hζS with hPSdef
  have hdom : ∀ f : charSpanZero (pairOf ζ), (f : ↥L → ℂ) ∈ dadeDomain L A := fun f =>
    mem_dadeDomain_of_mem_span_indFam hA (hPS.trans (hS ▸ indFam_mono H Set.sdiff_subset))
      (charSpanZero_le _ f.2) (charSpanZero_apply_one f)
  have hτ : ∀ f : charSpanZero (pairOf ζ),
      (charSpanZeroRestrict (spanRestrict hPS ν) f : G → ℂ)
        = ((dadeMap hD ⟨(f : ↥L → ℂ), hdom f⟩ : classFun G) : G → ℂ) := fun f => by
    rw [coe_charSpanZeroRestrict_spanRestrict]
    exact hντ _ _ rfl
  have hτ1 : ∀ f : charSpanZero (pairOf ζ),
      (charSpanZeroRestrict (spanRestrict hPS ν) f : G → ℂ) 1 = 0 := fun f => by
    rw [hτ f]
    exact dadeMap_one_eq_zero hD _
  have hτstar : ∀ f : charSpanZero (pairOf ζ),
      (charSpanZeroRestrict (spanRestrict hPS ν)
          (starCharSpanZero (star_mem_pairOf (ζ := ζ)) f) : G → ℂ)
        = star ((charSpanZeroRestrict (spanRestrict hPS ν) f : G → ℂ)) := fun f => by
    rw [hτ, hτ]
    have h : (⟨((starCharSpanZero (star_mem_pairOf (ζ := ζ)) f : charSpanZero (pairOf ζ)) :
            ↥L → ℂ), hdom (starCharSpanZero (star_mem_pairOf (ζ := ζ)) f)⟩ : dadeDomain L A)
        = ⟨star (f : ↥L → ℂ), star_mem_dadeDomain (hdom f)⟩ :=
      Subtype.ext (coe_starCharSpanZero _ f)
    rw [h]
    exact dadeMap_star hD (hdom f)
  obtain ⟨ε, hε, η, -, hηIrr, hηeq, hηnr, hηstar⟩ :=
    exists_sign_nonreal_root_of_isCoherentWith (pairOf_subset_Irr hζIrr)
      (two_le_ncard_pairOf (star_ne_self_of_odd hodd hS hζS hζIrr)) (star_mem_pairOf (ζ := ζ))
      (star_ne_self_of_mem_pairOf (star_ne_self_of_odd hodd hS hζS hζIrr)) hτ1 hτstar
      (isCoherentWith_spanRestrict hPS hνiso)
  have hval := hηeq ⟨ζ, mem_pairOf⟩
  rw [coherentVal_spanRestrict, coherentVal_apply] at hval
  have hvalstar := hηeq (starElem (star_mem_pairOf (ζ := ζ)) ⟨ζ, mem_pairOf⟩)
  rw [coherentVal_spanRestrict, coherentVal_apply, hηstar ⟨ζ, mem_pairOf⟩] at hvalstar
  have hsub : (⟨((starElem (star_mem_pairOf (ζ := ζ)) ⟨ζ, mem_pairOf⟩ : pairOf ζ) : ↥L → ℂ),
        Submodule.subset_span (hPS (starElem (star_mem_pairOf (ζ := ζ)) ⟨ζ, mem_pairOf⟩).2)⟩ :
          Submodule.span ℤ S)
      = ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ :=
    Subtype.ext coe_starElem_pairOf
  rw [hsub] at hvalstar
  exact ⟨ε, hε, η ⟨ζ, mem_pairOf⟩, hηIrr _, hηnr _, hval, hvalstar⟩

include hodd hD hA hS hνiso hντ in
theorem exists_sign_nonreal_Irr_nu (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ χ ∈ Irr G, star χ ≠ χ ∧
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) = ε • χ := by
  obtain ⟨ε, hε, χ, hχ, hχnr, hval, -⟩ :=
    exists_sign_nonreal_Irr_aux hodd hD hA hS hνiso hντ hζS hζIrr
  exact ⟨ε, hε, χ, hχ, hχnr, hval⟩

include hodd hD hA hS hνiso hντ in
theorem coe_nu_star_eq (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ)
      = star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) := by
  obtain ⟨ε, hε, χ, -, -, hval, hvalstar⟩ :=
    exists_sign_nonreal_Irr_aux hodd hD hA hS hνiso hντ hζS hζIrr
  have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
  rw [hval, hvalstar, star_smul, hstarε]

include hodd hD hA hS hνiso hντ in
theorem nu_mem_signedIrr (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) ∈ signedIrr G := by
  obtain ⟨ε, hε, χ, hχ, -, hval⟩ :=
    exists_sign_nonreal_Irr_nu hodd hD hA hS hνiso hντ hζS hζIrr
  rw [hval]
  rcases hε with rfl | rfl
  · simpa using Irr_subset_signedIrr hχ
  · simpa using neg_mem_signedIrr_iff.2 (Irr_subset_signedIrr hχ)

include hodd hD hA hS hνiso hντ in
theorem star_nu_ne (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
      ≠ (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) := by
  obtain ⟨ε, hε, χ, -, hχnr, hval⟩ :=
    exists_sign_nonreal_Irr_nu hodd hD hA hS hνiso hντ hζS hζIrr
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
  rw [hval, star_smul, hstarε]
  intro hc
  exact hχnr (smul_right_injective _ hεne hc)

end Main

end NormalInducedFamily

end CFSG.FeitThompson

end
