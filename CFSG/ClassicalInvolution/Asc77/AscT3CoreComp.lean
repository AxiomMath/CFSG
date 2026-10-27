module

public import CFSG.ClassicalInvolution.Asc77.AscT3CoreRestrict
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreStab
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol
public import CFSG.ClassicalInvolution.RouteD.G2D4T3D4

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

abbrev barImg (H M : Subgroup G) : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H) :=
  (M.subgroupOf H).map (oddQuot ↥H)

omit [Fact p.Prime] in
theorem barImg_mem (H : Subgroup G) {M : Subgroup G} (hM : M ∈ Ω) (hMH : M ≤ H) :
    barImg H M ∈ oddQuotientFamily (restrictFamily Ω H) :=
  mem_oddQuotientFamily (subgroupOf_mem_restrictFamily hM hMH)

omit [Fact p.Prime] in
theorem isUniqueInvolution_barImg [Finite G] (H : Subgroup G) {M : Subgroup G} {z : G}
    (hz : IsUniqueInvolution M z) (hMH : M ≤ H) :
    IsUniqueInvolution (barImg H M) (oddQuot ↥H ⟨z, hMH hz.mem⟩) :=
  isUniqueInvolution_map_mk_of_odd (X := classicalInvolutionOddCore ↥H)
    (odd_natCard_oddCore_inf _) (isUniqueInvolution_subgroupOf hz hMH)

variable [Finite G]

theorem barImg_mem_comp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {H K : Subgroup G} (hK : K ∈ Ω) (hH : ∀ M ∈ aStar Ω K, M ≤ H)
    (D : OmegaLie p f (oddQuotientFamily (restrictFamily Ω H))) {i : Fin D.card}
    (hi : D.tag i = .G2) (hKi : barImg H K ∈ compMembers D i) :
    ∀ M ∈ aStar Ω K, barImg H M ∈ compMembers D i := by
  have hΛ : HypOmegaMod p f (restrictFamily Ω H) := hΩ.restrict H
  have hΦ : HypOmegaMod p f (oddQuotientFamily (restrictFamily Ω H)) :=
    oddQuotHyp p f hp hq ↥H _ hΛ _ (CFSG.ComponentClassification.OddCore.odd_card ↥H)
  have hi' : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inl hi
  intro M hM
  induction hM with
  | refl => exact hKi
  | @tail B C hB hbc ih =>
    have hBΩ : B ∈ Ω := mem_of_mem_aStar hK hB
    have hBH : B ≤ H := hH B hB
    obtain ⟨hCΩ, h | h | ⟨ht, hne⟩⟩ := hbc
    · obtain ⟨zB, zC, hv⟩ := h
      have hCH : C ≤ H := hH C (Relation.ReflTransGen.tail hB ⟨hCΩ, Or.inl ⟨zB, zC, hv⟩⟩)
      obtain ⟨a, hQ⟩ := quotViol_of_aViol hp hq hΛ (subgroupOf_mem_restrictFamily hBΩ hBH)
        (aViol_restrict hp hΩ hBH hCH hv)
      obtain ⟨i', R, S, hR, hS, hBR, hCS⟩ := hQ.exists_components D
      have := compMembers_unique hΦ D ih (⟨R, hR, hBR⟩ : barImg H B ∈ compMembers D i')
      subst this
      exact ⟨S, hS, hCS⟩
    · obtain ⟨zC, zB, hv⟩ := h
      have hCH : C ≤ H :=
        hH C (Relation.ReflTransGen.tail hB ⟨hCΩ, Or.inr (Or.inl ⟨zC, zB, hv⟩)⟩)
      obtain ⟨a, hQ⟩ := quotViol_of_aViol hp hq hΛ (subgroupOf_mem_restrictFamily hCΩ hCH)
        (aViol_restrict hp hΩ hCH hBH hv)
      obtain ⟨i', R, S, hR, hS, hCR, hBS⟩ := hQ.exists_components D
      have := compMembers_unique hΦ D ih (⟨S, hS, hBS⟩ : barImg H B ∈ compMembers D i')
      subst this
      exact ⟨R, hR, hCR⟩
    · obtain ⟨-, z, hzB, hzC⟩ := ht
      have hCH : C ≤ H :=
        hH C (Relation.ReflTransGen.tail hB ⟨hCΩ, Or.inr (Or.inr ⟨⟨hCΩ, z, hzB, hzC⟩, hne⟩)⟩)
      exact twin_mem_compMembers hp D hi' ih
        ⟨barImg_mem H hCΩ hCH, _, isUniqueInvolution_barImg H hzB hBH,
          isUniqueInvolution_barImg H hzC hCH⟩

theorem exists_tag_g2 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {H K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω) (hKH : K ≤ H) (hJH : J ≤ H)
    (hv : AViol Ω K J zK zJ) (D : OmegaLie p f (oddQuotientFamily (restrictFamily Ω H))) :
    ∃ i : Fin D.card, D.tag i = .G2 ∧ barImg H K ∈ compMembers D i := by
  have hΛ : HypOmegaMod p f (restrictFamily Ω H) := hΩ.restrict H
  have hΦ : HypOmegaMod p f (oddQuotientFamily (restrictFamily Ω H)) :=
    oddQuotHyp p f hp hq ↥H _ hΛ _ (CFSG.ComponentClassification.OddCore.odd_card ↥H)
  obtain ⟨a, hQ⟩ := quotViol_of_aViol hp hq hΛ (subgroupOf_mem_restrictFamily hK hKH)
    (aViol_restrict hp hΩ hKH hJH hv)
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := hQ.exists_components D
  refine ⟨i, ?_, ⟨R, hR, hKR⟩⟩
  by_contra hne
  rw [hKR, hJS] at hQ
  by_cases hD : D.tag i = .trialityD4
  · exact G2D4Models.quotViol_false_of_trialityD4 hp hq hΦ D hD hR hS hQ
  · exact hQ.false_of_classical hp hq hΦ D hne hD hR hS

theorem hom_surjective (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {H K : Subgroup G}
    (hK : K ∈ Ω) (hHdef : omegaGen (aStar Ω K) = H)
    (D : OmegaLie p f (oddQuotientFamily (restrictFamily Ω H))) {i : Fin D.card}
    (hi : D.tag i = .G2) (hKi : barImg H K ∈ compMembers D i) : Function.Surjective (D.hom i) := by
  have hMH : ∀ M ∈ aStar Ω K, M ≤ H := fun M hM => hHdef ▸ le_omegaGen hM
  have hcomp := barImg_mem_comp hp hq hΩ hK hMH D hi hKi
  have hMQ : ∀ M ∈ aStar Ω K,
      M ≤ ((D.hom i).range.comap (oddQuot ↥H)).map H.subtype := by
    intro M hM m hm
    obtain ⟨R, -, hMR⟩ := hcomp M hM
    refine ⟨⟨m, hMH M hM hm⟩, ?_, rfl⟩
    have hmem : oddQuot ↥H ⟨m, hMH M hM hm⟩ ∈ barImg H M :=
      ⟨⟨m, hMH M hM hm⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    rw [hMR] at hmem
    exact Subgroup.map_le_range _ _ hmem
  have hHQ : H ≤ ((D.hom i).range.comap (oddQuot ↥H)).map H.subtype :=
    hHdef.symm.le.trans (iSup₂_le fun M hM => hMQ M hM)
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨q, hq', hqy⟩ := hHQ y'.2
  have hqy' : q = y' := Subtype.ext hqy
  subst hqy'
  exact hq'

omit [Fact p.Prime] in
structure G2Section (H : Subgroup G) (z : G) : Prop where
  quasisimple : CFSG.IsQuasisimple (↥H ⧸ classicalInvolutionOddCore ↥H)
  conj : ∀ x ∈ H, x * x = 1 → x ≠ 1 → ∃ h ∈ H, h * z * h⁻¹ = x

theorem g2Section_of_violation (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {n : ℕ}
    (hn : CITBelowU p f n) {H K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω)
    (hHdef : omegaGen (aStar Ω K) = H) (hv : AViol Ω K J zK zJ) (hlt : Nat.card ↥H < n) :
    G2Section H zK := by
  have hMH : ∀ M ∈ aStar Ω K, M ≤ H := fun M hM => hHdef ▸ le_omegaGen hM
  have hKH : K ≤ H := hMH K Relation.ReflTransGen.refl
  have hJS : J ∈ aStar Ω K := Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  have hJH : J ≤ H := hMH J hJS
  have hΛ : HypOmegaMod p f (restrictFamily Ω H) := hΩ.restrict H
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hΦ : HypOmegaMod p f (oddQuotientFamily (restrictFamily Ω H)) :=
    oddQuotHyp p f hp hq ↥H _ hΛ _ hodd
  have hO : classicalInvolutionOddCore (↥H ⧸ classicalInvolutionOddCore ↥H) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥H
  have hlt' : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hlt
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΦ.conjInvariant hΦ.classical
    ⟨_, barImg_mem H hK hKH⟩ hO hlt'
  obtain ⟨i, hi, hKi⟩ := exists_tag_g2 hp hq hΩ hK hKH hJH hv D
  have hsurj := hom_surjective hp hq hΩ hK hHdef D hi hKi
  have hinj := hom_injective_of_g2d4 hp D (Or.inl hi)
  have hqs : CFSG.IsQuasisimple (D.model i).K := by
    have h0 := ModelFacts.modelClauseZero (D.tag i) (D.rank i) p (D.exp i) Fact.out
      (D.isFundTag i) (D.admissible i)
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp h0.1
  let e : (D.model i).K ≃* (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    MulEquiv.ofBijective (D.hom i) ⟨hinj, hsurj⟩
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs, ?_⟩
  intro x hxH hx2 hx1
  have hz : IsUniqueInvolution K zK := hv.hzK
  have hzH : zK ∈ H := hKH hz.mem
  set z' : ↥H := ⟨zK, hzH⟩ with hz'
  set x' : ↥H := ⟨x, hxH⟩ with hx'
  have hz'2 : z' * z' = 1 := Subtype.ext hz.sq
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hz'1 : oddQuot ↥H z' ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val
    (eq_one_of_mul_self_of_mem_odd hodd ((QuotientGroup.eq_one_iff _).mp h) hz'2))
  have hx'1 : oddQuot ↥H x' ≠ 1 := fun h => hx1 (congrArg Subtype.val
    (eq_one_of_mul_self_of_mem_odd hodd ((QuotientGroup.eq_one_iff _).mp h) hx'2))
  obtain ⟨c₁, hc₁⟩ := hsurj (oddQuot ↥H z')
  obtain ⟨c₂, hc₂⟩ := hsurj (oddQuot ↥H x')
  have hc₁sq : c₁ * c₁ = 1 :=
    hinj (by rw [map_mul, hc₁, ← map_mul, hz'2, map_one, map_one])
  have hc₂sq : c₂ * c₂ = 1 :=
    hinj (by rw [map_mul, hc₂, ← map_mul, hx'2, map_one, map_one])
  have hc₁ne : c₁ ≠ 1 := fun h => hz'1 (by rw [← hc₁, h, map_one])
  have hc₂ne : c₂ ≠ 1 := fun h => hx'1 (by rw [← hc₂, h, map_one])
  obtain ⟨h₀, hh₀⟩ := g2_model_involutions_conj hi hp (D.admissible i) hc₁sq hc₂sq hc₁ne hc₂ne
  obtain ⟨h₁, hh₁⟩ := QuotientGroup.mk'_surjective _ (D.hom i h₀)
  have hconj : oddQuot ↥H (h₁ * z' * h₁⁻¹) = oddQuot ↥H x' := by
    rw [map_mul, map_mul, map_inv, hh₁, ← hc₁, ← map_inv, ← map_mul, ← map_mul, hh₀, hc₂]
  have hu2 : h₁ * z' * h₁⁻¹ * (h₁ * z' * h₁⁻¹) = 1 := by
    calc h₁ * z' * h₁⁻¹ * (h₁ * z' * h₁⁻¹) = h₁ * (z' * z') * h₁⁻¹ := by group
      _ = 1 := by rw [hz'2]; group
  obtain ⟨m, -, hm⟩ := exists_conj_of_map_eq_of_involutions hodd hu2 hx'2 hconj
  refine ⟨((m * h₁ : ↥H) : G), (m * h₁).2, ?_⟩
  have := congrArg Subtype.val hm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  have hx'v : (x' : G) = x := rfl
  have hz'v : (z' : G) = zK := rfl
  rw [hz'v, hx'v] at this
  rw [← this]
  group

end CFSG.ClassicalInvolution.Asc77.T3Core
