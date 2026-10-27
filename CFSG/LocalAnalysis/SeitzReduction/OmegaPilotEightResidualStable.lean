module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualGeneric
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightEndSign
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHabel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualField

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamily)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (plusCX plusCXstar coordinate_plus_pointFamily_orbit_subset)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit (conj_conjugacyFamily)
open scoped Pointwise

section FieldPart

variable {K : Type} [Field K] {n f : ℕ}

@[expose] noncomputable def plusImageFieldPart (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K) :=
  Classical.choose (plusRealization hf hK hn).2.2.2.2

theorem plusImageFieldPart_kappa (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (g : similarityPairs (coordinateQuadPlus n K)) :
    plusImageFieldPart hf hK hn ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right :=
  (Classical.choose_spec (plusRealization hf hK hn).2.2.2.2).1 g

theorem plusImageFieldPart_eq_one_iff (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (β : matrixProjectiveImage (coordinateQuadPlus n K)) :
    plusImageFieldPart hf hK hn β = 1 ↔
      (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) ∈
        (isometryConjugationHom (coordinateQuadPlus n K)).range := by
  have hker := (Classical.choose_spec (plusRealization hf hK hn).2.2.2.2).2.1
  change Classical.choose (plusRealization hf hK hn).2.2.2.2 β = 1 ↔ _
  rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  rfl

theorem conj_mem_isometryRange (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    MulAut.conj x ∈ (isometryConjugationHom (coordinateQuadPlus n K)).range := by
  have h : MulAut.conj x ∈ inner (matrixProjectiveDerived (coordinateQuadPlus n K)) := ⟨x, rfl⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.inner_eq_map_commutator] at h
  exact Subgroup.map_le_range _ _ h

theorem conj_mem_plusImage (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    MulAut.conj x ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
  obtain ⟨A, hA⟩ := conj_mem_isometryRange x
  rw [← hA]
  exact ⟨_, rfl⟩

theorem plusImageFieldPart_conj (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    plusImageFieldPart hf hK hn ⟨MulAut.conj x, conj_mem_plusImage x⟩ = 1 :=
  (plusImageFieldPart_eq_one_iff hf hK hn _).2 (conj_mem_isometryRange x)

end FieldPart

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldPair)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryAut)

omit [Finite K] [CharP K 2] in
theorem plusImageFieldPart_conj_mul_fieldAutHom (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (x : matrixProjectiveDerived (coordinateQuadPlus 4 K)) (c : K ≃+* K)
    (h : MulAut.conj x * fieldAutHom K 4 c ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    plusImageFieldPart hf hK (by norm_num) ⟨_, h⟩ = c := by
  have h1 : (⟨MulAut.conj x * fieldAutHom K 4 c, h⟩ :
      matrixProjectiveImage (coordinateQuadPlus 4 K)) =
      ⟨MulAut.conj x, conj_mem_plusImage x⟩ * ⟨fieldAutHom K 4 c, ⟨_, rfl⟩⟩ := Subtype.ext rfl
  rw [h1, map_mul, plusImageFieldPart_conj, one_mul]
  exact plusImageFieldPart_kappa hf hK _
    (fieldPair (coordinateQuadPlus 4 K) c (E7Pilot.coordinateQuadPlus_fieldMap 4 c))

theorem eq_conj_mul_fieldAutHom_of_smul_plusCX
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hβ : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hβX : β • plusCX 4 K = plusCX 4 K) :
    ∃ (x : matrixProjectiveDerived (coordinateQuadPlus 4 K)) (c : K ≃+* K),
      β = MulAut.conj x * fieldAutHom K 4 c := by
  obtain ⟨x, c, h | h⟩ := mem_image_normalForm le_rfl coordinateQuadPlus_lastPlaneVec hβ
  · exact ⟨x, c, h⟩
  · exfalso
    obtain ⟨hX, -⟩ := symmetryAut_lastPlaneVec_smul_plusCX (F := K)
    apply plusCX_ne_plusCXstar 4 K (by norm_num)
    rw [← hβX, h, mul_smul, mul_smul, fieldAutHom_smul_plusCX (by norm_num), hX, plusCXstar,
      conj_conjugacyFamily]

theorem eq_conj_of_smul_plusCX_of_fp_eq_one (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hβ : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hβX : β • plusCX 4 K = plusCX 4 K)
    (hfp : plusImageFieldPart hf hK (by norm_num) ⟨β, hβ⟩ = 1) :
    ∃ x : matrixProjectiveDerived (coordinateQuadPlus 4 K), β = MulAut.conj x := by
  obtain ⟨x, c, rfl⟩ := eq_conj_mul_fieldAutHom_of_smul_plusCX hβ hβX
  rw [plusImageFieldPart_conj_mul_fieldAutHom] at hfp
  exact ⟨x, by rw [hfp, map_one, mul_one]⟩

theorem mul_conj_mul_inv {P : Type*} [Group P] (γ : MulAut P) (x : P) :
    γ * MulAut.conj x * γ⁻¹ = MulAut.conj (γ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

end Four

section Stable

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem fusionStableIn_plusFour (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    FusionStableIn (matrixProjectiveImage (coordinateQuadPlus 4 K))
      (plusImageFieldPart hf hK (by norm_num)) := by
  classical
  set E := matrixProjectiveImage (coordinateQuadPlus 4 K) with hE
  set fp := plusImageFieldPart (n := 4) hf hK (by norm_num) with hfpdef
  set F₀ := projectivePointFamily (coordinateQuadPlus 4 K) with hF₀
  set X := plusCX 4 K with hX
  set X' := plusCXstar 4 K (by norm_num) with hX'
  obtain ⟨fpT, hfpT⟩ : ∃ fpT : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) →
      (K ≃+* K), ∀ β (h : β ∈ E), fpT β = fp ⟨β, h⟩ :=
    ⟨fun β => if h : β ∈ E then fp ⟨β, h⟩ else 1, fun β h => by simp [h]⟩
  have hmemE : ∀ δ, δ ∈ E ↔ δ • F₀ = F₀ := mem_image_iff_smul_pointFamily le_rfl
  have hXX : X ≠ X' := plusCX_ne_plusCXstar 4 K (by norm_num)
  have hγ₀F := plusFlipAut_smul_pointFamily 4 K (by norm_num : 0 < 4)
  have hγ₀X := plusFlipAut_smul_plusCX 4 K (by norm_num : 0 < 4)
  have hγ₀X' := plusFlipAut_smul_plusCXstar 4 K (by norm_num : 0 < 4)
  have hT : ∀ (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) {Y},
      Y ∈ plusFourTripleSet K → δ • Y ∈ plusFourTripleSet K :=
    fun δ _ hY => smul_mem_plusFourTripleSet δ hY
  have hfixT : ∀ β, β ∈ E → β • X = X → ∀ Y ∈ plusFourTripleSet K, β • Y = Y := by
    intro β hβ hβX Y hY
    rcases hY with rfl | rfl | rfl
    · exact (hmemE β).1 hβ
    · exact hβX
    · rcases smul_plusCX_of_mem_image hβ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hβX.symm.trans h) hXX
  have hconjN : ∀ β γ, β ∈ E → β • X = X → γ * β * γ⁻¹ ∈ E ∧ (γ * β * γ⁻¹) • X = X := by
    intro β γ hβ hβX
    have key : ∀ Y ∈ plusFourTripleSet K, (γ * β * γ⁻¹) • Y = Y := by
      intro Y hY
      rw [mul_smul, mul_smul, hfixT β hβ hβX _ (hT γ⁻¹ hY), smul_inv_smul]
    exact ⟨(hmemE _).2 (key _ (Or.inl rfl)), key _ (Or.inr (Or.inl rfl))⟩
  obtain ⟨H, hmemH⟩ : ∃ H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      ∀ γ, γ ∈ H ↔ ∀ β, β ∈ E → β • X = X → fpT (γ * β * γ⁻¹) = fpT β :=
    ⟨{ carrier := {γ | ∀ β, β ∈ E → β • X = X → fpT (γ * β * γ⁻¹) = fpT β}
       mul_mem' := fun {γ₁ γ₂} h₁ h₂ β hβ hβX => by
         obtain ⟨hβ', hβX'⟩ := hconjN β γ₂ hβ hβX
         have e1 : γ₁ * γ₂ * β * (γ₁ * γ₂)⁻¹ = γ₁ * (γ₂ * β * γ₂⁻¹) * γ₁⁻¹ := by group
         rw [e1, h₁ _ hβ' hβX', h₂ β hβ hβX]
       one_mem' := fun β _ _ => by simp only [one_mul, inv_one, mul_one]
       inv_mem' := fun {γ} h β hβ hβX => by
         obtain ⟨hβ', hβX'⟩ := hconjN β γ⁻¹ hβ hβX
         have h1 := h _ hβ' hβX'
         have e1 : γ * (γ⁻¹ * β * γ⁻¹⁻¹) * γ⁻¹ = β := by group
         rw [e1] at h1
         exact h1.symm }, fun _ => Iff.rfl⟩
  have hEH : E ≤ H := by
    intro ε hε
    rw [hmemH]
    intro β hβ _
    have hm : ε * β * ε⁻¹ ∈ E := mul_mem (mul_mem hε hβ) (inv_mem hε)
    rw [hfpT _ hm, hfpT _ hβ]
    have e1 : (⟨ε * β * ε⁻¹, hm⟩ : E) = ⟨ε, hε⟩ * ⟨β, hβ⟩ * (⟨ε, hε⟩ : E)⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, LinearPilot.ringEquiv_mul_comm (fp ⟨ε, hε⟩), mul_assoc,
      mul_inv_cancel, mul_one]
  have hHn : H.Normal := by
    refine ⟨fun h hh γ => ?_⟩
    rw [hmemH]
    intro β hβ hβX
    obtain ⟨hβ', hβX'⟩ := hconjN β γ⁻¹ hβ hβX
    have h1 := (hmemH h).1 hh _ hβ' hβX'
    obtain ⟨hhβ', hhβX'⟩ := hconjN _ h hβ' hβX'
    have hcE : h * (γ⁻¹ * β * γ⁻¹⁻¹) * h⁻¹ * (γ⁻¹ * β * γ⁻¹⁻¹)⁻¹ ∈ E :=
      mul_mem hhβ' (inv_mem hβ')
    have hcX : (h * (γ⁻¹ * β * γ⁻¹⁻¹) * h⁻¹ * (γ⁻¹ * β * γ⁻¹⁻¹)⁻¹) • X = X := by
      have h2 : (γ⁻¹ * β * γ⁻¹⁻¹)⁻¹ • X = X := by
        conv_lhs => rw [← hβX']
        rw [inv_smul_smul]
      rw [mul_smul, h2, hhβX']
    have hcfp : fp ⟨_, hcE⟩ = 1 := by
      have e1 : (⟨_, hcE⟩ : E) = ⟨_, hhβ'⟩ * (⟨_, hβ'⟩ : E)⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_inv, ← hfpT _ hhβ', ← hfpT _ hβ', h1, mul_inv_cancel]
    obtain ⟨x, hx⟩ := eq_conj_of_smul_plusCX_of_fp_eq_one hf hK hcE hcX hcfp
    have hkey : γ * h * γ⁻¹ * β * (γ * h * γ⁻¹)⁻¹ = MulAut.conj (γ x) * β := by
      rw [← mul_conj_mul_inv, ← hx]
      group
    have hm : MulAut.conj (γ x) * β ∈ E := mul_mem (conj_mem_plusImage _) hβ
    rw [hkey, hfpT _ hm, hfpT _ hβ]
    have e3 : (⟨MulAut.conj (γ x) * β, hm⟩ : E) = ⟨_, conj_mem_plusImage (γ x)⟩ * ⟨β, hβ⟩ :=
      Subtype.ext rfl
    rw [e3, map_mul, plusImageFieldPart_conj hf hK _ (γ x), one_mul]
  have hstab : E = MulAction.stabilizer (MulAut (matrixProjectiveDerived
      (coordinateQuadPlus 4 K))) F₀ := by
    ext δ
    rw [hmemE, MulAction.mem_stabilizer_iff]
  have hidx : E.index = 1 ∨ E.index = 3 := by
    rw [hstab, MulAction.index_stabilizer]
    exact orbit_pointFamily_ncard_four
  have hHtop : H = ⊤ := by
    rcases hidx with h1 | h3
    · exact eq_top_iff.2 ((Subgroup.index_eq_one.1 h1) ▸ hEH)
    · have hdvd := Subgroup.index_dvd_of_le hEH
      rw [h3] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact Subgroup.index_eq_one.1 h
      · exfalso
        have hrel := Subgroup.relIndex_mul_index hEH
        rw [h, h3] at hrel
        have hrel1 : E.relIndex H = 1 := by omega
        have hHE : H ≤ E := Subgroup.relIndex_eq_one.1 hrel1
        have hEn : E.Normal := by
          have h4 : H = E := le_antisymm hHE hEH
          rw [← h4]
          exact hHn
        have hEne : E ≠ ⊤ := fun h' => by
          rw [h', Subgroup.index_top] at h3
          omega
        obtain ⟨ε, hε⟩ : ∃ ε, ε ∉ E := by
          by_contra hc
          push Not at hc
          exact hEne (eq_top_iff.2 fun x _ => hc x)
        have hγ₀E : plusFlipAut 4 K (by norm_num) ∈ E := plusFlipAut_mem_image le_rfl
        have h4 := hEn.conj_mem _ hγ₀E ε⁻¹
        rw [hmemE, inv_inv, mul_smul, mul_smul] at h4
        have h5 : plusFlipAut 4 K (by norm_num) • (ε • F₀) = ε • F₀ := by
          have h6 := congrArg (ε • ·) h4
          simp only [smul_inv_smul] at h6
          exact h6
        have h7 : ε • F₀ ≠ F₀ := fun h' => hε ((hmemE ε).2 h')
        rcases hT ε (Or.inl rfl : F₀ ∈ plusFourTripleSet K) with h' | h' | h'
        · exact h7 h'
        · rw [h', hγ₀X] at h5
          exact hXX h5.symm
        · rw [h', hγ₀X'] at h5
          exact hXX h5
  intro β γ hβ hγ
  by_cases hγE : γ ∈ E
  · have e1 : (⟨γ * β * γ⁻¹, hγ⟩ : E) = ⟨γ, hγE⟩ * ⟨β, hβ⟩ * (⟨γ, hγE⟩ : E)⁻¹ :=
      Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, LinearPilot.ringEquiv_mul_comm (fp ⟨γ, hγE⟩), mul_assoc,
      mul_inv_cancel, mul_one]
  ·
    have hβX : β • X = X := by
      have h2 : γ⁻¹ • F₀ ≠ F₀ := fun h' => hγE ((hmemE γ).2 (by
        have h8 := congrArg (γ • ·) h'
        simp only [smul_inv_smul] at h8
        exact h8.symm))
      have h3 : β • (γ⁻¹ • F₀) = γ⁻¹ • F₀ := by
        have h8 := congrArg (γ⁻¹ • ·) ((hmemE _).1 hγ)
        simp only [mul_smul, inv_smul_smul] at h8
        exact h8
      rcases smul_plusCX_of_mem_image hβ with ⟨hX1, -⟩ | ⟨hX1, hX2⟩
      · exact hX1
      · exfalso
        rcases hT γ⁻¹ (Or.inl rfl : F₀ ∈ plusFourTripleSet K) with h' | h' | h'
        · exact h2 h'
        · rw [h', hX1] at h3
          exact hXX h3.symm
        · rw [h', hX2] at h3
          exact hXX h3
    have h1 := (hmemH γ).1 (hHtop ▸ Subgroup.mem_top γ) β hβ hβX
    rwa [hfpT _ hγ, hfpT _ hβ] at h1

end Stable

end CFSG.SeitzReduction.OmegaPilot
