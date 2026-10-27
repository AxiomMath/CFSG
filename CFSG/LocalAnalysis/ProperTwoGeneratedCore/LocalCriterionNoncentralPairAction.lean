module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionPerfect
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.HighRankPair

universe u

variable {G : Type u} [Group G]

theorem pointRoots_eq {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (u : G) :
    pointRoots H z u = involutionPointClass z ∩ (H : Set G) ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) := by
  ext x
  constructor
  · rintro ⟨⟨g, rfl⟩, hxu⟩
    exact ⟨⟨⟨g, rfl⟩, (pointClass_conjugate_mem_iff h g).mpr g.2⟩, hxu⟩
  · rintro ⟨⟨⟨g, rfl⟩, hgH⟩, hxu⟩
    exact ⟨⟨⟨g, (pointClass_conjugate_mem_iff h g).mp hgH⟩, rfl⟩, hxu⟩

theorem localHull_isPerfect {z u : G} (huz : Commute u z)
    (hclass : involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) =
      conjugacyWithin (localInvolutionPointHull z u) z) {a b : G}
    (ha : a ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G))
    (hb : b ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G))
    (hab : a * b ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) :
    Group.IsPerfect (localInvolutionPointHull z u) := by
  have hDL : ∀ x ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G),
      x ∈ localInvolutionPointHull z u := fun x hx => Subgroup.subset_closure hx
  have hzL := hDL z ⟨distinguished_mem_pointClass z,
    Subgroup.mem_centralizer_singleton_iff.mpr huz.eq.symm⟩
  have hconj : ∀ x (hx : x ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)),
      IsConj (⟨z, hzL⟩ : localInvolutionPointHull z u) ⟨x, hDL x hx⟩ := by
    intro x hx
    rw [hclass] at hx
    obtain ⟨l, hl⟩ := hx
    exact isConj_iff.mpr ⟨l⁻¹, Subtype.ext (by simpa using hl)⟩
  have hgen : Subgroup.closure (conjugatesOf (⟨z, hzL⟩ : localInvolutionPointHull z u)) = ⊤ := by
    apply Subgroup.map_injective (localInvolutionPointHull z u).subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    change _ = Subgroup.closure _
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      rw [hclass]
      exact ⟨c⁻¹, by simp⟩
    · intro hx
      exact ⟨⟨x, hDL x hx⟩, hconj x hx, rfl⟩
  exact single_class_generated_group_isPerfect _ _ _ hgen (hconj a ha) (hconj b hb)
    (hconj (a * b) hab)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

universe u

theorem noncentral_pair_action {G : Type u} [Group G] [Finite G]
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    (hSz : SuzukiOuterOdd) (hU : UnitaryAutomorphismRealization) :
    NoncentralPairActionTheorem G := by
  intro H z h beta hbeta t ht u v hu hu2 huz hut hv hv2 huv hmove
  classical
  have hbase := rightCosetStabilizer_base H
  have huH : u ∈ H := hbase ▸ hu.1
  have hvH : v ∈ H := hbase ▸ hv.1
  have htH : t ∉ H := by
    intro htH
    apply hbeta
    rw [← ht.2]
    exact (mem_rightCosetStabilizer_iff H _ t).mp (by rw [hbase]; exact htH)
  have hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq.symm))
  obtain ⟨-, hLnormal, -, hclassY, hYL, -, -, hxor⟩ :=
    minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hR1 huH hu2 huz hescape
  have hvY : v ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huv.eq.symm
  have hvN : v ∈ Subgroup.normalizer ((localInvolutionPointHull z u : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (localInvolutionPointHull_le_centralizer z u)).mp hLnormal hvY
  have hv2' : v * v = 1 := by rw [← sq, ← hv2, pow_orderOf_eq_one]
  have hroots := pointRoots_eq h.local_datum u
  have hvroot : ∀ x ∈ involutionPointClass z ∩ (H : Set G) ∩
      (Subgroup.centralizer ({u} : Set G) : Set G), v * x * v⁻¹ ∈ involutionPointClass z ∩
        (H : Set G) ∩ (Subgroup.centralizer ({u} : Set G) : Set G) := by
    rintro x ⟨⟨⟨g, rfl⟩, hxH⟩, hxY⟩
    refine ⟨⟨⟨g * v⁻¹, by simp [rightConjugateElem, mul_assoc]⟩,
      H.mul_mem (H.mul_mem hvH hxH) (H.inv_mem hvH)⟩, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hvY hxY) (Subgroup.inv_mem _ hvY)
  rcases hxor with ⟨⟨-, hone, -⟩, -⟩ | ⟨⟨-, U, hUset, helem, hU4, -, -, -, hRL, hmodels, -⟩, -⟩
  ·
    exfalso
    obtain ⟨x, hx, hvx⟩ := hmove
    rw [hroots] at hx
    have hvz := hvroot x hx
    rw [hone] at hx hvz
    rw [Set.mem_singleton_iff.mp hx] at hvz hvx
    exact hvx (mul_inv_eq_iff_eq_mul.mp (Set.mem_singleton_iff.mp hvz))
  have hmemU : ∀ x ∈ U, x = 1 ∨ x ∈ involutionPointClass z ∩ (H : Set G) ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) := by
    intro x hx
    have hx' : x ∈ (U : Set G) := hx
    rwa [hUset] at hx'
  have hUL : U ≤ localInvolutionPointHull z u := fun x hx => by
    rcases hmemU x hx with rfl | hx'
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx'.1.1, hx'.2⟩
  have hUH : U ≤ H := fun x hx => by
    rcases hmemU x hx with rfl | hx'
    · exact H.one_mem
    · exact hx'.1.2
  have hvU : ∀ x ∈ U, v * x * v⁻¹ ∈ U := by
    intro x hx
    have hU' : v * x * v⁻¹ ∈ (U : Set G) := by
      rw [hUset]
      rcases hmemU x hx with rfl | hx'
      · exact Or.inl (by simp)
      · exact Or.inr (hvroot x hx')
    exact hU'
  have h1D : (1 : G) ∉ involutionPointClass z := fun h1 => by
    have := order_two_of_mem_pointClass h.local_datum.distinguished_order h1
    simp at this
  have hUroots : pointRoots H z u = (U : Set G) \ {1} := by
    rw [hroots]
    ext x
    constructor
    · intro hx
      refine ⟨?_, fun hx1 => h1D (Set.mem_singleton_iff.mp hx1 ▸ hx.1.1)⟩
      rw [hUset]
      exact Or.inr hx
    · rintro ⟨hx, hx1⟩
      exact (hmemU x hx).resolve_left hx1
  have hmoveU : ∃ x ∈ U, ¬ Commute v x := by
    obtain ⟨x, hx, hvx⟩ := hmove
    rw [hUroots] at hx
    exact ⟨x, hx.1, hvx⟩
  have hcen : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hRL (Subgroup.mem_map_of_mem _ hx)).2
    rwa [Subtype.ext hyx] at hy
  have hU2 : 2 < Nat.card U := by omega
  obtain ⟨a, ha1, -⟩ := exists_ne_ne_of_two_lt_card hU2 1 1
  obtain ⟨b, hb1, hba⟩ := exists_ne_ne_of_two_lt_card hU2 1 a
  have hmemDY : ∀ x : U, x ≠ 1 → (x : G) ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) := by
    intro x hx
    rcases hmemU x x.2 with hx1 | hx'
    · exact absurd (Subtype.ext hx1) hx
    · exact ⟨hx'.1.1, hx'.2⟩
  have hab : a * b ≠ 1 := by
    intro hab
    apply hba
    have ha2 : a * a = 1 := Subtype.ext (by
      simpa [sq] using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a a.2)
    exact (eq_inv_of_mul_eq_one_right hab).trans (inv_eq_of_mul_eq_one_right ha2)
  have := localHull_isPerfect huz (hclassY.trans hYL) (hmemDY a ha1) (hmemDY b hb1)
    (hmemDY (a * b) hab)
  have hfixmem : ∀ (γ : rightCosetSpace H) (g : G), g ∈ rightCosetStabilizer H γ →
      pointRightCosetMul H γ g = γ := fun γ g hg => by
    rw [pointRightCosetMul_eq_translate]
    exact (mem_rightCosetStabilizer_iff H γ g).mp hg
  let αΔ : elementFixedSet H u := ⟨rightCosetMk H 1, hfixmem _ u hu.1⟩
  let βΔ : elementFixedSet H u := ⟨beta, hfixmem _ u hu.2⟩
  have hvα : pointRightCosetMul H (αΔ : pointRightCosetSpace H) v = αΔ := hfixmem _ v hv.1
  have hvβ : pointRightCosetMul H (βΔ : pointRightCosetSpace H) v = βΔ := hfixmem _ v hv.2
  have hαβ : αΔ ≠ βΔ := fun hαβ => hbeta (congrArg Subtype.val hαβ).symm
  have hHα : ∀ l : localInvolutionPointHull z u, (l : G) ∈ H →
      (letI := hullFixedSetAction H z u; l • αΔ = αΔ) := by
    intro l hl
    apply Subtype.ext
    exact hfixmem _ _ (by rw [hbase]; exact H.inv_mem hl)
  rcases hmodels with ⟨-, f, hf, hUc, E, ψ, hψα, hψ⟩ | ⟨-, m, hm, hUc, E, ψ, hψα, hψ⟩ |
    ⟨-, f, hf, hUc, K, hK, hKfin, A, hA, hKcard, hfixedK, ρ, hρ, E, ψ, hψα, hψ⟩
  ·
    have hUB : ∀ x (hx : x ∈ U), E (QuotientGroup.mk ⟨x, hUL hx⟩) •
        GorensteinWalter.psl2ProjectiveInfinity (BinaryGaloisField f) =
          GorensteinWalter.psl2ProjectiveInfinity (BinaryGaloisField f) := by
      intro x hx
      have h1 := hψ ⟨x, hUL hx⟩ αΔ
      rw [hHα _ (hUH hx), hψα αΔ rfl] at h1
      exact h1.symm
    obtain ⟨a, ha1, hfa, hFI, hSC, hcount⟩ :=
      linear_square_field_action hcen helem hUL hf hUc E hUB hvN hv2' hvU hmoveU
    refine ⟨a, ha1, hFI, hSC, ?_, by rw [hUroots]; exact hcount⟩
    rw [hUroots, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem U.one_mem,
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hUc, hfa]
  ·
    exfalso
    let := suzukiOvoidAction m
    obtain ⟨θ, hθ, hθθ⟩ := exists_quotient_involution _ hvN hv2' E
    obtain ⟨τ, hτ, hττ, hτfix⟩ :=
      exists_point_involution hvY hvN hv2' E (fun x p => x • p) ψ hψ θ hθ
    have htriv := suzuki_point_involution_trivial hSz hm θ hθθ τ hτ hττ
      (ψ.injective.ne hαβ) (hτfix αΔ hvα) (hτfix βΔ hvβ)
    obtain ⟨x, hx, hvx⟩ := hmoveU
    exact hvx (commute_of_quotient_fixed helem hvN ⟨x, hUL hx⟩ hx (hvU x hx)
      (E.injective (by rw [← hθ, htriv])))
  ·
    exfalso
    obtain ⟨θ, hθ, hθθ⟩ := exists_quotient_involution _ hvN hv2' E
    obtain ⟨τ, hτ, hττ, hτfix⟩ :=
      exists_point_involution hvY hvN hv2' E (fun x p => ρ x p) ψ hψ θ hθ
    have hKcard' : Nat.card K = (2 ^ f) ^ 2 := by rw [hKcard, hUc]
    have hfixedK' : Nat.card {x : K // A.conj x = x} = 2 ^ f := by rw [hfixedK, hUc]
    have hB : ∀ y : ProjectiveSpecialUnitaryMatrixGroup A,
        y ∈ unitaryCoordinateStabilizer A 0 ↔ ρ y (ψ αΔ) = ψ αΔ := by
      intro y
      rw [hψα αΔ rfl]
      constructor
      · intro hy
        apply Subtype.ext
        rw [hρ]
        exact hy
      · intro hy
        have hy' := congrArg Subtype.val hy
        rw [hρ] at hy'
        exact hy'
    have hθB : ∀ y ∈ unitaryCoordinateStabilizer A 0, θ y ∈ unitaryCoordinateStabilizer A 0 := by
      intro y hy
      rw [hB] at hy ⊢
      rw [← hτfix αΔ hvα, ← hτ, hy]
    obtain ⟨σ, A', -, hreal⟩ := hU K A f hf hKcard' hfixedK' hA θ
    have hfix := unitary_realized_involution_fixed A f hf hKcard' hfixedK' hA θ hθθ hθB σ A' hreal
    obtain ⟨x, hx, hvx⟩ := hmoveU
    apply hvx
    apply commute_of_quotient_fixed helem hvN ⟨x, hUL hx⟩ hx (hvU x hx)
    apply E.injective
    rw [← hθ]
    by_cases hx1 : x = 1
    · subst hx1
      have h1 : (⟨1, hUL hx⟩ : localInvolutionPointHull z u) = 1 := rfl
      rw [h1, QuotientGroup.mk_one, map_one, map_one]
    · apply hfix
      · have h1 := hψ ⟨x, hUL hx⟩ αΔ
        rw [hHα _ (hUH hx)] at h1
        rw [hB]
        exact h1.symm
      · have hl2 : (⟨x, hUL hx⟩ : localInvolutionPointHull z u) ^ 2 = 1 := Subtype.ext (by
          simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx)
        rw [MulEquiv.orderOf_eq]
        refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hl2, QuotientGroup.mk_one]) ?_
        intro hq
        have hmem := (QuotientGroup.eq_one_iff _).mp hq
        have hord : orderOf (⟨x, hUL hx⟩ : localInvolutionPointHull z u) = 2 :=
          orderOf_eq_prime hl2 (fun h1 => hx1 (congrArg Subtype.val h1))
        have hdvd : orderOf (⟨_, hmem⟩ : CFSG.oddCore (localInvolutionPointHull z u)) ∣
            Nat.card (CFSG.oddCore (localInvolutionPointHull z u)) := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, hord] at hdvd
        exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
          (even_iff_two_dvd.mpr hdvd)

end CFSG.ProperTwoGeneratedCore.HighRankPair
