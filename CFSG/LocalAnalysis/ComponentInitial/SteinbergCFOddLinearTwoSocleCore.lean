module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearTwoSocle
public import CFSG.CharacterTheory.Semidihedral.ProjectiveNonsquareInvolutions
public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergCF

open Equiv Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.SymmetricLocal
  (faithful_projective_linear_two_socle_involution_component_model)
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField subfieldCoordinateImage
  subfieldCoordinateMap)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog (subfieldGImage)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD
  subfieldD_injective)

theorem exists_not_isSquare_unit (k : Type*) [Field k] [Finite k] (hk : Odd (Nat.card k)) :
    ∃ t : kˣ, ¬ IsSquare t := by
  have : Fintype k := Fintype.ofFinite k
  have hchar : ringChar k ≠ 2 := by
    intro h
    have h2 := (FiniteField.even_card_iff_char_two (F := k)).mp h
    rw [← Nat.card_eq_fintype_card] at h2
    exact Nat.not_even_iff_odd.mpr hk (Nat.even_iff.mpr h2)
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare hchar
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, by rw [mul_zero]⟩)
  refine ⟨Units.mk0 b hb0, ?_⟩
  rw [CFSG.Semidihedral.SemilinearOuterQuotient.isSquare_unit_iff]
  exact hb

theorem subgroupOf_coordinateD_ne_top (k : Type) [Field k] [Finite k] (hk : Odd (Nat.card k)) :
    (coordinateG k).subgroupOf (coordinateD k) ≠ ⊤ := by
  intro h
  obtain ⟨t, ht⟩ := exists_not_isSquare_unit k hk
  have hmem : CFSG.Semidihedral.MatrixCoverData.glProjective k
      (CFSG.Semidihedral.MatrixCoverData.J k t) ∈ (coordinateG k).subgroupOf (coordinateD k) := by
    rw [h]
    exact mem_top _
  apply ht
  rw [← CFSG.Semidihedral.MatrixCoverData.J_det k t]
  exact (CFSG.Semidihedral.ProjectiveNonsquareInvolutions.projective_mem_G_iff k _).mp hmem

theorem not_mem_of_outer {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal] {a : Y}
    (houter : MulAut.conjNormal a ∉ (MulAut.conj : D →* MulAut D).range) : a ∉ D := by
  intro haD
  apply houter
  refine ⟨⟨a, haD⟩, ?_⟩
  ext w
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem not_lieModel_psl_two_of_centralizer_le_zpowers_sup {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} [D.Normal] (hDsimple : IsSimpleGroup D) (hDnonab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)))
    (hCa : centralizer ({a} : Set Y) ≤ zpowers a ⊔ J) {p f : ℕ} (hp : Odd p) :
    ¬ CFSG.Blueprint.LieModel D .PSL 2 p f := by
  intro hmodel
  rcases hmodel with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  swap
  · exact absurd h0 (by norm_num)
  swap
  · exact absurd h0 (by norm_num)
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨⟨hpp, hf, -, h22, h23⟩, K, hKf, hKfin, hK, ⟨ψ⟩⟩ := hm
  have : Fact p.Prime := ⟨hpp⟩
  have h2 : 2 ≤ p ^ f := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hne2 : p ^ f ≠ 2 := fun h => h22 (by rw [h])
  have hne3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
  have h4 : 4 ≤ p ^ f := by omega
  let φ : D ≃* coordinateG K := ψ.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (pslEquivCoordinateG K))
  obtain ⟨-, -, σ, -, -, hk, ρ, -, -, -, -, d, -, -, -, -, hW, hL, -, -, -, -, -, -, -, -, -, -,
    -, houter, -, -, -, -⟩ :=
    faithful_projective_linear_two_socle_involution_component_model hDsimple hDnonab hCD ha hJD
      hJ hf hK h4 φ
  have haD : a ∉ D := not_mem_of_outer houter
  have hDC : D ⊓ centralizer ({a} : Set Y) = J := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.mp hx
      have hcJ : ∀ h ∈ J, a * h = h * a := fun h hh =>
        mem_centralizer_iff.mp (hJ.1 hh) a (Set.mem_singleton a)
      have hnorm : zpowers a ≤ normalizer (J : Set Y) := by
        rw [zpowers_le, mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [hcJ y hy, mul_inv_cancel_right]
          exact hy
        · intro hy
          have h1 := hcJ _ hy
          have h2 : a * y * a⁻¹ = y := by
            have h3 : a * (a * y * a⁻¹) = a * y := by
              rw [h1]
              group
            exact mul_left_cancel h3
          rwa [h2] at hy
      have hx' : x ∈ ((zpowers a ⊔ J : Subgroup Y) : Set Y) := hCa hxC
      rw [coe_mul_of_left_le_normalizer_right (zpowers a) J hnorm] at hx'
      obtain ⟨y, hy, j, hj, hyj⟩ := hx'
      simp only at hyj
      subst hyj
      have hyD : y ∈ D := by
        have := D.mul_mem hxD (D.inv_mem (hJD hj))
        rwa [mul_inv_cancel_right] at this
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · have h1 : a ^ n = 1 := by
          rw [← zpow_mod_orderOf, ha]
          exact_mod_cast (by rw [h, zpow_zero] : a ^ (n % 2) = 1)
        rw [h1, one_mul]
        exact hj
      · exfalso
        apply haD
        have h1 : a ^ n = a := by
          rw [← zpow_mod_orderOf, ha]
          exact_mod_cast (by rw [h, zpow_one] : a ^ (n % 2) = a)
        rwa [h1] at hyD
    · exact le_inf hJD hJ.1
  have heq : subfieldCoordinateImage K (fixedField K σ) = subfieldGImage (fixedField K σ) := by
    have h1 : CFSG.LocalAnalysis.ComponentInitial.conjSub d
        (subfieldCoordinateImage K (fixedField K σ)) =
        CFSG.LocalAnalysis.ComponentInitial.conjSub d (subfieldGImage (fixedField K σ)) := by
      rw [← hW, hDC, hL]
    have h2 := congrArg (CFSG.LocalAnalysis.ComponentInitial.conjSub d⁻¹) h1
    rwa [CFSG.LocalAnalysis.ComponentInitial.conjSub_inv_conjSub,
      CFSG.LocalAnalysis.ComponentInitial.conjSub_inv_conjSub] at h2
  set k := fixedField K σ with hkdef
  have hinj : Function.Injective ((coordinateD K).subtype.comp (subfieldD k)) :=
    (coordinateD K).subtype_injective.comp (subfieldD_injective k)
  have htop : (coordinateG k).subgroupOf (coordinateD k) = ⊤ := by
    apply map_injective hinj
    rw [← MonoidHom.range_eq_map]
    exact heq.symm
  exact subgroupOf_coordinateD_ne_top k (by rw [hk]; exact hp.pow) htop

theorem isQuasisimple_of_isSimpleGroup' {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : CFSG.Assembly.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hQ
  have hZ : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (by rw [h]; exact mem_top b) a) hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · refine absurd ?_ hab
      rw [← commutatorElement_eq_one_iff_mul_comm, ← mem_bot, ← h, commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    · exact h
  · let e : Q ⧸ center Q ≃* Q :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

theorem exists_ne_GL_three_two : ∃ a b : GL (Fin 3) (ZMod 2), a * b ≠ b * a := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1, 0; 0, 1, 0; 0, 0, 1] (by decide),
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide), ?_⟩
  intro h
  have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) h
  revert this
  decide

theorem not_lieModel_psl_two_of_centralizer_eq_zpowers_sup {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} [D.Normal] (hDsimple : IsSimpleGroup D) (hDnonab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hCa : centralizer ({a} : Set Y) = zpowers a ⊔ J)
    (hJa : J ≤ centralizer ({a} : Set Y)) (hJ : Nonempty (GL (Fin 3) (ZMod 2) ≃* J))
    {p f : ℕ} (hp : Odd p) : ¬ CFSG.Blueprint.LieModel D .PSL 2 p f := by
  obtain ⟨eJ⟩ := hJ
  have : IsSimpleGroup J := by
    have := BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
    exact eJ.symm.isSimpleGroup
  have hJnonab : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_GL_three_two
    exact ⟨eJ x, eJ y, fun h => hxy (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  have hcJ : ∀ h ∈ J, a * h = h * a := fun h hh =>
    mem_centralizer_iff.mp (hJa hh) a (Set.mem_singleton a)
  have haN : a ∈ normalizer (J : Set Y) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcJ y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hcJ _ hy
      have h2 : a * y * a⁻¹ = y := by
        have h3 : a * (a * y * a⁻¹) = a * y := by
          rw [h1]
          group
        exact mul_left_cancel h3
      rwa [h2] at hy
  have hCN : centralizer ({a} : Set Y) ≤ normalizer (J : Set Y) := by
    rw [hCa]
    exact sup_le ((zpowers_le).mpr haN) le_normalizer
  have hJn : (J.subgroupOf (centralizer ({a} : Set Y))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJa).mpr hCN
  have hcomp : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)) :=
    ⟨hJa, CFSG.Assembly.IsSubnormal.step hJa hJn (CFSG.Assembly.IsSubnormal.refl _),
      isQuasisimple_of_isSimpleGroup' hJnonab⟩
  exact not_lieModel_psl_two_of_centralizer_le_zpowers_sup hDsimple hDnonab hCD ha hJD hcomp
    hCa.le hp

end CFSG.LocalAnalysis.ComponentInitial.SteinbergCF
