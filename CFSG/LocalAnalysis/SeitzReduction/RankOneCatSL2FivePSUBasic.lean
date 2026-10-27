module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListBasic

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial

namespace FiveList

theorem lieModel_of_isComponent_unitary {E W : Type} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 1 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    (finrank E W = 2 ∧ StatedLieAdmissible .PSL 2 ℓ e ∧ LieModel (L ⧸ center L) .PSL 2 ℓ e) ∨
      (StatedLieAdmissible .PSU (finrank E W) ℓ e ∧
        LieModel (L ⧸ center L) .PSU (finrank E W) ℓ e) := by
  have hq3 := CatLeafProof.OddInner.three_le_pow hℓ hℓ2 he
  have hfix := CatLeafProof.OddInner.card_fixedSubfield hsigma hne hE
  rcases Nat.lt_or_ge (finrank E W) 3 with hW3 | hW3
  · rcases Nat.lt_or_ge (finrank E W) 2 with hW2 | hW2
    · have := CatalogueBUnitaryIsometry.isometry_one_solvable h (by omega)
      exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
    have hd : finrank E W = 2 := by omega
    by_cases h3 : ℓ ^ e = 3
    · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hd
        (hfix.trans h3)
      exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
    have hq5 := CatLeafProof.OddInner.five_le_pow hℓ hℓ2 he h3
    have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
      hne hd (by rw [hfix]; omega) (by rw [hfix]; exact h3)
    obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      sigma h hsym hnd hsigma hne hd
    have hadm : StatedLieAdmissible .PSL 2 ℓ e :=
      CatLeafProof.OddInner.admissible_PSL hℓ he le_rfl (Or.inr (by omega)) (Or.inr h3)
    obtain rfl := CentralQuotientLift.eq_of_isComponent_of_quasisimple hquasi
      (Abelianization.commutator_subset_ker _) hL
    have hSL : LieModel (Matrix.SpecialLinearGroup (Fin (1 + 1))
        (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ⧸ center _) .PSL (1 + 1) ℓ e :=
      Or.inl ⟨by decide,
        LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 _ hadm hfix⟩
    exact Or.inl ⟨hd, hadm, lieModel_centerQuotient_of_mulEquiv eSL.symm hSL⟩
  · have hadm : StatedLieAdmissible .PSU (finrank E W) ℓ e :=
      ⟨hℓ, he, hW3, fun h' => by have := (Prod.mk.inj h').2; omega⟩
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hℓ hℓ2 he hE hW3 h hsym hnd hsigma
      hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    exact Or.inr ⟨hadm, Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩⟩

theorem sixteen_dvd_card_sesqUnitaryGroup {p f : ℕ} {K V : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f = 5) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hdim : 2 ≤ finrank K V) :
    16 ∣ Nat.card (sesqUnitaryGroup B) := by
  obtain ⟨hU, -⟩ := LinearGroups.unitary_full_group_order h hB hBl rfl (by omega)
  rw [hq, show (5 : ℕ) = 5 ^ 1 by norm_num] at hU
  have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 (finrank K V) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]
    omega
  have h1 := Finset.prod_dvd_prod_of_subset _ _
    (fun i => (((5 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i)) hsub
  have h2 : ∏ i ∈ ({1, 2} : Finset ℕ), (((5 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 144 := by
    rw [Finset.prod_pair (by norm_num)]
    norm_num
  rw [h2] at h1
  have h3 : (16 : ℤ) ∣ (Nat.card (sesqUnitaryGroup B) : ℤ) := by
    rw [hU]
    exact Dvd.dvd.mul_left ((by norm_num : (16 : ℤ) ∣ 144).trans h1) _
  exact_mod_cast h3

theorem relIndex_unitarySpecial_dvd {p f : ℕ} {K V : Type} [Field K]
    (h : UnitaryFieldData p f K) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : 1 ≤ finrank K V) (G₀ : Subgroup (sesqUnitaryGroup B)) :
    (CatalogueBUnitaryB.unitarySpecial B).relIndex G₀ ∣ p ^ f + 1 := by
  obtain ⟨-, -, -, hcard, hker, -⟩ := LinearGroups.unitary_full_group_order h hB hBl rfl hV
  have hS : CatalogueBUnitaryB.unitarySpecial B = (LinearGroups.unitaryDet B).ker := hker.symm
  have hidx : (CatalogueBUnitaryB.unitarySpecial B).index = p ^ f + 1 := by
    rw [hS, Subgroup.index_ker, hcard]
  rw [← hidx]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem relIndex_sesqSpecialUnitaryGroup_dvd {p f : ℕ} {K V : Type} [Field K]
    (h : UnitaryFieldData p f K) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : 1 ≤ finrank K V) {G₀ : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hG₀ : G₀ ≤ sesqUnitaryGroup B) :
    (sesqSpecialUnitaryGroup B).relIndex G₀ ∣ p ^ f + 1 := by
  rw [← Subgroup.relIndex_subgroupOf hG₀]
  exact relIndex_unitarySpecial_dvd h hB hBl hV (G₀.subgroupOf (sesqUnitaryGroup B))

theorem card_normOneScalars_dvd_six {n p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f = 5) (hn : 1 ≤ n) :
    Nat.card (ClassicalGroups.UnitaryFlag.normOneScalars h
      (ClassicalGroups.UnitaryFlag.gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        n) ∣ 6 := by
  rw [RankThree.Classical.card_normOneScalars_one h hn, hq]
  exact Nat.gcd_dvd_right _ _

theorem thirty_two_dvd_of_two_pow_seven_dvd {s i z c : ℕ} (h7 : 2 ^ 7 ∣ s * i) (hi : i ∣ 6)
    (hs : s ∣ z * c) (hz : z ∣ 6) : 32 ∣ c := by
  have h1 : 2 ^ 7 ∣ s * 6 := h7.trans (Nat.mul_dvd_mul_left s hi)
  have h2 : 2 ^ 6 ∣ s * 3 := by
    rw [show s * 6 = 2 * (s * 3) by ring, show 2 ^ 7 = 2 * 2 ^ 6 by norm_num] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have h3 : 2 ^ 6 ∣ s := Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h2
  have hzc : z * c ∣ c * 6 := by
    rw [mul_comm c 6]
    exact Nat.mul_dvd_mul_right hz c
  have h4 : 2 ^ 6 ∣ c * 6 := h3.trans (hs.trans hzc)
  have h5 : 2 ^ 5 ∣ c * 3 := by
    rw [show c * 6 = 2 * (c * 3) by ring, show 2 ^ 6 = 2 * 2 ^ 5 by norm_num] at h4
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
  have h6 : 2 ^ 5 ∣ c := Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h5
  simpa using h6

theorem exists_component_of_map_inf {X Y : Type} [Group X] [Group Y] (Z : Subgroup X)
    [Z.Normal] (hZc : Z ≤ center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    (φ : X →* Y) (hφ : Function.Injective φ) (G₀ S₀ : Subgroup Y)
    (hmap : (fixedSubgroup ψ).map φ = G₀ ⊓ S₀) (hnormal : ((G₀ ⊓ S₀).subgroupOf G₀).Normal)
    {L : Subgroup (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))}
    (hL : IsComponent L) :
    ∃ N : Subgroup G₀, IsComponent N ∧ Nonempty (L ⧸ center L ≃* N ⧸ center N) := by
  obtain ⟨M, hM, ⟨eLM⟩⟩ := CatLeafProof.exists_component_of_quotientFixed Z hZc ψ hinv hL
  have hMF : Assembly.IsComponentOf (M.map (fixedSubgroup ψ).subtype) (fixedSubgroup ψ) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le M)).2 ?_
    have hMM : (M.map (fixedSubgroup ψ).subtype).subgroupOf (fixedSubgroup ψ) = M :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := isComponentOf_map_of_injective hMF φ hφ
  rw [hmap] at h1
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  let eMN := ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
      ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective φ hφ)).trans
    (Subgroup.subgroupOfEquivOfLe h2.1).symm
  exact ⟨_, h3, ⟨eLM.trans (QuotientGroup.congr _ _ eMN (Subgroup.map_center_eq eMN))⟩⟩

end FiveList

end CFSG.SeitzReduction.RankOne
