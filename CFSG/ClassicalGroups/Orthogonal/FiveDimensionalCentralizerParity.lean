module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizer
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSimilarity
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizerParity

open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open TauCeti QuadraticMap

variable {K : Type} [Field K] [Finite K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V}

theorem exists_centralizer_element_not_mem_commutator
    (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    ∃ c : TauCeti.QuadraticMap.orthogonalGroup Q,
      c ∈ C0 F ∧ c * F.tO = F.tO * c ∧
      c ∉ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  have hchar : ringChar K ≠ 2 := by
    intro h2
    have hEven : Even (Nat.card K) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr (FiniteField.even_card_iff_char_two.mp h2)
    exact (Nat.not_even_iff_odd.mpr hodd) hEven
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hchar
  have hν0 : ν ≠ 0 := fun h => hν (h ▸ IsSquare.zero)
  have hKodd : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, hab⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hKodd
    (b := (1 : K)) (c := (1 : K)) one_ne_zero one_ne_zero ν
  have hab' : a ^ 2 + b ^ 2 = ν := by simpa using hab
  let v : V := a • F.e 0 + b • F.e 1
  have hvQ : Q v = ν := by
    rw [CFSG.RankThree.Classical.quad_smul_add_smul Q (F.orth 0 1 (by norm_num))]
    simp [F.norm 0 (by norm_num), F.norm 1 (by norm_num), hab']
  have hv0 : Q v ≠ 0 := by rw [hvQ]; exact hν0
  have hw : Q (F.e 2) = 1 := F.norm 2 (by norm_num)
  have hw0 : Q (F.e 2) ≠ 0 := by rw [hw]; exact one_ne_zero
  letI : Invertible (Q v) := invertibleOfNonzero hv0
  letI : Invertible (Q (F.e 2)) := invertibleOfNonzero hw0
  let c : TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflectionOrthogonal Q v *
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)
  have htv : (F.tO : V ≃ₗ[K] V) v = -v := by
    simp [FrameData.tO, v, F.t_e, add_comm]
  have hzv : (F.zO : V ≃ₗ[K] V) v = -v := by
    simp [FrameData.zO, v, F.z_e, add_comm]
  have htw : (F.tO : V ≃ₗ[K] V) (F.e 2) = F.e 2 := by
    simp [FrameData.tO, F.t_e]
  have hzw : (F.zO : V ≃ₗ[K] V) (F.e 2) = -F.e 2 := by
    simp [FrameData.zO, F.z_e]
  have htvQ : Q ((F.tO : V ≃ₗ[K] V) v) ≠ 0 := by
    rw [htv]
    simpa using hv0
  have hzvQ : Q ((F.zO : V ≃ₗ[K] V) v) ≠ 0 := by
    rw [hzv]
    simpa using hv0
  have htwQ : Q ((F.tO : V ≃ₗ[K] V) (F.e 2)) ≠ 0 := by
    rw [htw]
    exact hw0
  have hzwQ : Q ((F.zO : V ≃ₗ[K] V) (F.e 2)) ≠ 0 := by
    rw [hzw]
    simpa using hw0
  haveI : Invertible (Q ((F.tO : V ≃ₗ[K] V) v)) := invertibleOfNonzero htvQ
  haveI : Invertible (Q ((F.zO : V ≃ₗ[K] V) v)) := invertibleOfNonzero hzvQ
  haveI : Invertible (Q ((F.tO : V ≃ₗ[K] V) (F.e 2))) := invertibleOfNonzero htwQ
  haveI : Invertible (Q ((F.zO : V ≃ₗ[K] V) (F.e 2))) := invertibleOfNonzero hzwQ
  have htv_ref : TauCeti.QuadraticMap.reflectionOrthogonal Q ((F.tO : V ≃ₗ[K] V) v) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q v := by
    ext x
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
    rw [htv]
    simp [QuadraticMap.map_neg, polar_neg_left, neg_div, neg_smul, smul_neg]
  have hzv_ref : TauCeti.QuadraticMap.reflectionOrthogonal Q ((F.zO : V ≃ₗ[K] V) v) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q v := by
    ext x
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
    rw [hzv]
    simp [QuadraticMap.map_neg, polar_neg_left, neg_div, neg_smul, smul_neg]
  have htw_ref : TauCeti.QuadraticMap.reflectionOrthogonal Q ((F.tO : V ≃ₗ[K] V) (F.e 2)) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by
    ext x
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
    rw [htw]
  have hzw_ref : TauCeti.QuadraticMap.reflectionOrthogonal Q ((F.zO : V ≃ₗ[K] V) (F.e 2)) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by
    ext x
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
      TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
    rw [hzw]
    simp [QuadraticMap.map_neg, polar_neg_left, neg_div, neg_smul, smul_neg]
  have ht_sv_conj : F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.tO⁻¹ =
      TauCeti.QuadraticMap.reflectionOrthogonal Q v := by
    rw [TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv]
    exact htv_ref
  have hz_sv_conj : F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.zO⁻¹ =
      TauCeti.QuadraticMap.reflectionOrthogonal Q v := by
    rw [TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv]
    exact hzv_ref
  have ht_sw_conj : F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.tO⁻¹ =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by
    rw [TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv]
    exact htw_ref
  have hz_sw_conj : F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.zO⁻¹ =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by
    rw [TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv]
    exact hzw_ref
  have ht_sv : F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q v =
      TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.tO := by
    calc F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q v
        = (F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.tO⁻¹) * F.tO := by
          group
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.tO := by rw [ht_sv_conj]
  have hz_sv : F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q v =
      TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.zO := by
    calc F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q v
        = (F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.zO⁻¹) * F.zO := by
          group
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.zO := by rw [hz_sv_conj]
  have ht_sw : F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.tO := by
    calc F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)
        = (F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.tO⁻¹) * F.tO := by
          group
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.tO := by rw [ht_sw_conj]
  have hz_sw : F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.zO := by
    calc F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)
        = (F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.zO⁻¹) * F.zO := by
          group
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.zO := by rw [hz_sw_conj]
  have hct : c * F.tO = F.tO * c := by
    dsimp only [c]
    calc
      TauCeti.QuadraticMap.reflectionOrthogonal Q v *
          TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.tO
          = TauCeti.QuadraticMap.reflectionOrthogonal Q v *
              (TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.tO) := by
            rw [mul_assoc]
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q v *
            (F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)) := by rw [← ht_sw]
      _ = (TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.tO) *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by rw [← mul_assoc]
      _ = (F.tO * TauCeti.QuadraticMap.reflectionOrthogonal Q v) *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by rw [← ht_sv]
      _ = F.tO * (TauCeti.QuadraticMap.reflectionOrthogonal Q v *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)) := by rw [mul_assoc]
  have hcz : c ∈ Subgroup.centralizer ({F.zO} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    dsimp only [c]
    calc
      (TauCeti.QuadraticMap.reflectionOrthogonal Q v *
          TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)) * F.zO
          = TauCeti.QuadraticMap.reflectionOrthogonal Q v *
              (TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) * F.zO) := by rw [mul_assoc]
      _ = TauCeti.QuadraticMap.reflectionOrthogonal Q v *
            (F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)) := by rw [← hz_sw]
      _ = (TauCeti.QuadraticMap.reflectionOrthogonal Q v * F.zO) *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by rw [← mul_assoc]
      _ = (F.zO * TauCeti.QuadraticMap.reflectionOrthogonal Q v) *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2) := by rw [← hz_sv]
      _ = F.zO * (TauCeti.QuadraticMap.reflectionOrthogonal Q v *
            TauCeti.QuadraticMap.reflectionOrthogonal Q (F.e 2)) := by rw [mul_assoc]
  have hcSO : c ∈ QuadraticMap.specialOrthogonalWithin Q := by
    rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
    dsimp only [c]
    rw [Subgroup.coe_mul, map_mul, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.det_reflection, TauCeti.QuadraticMap.det_reflection]
    norm_num
  have hcC0 : c ∈ C0 F := ⟨hcSO, hcz⟩
  have hQ : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp F.nondeg
  have hdetc : CFSG.ClassicalInvolution.detSpinorNorm hQ c =
      (1, TauCeti.squareClassHom (unitOfInvertible (Q v))) := by
    dsimp only [c]
    rw [map_mul, CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal,
      CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal]
    have hwunit : unitOfInvertible (Q (F.e 2)) = 1 := by
      apply Units.ext
      simp [hw]
    rw [hwunit, map_one]
    ext <;> norm_num
  have hσ : TauCeti.squareClassHom (unitOfInvertible (Q v)) ≠ 1 := by
    intro h
    have h1 : unitOfInvertible (Q v) ∈ (TauCeti.squareClassHom (K := K)).ker := h
    rw [TauCeti.ker_squareClassHom] at h1
    obtain ⟨u, hu⟩ := (Subgroup.mem_square.mp h1).exists_sq
    refine hν ⟨(u : K), ?_⟩
    have huK := congrArg (fun x : Kˣ => (x : K)) hu
    simpa [hvQ, pow_two] using huK
  refine ⟨c, hcC0, hct, ?_⟩
  intro hcD
  haveI : IsMulCommutative (Kˣ × Multiplicative (SquareClassGroup K)) :=
    IsMulCommutative.of_comm (fun a b => by
      ext <;> simp [mul_comm, add_comm])
  have hker : c ∈ (CFSG.ClassicalInvolution.detSpinorNorm hQ).ker :=
    Abelianization.commutator_subset_ker (CFSG.ClassicalInvolution.detSpinorNorm hQ) hcD
  have hc1 : CFSG.ClassicalInvolution.detSpinorNorm hQ c = 1 := MonoidHom.mem_ker.mp hker
  rw [hdetc] at hc1
  exact hσ (by simpa using congrArg Prod.snd hc1)

theorem exists_commutator_conjugator_same_t
    (F : FrameData Q) (hodd : Odd (Nat.card K))
    (u : TauCeti.QuadraticMap.orthogonalGroup Q) (hu : u ∈ C0 F) :
    ∃ h : TauCeti.QuadraticMap.orthogonalGroup Q,
      h ∈ C0 F ∧ h ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      h * F.tO * h⁻¹ = u * F.tO * u⁻¹ := by
  obtain ⟨c, hcC0, hct, hcD⟩ := exists_centralizer_element_not_mem_commutator F hodd
  by_cases huD : u ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q)
  · exact ⟨u, hu, huD, rfl⟩
  · refine ⟨u * c, C0 F |>.mul_mem hu hcC0, ?_, ?_⟩
    · have hdim : Module.finrank K V = 5 := by
        rw [Module.finrank_eq_card_basis F.e, Fintype.card_fin]
      have hDrel : ((commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf
          (QuadraticMap.specialOrthogonalWithin Q)).index = 2 := by
        change (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).relIndex
          (QuadraticMap.specialOrthogonalWithin Q) = 2
        exact CFSG.ClassicalGroups.Orthogonal.commutator_relIndex_specialOrthogonalWithin_five
          hodd Q F.nondeg hdim
      let u' : QuadraticMap.specialOrthogonalWithin Q := ⟨u, hu.1⟩
      let c' : QuadraticMap.specialOrthogonalWithin Q := ⟨c, hcC0.1⟩
      have hu' : u' ∉ (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf
          (QuadraticMap.specialOrthogonalWithin Q) := by
        intro h
        exact huD (by simpa using Subgroup.mem_subgroupOf.mp h)
      have hc' : c' ∉ (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf
          (QuadraticMap.specialOrthogonalWithin Q) := by
        intro h
        exact hcD (by simpa using Subgroup.mem_subgroupOf.mp h)
      have hprod : u' * c' ∈ (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf
          (QuadraticMap.specialOrthogonalWithin Q) :=
        (Subgroup.mul_mem_iff_of_index_two hDrel).2
          ⟨fun h => absurd h hu', fun h => absurd h hc'⟩
      simpa using Subgroup.mem_subgroupOf.mp hprod
    · have hct' : c * F.tO * c⁻¹ = F.tO := by
        rw [hct]
        group
      calc (u * c) * F.tO * (u * c)⁻¹ = u * (c * F.tO * c⁻¹) * u⁻¹ := by group
        _ = u * F.tO * u⁻¹ := by rw [hct']

end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizerParity
