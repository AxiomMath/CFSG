module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisMk
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.CentralizerExtraspecial
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4OrderThreeFixed
public import CFSG.Sporadic.Schreier.J4SOutOdd

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coordinates

theorem exists_heisData :
    ∃ D : HeisCoordData 11 Q11, D.x = ⟨qx, qx_mem⟩ ∧ D.y = ⟨qy, qy_mem⟩ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine HeisCoordData.exists_of_extraspecial Q11 ⟨qx, qx_mem⟩ ⟨qy, qy_mem⟩
    closure_Q11_gens commutator_Q11.le ?_ pow_eleven_Q11
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q11)
  rw [card_Q11, card_center_Q11] at h
  omega

@[expose] def heisData :
    HeisCoordData 11 Q11 := Classical.choose exists_heisData

theorem heisData_x :
    heisData.x = ⟨qx, qx_mem⟩ := (Classical.choose_spec exists_heisData).1

theorem heisData_y :
    heisData.y = ⟨qy, qy_mem⟩ := (Classical.choose_spec exists_heisData).2

theorem π_qz :
    heisData.π ⟨qz, qz_mem⟩ = 1 := by
  have : (⟨qz, qz_mem⟩ : Q11) ∈ heisData.π.ker := by
    rw [heisData.ker_eq, center_Q11_eq]; exact Subgroup.mem_zpowers _
  exact this

theorem actMat_nrm₂ :
    heisData.actMat ⟨nrm₂, nrm₂_mem_normalizer⟩ = J4Matrix := by
  have hx : Q11.normalizerMonoidHom ⟨nrm₂, nrm₂_mem_normalizer⟩ ⟨qx, qx_mem⟩ =
      ⟨qx, qx_mem⟩ ^ 8 * ⟨qy, qy_mem⟩ ^ 6 * ⟨qz, qz_mem⟩ ^ 3 := by
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    simpa using nrm₂_qx
  have hy : Q11.normalizerMonoidHom ⟨nrm₂, nrm₂_mem_normalizer⟩ ⟨qy, qy_mem⟩ =
      ⟨qx, qx_mem⟩ ^ 10 * ⟨qy, qy_mem⟩ ^ 5 * ⟨qz, qz_mem⟩ ^ 8 := by
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    simpa using nrm₂_qy
  have hπx : heisData.π ⟨qx, qx_mem⟩ = Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod 11) := by
    rw [← heisData_x]; exact heisData.π_x
  have hπy : heisData.π ⟨qy, qy_mem⟩ = Multiplicative.ofAdd (![0, 1] : Fin 2 → ZMod 11) := by
    rw [← heisData_y]; exact heisData.π_y
  have hcol0 : Multiplicative.toAdd (heisData.π (Q11.normalizerMonoidHom
      ⟨nrm₂, nrm₂_mem_normalizer⟩ heisData.x)) = ![8, 6] := by
    have hπ : heisData.π (⟨qx, qx_mem⟩ ^ 8 * ⟨qy, qy_mem⟩ ^ 6 * ⟨qz, qz_mem⟩ ^ 3) =
        heisData.π ⟨qx, qx_mem⟩ ^ 8 * heisData.π ⟨qy, qy_mem⟩ ^ 6 *
          heisData.π ⟨qz, qz_mem⟩ ^ 3 := by simp only [map_mul, map_pow]
    rw [heisData_x, hx, hπ, hπx, hπy, π_qz]
    ext k; fin_cases k <;> simp
  have hcol1 : Multiplicative.toAdd (heisData.π (Q11.normalizerMonoidHom
      ⟨nrm₂, nrm₂_mem_normalizer⟩ heisData.y)) = ![10, 5] := by
    have hπ : heisData.π (⟨qx, qx_mem⟩ ^ 10 * ⟨qy, qy_mem⟩ ^ 5 * ⟨qz, qz_mem⟩ ^ 8) =
        heisData.π ⟨qx, qx_mem⟩ ^ 10 * heisData.π ⟨qy, qy_mem⟩ ^ 5 *
          heisData.π ⟨qz, qz_mem⟩ ^ 8 := by simp only [map_mul, map_pow]
    rw [heisData_y, hy, hπ, hπx, hπy, π_qz]
    ext k; fin_cases k <;> simp
  ext i j
  fin_cases j
  · have := congrFun hcol0 i
    fin_cases i <;> simpa [HeisCoordData.actMat, HeisCoordData.gen2, J4Matrix] using this
  · have := congrFun hcol1 i
    fin_cases i <;> simpa [HeisCoordData.actMat, HeisCoordData.gen2, J4Matrix] using this

end Coordinates

section Centralizer

theorem mem_center_of_conj_eq {G : Type*} [Group G] {a b : G}
    (h : ∀ g : G, a * g * a⁻¹ = b * g * b⁻¹) : a⁻¹ * b ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
    _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h g]
    _ = (a⁻¹ * b) * g := by group

theorem odd_card_centralizer_of_pointwise {G : Type*} [Group G] (Q : Subgroup G)
    (hZ : Subgroup.center G = ⊥) (hodd : Odd (Nat.card (pointwiseFixingAut Q))) :
    Odd (Nat.card (Subgroup.centralizer (Q : Set G))) := by
  let f : Subgroup.centralizer (Q : Set G) →* pointwiseFixingAut Q :=
    { toFun := fun g => ⟨MulAut.conj (g : G), fun q hq => by
        have h := Subgroup.mem_centralizer_iff.1 g.2 q hq
        simp only [MulAut.conj_apply]
        rw [← h]; group⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : MulAut.conj (a : G) = MulAut.conj (b : G) := congrArg Subtype.val hab
    have h2 : (a : G)⁻¹ * (b : G) ∈ Subgroup.center G := by
      refine mem_center_of_conj_eq fun g => ?_
      have e := congrArg (fun α : MulAut G => α g) h1
      simpa only [MulAut.conj_apply] using e
    rw [hZ, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective f hinj)

theorem odd_card_centralizer_Q11 :
    Odd (Nat.card (Subgroup.centralizer (Q11 : Set J))) :=
  odd_card_centralizer_of_pointwise Q11 center_J odd_card_pointwiseFixingAut_Q11

theorem hbig_rowGroup :
    ∀ g ∈ rowGroup, orderOf g = 3 → 3 ≤ Module.finrank (ZMod 2) (LinearMap.ker
      ((g : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - LinearMap.id)) := by
  rintro _ ⟨h, rfl⟩ ho
  have hoh : orderOf h⁻¹ = orderOf (rowLin h) := by
    rw [orderOf_inv, orderOf_injective rowLin rowLin_injective h]
  have h3 := R3E_J4_elements_of_order_three_left_fixed_space_dim_ge_three h⁻¹ (hoh ▸ ho)
  rw [rowLin_sub_one_eq]
  rwa [← φ_apply] at h3

theorem centralizer_Q11_le_zpowers :
    Subgroup.centralizer (Q11 : Set J) ≤ Subgroup.zpowers qz :=
  centralizer_le_zpowers_of_realization (G := J) jq_nondegenerate rowLin rowLin_injective
    rowGroup_le_orthogonal small_rank_rowGroup hbig_rowGroup odd_card_centralizer_Q11
    isExtraspecial_Q11 card_Q11 exponent_Q11 (x := ⟨qx, qx_mem⟩) (y := ⟨qy, qy_mem⟩)
    (z := ⟨qz, qz_mem⟩) closure_Q11_gens qz_eq_commutator (Module.finrank_fin_fun (ZMod 2))
    finrank_ker_rowLin_qz

theorem centralizer_Q11_le :
    Subgroup.centralizer (Q11 : Set J) ≤ Q11 :=
  centralizer_Q11_le_zpowers.trans ((Subgroup.zpowers_le).2 qz_mem)

end Centralizer

section Solvable

theorem center_Q11_eq_zpowers_comm :
    Subgroup.center Q11 = Subgroup.zpowers ⁅heisData.x, heisData.y⁆ := by
  rw [heisData_x, heisData_y, ← qz_eq_commutator, center_Q11_eq]

theorem actMat_eq_one_mem
    (n : Subgroup.normalizer (Q11 : Set J))
    (h : heisData.actMat n = 1) : (n : J) ∈ Q11 := by
  obtain ⟨q₀, hq₀⟩ := heisData.exists_mul_mem_centralizer center_Q11_eq_zpowers_comm n h
  have hc := centralizer_Q11_le hq₀
  have := Q11.mul_mem q₀.2 hc
  simpa using this

theorem det_actHom_nrm₂ :
    orderOf (Matrix.GeneralLinearGroup.det (heisData.actHom ⟨nrm₂, nrm₂_mem_normalizer⟩)) = 10 := by
  have h : ((Matrix.GeneralLinearGroup.det (heisData.actHom ⟨nrm₂, nrm₂_mem_normalizer⟩) :
      (ZMod 11)ˣ) : ZMod 11) = 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, heisData.coe_actHom, actMat_nrm₂]
    simp [J4Matrix, Matrix.det_fin_two]
    decide
  rw [← orderOf_units, h, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hm0
  interval_cases m <;> revert hm0 <;> decide +kernel

theorem isSolvable_normalizer_Q11 :
    Group.IsSolvable (Subgroup.normalizer (Q11 : Set J)) := by
  refine isSolvable_normalizer_of_heis (M := 2 ^ 21 * 3 ^ 3 * 5 * 7 * 23 * 29 * 31 * 37 * 43)
    heisData card_Q11 actMat_eq_one_mem ?_ ?_ ⟨nrm₂, nrm₂_mem_normalizer⟩ det_actHom_nrm₂
  · rw [card_J_eq]; ring
  · norm_num

end Solvable

section Torus

theorem torus_Q11 :
    ∃ t, t ∈ Subgroup.normalizer (Q11 : Set J) ∧
      ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod 11) = 11 - 1 ∧ 6 ∣ e ∧
      (∀ x ∈ Q11, ∃ z ∈ Q11 ⊓ Subgroup.centralizer (Q11 : Set J),
        t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      (∀ x ∈ Q11, ∃ z ∈ Q11 ⊓ Subgroup.centralizer (Q11 : Set J),
        t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
      ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup J,
        Q11 ⊓ Subgroup.centralizer (Q11 : Set J) ≤ F → F ≤ Q11 → F.relIndex Q11 = 11 →
          t ^ j ∉ Subgroup.normalizer (F : Set J) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨nrm₂, nrm₂_mem_normalizer, 4, 7, 60, by norm_num, ?_, by norm_num, ?_, ?_, ?_⟩
  · simpa using orderOf_seven
  · exact conj_pow_scalar heisData ⟨nrm₂, nrm₂_mem_normalizer⟩ 4 7
      (by rw [actMat_nrm₂, J4Matrix_pow_four]; simp)
  · exact conj_pow_inv heisData ⟨nrm₂, nrm₂_mem_normalizer⟩ 60
      (by rw [actMat_nrm₂, J4Matrix_pow_sixty])
  · intro j hj0 hj4 F hZF _ hF
    exact pow_not_mem_normalizer_of_no_eigenvector heisData ⟨nrm₂, nrm₂_mem_normalizer⟩ j
      (by rw [actMat_nrm₂]; exact J4Matrix_no_eigenvector j (by omega)) F hZF hF

end Torus

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
