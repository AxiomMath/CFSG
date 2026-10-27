module

public import CFSG.CGT.Timmesfeld75.ListWCLinClass
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem vecMulVec_left_cancel {c a b : Fin m → K} (hc : c ≠ 0)
    (h : vecMulVec c a = vecMulVec c b) : a = b := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  have hi' : c i ≠ 0 := by simpa using hi
  funext j
  have := congrFun₂ h i j
  simp only [vecMulVec_apply] at this
  exact mul_left_cancel₀ hi' this

theorem vecMulVec_right_cancel {a v w : Fin m → K} (ha : a ≠ 0)
    (h : vecMulVec v a = vecMulVec w a) : v = w := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
  have hj' : a j ≠ 0 := by simpa using hj
  funext i
  have := congrFun₂ h i j
  simp only [vecMulVec_apply] at this
  exact mul_right_cancel₀ hj' this

theorem card_dotProduct_eq_zero [Finite K] {c : Fin m → K} (hc : c ≠ 0) :
    Nat.card {a : Fin m → K // a ⬝ᵥ c = 0} = Nat.card K ^ (m - 1) := by
  have hf : dotLin c ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    have := LinearMap.congr_fun h (Pi.single i 1)
    rw [dotLin_apply, dotProduct_single, mul_one] at this
    exact hi this
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [Module.finrank_fin_fun] at hr
  have h1 : Nat.card {a : Fin m → K // a ⬝ᵥ c = 0} = Nat.card (LinearMap.ker (dotLin c)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      rw [LinearMap.mem_ker, dotLin_apply, dotProduct_comm])
  rw [h1, Module.natCard_eq_pow_finrank (K := K)]
  congr 1
  omega

theorem card_tvCenterSL [Finite K] {c : Fin m → K} (hc : c ≠ 0) :
    Nat.card (tvCenterSL c) = Nat.card K ^ (m - 1) := by
  rw [← card_dotProduct_eq_zero hc]
  refine (Nat.card_congr (Equiv.ofBijective (fun a : {a : Fin m → K // a ⬝ᵥ c = 0} =>
    (⟨tvSL c a a.2, a, a.2, rfl⟩ : tvCenterSL c)) ⟨fun a b hab => ?_, fun x => ?_⟩)).symm
  · have h := congrArg (fun x : tvCenterSL c => ((x : SL(m, K)) : Matrix (Fin m) (Fin m) K)) hab
    simp only [coe_tvSL, add_right_inj] at h
    exact Subtype.ext (vecMulVec_left_cancel hc h)
  · obtain ⟨a, ha, hx⟩ := x.2
    exact ⟨⟨a, ha⟩, Subtype.ext (Subtype.ext hx.symm)⟩

theorem card_tvAxisSL [Finite K] {a : Fin m → K} (ha : a ≠ 0) :
    Nat.card (tvAxisSL a) = Nat.card K ^ (m - 1) := by
  rw [← card_dotProduct_eq_zero ha]
  refine (Nat.card_congr ((Equiv.subtypeEquivRight fun v => by
    rw [dotProduct_comm]).trans (Equiv.ofBijective (fun v : {v : Fin m → K // a ⬝ᵥ v = 0} =>
    (⟨tvSL v a v.2, v, v.2, rfl⟩ : tvAxisSL a)) ⟨fun v w hvw => ?_, fun x => ?_⟩))).symm
  · have h := congrArg (fun x : tvAxisSL a => ((x : SL(m, K)) : Matrix (Fin m) (Fin m) K)) hvw
    simp only [coe_tvSL, add_right_inj] at h
    exact Subtype.ext (vecMulVec_right_cancel ha h)
  · obtain ⟨v, hv, hx⟩ := x.2
    exact ⟨⟨v, hv⟩, Subtype.ext (Subtype.ext hx.symm)⟩

theorem statedScalars_subgroupOf_le_center :
    (StatedScalars (Fin m) K).subgroupOf (StatedSL m K) ≤ Subgroup.center (StatedSL m K) := by
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 hz y)

theorem odd_card_statedScalars [Finite K] [CharP K 2] (hm : 1 ≤ m) :
    Odd (Nat.card ((StatedScalars (Fin m) K).subgroupOf (StatedSL m K))) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨⟨z, hz⟩, hzord⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 h)
  rw [Subgroup.orderOf_mk] at hzord
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzord, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzord
    omega
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨u, hu⟩ := hz
  have hzm : ((z : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = Matrix.scalar (Fin m) (u : K) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]
  have huu : (u : K) * u = 1 := by
    have h1 := congrArg (fun y : StatedSL m K =>
      ((y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⟨0, hm⟩ ⟨0, hm⟩) hz2
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, hzm] at h1
    simpa [Matrix.scalar_apply] using h1
  have hu1 := eq_one_of_mul_self_eq_one_char_two huu
  apply hz1
  apply Subtype.ext
  apply Units.ext
  rw [hzm, hu1]
  simp

theorem map_tvCenterSL (c : Fin m → K) :
    (tvCenterSL c).map (specialLinearGroupEquivStatedSL m K).toMonoidHom =
      (transvCenter m K c).subgroupOf (StatedSL m K) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  have hcoe : (((specialLinearGroupEquivStatedSL m K).symm y : SL(m, K)) :
      Matrix (Fin m) (Fin m) K) = ((y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    rw [← specialLinearGroupEquivStatedSL_coe m K, MulEquiv.apply_symm_apply]
  rw [mem_tvCenterSL, hcoe]
  rfl

theorem map_tvAxisSL (a : Fin m → K) :
    (tvAxisSL a).map (specialLinearGroupEquivStatedSL m K).toMonoidHom =
      (transvAxis m K a).subgroupOf (StatedSL m K) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  have hcoe : (((specialLinearGroupEquivStatedSL m K).symm y : SL(m, K)) :
      Matrix (Fin m) (Fin m) K) = ((y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    rw [← specialLinearGroupEquivStatedSL_coe m K, MulEquiv.apply_symm_apply]
  rw [mem_tvAxisSL, hcoe]
  rfl

theorem card_map_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H) {T : Subgroup G}
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) : Nat.card (T.map f) = Nat.card T := by
  have h1 : ((T.map f : Subgroup H) : Set H) = f '' (T : Set G) := Subgroup.coe_map f T
  calc Nat.card (T.map f) = Nat.card (f '' (T : Set G)) := by rw [← h1]; rfl
    _ = Nat.card (T : Set G) := Nat.card_image_of_injOn fun x hx y hy hxy => hinj x hx y hy hxy
    _ = Nat.card T := rfl

variable [Finite K] [CharP K 2]

theorem psl_wc (hm : 3 ≤ m) {T : Subgroup (StatedProj (StatedSL m K))} (hT : IsWC T)
    (hT1 : T ≠ ⊥) :
    Nat.card T = Nat.card K ^ (m - 1) ∧
    ((∃ c : Fin m → K, c ≠ 0 ∧ T = transvImage m K (transvCenter m K c)) ∨
      (∃ a : Fin m → K, a ≠ 0 ∧ T = transvImage m K (transvAxis m K a))) ∧
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y := by
  obtain ⟨T', hT', himg, hinj⟩ := hT.exists_lift_central_odd statedScalars_subgroupOf_le_center
    (odd_card_statedScalars (by omega))
  set ε := specialLinearGroupEquivStatedSL m K with hε
  set U := T'.map ε.symm.toMonoidHom with hUdef
  have hU : IsWC U := hT'.map_mulEquiv ε.symm
  have hU1 : U ≠ ⊥ := by
    intro h
    apply hT1
    rw [← himg, ← map_symm_map_mulEquiv ε T', ← hUdef, h, Subgroup.map_bot, Subgroup.map_bot]
  have hback : U.map ε.toMonoidHom = T' := map_symm_map_mulEquiv ε T'
  have hcard : Nat.card T = Nat.card U := by
    rw [← himg, card_map_of_injOn _ hinj, hUdef,
      Subgroup.card_map_of_injective ε.symm.injective]
  have hconj : (∀ u ∈ U, u ≠ 1 → IsTransvection u) →
      ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y := by
    intro htr x hx hx1 y hy hy1
    rw [← himg] at hx hy
    obtain ⟨x', hx'T, rfl⟩ := hx
    obtain ⟨y', hy'T, rfl⟩ := hy
    have hmemU : ∀ z ∈ T', ε.symm z ∈ U := fun z hz => ⟨z, hz, rfl⟩
    have hne : ∀ {z : StatedSL m K}, QuotientGroup.mk' _ z ≠ (1 : StatedProj (StatedSL m K)) →
        ε.symm z ≠ 1 := fun {z} hz h => hz (by rw [← ε.apply_symm_apply z, h, map_one, map_one])
    obtain ⟨W, hW⟩ := exists_conj_of_isTransvection (htr _ (hmemU x' hx'T) (hne hx1))
      (htr _ (hmemU y' hy'T) (hne hy1))
    refine isConj_iff.2 ⟨QuotientGroup.mk' _ (ε W), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    have h := congrArg ε hW
    rwa [map_mul, map_mul, map_inv, ε.apply_symm_apply, ε.apply_symm_apply] at h
  rcases sl_wc hm hU hU1 with ⟨c, hc, hUc⟩ | ⟨a, ha, hUa⟩
  · refine ⟨by rw [hcard, hUc, card_tvCenterSL hc], Or.inl ⟨c, hc, ?_⟩, hconj ?_⟩
    · rw [← himg, ← hback, hUc, map_tvCenterSL]
      rfl
    · rintro u hu hu1
      rw [hUc] at hu
      obtain ⟨b, hbc, hub⟩ := hu
      have hb : b ≠ 0 := by
        rintro rfl
        apply hu1
        apply Subtype.ext
        rw [hub, vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]
      exact isTransvection_of_coe hc hb hbc hub
  · refine ⟨by rw [hcard, hUa, card_tvAxisSL ha], Or.inr ⟨a, ha, ?_⟩, hconj ?_⟩
    · rw [← himg, ← hback, hUa, map_tvAxisSL]
      rfl
    · rintro u hu hu1
      rw [hUa] at hu
      obtain ⟨v, hav, huv⟩ := hu
      have hv : v ≠ 0 := by
        rintro rfl
        apply hu1
        apply Subtype.ext
        rw [huv, zero_vecMulVec, add_zero, Matrix.SpecialLinearGroup.coe_one]
      exact isTransvection_of_coe hv ha hav huv

end CFSG.CGT.Timmesfeld75
