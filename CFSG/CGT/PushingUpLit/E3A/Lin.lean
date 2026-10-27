module

public import CFSG.CGT.Timmesfeld75.ListWCLinPSL
public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.E3A

open Matrix CFSG CFSG.RankThree.PartOne CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem exists_scalar_add_vecMulVec (hm : 2 ≤ m) {c : Fin m → K} (hc : c ≠ 0)
    (M : Matrix (Fin m) (Fin m) K)
    (h : ∀ a : Fin m → K, a ⬝ᵥ c = 0 → M * vecMulVec c a = vecMulVec c a * M) :
    ∃ (ν : K) (w : Fin m → K), w ⬝ᵥ c = 0 ∧
      M = ν • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c w := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hc
  have hi : c i₀ ≠ 0 := by simpa using hi₀
  have hstar : ∀ a, a ⬝ᵥ c = 0 → vecMulVec (M *ᵥ c) a = vecMulVec c (a ᵥ* M) := by
    intro a ha
    rw [← mul_vecMulVec, ← vecMulVec_mul]
    exact h a ha
  obtain ⟨j₀, hj₀⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i₀
  set av : Fin m → Fin m → K := fun j => Pi.single j 1 - (c j / c i₀) • Pi.single i₀ 1 with hav
  have hav_dot : ∀ j, av j ⬝ᵥ c = 0 := fun j => by
    simp only [hav, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hi, sub_self]
  have hav_ne : av j₀ ≠ 0 := by
    intro h0
    have := congrFun h0 j₀
    simp [hav, hj₀] at this
  obtain ⟨ν, hMc, -⟩ := exists_smul_of_vecMulVec_eq (hstar (av j₀) (hav_dot j₀)) hc hav_ne
  have hrow : ∀ a, a ⬝ᵥ c = 0 → a ᵥ* M = ν • a := by
    intro a ha
    have h1 := hstar a ha
    rw [hMc, smul_vecMulVec, ← vecMulVec_smul] at h1
    exact (vecMulVec_left_cancel hc h1).symm
  set H : Matrix (Fin m) (Fin m) K := M - ν • (1 : Matrix (Fin m) (Fin m) K) with hH
  have hHrow : ∀ j k, H j k = (c j / c i₀) * H i₀ k := by
    intro j k
    have h1 : av j ᵥ* H = 0 := by
      rw [hH, vecMul_sub, vecMul_smul, vecMul_one, hrow (av j) (hav_dot j), sub_self]
    have h2 := congrFun h1 k
    simp only [hav, sub_vecMul, smul_vecMul, single_vecMul, Matrix.row, Pi.sub_apply,
      Pi.smul_apply, one_smul, smul_eq_mul, Pi.zero_apply] at h2
    exact sub_eq_zero.1 h2
  set w : Fin m → K := (c i₀)⁻¹ • H i₀ with hw
  have hHeq : H = vecMulVec c w := by
    ext j k
    rw [vecMulVec_apply, hw, hHrow j k]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hwc : w ⬝ᵥ c = 0 := by
    have h1 : H *ᵥ c = 0 := by
      rw [hH, sub_mulVec, smul_mulVec, one_mulVec, hMc, sub_self]
    rw [hHeq, vecMulVec_mulVec] at h1
    have h2 := congrFun h1 i₀
    simp only [Pi.smul_apply, Pi.zero_apply] at h2
    have h3 := (mul_eq_zero.1 (by simpa using h2 : c i₀ * (w ⬝ᵥ c) = 0)).resolve_left hi
    exact h3
  refine ⟨ν, w, hwc, ?_⟩
  rw [← hHeq, hH]
  abel

@[expose] noncomputable def toPSL (m : ℕ) (K : Type) [Field K] :
    SL(m, K) →* StatedProj (StatedSL m K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf (StatedSL m K))).comp
    (specialLinearGroupEquivStatedSL m K).toMonoidHom

theorem toPSL_surjective : Function.Surjective (toPSL m K) :=
  (QuotientGroup.mk'_surjective _).comp (specialLinearGroupEquivStatedSL m K).surjective

theorem toPSL_eq_one_iff {x : SL(m, K)} : toPSL m K x = 1 ↔ x ∈ Subgroup.center SL(m, K) := by
  have h1 : toPSL m K x = 1 ↔ specialLinearGroupEquivStatedSL m K x ∈
      (StatedScalars (Fin m) K).subgroupOf (StatedSL m K) := QuotientGroup.eq_one_iff _
  rw [h1, ← map_center_eq_statedScalars m K]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := (specialLinearGroupEquivStatedSL m K).injective hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem transvImage_center_eq (c : Fin m → K) :
    transvImage m K (transvCenter m K c) = (tvCenterSL c).map (toPSL m K) := by
  rw [transvImage, ← map_tvCenterSL, Subgroup.map_map]
  rfl

theorem transvImage_axis_eq (a : Fin m → K) :
    transvImage m K (transvAxis m K a) = (tvAxisSL a).map (toPSL m K) := by
  rw [transvImage, ← map_tvAxisSL, Subgroup.map_map]
  rfl

theorem eq_one_of_mem_center_of_mul_self [CharP K 2] (hm : 1 ≤ m) {z : SL(m, K)}
    (hz : z ∈ Subgroup.center SL(m, K)) (h : z * z = 1) : z = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have h1 : ((z * z : SL(m, K)) : Matrix (Fin m) (Fin m) K) = 1 := by rw [h]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hr, ← map_mul] at h1
  have h2 : r * r = 1 := by
    have := congrFun₂ h1 ⟨0, hm⟩ ⟨0, hm⟩
    simpa [Matrix.scalar_apply] using this
  have h3 := eq_one_of_mul_self_eq_one_char_two h2
  apply Subtype.ext
  rw [← hr, h3]
  simp

theorem centralizer_map_le [CharP K 2] (hm : 1 ≤ m) {U : Subgroup SL(m, K)}
    (hU : ∀ t ∈ U, t * t = 1)
    (hcore : ∀ g : SL(m, K), (∀ t ∈ U, g * t = t * g) →
      ∃ u ∈ U, g * u⁻¹ ∈ Subgroup.center SL(m, K)) :
    Subgroup.centralizer ((U.map (toPSL m K) : Subgroup (StatedProj (StatedSL m K))) :
      Set (StatedProj (StatedSL m K))) ≤ U.map (toPSL m K) := by
  intro x hx
  obtain ⟨g, rfl⟩ := toPSL_surjective x
  have hcomm : ∀ t ∈ U, g * t = t * g := by
    intro t ht
    have h1 := Subgroup.mem_centralizer_iff.1 hx (toPSL m K t) ⟨t, ht, rfl⟩
    have hz : g * t * g⁻¹ * t⁻¹ ∈ Subgroup.center SL(m, K) := by
      rw [← toPSL_eq_one_iff]
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    set z : SL(m, K) := g * t * g⁻¹ * t⁻¹ with hzdef
    have hzc : ∀ y, y * z = z * y := Subgroup.mem_center_iff.1 hz
    have hgt : g * t * g⁻¹ = z * t := by rw [hzdef]; group
    have hsq : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      have : (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      rw [this, hU t ht]
      group
    have hzz : z * z = 1 := by
      rw [hgt] at hsq
      have : z * t * (z * t) = z * z * (t * t) := by
        calc z * t * (z * t) = z * (t * z) * t := by group
          _ = z * (z * t) * t := by rw [hzc t]
          _ = z * z * (t * t) := by group
      rw [this, hU t ht, mul_one] at hsq
      exact hsq
    have hz1 := eq_one_of_mem_center_of_mul_self hm hz hzz
    have : g * t * g⁻¹ = t := by
      have h2 : g * t * g⁻¹ * t⁻¹ = 1 := hz1
      exact mul_inv_eq_one.1 h2
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [this]
  obtain ⟨u, hu, hgu⟩ := hcore g hcomm
  have h3 := (toPSL_eq_one_iff.2 hgu)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact ⟨u, hu, h3.symm⟩

theorem scalar_add_mul_one_sub (ν : K) (X Y : Matrix (Fin m) (Fin m) K) (h1 : ν • Y = X)
    (h2 : X * Y = 0) : (ν • (1 : Matrix (Fin m) (Fin m) K) + X) * (1 - Y) = ν • 1 := by
  rw [Matrix.add_mul, smul_mul_assoc, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h2,
    smul_sub, h1]
  abel

theorem tvCenterSL_mul_self [CharP K 2] {c : Fin m → K} {t : SL(m, K)} (ht : t ∈ tvCenterSL c) :
    t * t = 1 := by
  obtain ⟨a, ha, hta⟩ := ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hta, one_add_vecMulVec_mul_center m K c a a ha]
  have : a + a = 0 := funext fun i => CharTwo.add_self_eq_zero (a i)
  rw [this, vecMulVec_zero, add_zero]
  rfl

theorem tvAxisSL_mul_self [CharP K 2] {a : Fin m → K} {t : SL(m, K)} (ht : t ∈ tvAxisSL a) :
    t * t = 1 := by
  obtain ⟨v, hv, htv⟩ := ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, htv, one_add_vecMulVec_mul_axis m K a v v hv]
  have : v + v = 0 := funext fun i => CharTwo.add_self_eq_zero (v i)
  rw [this, zero_vecMulVec, add_zero]
  rfl

theorem hcore_center (hm : 2 ≤ m) {c : Fin m → K} (hc : c ≠ 0) (g : SL(m, K))
    (hg : ∀ t ∈ tvCenterSL c, g * t = t * g) :
    ∃ u ∈ tvCenterSL c, g * u⁻¹ ∈ Subgroup.center SL(m, K) := by
  have hM : ∀ a : Fin m → K, a ⬝ᵥ c = 0 →
      (g : Matrix (Fin m) (Fin m) K) * vecMulVec c a =
        vecMulVec c a * (g : Matrix (Fin m) (Fin m) K) := by
    intro a ha
    have h1 := congrArg (fun x : SL(m, K) => (x : Matrix (Fin m) (Fin m) K))
      (hg (tvSL c a ha) ⟨a, ha, rfl⟩)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul] at h1
    exact add_left_cancel h1
  obtain ⟨ν, w, hw, hgM⟩ := exists_scalar_add_vecMulVec hm hc _ hM
  have hgc : (g : Matrix (Fin m) (Fin m) K) *ᵥ c = ν • c := by
    rw [hgM, add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hw]
    simp
  have hν : ν ≠ 0 := by
    intro h0
    exact mulVec_ne_zero' g hc (by rw [hgc, h0, zero_smul])
  have hw' : (ν⁻¹ • w) ⬝ᵥ c = 0 := by rw [smul_dotProduct, hw, smul_zero]
  refine ⟨tvSL c (ν⁻¹ • w) hw', ⟨_, hw', rfl⟩, ?_⟩
  have hmat : ((g * (tvSL c (ν⁻¹ • w) hw')⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      ν • (1 : Matrix (Fin m) (Fin m) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL_inv, hgM]
    exact scalar_add_mul_one_sub ν _ _
      (by rw [← vecMulVec_smul, smul_smul, mul_inv_cancel₀ hν, one_smul])
      (by rw [vecMulVec_mul_vecMulVec, hw, zero_smul, vecMulVec_zero])
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨ν, ?_, ?_⟩
  · have hdet : ((g * (tvSL c (ν⁻¹ • w) hw')⁻¹ : SL(m, K)) :
        Matrix (Fin m) (Fin m) K).det = 1 := Matrix.SpecialLinearGroup.det_coe _
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
    exact hdet
  · rw [hmat, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem hcore_axis (hm : 2 ≤ m) {a : Fin m → K} (ha : a ≠ 0) (g : SL(m, K))
    (hg : ∀ t ∈ tvAxisSL a, g * t = t * g) :
    ∃ u ∈ tvAxisSL a, g * u⁻¹ ∈ Subgroup.center SL(m, K) := by
  have hM : ∀ b : Fin m → K, b ⬝ᵥ a = 0 →
      (g : Matrix (Fin m) (Fin m) K)ᵀ * vecMulVec a b =
        vecMulVec a b * (g : Matrix (Fin m) (Fin m) K)ᵀ := by
    intro b hb
    have hab : a ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact hb
    have h1 := congrArg (fun x : SL(m, K) => (x : Matrix (Fin m) (Fin m) K))
      (hg (tvSL b a hab) ⟨b, hab, rfl⟩)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul] at h1
    have h2 := add_left_cancel h1
    have h3 := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_vecMulVec] at h3
    exact h3.symm
  obtain ⟨ν, w, hw, hgT⟩ := exists_scalar_add_vecMulVec hm ha _ hM
  have hg' : (g : Matrix (Fin m) (Fin m) K) =
      ν • (1 : Matrix (Fin m) (Fin m) K) + vecMulVec w a := by
    have := congrArg Matrix.transpose hgT
    rwa [Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.transpose_vecMulVec] at this
  have haw : a ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hw
  have hga : a ᵥ* (g : Matrix (Fin m) (Fin m) K) = ν • a := by
    rw [hg', vecMul_add, vecMul_smul, vecMul_one, vecMul_vecMulVec, haw, zero_smul, add_zero]
  have hν : ν ≠ 0 := by
    intro h0
    exact vecMul_ne_zero' g ha (by rw [hga, h0, zero_smul])
  have haw' : a ⬝ᵥ (ν⁻¹ • w) = 0 := by rw [dotProduct_smul, haw, smul_zero]
  refine ⟨tvSL (ν⁻¹ • w) a haw', ⟨_, haw', rfl⟩, ?_⟩
  have hmat : ((g * (tvSL (ν⁻¹ • w) a haw')⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      ν • (1 : Matrix (Fin m) (Fin m) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL_inv, hg']
    exact scalar_add_mul_one_sub ν _ _
      (by rw [← smul_vecMulVec, smul_smul, mul_inv_cancel₀ hν, one_smul])
      (by rw [vecMulVec_mul_vecMulVec, haw', zero_smul, vecMulVec_zero])
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨ν, ?_, ?_⟩
  · have hdet : ((g * (tvSL (ν⁻¹ • w) a haw')⁻¹ : SL(m, K)) :
        Matrix (Fin m) (Fin m) K).det = 1 := Matrix.SpecialLinearGroup.det_coe _
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
    exact hdet
  · rw [hmat, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem centralizer_transvImage_center [CharP K 2] (hm : 3 ≤ m) {c : Fin m → K} (hc : c ≠ 0) :
    Subgroup.centralizer (transvImage m K (transvCenter m K c) :
      Set (StatedProj (StatedSL m K))) ≤ transvImage m K (transvCenter m K c) := by
  rw [transvImage_center_eq]
  exact centralizer_map_le (by omega) (fun t ht => tvCenterSL_mul_self ht)
    (fun g hg => hcore_center (by omega) hc g hg)

theorem centralizer_transvImage_axis [CharP K 2] (hm : 3 ≤ m) {a : Fin m → K} (ha : a ≠ 0) :
    Subgroup.centralizer (transvImage m K (transvAxis m K a) :
      Set (StatedProj (StatedSL m K))) ≤ transvImage m K (transvAxis m K a) := by
  rw [transvImage_axis_eq]
  exact centralizer_map_le (by omega) (fun t ht => tvAxisSL_mul_self ht)
    (fun g hg => hcore_axis (by omega) ha g hg)

theorem commutative_transvImage_center (c : Fin m → K) :
    ∀ x ∈ transvImage m K (transvCenter m K c), ∀ y ∈ transvImage m K (transvCenter m K c),
      x * y = y * x := by
  rw [transvImage_center_eq]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, tvCenterSL_comm x hx y hy]

theorem commutative_transvImage_axis (a : Fin m → K) :
    ∀ x ∈ transvImage m K (transvAxis m K a), ∀ y ∈ transvImage m K (transvAxis m K a),
      x * y = y * x := by
  rw [transvImage_axis_eq]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, tvAxisSL_comm x hx y hy]

theorem lin_centralizer_le {G : Type} [Group G] [CharP K 2] (hm : 3 ≤ m)
    (e : G ≃* StatedProj (StatedSL m K)) {R : Subgroup G}
    (hR : (∃ c : Fin m → K, c ≠ 0 ∧
        R.map e.toMonoidHom = transvImage m K (transvCenter m K c)) ∨
      (∃ a : Fin m → K, a ≠ 0 ∧ R.map e.toMonoidHom = transvImage m K (transvAxis m K a))) :
    (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ Subgroup.centralizer (R : Set G) ≤ R := by
  have key : ∀ V : Subgroup (StatedProj (StatedSL m K)), R.map e.toMonoidHom = V →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) →
      Subgroup.centralizer (V : Set (StatedProj (StatedSL m K))) ≤ V →
      (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ Subgroup.centralizer (R : Set G) ≤ R := by
    intro V hV hcomm hcent
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · apply e.injective
      rw [map_mul, map_mul]
      exact hcomm _ (hV ▸ ⟨x, hx, rfl⟩) _ (hV ▸ ⟨y, hy, rfl⟩)
    · have h1 : e x ∈ Subgroup.centralizer (V : Set (StatedProj (StatedSL m K))) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro v hv
        rw [← hV] at hv
        obtain ⟨r, hr, rfl⟩ := hv
        have := Subgroup.mem_centralizer_iff.1 hx r hr
        rw [show (e.toMonoidHom r : StatedProj (StatedSL m K)) = e r from rfl, ← map_mul, ← map_mul,
          this]
      have h2 := hcent h1
      rw [← hV] at h2
      obtain ⟨r, hr, hre⟩ := h2
      have : r = x := e.injective hre
      exact this ▸ hr
  rcases hR with ⟨c, hc, hR⟩ | ⟨a, ha, hR⟩
  · exact key _ hR (commutative_transvImage_center c) (centralizer_transvImage_center hm hc)
  · exact key _ hR (commutative_transvImage_axis a) (centralizer_transvImage_axis hm ha)

theorem exists_noncomm_of_block {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule X n) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨f, -⟩ := hnat
  have hAc : IsMulCommutative (alternatingGroup (Fin (2 * n + 1))) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (f.symm a)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (f.symm b)
    have h1 : f.symm a * f.symm b = f.symm b * f.symm a := by
      rw [← hx, ← hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x y]
    have h2 := congrArg f h1
    simpa using h2
  have := alternatingGroup.isMulCommutative_iff_card_le_three.1 hAc
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem false_of_lin {G : Type} [Group G] [CharP K 2] {X R : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hm : 3 ≤ m) (e : G ≃* StatedProj (StatedSL m K))
    (hR : (∃ c : Fin m → K, c ≠ 0 ∧
        R.map e.toMonoidHom = transvImage m K (transvCenter m K c)) ∨
      (∃ a : Fin m → K, a ≠ 0 ∧ R.map e.toMonoidHom = transvImage m K (transvAxis m K a)))
    (hnat : IsNaturalAltModule ↥X n) (hXC : X ≤ Subgroup.centralizer (R : Set G)) : False := by
  obtain ⟨hcomm, hcent⟩ := lin_centralizer_le hm e hR
  have hXR : X ≤ R := hXC.trans hcent
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_block hn hnat
  exact hab (Subtype.ext (hcomm a (hXR a.2) b (hXR b.2)))

end CFSG.CGT.PushingUpLit.E3A
