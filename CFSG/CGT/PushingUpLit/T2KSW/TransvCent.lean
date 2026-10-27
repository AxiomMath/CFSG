module

public import CFSG.CGT.Timmesfeld75.StdPair
import CFSG.CGT.Timmesfeld75.ListWCLin

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank Matrix

section MatrixLevel

variable {K : Type} [Field K] {m : ℕ}

theorem exists_ne_zero_orthogonal (hm : 2 ≤ m) {a : Fin m → K} (ha : a ≠ 0) :
    ∃ v : Fin m → K, v ≠ 0 ∧ a ⬝ᵥ v = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  have hi' : a i ≠ 0 := by simpa using hi
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i := by
    by_contra h
    push Not at h
    have h0 : (⟨0, by omega⟩ : Fin m) = i := h _
    have h1 : (⟨1, by omega⟩ : Fin m) = i := h _
    have := h0.trans h1.symm
    simp [Fin.ext_iff] at this
  refine ⟨Pi.single j (a i) - Pi.single i (a j), fun h => ?_, ?_⟩
  · have := congrFun h j
    simp [Pi.single_eq_of_ne hj] at this
    exact hi' this
  · rw [dotProduct_sub, dotProduct_single, dotProduct_single]
    ring

theorem exists_scalar_of_comm_axis (hm : 2 ≤ m) {a : Fin m → K} (ha : a ≠ 0)
    {X : Matrix (Fin m) (Fin m) K}
    (hX : ∀ v, a ⬝ᵥ v = 0 → X * vecMulVec v a = vecMulVec v a * X) :
    ∃ μ : K, (∀ v, a ⬝ᵥ v = 0 → X *ᵥ v = μ • v) ∧ a ᵥ* X = μ • a := by
  have hv : ∀ v, v ≠ 0 → a ⬝ᵥ v = 0 → ∃ μ : K, X *ᵥ v = μ • v ∧ a ᵥ* X = μ • a := by
    intro v hv0 hav
    have h := hX v hav
    rw [mul_vecMulVec, vecMulVec_mul] at h
    exact exists_smul_of_vecMulVec_eq h hv0 ha
  obtain ⟨v₀, hv₀, hav₀⟩ := exists_ne_zero_orthogonal hm ha
  obtain ⟨μ, -, hμ⟩ := hv v₀ hv₀ hav₀
  refine ⟨μ, fun v hav => ?_, hμ⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · obtain ⟨μ', h1, h2⟩ := hv v hv0 hav
    have : μ' = μ := smul_left_injective K ha (h2.symm.trans hμ)
    rw [h1, this]

theorem mul_comm_of_comm_axis (hm : 2 ≤ m) {a : Fin m → K} (ha : a ≠ 0)
    {X Y : Matrix (Fin m) (Fin m) K}
    (hX : ∀ v, a ⬝ᵥ v = 0 → X * vecMulVec v a = vecMulVec v a * X)
    (hY : ∀ v, a ⬝ᵥ v = 0 → Y * vecMulVec v a = vecMulVec v a * Y) : X * Y = Y * X := by
  obtain ⟨μ, hXv, hXa⟩ := exists_scalar_of_comm_axis hm ha hX
  obtain ⟨μ', hYv, hYa⟩ := exists_scalar_of_comm_axis hm ha hY
  have key : ∀ (X Y : Matrix (Fin m) (Fin m) K) (μ μ' : K),
      (∀ v, a ⬝ᵥ v = 0 → X *ᵥ v = μ • v) → (a ᵥ* Y = μ' • a) → ∀ x : Fin m → K,
      X *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x) + μ' • (X *ᵥ x) - (μ * μ') • x := by
    intro X Y μ μ' hXv hYa x
    have h1 : a ⬝ᵥ (Y *ᵥ x - μ' • x) = 0 := by
      rw [dotProduct_sub, dotProduct_mulVec, hYa, smul_dotProduct, dotProduct_smul, sub_self]
    have h2 := hXv _ h1
    rw [mulVec_sub, mulVec_smul, smul_sub] at h2
    rw [mul_smul, eq_add_of_sub_eq h2]
    abel
  have hext : ∀ x, (X * Y) *ᵥ x = (Y * X) *ᵥ x := by
    intro x
    rw [← mulVec_mulVec, ← mulVec_mulVec, key X Y μ μ' hXv hYa x, key Y X μ' μ hYv hXa x,
      mul_comm μ' μ]
    abel
  ext i j
  have := congrFun (hext (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

end MatrixLevel

section GroupLevel

theorem commute_of_mk_commute_central_odd {S : Type*} [Group S] {N : Subgroup S} [N.Normal]
    (hNc : N ≤ Subgroup.center S) (hodd : Odd (Nat.card N)) {g t : S} (ht : t * t = 1)
    (h : (QuotientGroup.mk g : S ⧸ N) * QuotientGroup.mk t =
      QuotientGroup.mk t * QuotientGroup.mk g) : g * t = t * g := by
  have hz : (g * t)⁻¹ * (t * g) ∈ N := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, h]
  set z := (g * t)⁻¹ * (t * g) with hzdef
  have hzc : ∀ y, y * z = z * y := Subgroup.mem_center_iff.1 (hNc hz)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hz1 : z = t⁻¹ * g⁻¹ * t * g := by rw [hzdef]; group
  have hz2 : z = g⁻¹ * t * g * t⁻¹ := by
    have := hzc t
    calc z = t * z * t⁻¹ := by rw [this]; group
      _ = g⁻¹ * t * g * t⁻¹ := by rw [hz1]; group
  have hzz : z * z = 1 := by
    calc z * z = (t⁻¹ * g⁻¹ * t * g) * (g⁻¹ * t * g * t⁻¹) := congrArg₂ _ hz1 hz2
      _ = t⁻¹ * g⁻¹ * (t * t) * g * t⁻¹ := by group
      _ = t⁻¹ * g⁻¹ * 1 * g * t⁻¹ := by rw [ht]
      _ = (t * t)⁻¹ := by group
      _ = 1 := by rw [ht, inv_one]
  have hz0 : z = 1 := by
    set z' : N := ⟨z, hz⟩ with hz'
    have h2 : orderOf z' ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [sq]
      exact Subtype.ext hzz)
    have hd : orderOf z' ∣ Nat.card N := orderOf_dvd_natCard z'
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
    · exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
    · rw [h1] at hd
      exact absurd (even_iff_two_dvd.2 hd) (Nat.not_even_iff_odd.2 hodd)
  rw [hzdef, inv_mul_eq_one] at hz0
  exact hz0

end GroupLevel

section Transvections

variable {K : Type} [Field K] {m : ℕ}

abbrev statedMat (g : StatedSL m K) : Matrix (Fin m) (Fin m) K :=
  ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)

theorem statedMat_mul (g h : StatedSL m K) : statedMat (g * h) = statedMat g * statedMat h := rfl

theorem commute_of_mem_centralizer_transvImage [Finite K] [CharP K 2] (hm : 1 ≤ m)
    {U : Subgroup (GL (Fin m) K)}
    (hU : ∀ t : StatedSL m K, t ∈ U.subgroupOf (StatedSL m K) → t * t = 1)
    {g : StatedSL m K}
    (hg : (QuotientGroup.mk g : StatedProj (StatedSL m K)) ∈
      Subgroup.centralizer (transvImage m K U : Set (StatedProj (StatedSL m K))))
    {t : StatedSL m K} (ht : t ∈ U.subgroupOf (StatedSL m K)) : g * t = t * g := by
  have hmem : (QuotientGroup.mk t : StatedProj (StatedSL m K)) ∈ transvImage m K U :=
    ⟨t, ht, rfl⟩
  have h := Subgroup.mem_centralizer_iff.1 hg _ hmem
  exact commute_of_mk_commute_central_odd statedScalars_subgroupOf_le_center
    (odd_card_statedScalars hm) (hU t ht) h.symm

theorem exists_mem_transvAxis {a v : Fin m → K} (h : a ⬝ᵥ v = 0) :
    ∃ t ∈ (transvAxis m K a).subgroupOf (StatedSL m K),
      statedMat t = 1 + vecMulVec v a := by
  refine ⟨specialLinearGroupEquivStatedSL m K (tvSL v a h), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨v, h, by rw [specialLinearGroupEquivStatedSL_coe, coe_tvSL]⟩
  · show ((specialLinearGroupEquivStatedSL m K (tvSL v a h) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = 1 + vecMulVec v a
    rw [specialLinearGroupEquivStatedSL_coe, coe_tvSL]

theorem exists_mem_transvCenter {c a : Fin m → K} (h : a ⬝ᵥ c = 0) :
    ∃ t ∈ (transvCenter m K c).subgroupOf (StatedSL m K),
      statedMat t = 1 + vecMulVec c a := by
  refine ⟨specialLinearGroupEquivStatedSL m K (tvSL c a h), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨a, h, by rw [specialLinearGroupEquivStatedSL_coe, coe_tvSL]⟩
  · show ((specialLinearGroupEquivStatedSL m K (tvSL c a h) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c a
    rw [specialLinearGroupEquivStatedSL_coe, coe_tvSL]

theorem fun_add_self_eq_zero_of_charTwo [CharP K 2] (v : Fin m → K) : v + v = 0 := by
  ext i
  simp [CharTwo.add_self_eq_zero]

theorem sq_eq_one_of_mem_transvAxis [CharP K 2] {a : Fin m → K} {t : StatedSL m K}
    (ht : t ∈ (transvAxis m K a).subgroupOf (StatedSL m K)) : t * t = 1 := by
  rw [Subgroup.mem_subgroupOf] at ht
  obtain ⟨v, hv, hmat⟩ := ht
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
  rw [hmat, one_add_vecMulVec_mul_axis m K a v v hv, fun_add_self_eq_zero_of_charTwo,
    zero_vecMulVec, add_zero]

theorem sq_eq_one_of_mem_transvCenter [CharP K 2] {c : Fin m → K} {t : StatedSL m K}
    (ht : t ∈ (transvCenter m K c).subgroupOf (StatedSL m K)) : t * t = 1 := by
  rw [Subgroup.mem_subgroupOf] at ht
  obtain ⟨a, ha, hmat⟩ := ht
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
  rw [hmat, one_add_vecMulVec_mul_center m K c a a ha, fun_add_self_eq_zero_of_charTwo,
    vecMulVec_zero, add_zero]

theorem statedMat_comm_of_mem_centralizer_axis [Finite K] [CharP K 2] (hm : 1 ≤ m)
    {a : Fin m → K} {g : StatedSL m K}
    (hg : (QuotientGroup.mk g : StatedProj (StatedSL m K)) ∈
      Subgroup.centralizer (transvImage m K (transvAxis m K a) : Set (StatedProj (StatedSL m K))))
    {v : Fin m → K} (hv : a ⬝ᵥ v = 0) :
    statedMat g * vecMulVec v a = vecMulVec v a * statedMat g := by
  obtain ⟨t, ht, htm⟩ := exists_mem_transvAxis hv
  have h := congrArg statedMat
    (commute_of_mem_centralizer_transvImage hm (fun t ht => sq_eq_one_of_mem_transvAxis ht) hg ht)
  rw [statedMat_mul, statedMat_mul, htm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul] at h
  exact add_left_cancel h

theorem statedMat_comm_of_mem_centralizer_center [Finite K] [CharP K 2] (hm : 1 ≤ m)
    {c : Fin m → K} {g : StatedSL m K}
    (hg : (QuotientGroup.mk g : StatedProj (StatedSL m K)) ∈
      Subgroup.centralizer (transvImage m K (transvCenter m K c) : Set (StatedProj (StatedSL m K))))
    {a : Fin m → K} (ha : a ⬝ᵥ c = 0) :
    statedMat g * vecMulVec c a = vecMulVec c a * statedMat g := by
  obtain ⟨t, ht, htm⟩ := exists_mem_transvCenter ha
  have h := congrArg statedMat
    (commute_of_mem_centralizer_transvImage hm (fun t ht => sq_eq_one_of_mem_transvCenter ht) hg ht)
  rw [statedMat_mul, statedMat_mul, htm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul] at h
  exact add_left_cancel h

theorem mk_mul_comm_of_statedMat {g g' : StatedSL m K}
    (h : statedMat g * statedMat g' = statedMat g' * statedMat g) :
    (QuotientGroup.mk g : StatedProj (StatedSL m K)) * QuotientGroup.mk g' =
      QuotientGroup.mk g' * QuotientGroup.mk g := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact h

variable [Finite K] [CharP K 2]

theorem centralizer_transvAxis_comm (hm : 2 ≤ m) {a : Fin m → K} (ha : a ≠ 0) :
    ∀ x ∈ Subgroup.centralizer
        (transvImage m K (transvAxis m K a) : Set (StatedProj (StatedSL m K))),
      ∀ y ∈ Subgroup.centralizer
        (transvImage m K (transvAxis m K a) : Set (StatedProj (StatedSL m K))),
        x * y = y * x := by
  intro x hx y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
  exact mk_mul_comm_of_statedMat (mul_comm_of_comm_axis hm ha
    (fun v hv => statedMat_comm_of_mem_centralizer_axis (by omega) hx hv)
    (fun v hv => statedMat_comm_of_mem_centralizer_axis (by omega) hy hv))

theorem centralizer_transvCenter_comm (hm : 2 ≤ m) {c : Fin m → K} (hc : c ≠ 0) :
    ∀ x ∈ Subgroup.centralizer
        (transvImage m K (transvCenter m K c) : Set (StatedProj (StatedSL m K))),
      ∀ y ∈ Subgroup.centralizer
        (transvImage m K (transvCenter m K c) : Set (StatedProj (StatedSL m K))),
        x * y = y * x := by
  intro x hx y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
  have hT : ∀ g : StatedSL m K, (QuotientGroup.mk g : StatedProj (StatedSL m K)) ∈
      Subgroup.centralizer
        (transvImage m K (transvCenter m K c) : Set (StatedProj (StatedSL m K))) →
      ∀ v, c ⬝ᵥ v = 0 → (statedMat g)ᵀ * vecMulVec v c = vecMulVec v c * (statedMat g)ᵀ := by
    intro g hg v hv
    have h := statedMat_comm_of_mem_centralizer_center (by omega) hg
      (by rwa [dotProduct_comm] : v ⬝ᵥ c = 0)
    have h' := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, transpose_vecMulVec] at h'
    exact h'.symm
  have := mul_comm_of_comm_axis hm hc (hT g hx) (hT g' hy)
  apply mk_mul_comm_of_statedMat
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul]
  exact this.symm

end Transvections

section Consumer

theorem comm_of_le_centralizer_transv {G : Type*} [Group G] {m f : ℕ} (hm : 2 ≤ m) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (e : G ≃* StatedProj (StatedSL m K))
    {E L : Subgroup G}
    (hE : (∃ c : Fin m → K, c ≠ 0 ∧ E.map e.toMonoidHom = transvImage m K (transvCenter m K c)) ∨
      (∃ a : Fin m → K, a ≠ 0 ∧ E.map e.toMonoidHom = transvImage m K (transvAxis m K a)))
    (hL : L ≤ Subgroup.centralizer (E : Set G)) : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  have : CharP K 2 := charP_two_of_card hK
  have hc : ∀ z ∈ L, e z ∈ Subgroup.centralizer
      (((E.map e.toMonoidHom : Subgroup (StatedProj (StatedSL m K)))) :
        Set (StatedProj (StatedSL m K))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (hL hz) w hw
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg e this
  intro x hx y hy
  apply e.injective
  rw [map_mul, map_mul]
  rcases hE with ⟨c, hc0, hEc⟩ | ⟨a, ha0, hEa⟩
  · exact centralizer_transvCenter_comm hm hc0 _ (hEc ▸ hc x hx) _ (hEc ▸ hc y hy)
  · exact centralizer_transvAxis_comm hm ha0 _ (hEa ▸ hc x hx) _ (hEa ▸ hc y hy)

end Consumer

end CFSG.CGT.PushingUpLit.T2KSW
