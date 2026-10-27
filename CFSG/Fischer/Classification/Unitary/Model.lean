module

public import CFSG.Fischer.Classification.Unitary.Basic
public import CFSG.Fischer.Pairs
public import CFSG.Fischer.Classification.Skeleton
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {m : ℕ}

theorem exists_smul_eq_of_mem_scalars {g : SUid frob m}
    (hg : g ∈ (StatedScalars (Fin m) K).subgroupOf (SUid frob m)) :
    ∃ c : K, ∀ x : Fin m → K, g • x = c • x := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨u, hu⟩ := hg
  refine ⟨u, fun x => ?_⟩
  rw [smul_def, ← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext k
  simp [Matrix.mulVec_diagonal]

theorem center_SUid (hm : 3 ≤ m) :
    Subgroup.center (SUid frob m) = (StatedScalars (Fin m) K).subgroupOf (SUid frob m) := by
  apply le_antisymm
  · intro z hz
    refine mem_scalars_of_smul_eq isUnitaryInvolution_frob hm fun x => ?_
    induction x using isoPts_ind with
    | h v hv0 hv =>
    rw [smul_pt]
    have hc : tvU (z • v) = tvU v := by
      rw [← conj_tvU z hv, (Subgroup.mem_center_iff.1 hz (tvU v)).symm, mul_inv_cancel_right]
    obtain ⟨c, hc⟩ := (tvU_eq_tvU_iff hv0 hv ((smul_ne_zero_iff_ne z).2 hv0)
      (by rw [herm_smul_smul, hv])).1 hc.symm
    exact (pt_eq_pt_iff _ _ _ _).2 ⟨c, hc.symm⟩
  · intro g hg
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hg h)

abbrev PG (m : ℕ) := SUid frob m ⧸ Subgroup.center (SUid frob m)

noncomputable abbrev tq (v : Fin m → K) : PG m := QuotientGroup.mk (tvU v)

@[expose] def DG (m : ℕ) : Set (PG m) :=
  {q | ∃ v : Fin m → K, v ≠ 0 ∧ herm frob v v = 0 ∧ tq v = q}

theorem tq_mem_DG {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) : tq v ∈ DG m :=
  ⟨v, hv0, hv, rfl⟩

theorem tq_mul_self {v : Fin m → K} (hv : herm frob v v = 0) : tq v * tq v = 1 := by
  rw [← QuotientGroup.mk_mul, tvU_mul_self hv, QuotientGroup.mk_one]

theorem conj_tq (g : SUid frob m) {v : Fin m → K} (hv : herm frob v v = 0) :
    (QuotientGroup.mk g : PG m) * tq v * (QuotientGroup.mk g)⁻¹ = tq (g • v) := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, conj_tvU g hv]

theorem tq_mul_tq_mul_tq {a b : Fin m → K} (ha : herm frob a a = 0) (hb : herm frob b b = 0) :
    tq a * tq b * tq a = tq (tvU a • b) := by
  rw [← conj_tq _ hb, ← QuotientGroup.mk_inv, tvU_inv ha]

theorem tq_eq_tq_iff (hm : 3 ≤ m) {a b : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0)
    (hb0 : b ≠ 0) (hb : herm frob b b = 0) : tq a = tq b ↔ ∃ c : K, b = c • a := by
  refine ⟨fun h => ?_, fun h => congrArg QuotientGroup.mk ((tvU_eq_tvU_iff ha0 ha hb0 hb).2 h)⟩
  rw [QuotientGroup.eq, tvU_inv ha, center_SUid hm] at h
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars h
  have hza := hc a
  rw [mul_smul, tvU_smul hb, smul_add, tvU_smul_self ha, smul_comm (tvU a) (herm frob b a) b,
    tvU_smul ha] at hza
  by_cases hab : herm frob a b = 0
  · have hba : herm frob b a = 0 := herm_eq_zero_comm frob frob_frob hab
    rw [hba, zero_smul, add_zero] at hza
    have hc1 : c = 1 := by
      have : (1 - c) • a = 0 := by rw [sub_smul, one_smul, ← hza, sub_self]
      exact (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right ha0)).symm
    have h1 : tvU a * tvU b = 1 := ext_smul _ fun x => by rw [hc x, hc1, one_smul, one_smul]
    rw [← tvU_eq_tvU_iff ha0 ha hb0 hb]
    calc tvU a = tvU a * (tvU a * tvU b) := by rw [h1, mul_one]
      _ = tvU b := by rw [← mul_assoc, tvU_mul_self ha, one_mul]
  · exfalso
    apply hab
    have hba : herm frob b a ≠ 0 := fun h0 => hab (herm_eq_zero_comm frob frob_frob h0)
    have hsum : ∀ x : Fin m → K, a + (x + a) = x := fun x => by
      rw [add_comm x a, ← add_assoc, ← two_smul K a, two_eq_zero, zero_smul, zero_add]
    rw [smul_add, smul_smul, mul_comm (herm frob b a) (herm frob a b), herm_mul_herm_comm hab,
      one_smul, hsum] at hza
    have hb' : b = ((herm frob b a)⁻¹ * c) • a := by
      rw [← smul_smul, ← hza, smul_smul, inv_mul_cancel₀ hba, one_smul]
    rw [hb', herm_smul_right, ha, mul_zero]

theorem tq_commute_iff (hm : 3 ≤ m) {a b : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0)
    (hb0 : b ≠ 0) (hb : herm frob b b = 0) : tq a * tq b = tq b * tq a ↔ herm frob a b = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [← QuotientGroup.mk_mul, tvU_commute ha hb h,
    QuotientGroup.mk_mul]⟩
  by_contra hab
  have h3 : (tq a * tq b) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, tvU_mul_tvU_pow_three ha hb hab,
      QuotientGroup.mk_one]
  have h2 : (tq a * tq b) ^ 2 = 1 := by
    rw [sq, mul_assoc, ← mul_assoc (tq b), ← h, mul_assoc, tq_mul_self hb, mul_one,
      tq_mul_self ha]
  have h1 : tq a * tq b = 1 := by
    calc tq a * tq b = (tq a * tq b) ^ 3 * ((tq a * tq b) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have heq : tq a = tq b := by
    calc tq a = tq a * (tq a * tq b) := by rw [h1, mul_one]
      _ = tq b := by rw [← mul_assoc, tq_mul_self ha, one_mul]
  obtain ⟨c, rfl⟩ := (tq_eq_tq_iff hm ha0 ha hb0 hb).1 heq
  exact hab (by rw [herm_smul_right, ha, mul_zero])

theorem exists_partner_frob {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    ∃ u : Fin m → K, u ≠ 0 ∧ herm frob u u = 0 ∧ herm frob v u = 1 := by
  obtain ⟨u, hu, hvu⟩ := exists_partner isUnitaryInvolution_frob hv0 hv
  refine ⟨u, ?_, hu, hvu⟩
  rintro rfl
  rw [herm_zero_right] at hvu
  exact zero_ne_one hvu

theorem tq_ne_one (hm : 3 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    tq v ≠ 1 := by
  obtain ⟨u, hu0, hu, hvu⟩ := exists_partner_frob hv0 hv
  intro h
  have := (tq_commute_iff hm hv0 hv hu0 hu).1 (by rw [h, one_mul, mul_one])
  rw [hvu] at this
  exact one_ne_zero this

@[expose] noncomputable def isoVec (hm : 2 ≤ m) : Fin m → K :=
  Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1

theorem isoVec_isotropic (hm : 2 ≤ m) : herm frob (isoVec hm) (isoVec hm) = 0 :=
  isotropic_single_add_single (by simp [Fin.ext_iff]) one_ne_zero

theorem isoVec_ne_zero (hm : 2 ≤ m) : isoVec hm ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by omega⟩
  simp [isoVec, Fin.ext_iff] at this

theorem DG_eq_isConj (hm : 3 ≤ m) {v₀ : Fin m → K} (hv₀0 : v₀ ≠ 0)
    (hv₀ : herm frob v₀ v₀ = 0) : DG m = {q | IsConj (tq v₀) q} := by
  ext q
  constructor
  · rintro ⟨w, hw0, hw, rfl⟩
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob hm hv₀0 hv₀ hw0 hw
    refine isConj_iff.2 ⟨QuotientGroup.mk t, ?_⟩
    rw [conj_tq t hv₀, ht]
  · intro h
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    rw [conj_tq g hv₀]
    exact ⟨g • v₀, (smul_ne_zero_iff_ne g).2 hv₀0, by rw [herm_smul_smul, hv₀], rfl⟩

theorem mul_sq_eq_one_of_commute {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (h : x * y = y * x) : (x * y) ^ 2 = 1 := by
  rw [sq, mul_assoc, ← mul_assoc y, ← h, mul_assoc, hy, mul_one, hx]

theorem orderOf_tq (hm : 3 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    orderOf (tq v) = 2 :=
  orderOf_eq_prime (by rw [sq, tq_mul_self hv]) (tq_ne_one hm hv0 hv)

theorem orderOf_tq_mul_tq_mem {a b : Fin m → K} (ha : herm frob a a = 0)
    (hb : herm frob b b = 0) : orderOf (tq a * tq b) ∈ ({1, 2, 3} : Set ℕ) := by
  by_cases hab : herm frob a b = 0
  · have h2 : (tq a * tq b) ^ 2 = 1 := mul_sq_eq_one_of_commute (tq_mul_self ha)
      (tq_mul_self hb) (by rw [← QuotientGroup.mk_mul, tvU_commute ha hb hab,
        QuotientGroup.mk_mul])
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h | h <;>
      simp [h]
  · have h3 : (tq a * tq b) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, tvU_mul_tvU_pow_three ha hb hab,
        QuotientGroup.mk_one]
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h <;>
      simp [h]

theorem closure_DG (hm : 4 ≤ m) : Subgroup.closure (DG m) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∈ T frob m := by
    rw [T_eq_top isUnitaryInvolution_frob (by omega) fun h => by omega]
    exact Subgroup.mem_top g
  rw [T_eq_closure_tvU] at hg
  have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center (SUid frob m))) hg
  rw [MonoidHom.map_closure] at h
  refine Subgroup.closure_mono ?_ h
  rintro _ ⟨_, ⟨v, hv0, hv, rfl⟩, rfl⟩
  exact ⟨v, hv0, hv, rfl⟩

theorem pair_DG (hm : 4 ≤ m) : Pair (PG m) (DG m) := by
  refine ⟨inferInstance, ⟨tq (isoVec (by omega)), DG_eq_isConj (by omega)
    (isoVec_ne_zero (by omega)) (isoVec_isotropic (by omega))⟩, ?_, ?_, closure_DG hm⟩
  · rintro _ ⟨v, hv0, hv, rfl⟩
    exact orderOf_tq (by omega) hv0 hv
  · rintro _ ⟨a, -, ha, rfl⟩ _ ⟨b, -, hb, rfl⟩
    exact orderOf_tq_mul_tq_mem ha hb

theorem exists_tq_not_commute (hm : 4 ≤ m) :
    ∃ a b : Fin m → K, a ≠ 0 ∧ herm frob a a = 0 ∧ b ≠ 0 ∧ herm frob b b = 0 ∧
      tq a * tq b ≠ tq b * tq a := by
  obtain ⟨u, hu0, hu, hvu⟩ := exists_partner_frob (isoVec_ne_zero (by omega : 2 ≤ m))
    (isoVec_isotropic (by omega))
  refine ⟨isoVec (by omega), u, isoVec_ne_zero _, isoVec_isotropic _, hu0, hu, fun h => ?_⟩
  have := (tq_commute_iff (by omega) (isoVec_ne_zero _) (isoVec_isotropic _) hu0 hu).1 h
  rw [hvu] at this
  exact one_ne_zero this

theorem isSimpleGroup_PG (hm : 4 ≤ m) : IsSimpleGroup (PG m) := by
  have := isSimpleGroup_statedProj_SUid isUnitaryInvolution_frob (n := m) (by omega)
    fun h => by omega
  exact (QuotientGroup.quotientMulEquivOfEq (center_SUid (by omega))).isSimpleGroup

theorem center_PG (hm : 4 ≤ m) : Subgroup.center (PG m) = ⊥ := by
  have := isSimpleGroup_PG hm
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (PG m)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, -, -, -, -, hab⟩ := exists_tq_not_commute hm
    have : tq a ∈ Subgroup.center (PG m) := by rw [h]; exact Subgroup.mem_top _
    exact hab (Subgroup.mem_center_iff.1 this (tq b)).symm

theorem commutator_PG (hm : 4 ≤ m) : commutator (PG m) = ⊤ := by
  have := isSimpleGroup_PG hm
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator (PG m)) with h | h
  · exfalso
    obtain ⟨a, b, -, -, -, -, hab⟩ := exists_tq_not_commute hm
    have hmem : ⁅tq a, tq b⁆ ∈ commutator (PG m) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact h

abbrev U2 (m : ℕ) := SUm m ⧸ Subgroup.center (SUm m)

@[expose] def DU (m : ℕ) : Set (U2 m) :=
  {q | ∃ h : SUm m, (h : GL (Fin m) K) ∈ TU m ∧ (QuotientGroup.mk h : U2 m) = q}

noncomputable def u2Equiv (m : ℕ) : U2 m ≃* PG m :=
  quotientCenterCongr (MulEquiv.subgroupCongr (SUm_eq m))

theorem u2Equiv_mk (h : SUm m) :
    u2Equiv m (QuotientGroup.mk h) = QuotientGroup.mk ⟨(h : GL (Fin m) K), SUm_eq m ▸ h.2⟩ := by
  rw [u2Equiv, quotientCenterCongr_mk]
  rfl

theorem image_DU (m : ℕ) : u2Equiv m '' DU m = DG m := by
  ext q
  constructor
  · rintro ⟨_, ⟨h, hT, rfl⟩, rfl⟩
    obtain ⟨v, hv0, hv, hx⟩ := mem_TU_iff.1 hT
    refine ⟨v, hv0, hv, ?_⟩
    rw [u2Equiv_mk]
    refine congrArg QuotientGroup.mk (ext_smul _ fun x => ?_)
    rw [tvU_smul hv, smul_def]
    exact (hx x).symm
  · rintro ⟨v, hv0, hv, rfl⟩
    refine ⟨QuotientGroup.mk ⟨((tvU v : SUid frob m) : GL (Fin m) K), (SUm_eq m).symm ▸ (tvU v).2⟩,
      ⟨_, mem_TU_iff.2 ⟨v, hv0, hv, coe_tvU_mulVec hv⟩, rfl⟩, ?_⟩
    rw [u2Equiv_mk]

@[expose] noncomputable def tqU (v : Fin m → K) : U2 m := (u2Equiv m).symm (tq v)

theorem tqU_eq (v : Fin m → K) : tqU v = (u2Equiv m).symm (tq v) := rfl

theorem u2Equiv_tqU (v : Fin m → K) : u2Equiv m (tqU v) = tq v := (u2Equiv m).apply_symm_apply _

theorem mem_DU_iff {q : U2 m} :
    q ∈ DU m ↔ ∃ v : Fin m → K, v ≠ 0 ∧ herm frob v v = 0 ∧ tqU v = q := by
  rw [← (u2Equiv m).injective.mem_set_image, image_DU]
  constructor
  · rintro ⟨v, hv0, hv, h⟩
    exact ⟨v, hv0, hv, (u2Equiv m).injective (by rw [u2Equiv_tqU, h])⟩
  · rintro ⟨v, hv0, hv, rfl⟩
    exact ⟨v, hv0, hv, (u2Equiv_tqU v).symm⟩

theorem tqU_mem_DU {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) : tqU v ∈ DU m :=
  mem_DU_iff.2 ⟨v, hv0, hv, rfl⟩

theorem tqU_eq_tqU_iff (hm : 3 ≤ m) {a b : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0)
    (hb0 : b ≠ 0) (hb : herm frob b b = 0) : tqU a = tqU b ↔ ∃ c : K, b = c • a := by
  rw [← tq_eq_tq_iff hm ha0 ha hb0 hb, tqU, tqU, (u2Equiv m).symm.injective.eq_iff]

theorem tqU_commute_iff (hm : 3 ≤ m) {a b : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0)
    (hb0 : b ≠ 0) (hb : herm frob b b = 0) :
    tqU a * tqU b = tqU b * tqU a ↔ herm frob a b = 0 := by
  rw [← tq_commute_iff hm ha0 ha hb0 hb, tqU, tqU, ← map_mul, ← map_mul,
    (u2Equiv m).symm.injective.eq_iff]

theorem tqU_mul_tqU_mul_tqU {a b : Fin m → K} (ha : herm frob a a = 0) (hb : herm frob b b = 0) :
    tqU a * tqU b * tqU a = tqU (tvU a • b) := by
  rw [tqU, tqU, tqU, ← map_mul, ← map_mul, tq_mul_tq_mul_tq ha hb]

end CFSG.Fischer.Classification.Unitary

namespace CFSG.Fischer.Classification

open CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification.Unitary

variable {m : ℕ}

theorem pair_DU (hm : 4 ≤ m) : Pair (U2 m) (DU m) :=
  (pair_congr (u2Equiv m) (image_DU m)).2 (pair_DG hm)

theorem center_U2 (hm : 4 ≤ m) : Subgroup.center (U2 m) = ⊥ := by
  have h := Subgroup.map_center_eq (u2Equiv m)
  rw [center_PG hm] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (u2Equiv m).injective).1 h

theorem commutator_U2 (hm : 4 ≤ m) : commutator (U2 m) = ⊤ :=
  (commutator_eq_top_congr (u2Equiv m)).2 (commutator_PG hm)

theorem isSimpleGroup_commutator_U2 (hm : 4 ≤ m) : IsSimpleGroup (commutator (U2 m)) := by
  have := isSimpleGroup_PG hm
  exact (((MulEquiv.subgroupCongr (commutator_U2 hm)).trans Subgroup.topEquiv).trans
    (u2Equiv m)).isSimpleGroup

theorem hyp_U2 (hm : 4 ≤ m) : Hyp (U2 m) (DU m) :=
  ⟨pair_DU hm, center_U2 hm, isSimpleGroup_commutator_U2 hm⟩

theorem fischerCentralQuotientModel_iff_U2 {G : Type*} [Group G] {D : Set G} :
    fischerCentralQuotientModel D (SUm m) (TU m) ↔ ∃ φ : G ≃* U2 m, φ '' D = DU m := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, Set.ext fun q => ⟨?_, fun hq => ?_⟩⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨h, hT, he⟩ := (hφ g).1 hg
      exact ⟨h, hT, he.symm⟩
    · refine ⟨φ.symm q, (hφ _).2 ?_, φ.apply_symm_apply q⟩
      obtain ⟨h, hT, he⟩ := hq
      exact ⟨h, hT, by rw [φ.apply_symm_apply, he]⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
    · obtain ⟨h, hT, he⟩ : φ g ∈ DU m := hφ ▸ ⟨g, hg, rfl⟩
      exact ⟨h, hT, he.symm⟩
    · obtain ⟨h, hT, he⟩ := hg
      have : φ g ∈ φ '' D := by rw [hφ]; exact ⟨h, hT, he.symm⟩
      obtain ⟨g', hg', hgg'⟩ := this
      rwa [← φ.injective hgg']

theorem classicalConclusion_of_mulEquiv_U2 {G : Type} [Group G] {D : Set G} (hm : 4 ≤ m)
    (φ : G ≃* U2 m) (hφ : φ '' D = DU m) : ClassicalConclusion G D :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, fischerCentralQuotientModel_iff_U2.2 ⟨φ, hφ⟩⟩)))

end CFSG.Fischer.Classification
