module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Blueprint.FischerDefs
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

noncomputable abbrev eF4 : F4 ≃+* K := F4.equivGaloisField

noncomputable abbrev frob : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 1

theorem card_K : Nat.card K = (2 ^ 1) ^ 2 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem frob_apply (c : K) : frob c = c ^ 2 := by
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]

theorem isUnitaryInvolution_frob : IsUnitaryInvolution frob :=
  CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution card_K

theorem frob_frob (c : K) : frob (frob c) = c := isUnitaryInvolution_frob.invol c

theorem eF4_inj {a b : F4} : eF4 a = eF4 b ↔ a = b := eF4.injective.eq_iff

theorem frob_eF4 (c : F4) : frob (eF4 c) = eF4 (c ^ 2) := by rw [frob_apply, map_pow]

@[expose] noncomputable def ω : K := eF4 F4.ω

theorem omega_eq : ω = eF4 F4.ω := rfl

theorem two_eq_zero : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  exact_mod_cast this

theorem add_self_K (c : K) : c + c = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem neg_K (c : K) : -c = c := neg_eq_of_add_eq_zero_left (add_self_K c)

theorem sub_K (a b : K) : a - b = a + b := by rw [sub_eq_add_neg, neg_K]

theorem frob_mul_self {c : K} (hc : c ≠ 0) : frob c * c = 1 := by
  obtain ⟨c, rfl⟩ := eF4.surjective c
  rw [Ne, ← map_zero eF4, eF4_inj] at hc
  rw [frob_eF4, ← map_mul, ← map_one eF4, eF4_inj]
  revert c
  decide

theorem mul_frob_self {c : K} (hc : c ≠ 0) : c * frob c = 1 := by
  rw [mul_comm, frob_mul_self hc]

theorem frob_eq_inv {c : K} (hc : c ≠ 0) : frob c = c⁻¹ :=
  eq_inv_of_mul_eq_one_left (frob_mul_self hc)

theorem add_frob_eq_zero_iff (c : K) : c + frob c = 0 ↔ c = 0 ∨ c = 1 := by
  obtain ⟨c, rfl⟩ := eF4.surjective c
  rw [frob_eF4, ← map_add, ← map_zero eF4, ← map_one eF4, eF4_inj, eF4_inj, eF4_inj]
  revert c
  decide

theorem add_frob_eq_zero_or_one (c : K) : c + frob c = 0 ∨ c + frob c = 1 := by
  obtain ⟨c, rfl⟩ := eF4.surjective c
  rw [frob_eF4, ← map_add, ← map_zero eF4, ← map_one eF4, eF4_inj, eF4_inj]
  revert c
  decide

theorem frob_eq_self_iff (c : K) : frob c = c ↔ c = 0 ∨ c = 1 := by
  obtain ⟨c, rfl⟩ := eF4.surjective c
  rw [frob_eF4, ← map_zero eF4, ← map_one eF4, eF4_inj, eF4_inj, eF4_inj]
  revert c
  decide

theorem one_add_frob_one : (1 : K) + frob 1 = 0 := by rw [map_one, add_self_K]

theorem omega_ne_zero : ω ≠ 0 := by
  rw [ω, Ne, ← map_zero eF4, eF4_inj]
  decide

theorem omega_ne_one : ω ≠ 1 := by
  rw [ω, Ne, ← map_one eF4, eF4_inj]
  decide

theorem frob_omega : frob ω = ω + 1 := by
  rw [ω, frob_eF4, ← map_one eF4, ← map_add, eF4_inj]
  decide

theorem omega_add_frob : ω + frob ω = 1 := by
  rw [frob_omega, ← add_assoc, add_self_K, zero_add]

theorem frob_omega_ne_one : frob ω ≠ 1 := by
  intro h
  apply omega_ne_one
  rw [← frob_frob ω, h, map_one]

theorem frob_ne_zero {c : K} (hc : c ≠ 0) : frob c ≠ 0 := (map_ne_zero frob).mpr hc

theorem herm_self_eq_zero_or_one {n : ℕ} (x : Fin n → K) :
    herm frob x x = 0 ∨ herm frob x x = 1 :=
  (frob_eq_self_iff _).1 (herm_self_fixed frob frob_frob x)

theorem fischerHermitianF4_eq_herm {m : ℕ} (x y : Fin m → K) :
    fischerHermitianF4 m x y = herm frob y x := by
  rw [fischerHermitianF4, herm_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_apply, mul_comm]

noncomputable abbrev SUm (m : ℕ) : Subgroup (GL (Fin m) K) :=
  fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) K => A.det = 1 ∧
    ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y

noncomputable abbrev TU (m : ℕ) : Set (GL (Fin m) K) :=
  fischerTransvections (fischerHermitianF4 m) fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0

theorem SUm_eq (m : ℕ) : SUm m = SUid frob m := by
  have h : {g : GL (Fin m) K | (g : Matrix (Fin m) (Fin m) K).det = 1 ∧
      ∀ x y, fischerHermitianF4 m ((g : Matrix (Fin m) (Fin m) K) *ᵥ x)
        ((g : Matrix (Fin m) (Fin m) K) *ᵥ y) = fischerHermitianF4 m x y} =
      (SUid frob m : Set (GL (Fin m) K)) := by
    ext g
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, mem_SUid_iff]
    simp only [fischerHermitianF4_eq_herm]
    exact and_congr_right fun _ => ⟨fun h x y => h y x, fun h x y => h y x⟩
  rw [SUm, fischerMatrixGroup, h, Subgroup.closure_eq]

theorem mem_TU_iff {m : ℕ} {g : GL (Fin m) K} :
    g ∈ TU m ↔ ∃ v : Fin m → K, v ≠ 0 ∧ herm frob v v = 0 ∧
      ∀ x, (g : Matrix (Fin m) (Fin m) K) *ᵥ x = x + herm frob v x • v := by
  simp only [TU, fischerTransvections, Set.mem_ofPred_eq, fischerHermitianF4_eq_herm]
  exact ⟨fun ⟨v, ⟨h0, h1⟩, h2⟩ => ⟨v, h0, h1, h2⟩, fun ⟨v, h0, h1, h2⟩ => ⟨v, ⟨h0, h1⟩, h2⟩⟩

variable {m : ℕ}

@[expose] noncomputable def tvU (v : Fin m → K) : SUid frob m := by
  classical
  exact if h : herm frob v v = 0 then tv frob_frob h one_add_frob_one else 1

theorem tvU_smul {v : Fin m → K} (hv : herm frob v v = 0) (x : Fin m → K) :
    tvU v • x = x + herm frob v x • v := by
  rw [tvU, dite_eq_left hv, tv_smul, one_mul]

theorem coe_tvU_mulVec {v : Fin m → K} (hv : herm frob v v = 0) (x : Fin m → K) :
    (((tvU v : SUid frob m) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x =
      x + herm frob v x • v :=
  tvU_smul hv x

theorem tvU_zero : tvU (0 : Fin m → K) = 1 :=
  ext_smul _ fun x => by rw [tvU_smul (herm_zero_left frob 0), smul_zero, add_zero, one_smul]

theorem tvU_smul_self {v : Fin m → K} (hv : herm frob v v = 0) : tvU v • v = v := by
  rw [tvU_smul hv, hv, zero_smul, add_zero]

theorem tvU_smul_of_herm_eq_zero {v x : Fin m → K} (hv : herm frob v v = 0)
    (hx : herm frob v x = 0) : tvU v • x = x := by
  rw [tvU_smul hv, hx, zero_smul, add_zero]

theorem tvU_mul_self {v : Fin m → K} (hv : herm frob v v = 0) : tvU v * tvU v = 1 :=
  ext_smul _ fun x => by
    rw [mul_smul, tvU_smul hv, tvU_smul hv, herm_add_right, herm_smul_right, hv, mul_zero,
      add_zero, add_assoc, ← add_smul, add_self_K, zero_smul, add_zero, one_smul]

theorem tvU_inv {v : Fin m → K} (hv : herm frob v v = 0) : (tvU v)⁻¹ = tvU v :=
  inv_eq_of_mul_eq_one_right (tvU_mul_self hv)

theorem herm_smul_smul_self {v : Fin m → K} (hv : herm frob v v = 0) (c : K) :
    herm frob (c • v) (c • v) = 0 := by
  rw [herm_smul_left, herm_smul_right, hv, mul_zero, mul_zero]

theorem tvU_smul_vec {v : Fin m → K} (hv : herm frob v v = 0) {c : K} (hc : c ≠ 0) :
    tvU (c • v) = tvU v :=
  ext_smul _ fun x => by
    rw [tvU_smul (herm_smul_smul_self hv c), tvU_smul hv, herm_smul_left, smul_smul,
      show frob c * herm frob v x * c = (frob c * c) * herm frob v x by ring,
      frob_mul_self hc, one_mul]

theorem conj_tvU (g : SUid frob m) {v : Fin m → K} (hv : herm frob v v = 0) :
    g * tvU v * g⁻¹ = tvU (g • v) := by
  have hgv : herm frob (g • v) (g • v) = 0 := by rw [herm_smul_smul, hv]
  refine ext_smul _ fun x => ?_
  rw [conj_smul_of_tv g (tvU v) (c := 1) (fun y => by rw [one_mul]; exact tvU_smul hv y),
    tvU_smul hgv, one_mul]

theorem tvU_commute {a b : Fin m → K} (ha : herm frob a a = 0) (hb : herm frob b b = 0)
    (hab : herm frob a b = 0) : tvU a * tvU b = tvU b * tvU a := by
  have hba : herm frob b a = 0 := herm_eq_zero_comm frob frob_frob hab
  refine ext_smul _ fun x => ?_
  rw [mul_smul, mul_smul, tvU_smul ha, tvU_smul hb, tvU_smul ha, tvU_smul hb, herm_add_right,
    herm_add_right, herm_smul_right, herm_smul_right, hab, hba, mul_zero, mul_zero, add_zero,
    add_zero]
  abel

theorem herm_mul_herm_comm {a b : Fin m → K} (hab : herm frob a b ≠ 0) :
    herm frob a b * herm frob b a = 1 := by
  rw [herm_conj frob frob_frob a b]
  exact mul_frob_self hab

theorem tvU_braid {a b : Fin m → K} (ha : herm frob a a = 0) (hb : herm frob b b = 0)
    (hab : herm frob a b ≠ 0) : tvU a * tvU b * tvU a = tvU b * tvU a * tvU b := by
  have e1 : tvU a * tvU b * tvU a = tvU (tvU a • b) := by
    rw [← conj_tvU _ hb, tvU_inv ha]
  have e2 : tvU b * tvU a * tvU b = tvU (tvU b • a) := by
    rw [← conj_tvU _ ha, tvU_inv hb]
  have hv : tvU a • b = herm frob a b • (tvU b • a) := by
    rw [tvU_smul ha, tvU_smul hb, smul_add, smul_smul, herm_mul_herm_comm hab, one_smul,
      add_comm]
  rw [e1, e2, hv, tvU_smul_vec (by rw [herm_smul_smul, ha]) hab]

theorem pow_three_of_braid {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y * x = y * x * y) : (x * y) ^ 3 = 1 := by
  calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (y * x * y) * (y * x * y) := by rw [h]
    _ = y * x * (y * y) * x * y := by group
    _ = 1 := by rw [hy, mul_one, mul_assoc y x x, hx, mul_one, hy]

theorem tvU_mul_tvU_pow_three {a b : Fin m → K} (ha : herm frob a a = 0)
    (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0) : (tvU a * tvU b) ^ 3 = 1 :=
  pow_three_of_braid (tvU_mul_self ha) (tvU_mul_self hb) (tvU_braid ha hb hab)

theorem tvU_eq_tvU_iff {a b : Fin m → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0) (hb0 : b ≠ 0)
    (hb : herm frob b b = 0) : tvU a = tvU b ↔ ∃ c : K, b = c • a := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := exists_herm_ne_zero frob ha0
    have e := congrArg (· • y) h
    simp only [tvU_smul ha, tvU_smul hb, add_right_inj] at e
    have hby : herm frob b y ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at e
      exact ha0 ((smul_eq_zero.1 e).resolve_left hy)
    refine ⟨herm frob a y / herm frob b y, ?_⟩
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, e, smul_smul, inv_mul_cancel₀ hby, one_smul]
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; exact hb0 (zero_smul K a)
    exact (tvU_smul_vec ha hc).symm

theorem tvU_mem_T {v : Fin m → K} (hv : herm frob v v = 0) : tvU v ∈ T frob m := by
  rw [tvU, dite_eq_left hv]
  exact tv_mem_T _ _ _

theorem T_eq_closure_tvU (m : ℕ) :
    T frob m = Subgroup.closure {g | ∃ v : Fin m → K, v ≠ 0 ∧ herm frob v v = 0 ∧ g = tvU v} := by
  apply le_antisymm
  · rw [T, Subgroup.closure_le]
    rintro g ⟨a, c, ha, hc, hg⟩
    rcases (add_frob_eq_zero_iff c).1 hc with rfl | rfl
    · have : g = 1 := ext_smul _ fun x => by rw [hg, zero_mul, zero_smul, add_zero, one_smul]
      rw [this]
      exact Subgroup.one_mem _
    · by_cases ha0 : a = 0
      · have : g = 1 := ext_smul _ fun x => by
          rw [hg, ha0, smul_zero, add_zero, one_smul]
        rw [this]
        exact Subgroup.one_mem _
      · refine Subgroup.subset_closure ⟨a, ha0, ha, ext_smul _ fun x => ?_⟩
        rw [hg, tvU_smul ha, one_mul]
  · rw [Subgroup.closure_le]
    rintro _ ⟨v, -, hv, rfl⟩
    exact tvU_mem_T hv

theorem herm_single_add_single_left {n : ℕ} (i j : Fin n) (t : K) (x : Fin n → K) :
    herm frob (Pi.single i 1 + Pi.single j t) x = x i + frob t * x j := by
  rw [herm_add_left, herm_single_left, herm_single_left, map_one, one_mul]

theorem isotropic_single_add_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    herm frob (Pi.single i 1 + Pi.single j t : Fin n → K) (Pi.single i 1 + Pi.single j t) = 0 := by
  rw [herm_single_add_single hij, frob_mul_self ht, add_self_K]

theorem exists_ne_of_two_le {n : ℕ} (hn : 2 ≤ n) (j : Fin n) : ∃ i : Fin n, i ≠ j := by
  by_cases h : j.val = 0
  · refine ⟨⟨1, by omega⟩, fun e => ?_⟩
    rw [← e] at h
    exact one_ne_zero h
  · exact ⟨⟨0, by omega⟩, fun e => h (by rw [← e])⟩

theorem eq_zero_of_forall_isotropic {n : ℕ} (hn : 2 ≤ n) {x : Fin n → K}
    (h : ∀ z : Fin n → K, herm frob z z = 0 → herm frob z x = 0) : x = 0 := by
  funext j
  obtain ⟨i, hij⟩ := exists_ne_of_two_le hn j
  have h1 := h _ (isotropic_single_add_single hij one_ne_zero)
  have h2 := h _ (isotropic_single_add_single hij omega_ne_zero)
  rw [herm_single_add_single_left] at h1 h2
  rw [map_one, one_mul] at h1
  have h3 : (frob ω - 1) * x j = 0 := by linear_combination h2 - h1
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 frob_omega_ne_one)

theorem span_isotropic {n : ℕ} (hn : 2 ≤ n) :
    Submodule.span K {z : Fin n → K | herm frob z z = 0} = ⊤ := by
  set S := Submodule.span K {z : Fin n → K | herm frob z z = 0}
  have hne : (1 : K) - ω ≠ 0 := sub_ne_zero.2 (Ne.symm omega_ne_one)
  have hs : ∀ j : Fin n, (Pi.single j 1 : Fin n → K) ∈ S := by
    intro j
    obtain ⟨i, hij⟩ := exists_ne_of_two_le hn j
    have e : (Pi.single i 1 + Pi.single j 1 : Fin n → K) - (Pi.single i 1 + Pi.single j ω) =
        (1 - ω) • (Pi.single j 1 : Fin n → K) := by
      rw [add_sub_add_left_eq_sub, ← Pi.single_sub, ← Pi.single_smul, smul_eq_mul, mul_one]
    have e' : (Pi.single j 1 : Fin n → K) =
        (1 - ω)⁻¹ • ((Pi.single i 1 + Pi.single j 1 : Fin n → K) -
          (Pi.single i 1 + Pi.single j ω)) := by
      rw [e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e']
    exact S.smul_mem _ (S.sub_mem
      (Submodule.subset_span (isotropic_single_add_single hij one_ne_zero))
      (Submodule.subset_span (isotropic_single_add_single hij omega_ne_zero)))
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [show (Pi.single j (x j) : Fin n → K) = x j • (Pi.single j 1 : Fin n → K) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  exact S.smul_mem _ (hs j)

theorem linearMap_ext_isotropic {n : ℕ} (hn : 2 ≤ n) {M : Type*} [AddCommGroup M] [Module K M]
    {f g : (Fin n → K) →ₗ[K] M} (h : ∀ z : Fin n → K, herm frob z z = 0 → f z = g z) :
    f = g :=
  LinearMap.ext_on (span_isotropic hn) fun z hz => h z hz

end CFSG.Fischer.Classification.Unitary
