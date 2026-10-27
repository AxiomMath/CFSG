module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Fld
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ABGLocalTools

namespace Cat7E6

theorem mem_normalizer_of_comm {G : Type*} [Group G] {H : Subgroup G} {a : G}
    (h : ∀ x ∈ H, x * a = a * x) : a ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h _ hx
    rw [inv_mul_cancel_right] at h1
    rw [mul_left_cancel h1]
    exact hx

section Config

variable {K₀ : Type} [Group K₀] [Finite K₀] {q : ℕ} (c : Cat8.QConf K₀ q)

theorem finite_mulAut : Finite (MulAut K₀) :=
  Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀)) (fun _ _ h => MulEquiv.ext (congrFun h))

omit [Finite K₀] in
theorem isSylowOf_Q :
    IsSylowOf 2 c.Q (Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀))) := by
  obtain ⟨T, hT⟩ := c.Q_sylow
  refine ⟨T, ?_⟩
  rw [hT, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr c.Q_le]

omit [Finite K₀] in
theorem a_mem_C : c.a ∈ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) :=
  ⟨mem_sup_right (mem_zpowers _), mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite K₀] in
theorem comm_a_of_mem_Q {w : MulAut K₀} (hw : w ∈ c.Q) : w * c.a = c.a * w :=
  mem_centralizer_singleton_iff.mp (c.Q_le hw).2

theorem a_mem_Q : c.a ∈ c.Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut (K₀ := K₀)
  have hQ := isSylowOf_Q c
  have hle : c.Q ⊔ zpowers c.a ≤ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) :=
    sup_le c.Q_le (zpowers_le.mpr (a_mem_C c))
  have hp : IsPGroup 2 ↥(c.Q ⊔ zpowers c.a) :=
    IsPGroup.to_sup_of_normal_left' hQ.isPGroup (isPGroup_zpowers_of_sq c.adm.sq)
      (zpowers_le.mpr (mem_normalizer_of_comm fun x hx => comm_a_of_mem_Q c hx))
  have heq := hQ.eq_of_le le_sup_left hle hp
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

omit [Finite K₀] in
theorem conj_mem_Q {w : MulAut K₀} (hw : w ∈ c.Q) : c.g⁻¹ * w * c.g ∈ c.Q := by
  have h := (mem_normalizer_iff.mp (inv_mem c.g_norm) w).mp hw
  rwa [inv_inv] at h

theorem a_comm_conj : c.a * (c.g⁻¹ * c.a * c.g) = (c.g⁻¹ * c.a * c.g) * c.a :=
  (comm_a_of_mem_Q c (conj_mem_Q c (a_mem_Q c))).symm

omit [Finite K₀] in
theorem tau_comm {w : MulAut K₀} (hw : w ∈ c.Q) : c.tau * w = w * c.tau := by
  have h1 : w * c.a = c.a * w := comm_a_of_mem_Q c hw
  have h2 : (c.g * w * c.g⁻¹) * c.a = c.a * (c.g * w * c.g⁻¹) :=
    comm_a_of_mem_Q c ((mem_normalizer_iff.mp c.g_norm w).mp hw)
  have h3 : (c.g⁻¹ * c.a * c.g) * w = w * (c.g⁻¹ * c.a * c.g) := by
    calc (c.g⁻¹ * c.a * c.g) * w = c.g⁻¹ * (c.a * (c.g * w * c.g⁻¹)) * c.g := by group
      _ = c.g⁻¹ * ((c.g * w * c.g⁻¹) * c.a) * c.g := by rw [h2]
      _ = w * (c.g⁻¹ * c.a * c.g) := by group
  rw [Cat8.QConf.tau, mul_assoc, h3, ← mul_assoc, ← h1, mul_assoc]

theorem tau_ne_one : c.tau ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut (K₀ := K₀)
  intro h
  have hga : c.g⁻¹ * c.a * c.g = c.a := by
    have h1 : c.g⁻¹ * c.a * c.g = c.a⁻¹ := eq_inv_of_mul_eq_one_right (by
      rw [← Cat8.QConf.tau]; exact h)
    rw [h1, inv_eq_of_mul_eq_one_right c.adm.sq]
  have hgC : c.g ∈ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) := by
    refine ⟨mem_sup_left c.g_inn, mem_centralizer_singleton_iff.mpr ?_⟩
    calc c.g * c.a = c.g * (c.g⁻¹ * c.a * c.g) := by rw [hga]
      _ = c.a * c.g := by group
  have hQ := isSylowOf_Q c
  have hle : c.Q ⊔ zpowers c.g ≤ Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) :=
    sup_le c.Q_le (zpowers_le.mpr hgC)
  have hgp : IsPGroup 2 ↥(zpowers c.g) := by
    obtain ⟨k, hk⟩ := (hQ.isPGroup) ⟨c.g * c.g, c.g_sq⟩
    have hk' : (c.g * c.g) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hg2k : c.g ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ', pow_mul, sq, hk']
    rintro ⟨_, j, rfl⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2k, one_zpow]
  have hp : IsPGroup 2 ↥(c.Q ⊔ zpowers c.g) :=
    IsPGroup.to_sup_of_normal_left' hQ.isPGroup hgp (zpowers_le.mpr c.g_norm)
  have heq := hQ.eq_of_le le_sup_left hle hp
  apply c.g_not_mem
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

end Config

theorem exists_sq_eq_of_cyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (h8 : 8 ∣ Nat.card G) {x : G} (hx : x ^ 4 = 1) : ∃ y : G, x = y ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hog : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  have h4 : (orderOf g : ℤ) ∣ j * 4 :=
    orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_mul]; exact_mod_cast hx)
  obtain ⟨n, hn⟩ := h8
  rw [hog, hn] at h4
  obtain ⟨t, ht⟩ : (2 * n : ℤ) ∣ j := by
    obtain ⟨s, hs⟩ := h4
    exact ⟨s, by push_cast at hs; linarith⟩
  refine ⟨g ^ ((n : ℤ) * t), ?_⟩
  rw [ht, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem quat_a_inv {n : ℕ} (i : ZMod (2 * n)) :
    (QuaternionGroup.a i : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-i) :=
  inv_eq_of_mul_eq_one_right (by rw [QuaternionGroup.a_mul_a, add_neg_cancel,
    QuaternionGroup.a_zero])

theorem quat_two_n {n : ℕ} : ((n : ZMod (2 * n)) + n) = 0 := by
  have h : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
  push_cast at h
  linear_combination h

theorem quat_xa_inv {n : ℕ} (i : ZMod (2 * n)) :
    (QuaternionGroup.xa i : QuaternionGroup n)⁻¹ = QuaternionGroup.xa ((n : ZMod (2 * n)) + i) :=
  inv_eq_of_mul_eq_one_right (by
    rw [QuaternionGroup.xa_mul_xa]
    have : ((n : ZMod (2 * n)) + (n + i) - i) = 0 := by
      linear_combination (quat_two_n (n := n))
    rw [this, QuaternionGroup.a_zero])

theorem xa_commutator_a {n : ℕ} (i : ZMod (2 * n)) :
    (QuaternionGroup.xa i : QuaternionGroup n) * QuaternionGroup.a 1 * (QuaternionGroup.xa i)⁻¹ *
      (QuaternionGroup.a 1)⁻¹ = QuaternionGroup.a (-2) := by
  rw [quat_xa_inv, quat_a_inv, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
    QuaternionGroup.a_mul_a]
  congr 1
  linear_combination (quat_two_n (n := n))

theorem exists_sq_eq_of_quaternion {e : ℕ} (he : 2 ≤ e) {x : QuaternionGroup (2 ^ e)}
    (hx4 : x ^ 4 = 1) (hc : ∀ y, (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) : ∃ w, x = w ^ 2 := by
  rcases x with i | i
  ·
    set H := zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 ^ e)) with hH
    have : NeZero (2 * 2 ^ e) := ⟨by positivity⟩
    have hmem : (QuaternionGroup.a i : QuaternionGroup (2 ^ e)) ∈ H := by
      refine ⟨(i.val : ℤ), ?_⟩
      change (QuaternionGroup.a 1 : QuaternionGroup (2 ^ e)) ^ (i.val : ℤ) = _
      rw [zpow_natCast, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    have hcard : 8 ∣ Nat.card H := by
      rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one]
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
      exact ⟨2 ^ k, by ring⟩
    obtain ⟨y, hy⟩ := exists_sq_eq_of_cyclic hcard (x := ⟨_, hmem⟩)
      (Subtype.ext (by rw [Subgroup.coe_pow]; exact hx4))
    exact ⟨y, by rw [← Subgroup.coe_pow, ← hy]⟩
  · exfalso
    have h := hc (QuaternionGroup.a 1)
    rw [xa_commutator_a, sq, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero] at h
    have h4 : ((4 : ℕ) : ZMod (2 * 2 ^ e)) = 0 := by
      have := QuaternionGroup.a.inj h
      push_cast
      linear_combination -this
    rw [ZMod.natCast_eq_zero_iff] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 : 2 * 2 ^ 2 ≤ 2 * 2 ^ e := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) he)
    omega

open CFSG.DisconnectedInvolutionGraph.Helpers in
theorem exists_sq_eq_of_unique_involution {G : Type*} [Group G] [Finite G] (hp : IsPGroup 2 G)
    (hrank : NoCommutingDistinctInvolutions G) (h16 : 16 ≤ Nat.card G) {x : G} (hx4 : x ^ 4 = 1)
    (hc : ∀ y, (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) : ∃ w, x = w ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases rank_one_two_cyclic_or_quaternion hp hrank with hcyc | ⟨e, -, ⟨φ⟩⟩
  · obtain ⟨k, hk⟩ := hp.exists_card_eq
    have h8 : 8 ∣ Nat.card G := by
      rw [hk] at h16 ⊢
      have hk4 : 4 ≤ k := by
        by_contra h
        push Not at h
        have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact ⟨2 ^ (k - 3), by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
    exact exists_sq_eq_of_cyclic h8 hx4
  · have hcard : Nat.card G = 4 * 2 ^ e := by
      rw [← Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have he : 2 ≤ e := by
      by_contra h
      push Not at h
      have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨w, hw⟩ := exists_sq_eq_of_quaternion he (x := φ.symm x)
      (by rw [← map_pow, hx4, map_one])
      (fun y => by
        have := hc (φ y)
        apply φ.injective
        rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
          this, map_one])
    exact ⟨φ w, by rw [← map_pow, ← hw, MulEquiv.apply_symm_apply]⟩

end Cat7E6

end CFSG.ComponentClassification.GSThmB
