module

public import CFSG.GH74.GLS.Stage4.Q3n.Derived

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open Subgroup

theorem exists_elements_of_card_four {G : Type} [Group G] (U : Subgroup G) (hcard : Nat.card U = 4)
    (hexp : ∀ x ∈ U, x * x = 1) {z : G} (hz : z ∈ U) (hz1 : z ≠ 1) :
    ∃ t ∈ U, ∀ y ∈ U, y = 1 ∨ y = z ∨ y = t ∨ y = z * t := by
  classical
  have hUfin : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype (U : Set G) := Fintype.ofFinite _
  have hzz : z * z = 1 := hexp z hz
  have hfin : Finite (zpowers z) :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, by rw [pow_two]; exact hzz⟩)
  have hzmem : ∀ x : G, x ∈ zpowers z ↔ x = 1 ∨ x = z := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
      have : z ^ k = z ^ (k % 2) := by
        conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
      rw [this]
      rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact mem_zpowers _
  have hcz : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have : ¬ U ≤ zpowers z := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨t, htU, htz⟩ := Set.not_subset.1 this
  have ht1 : t ≠ 1 := fun h => htz ((hzmem t).2 (Or.inl h))
  have htz' : t ≠ z := fun h => htz ((hzmem t).2 (Or.inr h))
  refine ⟨t, htU, ?_⟩
  have hS : ({1, z, t, z * t} : Finset G).card = 4 := by
    have h1 : (1 : G) ≠ z := fun h => hz1 h.symm
    have h2 : (1 : G) ≠ t := fun h => ht1 h.symm
    have h3 : (1 : G) ≠ z * t := by
      intro h
      apply htz'
      have : t = z⁻¹ := by
        have := congrArg (fun a => z⁻¹ * a) h
        simpa using this.symm
      rw [this]
      exact inv_eq_of_mul_eq_one_right hzz
    have h4 : z ≠ t := fun h => htz' h.symm
    have h5 : z ≠ z * t := by
      intro h
      apply ht1
      have := congrArg (fun a => z⁻¹ * a) h
      simpa using this.symm
    have h6 : t ≠ z * t := by
      intro h
      apply hz1
      have := congrArg (fun a => a * t⁻¹) h
      simpa using this.symm
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]
  have hsub : ({1, z, t, z * t} : Finset G) ⊆ (U : Set G).toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Set.mem_toFinset, SetLike.mem_coe]
    rcases hy with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz
    · exact htU
    · exact U.mul_mem hz htU
  have hcard' : (U : Set G).toFinset.card = 4 := by
    rw [Set.toFinset_card, ← hcard, Nat.card_eq_fintype_card]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro y hy
  have : y ∈ (U : Set G).toFinset := by simpa using hy
  rw [← heq] at this
  simpa using this

namespace Q3nSetting

variable {G : Type} [Group G] [Finite G] {n : ℕ} (S : Q3nSetting G n)

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have h2 := S.z_ord
  rw [h, orderOf_one] at h2
  omega

theorem z_mem_K₁ : S.z ∈ S.K₁ := by
  have : S.z ∈ S.K₁ ⊓ S.K₂ := by rw [S.K_inter]; exact mem_zpowers _
  exact this.1

theorem z_mem_K₂ : S.z ∈ S.K₂ := by
  have : S.z ∈ S.K₁ ⊓ S.K₂ := by rw [S.K_inter]; exact mem_zpowers _
  exact this.2

theorem K_le_centralizer_z : S.K₁ ⊔ S.K₂ ≤ Subgroup.centralizer ({S.z} : Set G) := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (S.K_comm x hx S.z S.z_mem_K₂).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact S.K_comm S.z S.z_mem_K₁ x hx

theorem U_comm : ∀ x ∈ S.U, ∀ y ∈ S.U, x * y = y * x := by
  intro x hx y hy
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (S.U_exp x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (S.U_exp y hy)
  have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (S.U_exp _ (S.U.mul_mem hx hy))
  calc x * y = (x * y)⁻¹ := hxy'.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem U_le_centralizer_z : S.U ≤ Subgroup.centralizer ({S.z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact S.U_comm S.z S.z_mem_U x hx

theorem index_K_le_two :
    ((S.K₁ ⊔ S.K₂).subgroupOf (Subgroup.centralizer ({S.z} : Set G))).index ≤ 2 := by
  classical
  obtain ⟨t, htU, ht⟩ := exists_elements_of_card_four S.U S.U_card S.U_exp S.z_mem_U S.z_ne_one
  set Mg := Subgroup.centralizer ({S.z} : Set G) with hMg
  set K := S.K₁ ⊔ S.K₂ with hK
  have hKM : K ≤ Mg := S.K_le_centralizer_z
  have hUM : S.U ≤ Mg := S.U_le_centralizer_z
  have hnorm : (K.subgroupOf Mg).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact S.K_normal g g.2 x hx
  let tM : Mg := ⟨t, hUM htU⟩
  let f : Bool → Mg ⧸ K.subgroupOf Mg := fun b =>
    if b then QuotientGroup.mk 1 else QuotientGroup.mk tM
  have hzK : S.z ∈ K := Subgroup.mem_sup_left S.z_mem_K₁
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      obtain ⟨x, hx, y, hy, hcxy⟩ := S.C_eq (c : G) c.2
      have hyM : y ∈ Mg := hUM hy
      have hcy : (QuotientGroup.mk c : Mg ⧸ K.subgroupOf Mg) = QuotientGroup.mk ⟨y, hyM⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        change (((c : G)⁻¹ * y : G)) ∈ K
        rw [hcxy]
        have : (x * y)⁻¹ * y = y⁻¹ * x⁻¹ * y := by group
        rw [this]
        have hxK : x⁻¹ ∈ K := K.inv_mem hx
        have := S.K_normal y⁻¹ (Subgroup.inv_mem _ hyM) x⁻¹ hxK
        simpa [mul_assoc] using this
      rw [hcy]
      rcases ht y hy with h | h | h | h
      · refine ⟨true, ?_⟩
        simp only [f, ↓reduceIte]
        congr 1
        exact Subtype.ext h.symm
      · refine ⟨true, ?_⟩
        simp only [f, ↓reduceIte]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        change (((1 : Mg) : G)⁻¹ * y : G) ∈ K
        rw [h]; simpa using hzK
      · refine ⟨false, ?_⟩
        simp only [f, Bool.false_eq_true, ↓reduceIte]
        congr 1
        exact Subtype.ext h.symm
      · refine ⟨false, ?_⟩
        simp only [f, Bool.false_eq_true, ↓reduceIte]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        change ((t : G)⁻¹ * y : G) ∈ K
        rw [h]
        have : t⁻¹ * (S.z * t) = t⁻¹ * S.z * t := by group
        rw [this]
        have := S.K_normal t⁻¹ (Subgroup.inv_mem _ (hUM htU)) S.z hzK
        simpa [mul_assoc] using this
  have hcard : Nat.card (Mg ⧸ K.subgroupOf Mg) ≤ Nat.card Bool :=
    Nat.card_le_card_of_surjective f hsurj
  rw [Subgroup.index]
  simpa using hcard

theorem card_C0 : ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 ∧
    Nat.card ↥(Subgroup.centralizer (S.U : Set G)) = m * (4 * S.k ^ 2) := by
  classical
  set C0 := Subgroup.centralizer (S.U : Set G) with hC0
  have hHC : S.H ≤ C0 := S.H_le_centralizer
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHC
  have hsub : (C0 : Set G) ⊆ (S.H : Set G) ∪ (fun h => h * S.w₀) '' (S.H : Set G) := by
    intro c hc
    obtain ⟨h, hh, hcase⟩ := S.C0_eq c hc
    rcases hcase with rfl | rfl
    · exact Or.inl hh
    · exact Or.inr ⟨h, hh, rfl⟩
  have hle : Nat.card C0 ≤ 2 * Nat.card S.H := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (S.H : Set G) ((fun h => h * S.w₀) '' (S.H : Set G))
    have h3 : ((fun h => h * S.w₀) '' (S.H : Set G)).ncard = (S.H : Set G).ncard :=
      Set.ncard_image_of_injective _ (mul_left_injective S.w₀)
    rw [h3] at h2
    have e1 : Nat.card ↥C0 = (C0 : Set G).ncard := Nat.card_coe_set_eq (C0 : Set G)
    have e2 : Nat.card ↥S.H = (S.H : Set G).ncard := Nat.card_coe_set_eq (S.H : Set G)
    rw [e1, e2]
    omega
  rw [S.card_H] at hm hle
  refine ⟨m, ?_, ?_, by rw [hm]; ring⟩
  · have : 0 < Nat.card C0 := Nat.card_pos
    rw [hm] at this
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at this; simp at this
    · exact h
  · have hk0 : 0 < 4 * S.k ^ 2 := by
      have := S.k_odd.pos
      positivity
    rw [hm] at hle
    nlinarith

theorem three_not_dvd_card_C0 (hn : 1 ≤ n) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (S.U : Set G)) := by
  obtain ⟨m, h1, h2, h⟩ := S.card_C0
  rw [h]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h3 | h3
  · have := Nat.le_of_dvd (by omega) h3
    omega
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
    · omega
    · exact S.three_not_dvd_k hn ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4))

theorem two_pow_dvd_two :
    2 ^ ((Nat.card ↥(Subgroup.centralizer (S.U : Set G))).factorization 2 - 2) ∣ 2 := by
  obtain ⟨m, h1, h2, h⟩ := S.card_C0
  rw [h]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : S.k ≠ 0 := S.k_odd.pos.ne'
  have hkv : padicValNat 2 S.k = 0 := padicValNat.eq_zero_of_not_dvd (by
    have := Nat.odd_iff.1 S.k_odd; omega)
  have h4 : padicValNat 2 (4 * S.k ^ 2) = 2 := by
    rw [padicValNat.mul (by norm_num) (pow_ne_zero 2 hk0), padicValNat.pow S.k 2, hkv]
    have : padicValNat 2 4 = 2 := by
      have := padicValNat.prime_pow (p := 2) 2
      simpa using this
    omega
  have hm0 : m ≠ 0 := by omega
  rw [Nat.factorization_def _ Nat.prime_two, padicValNat.mul hm0 (by positivity), h4]
  have hm : padicValNat 2 m ≤ 1 := by
    interval_cases m
    · simp
    · simp
  calc 2 ^ (padicValNat 2 m + 2 - 2) ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
    _ = 2 := by norm_num

theorem K_subgroupOf_normal :
    ((S.K₁ ⊔ S.K₂).subgroupOf (Subgroup.centralizer ({S.z} : Set G))).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact S.K_normal g g.2 x hx

theorem K₁_le_centralizer_z : S.K₁ ≤ Subgroup.centralizer ({S.z} : Set G) :=
  le_sup_left.trans S.K_le_centralizer_z

theorem K₂_le_centralizer_z : S.K₂ ≤ Subgroup.centralizer ({S.z} : Set G) :=
  le_sup_right.trans S.K_le_centralizer_z

end Q3nSetting

end CFSG.GH74.GLS.Stage4.Q3n
