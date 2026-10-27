module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Quat
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G]

theorem card_of_quat {Y : Subgroup G} {n : ℕ} (hY : IVK.IsQuaternionTwoGroup ↥Y n) :
    Nat.card ↥Y = 2 ^ n := by
  obtain ⟨hn, ⟨e⟩⟩ := hY
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  calc 4 * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2) := by norm_num
    _ = 2 ^ n := by rw [← pow_add]; congr 1; omega

theorem isPGroup_of_quat {Y : Subgroup G} {n : ℕ} (hY : IVK.IsQuaternionTwoGroup ↥Y n) :
    IsPGroup 2 ↥Y :=
  IsPGroup.of_card (card_of_quat hY)

theorem card_ge_of_quat {Y : Subgroup G} {n : ℕ} (hY : IVK.IsQuaternionTwoGroup ↥Y n) :
    8 ≤ Nat.card ↥Y := by
  rw [card_of_quat hY]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hY.1

theorem quat_invol_sub {Y : Subgroup G} {n : ℕ} (hY : IVK.IsQuaternionTwoGroup ↥Y n) {z : G}
    (hz : z ∈ Y) (hz2 : z * z = 1) (hz1 : z ≠ 1) : ∀ p ∈ Y, p * p = 1 → p = 1 ∨ p = z := by
  obtain ⟨hn, ⟨e⟩⟩ := hY
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  exact B.quat_sub_invol e hz hz2 hz1

theorem Four.mem_cases [Finite G] {U : Subgroup G} (hU : Four U) {z u : G} (hz : z ∈ U) (hu : u ∈ U)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hzu : u ≠ z) {v : G} (hv : v ∈ U) :
    v = 1 ∨ v = z ∨ v = u ∨ v = z * u := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hv1, hvz, hvu, hvzu⟩ := hcon
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right (hU.1 z hz)
  have hzu1 : z * u ≠ 1 := by
    intro e
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_right e
    exact hzu (this.trans hz')
  have hzuz : z * u ≠ z := fun e => hu1 (by simpa using e)
  have hzuu : z * u ≠ u := fun e => hz1 (by simpa using e)
  have hzu' : z ≠ u := fun e => hzu e.symm
  have hT : ({1, z, u, z * u, v} : Finset G).card = 5 := by
    have e1 : (1 : G) ∉ ({z, u, z * u, v} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz1.symm, hu1.symm, hzu1.symm, hv1.symm⟩
    have e2 : z ∉ ({u, z * u, v} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzu', hzuz.symm, hvz.symm⟩
    have e3 : u ∉ ({z * u, v} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzuu.symm, hvu.symm⟩
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_pair hvzu.symm]
  have hsub : (↑({1, z, u, z * u, v} : Finset G) : Set G) ⊆ (U : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz
    · exact hu
    · exact mul_mem hz hu
    · exact hv
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hT] at h1
  have h2 : (U : Set G).ncard = Nat.card U := (Nat.card_coe_set_eq (U : Set G)).symm
  have h3 := hU.2
  omega

theorem sr_ne_one' {m : ℕ} (a : ZMod m) : (DihedralGroup.sr a : DihedralGroup m) ≠ 1 := by
  intro h
  cases h

theorem no_quat_in_dihedral {T : Type} [Group T] [Finite T] {m : ℕ} (e : T ≃* DihedralGroup m) {Q : Subgroup T}
    {z : T} (hz : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z) (hcard : 4 < Nat.card Q)
    (hnc : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) : False := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  by_cases hrefl : ∃ i : ZMod m, e.symm (DihedralGroup.sr i) ∈ Q
  · obtain ⟨i, hi⟩ := hrefl
    have hsr2 : ∀ j : ZMod m, e.symm (DihedralGroup.sr j) * e.symm (DihedralGroup.sr j) = 1 := by
      intro j; rw [← map_mul]; simp
    have hi2 := hsr2 i
    have hQ : ∀ q ∈ Q, q = 1 ∨ q = z := by
      intro q hq
      cases hqe : e q with
      | r j =>
        by_cases hj : j = 0
        · left
          apply e.injective
          rw [hqe, hj, map_one, DihedralGroup.one_def]
        · exfalso
          have hs : e.symm (DihedralGroup.sr i) * q ∈ Q := Q.mul_mem hi hq
          have hsq : e.symm (DihedralGroup.sr i) * q = e.symm (DihedralGroup.sr (i + j)) := by
            apply e.injective
            rw [map_mul, MulEquiv.apply_symm_apply, hqe]
            simp [DihedralGroup.sr_mul_r]
          rw [hsq] at hs
          have h1 := hz _ hs (hsr2 _)
          have h2 := hz _ hi hi2
          have hne : e.symm (DihedralGroup.sr (i + j)) ≠ e.symm (DihedralGroup.sr i) := by
            intro heq
            have := e.symm.injective heq
            have h3 : i + j = i := by simpa using this
            exact hj (by simpa using h3)
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact hne (h1.trans h2.symm)
          · have := congrArg e h1
            rw [MulEquiv.apply_symm_apply, map_one] at this
            exact sr_ne_one' _ this
          · have := congrArg e h2
            rw [MulEquiv.apply_symm_apply, map_one] at this
            exact sr_ne_one' _ this
          · exact hne (h1.trans h2.symm)
      | sr j =>
        have h1 : q * q = 1 := by
          apply e.injective
          rw [map_mul, hqe]; simp
        exact hz q hq h1
    have hsub : ∀ q ∈ Q, q ∈ ({1, z} : Finset T) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hQ q hq
    have h1 := B.card_subgroup_le_finset Q _ hsub
    have h2 : ({1, z} : Finset T).card ≤ 2 := Finset.card_le_two
    omega
  · push Not at hrefl
    have hrot : ∀ q ∈ Q, ∃ j : ZMod m, e q = DihedralGroup.r j := by
      intro q hq
      cases hqe : e q with
      | r j => exact ⟨j, rfl⟩
      | sr j =>
        exfalso
        apply hrefl j
        have : e.symm (DihedralGroup.sr j) = q := by rw [← hqe]; simp
        rw [this]; exact hq
    obtain ⟨ja, hja⟩ := hrot a ha
    obtain ⟨jb, hjb⟩ := hrot b hb
    apply hab
    apply e.injective
    rw [map_mul, map_mul, hja, hjb]
    simp [DihedralGroup.r_mul_r, add_comm]

theorem sd_of_centralizer [Finite G] {Q : Subgroup G} {z y : G} {n : ℕ}
    (hQq : IVK.IsQuaternionTwoGroup ↥Q n) (hz : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hy2 : y * y = 1) (hyQ : y ∉ Q) (hyn : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hcent : ∀ q ∈ Q, y * q = q * y → q = 1 ∨ q = z)
    (h1024 : Bg.B_maximalClass_of_small_centralizer) (hshape : Bg.B_two_maximalClass_shape) :
    ∃ m, IVK.IsSemidihedralTwoGroup ↥(Q ⊔ zpowers y) m := by
  classical
  have hy1 : y ≠ 1 := fun e => hyQ (e ▸ Q.one_mem)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hnorm : zpowers y ≤ normalizer (Q : Set G) := by
    refine zpowers_le.2 (mem_normalizer_of_both (fun x hx => hyn x hx) (fun x hx => ?_))
    have := hyn x hx
    rw [hyinv] at this ⊢
    exact this
  have hinf : Q ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rcases (mem_zpowers_of_sq hy2).1 ha.2 with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exact absurd (h1 ▸ ha.1) hyQ
  have hord : Nat.card ↥(zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_two_of_sq_one hy2 hy1
  have hcardT : Nat.card ↥(Q ⊔ zpowers y) = 2 * 2 ^ n := by
    have hc := card_sup_mul_card_inf (A := Q) (B := zpowers y) hnorm
    rw [hinf, Subgroup.card_bot, hord, card_of_quat hQq] at hc
    omega
  have hT2 : IsPGroup 2 ↥(Q ⊔ zpowers y) := IsPGroup.of_card (n := n + 1) (by rw [hcardT, pow_succ']
  )
  have hn3 : 3 ≤ n := hQq.1
  have h8 : 2 ^ 3 ≤ 2 * 2 ^ n := by
    calc 2 ^ 3 ≤ 2 ^ 1 * 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 1 * 2 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hn3)
      _ = 2 * 2 ^ n := by norm_num
  have h16 : 8 < 2 * 2 ^ n := by
    calc 8 < 2 * 2 ^ 3 := by norm_num
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hn3)
  have hmem : ∀ x ∈ Q ⊔ zpowers y, x ∈ Q ∨ ∃ b ∈ Q, x = y * b := by
    intro x hx
    rw [sup_comm] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_le_normalizer hnorm hx
    rcases (mem_zpowers_of_sq hy2).1 ha with h1 | h1
    · left; rw [h1, one_mul]; exact hb
    · right; exact ⟨b, hb, by rw [h1]⟩
  set T : Subgroup G := Q ⊔ zpowers y with hTdef
  have hyT : y ∈ T := mem_sup_right (mem_zpowers y)
  have hzT : z ∈ T := mem_sup_left hz
  let x₀ : ↥T := ⟨y, hyT⟩
  have hcentcard : Nat.card ↥(centralizer ({x₀} : Set ↥T)) ≤ 2 ^ 2 := by
    have hsub : ∀ c ∈ (centralizer ({x₀} : Set ↥T)).map T.subtype, c ∈ ({1, z, y, y * z} : Finset G) := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hc
      have hcomm : (c' : G) * y = y * (c' : G) := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hc'
        exact congrArg Subtype.val this
      show (c' : G) ∈ ({1, z, y, y * z} : Finset G)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hmem (c' : G) c'.2 with hq | ⟨b, hb, hcb⟩
      · rcases hcent _ hq hcomm.symm with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
      · rw [hcb] at hcomm
        have hb' : y * b = b * y := by
          have : y * b * y = y * (y * b) := hcomm
          calc y * b = (y * b * y) * y⁻¹ := by group
            _ = (y * (y * b)) * y⁻¹ := by rw [this]
            _ = b * y := by
              calc (y * (y * b)) * y⁻¹ = (y * y) * b * y⁻¹ := by group
                _ = b * y := by rw [hy2, one_mul, hyinv]
        rcases hcent b hb hb' with h1 | h1
        · right; right; left; rw [hcb, h1, mul_one]
        · right; right; right; rw [hcb, h1]
    have h1 := B.card_subgroup_le_finset _ _ hsub
    have h2 : Nat.card ↥((centralizer ({x₀} : Set ↥T)).map T.subtype) =
        Nat.card ↥(centralizer ({x₀} : Set ↥T)) :=
      Subgroup.card_map_of_injective T.subtype_injective
    have h3 : ({1, z, y, y * z} : Finset G).card ≤ 4 := Finset.card_le_four
    calc Nat.card ↥(centralizer ({x₀} : Set ↥T)) ≤ 4 := by omega
      _ = 2 ^ 2 := by norm_num
  obtain ⟨m, hm, hlcs⟩ := h1024 2 Nat.prime_two ↥T hT2 (by rw [hcardT]; exact h8) x₀ hcentcard
  rcases hshape ↥T hT2 (by rw [hcardT]; exact h16) m hm hlcs with ⟨k, -, ⟨e⟩⟩ | ⟨k, -, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩
  · exfalso
    have hQT : Q ≤ T := le_sup_left
    refine no_quat_in_dihedral e (Q := Q.subgroupOf T) (z := ⟨z, hzT⟩) ?_ ?_ ?_
    · intro q hq hq2
      have hq' : (q : G) ∈ Q := hq
      have hq2' : (q : G) * (q : G) = 1 := by simpa using congrArg Subtype.val hq2
      rcases quat_invol_sub hQq hz hz2 hz1 _ hq' hq2' with h1 | h1
      · left; exact Subtype.ext h1
      · right; exact Subtype.ext h1
    · have : Nat.card ↥(Q.subgroupOf T) = Nat.card ↥Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv
      have := card_ge_of_quat hQq
      omega
    · obtain ⟨a, b, hab⟩ := quat_noncomm_group hQq
      refine ⟨⟨a, hQT a.2⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hQT b.2⟩,
        Subgroup.mem_subgroupOf.2 b.2, fun h => hab ?_⟩
      have h' : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val h
      exact Subtype.ext h'
  · exfalso
    have : NeZero (2 ^ k) := ⟨by positivity⟩
    have hy' : (⟨y, hyT⟩ : ↥T) * ⟨y, hyT⟩ = 1 := Subtype.ext (by simpa using hy2)
    have hz' : (⟨z, hzT⟩ : ↥T) * ⟨z, hzT⟩ = 1 := Subtype.ext (by simpa using hz2)
    have hey := B.quat_invol (e ⟨y, hyT⟩) (by rw [← map_mul, hy', map_one])
    have hez := B.quat_invol (e ⟨z, hzT⟩) (by rw [← map_mul, hz', map_one])
    have hne1 : ∀ w : ↥T, w ≠ 1 → e w ≠ 1 := fun w hw h => hw (e.injective (by rw [h, map_one]))
    have hy1' : (⟨y, hyT⟩ : ↥T) ≠ 1 := fun h => hy1 (by simpa using congrArg Subtype.val h)
    have hz1' : (⟨z, hzT⟩ : ↥T) ≠ 1 := fun h => hz1 (by simpa using congrArg Subtype.val h)
    have h1 := hey.resolve_left (hne1 _ hy1')
    have h2 := hez.resolve_left (hne1 _ hz1')
    have h3 := e.injective (h1.trans h2.symm)
    have hyz : y = z := congrArg Subtype.val h3
    apply hyQ
    rw [hyz]
    exact hz
  · exact ⟨k, hk, ⟨e⟩⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
