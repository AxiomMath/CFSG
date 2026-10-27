module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter QuaternionGroup DihedralGroup

universe u v

section IndexTwo

variable {G : Type u} [Group G] [Finite G]

theorem exists_index_two_of_isPGroup (hG : IsPGroup 2 G) (h2 : 2 ∣ Nat.card G) :
    ∃ M : Subgroup G, M.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      rw [hk] at h2
      norm_num at h2
    · exact h
  obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := k - 1) (G := G)
    (by rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1))
  refine ⟨M, ?_⟩
  have h := M.card_mul_index
  have h2' : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hM, hk, h2'] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) h

theorem exists_index_two_of_normal (K : Subgroup G) [K.Normal] (hK : IsPGroup 2 (G ⧸ K))
    (h2 : 2 ∣ K.index) : ∃ M : Subgroup G, M.index = 2 := by
  obtain ⟨M, hM⟩ := exists_index_two_of_isPGroup hK (by rwa [← Subgroup.index_eq_card])
  refine ⟨M.comap (QuotientGroup.mk' K), ?_⟩
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K), hM]

theorem exists_index_two_of_two_pow_index (K : Subgroup G) [K.Normal] {k : ℕ}
    (hK : K.index = 2 ^ k) (hk : 1 ≤ k) : ∃ M : Subgroup G, M.index = 2 :=
  exists_index_two_of_normal K
    (IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card]; exact hK))
    (by rw [hK]; exact dvd_pow_self 2 (by omega))

theorem le_of_noIndexTwo (K₁ K₂ : Subgroup G) [K₂.Normal] (hK₂ : ∃ k : ℕ, K₂.index = 2 ^ k)
    (h₁ : ∀ M : Subgroup K₁, M.index ≠ 2) : K₁ ≤ K₂ := by
  obtain ⟨k, hk⟩ := hK₂
  have hdvd : K₂.relIndex K₁ ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_index_of_normal K₂ K₁
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hj
  · exfalso
    obtain ⟨M, hM⟩ := exists_index_two_of_two_pow_index (G := K₁) (K₂.subgroupOf K₁) hj hpos
    exact h₁ M hM

theorem eq_of_noIndexTwo (K₁ K₂ : Subgroup G) [K₁.Normal] [K₂.Normal]
    (hK₁ : ∃ k : ℕ, K₁.index = 2 ^ k) (hK₂ : ∃ k : ℕ, K₂.index = 2 ^ k)
    (h₁ : ∀ M : Subgroup K₁, M.index ≠ 2) (h₂ : ∀ M : Subgroup K₂, M.index ≠ 2) : K₁ = K₂ :=
  le_antisymm (le_of_noIndexTwo K₁ K₂ hK₂ h₁) (le_of_noIndexTwo K₂ K₁ hK₁ h₂)

omit [Finite G] in
theorem hasNormalPComplement_subgroup (h : HasNormalPComplement 2 G) (K : Subgroup G) :
    HasNormalPComplement 2 K := by
  obtain ⟨N, hN, hcop, hq⟩ := h
  refine ⟨N.subgroupOf K, inferInstance, ?_, ?_⟩
  · have hcard : Nat.card (N.subgroupOf K) = Nat.card (N ⊓ K : Subgroup G) := by
      rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
    have hdvd : Nat.card (N.subgroupOf K) ∣ Nat.card N := by
      rw [hcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right hdvd hcop
  · let φ : K ⧸ N.subgroupOf K →* G ⧸ N := QuotientGroup.map (N.subgroupOf K) N K.subtype le_rfl
    apply hq.of_injective φ
    intro p q hpq
    induction p using QuotientGroup.induction_on with | H x => ?_
    induction q using QuotientGroup.induction_on with | H y => ?_
    change ((x : G) : G ⧸ N) = ((y : G) : G ⧸ N) at hpq
    rw [QuotientGroup.eq] at hpq ⊢
    rw [Subgroup.mem_subgroupOf]
    simpa using hpq

theorem odd_card_of_hasNormalPComplement (h : HasNormalPComplement 2 G)
    (hG : ∀ M : Subgroup G, M.index ≠ 2) : Odd (Nat.card G) := by
  obtain ⟨N, hN, hcop, hq⟩ := h
  by_contra hodd
  have heven : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have h2 : 2 ∣ N.index := by
    rw [← N.card_mul_index] at heven
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp heven with h | h
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h) (by norm_num)
    · exact h
  obtain ⟨M, hM⟩ := exists_index_two_of_normal N hq h2
  exact hG M hM

theorem exists_index_two_of_hasNormalPComplement (h : HasNormalPComplement 2 G)
    (h2 : 2 ∣ Nat.card G) : ∃ M : Subgroup G, M.index = 2 := by
  by_contra hM
  simp only [not_exists] at hM
  have hodd := odd_card_of_hasNormalPComplement h hM
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem odd_card_of_noIndexTwo_of_hasNormalPComplement (h : HasNormalPComplement 2 G)
    (K : Subgroup G) (hK : ∀ M : Subgroup K, M.index ≠ 2) : Odd (Nat.card K) :=
  odd_card_of_hasNormalPComplement (hasNormalPComplement_subgroup h K) hK

end IndexTwo

section Quaternion

theorem quaternionGroup_mul_ne {n : ℕ} (hn : 2 ≤ n) :
    (a 1 : QuaternionGroup n) * xa 0 ≠ xa 0 * a 1 := by
  rw [a_mul_xa, xa_mul_a]
  intro h
  have h' : (0 : ZMod (2 * n)) - 1 = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    linear_combination -h'
  have hdvd := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp h2
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem quaternionGroup_not_isMulCommutative {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsMulCommutative (QuaternionGroup n) := by
  intro h
  exact quaternionGroup_mul_ne hn (isMulCommutative_iff.mp h _ _)

theorem not_injective_quaternion_dihedral {n : ℕ} (hn : 2 ≤ n) {m : ℕ}
    (φ : QuaternionGroup n →* DihedralGroup m) : ¬ Function.Injective φ := by
  intro hφ
  have : NeZero n := ⟨by omega⟩
  have hrot : ∀ g : QuaternionGroup n, orderOf g ≠ 2 → ∃ i, φ g = DihedralGroup.r i := by
    intro g hg
    rcases h : φ g with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      apply hg
      rw [← orderOf_injective φ hφ g, h, orderOf_sr]
  have ha : orderOf (a 1 : QuaternionGroup n) ≠ 2 := by
    rw [orderOf_a_one]
    omega
  have hx : orderOf (xa 0 : QuaternionGroup n) ≠ 2 := by
    rw [orderOf_xa]
    norm_num
  obtain ⟨i, hi⟩ := hrot _ ha
  obtain ⟨j, hj⟩ := hrot _ hx
  apply quaternionGroup_mul_ne hn
  apply hφ
  rw [map_mul, map_mul, hi, hj, r_mul_r, r_mul_r, add_comm]

end Quaternion

section SylowTypes

variable {G : Type u} [Group G] [Finite G]

theorem two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

omit [Finite G] in
theorem not_hasSemidihedralSylow_and_dihedral {n : ℕ} (hSD : HasSemidihedralSylow G n)
    (hD : HasDihedralSylowTwo G) : False := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨f⟩ := hSD.2 S
  obtain ⟨m, -, ⟨e⟩⟩ := hD S
  obtain ⟨q⟩ := sdQuaternionEight_equiv hSD.1
  let φ : QuaternionGroup 2 →* DihedralGroup (2 ^ m) :=
    e.toMonoidHom.comp (f.toMonoidHom.comp ((sdQuaternionEight n).subtype.comp q.symm.toMonoidHom))
  apply not_injective_quaternion_dihedral le_rfl φ
  exact e.injective.comp (f.injective.comp ((sdQuaternionEight n).subtype_injective.comp
    q.symm.injective))

omit [Finite G] in
theorem not_hasWreathedSylow_and_dihedral {n : ℕ} (hW : HasWreathedSylow G n)
    (hD : HasDihedralSylowTwo G) : False := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨e⟩ := hW.2 S
  obtain ⟨m, -, ⟨d⟩⟩ := hD S
  obtain ⟨q⟩ := (wreath_center_involution_and_quaternion_coordinates n hW.1).quaternion_eight
  let φ : QuaternionGroup 2 →* DihedralGroup (2 ^ m) :=
    d.toMonoidHom.comp (e.symm.toMonoidHom.comp
      ((Original.Q (2 ^ n)).subtype.comp q.toMonoidHom))
  apply not_injective_quaternion_dihedral le_rfl φ
  exact d.injective.comp (e.symm.injective.comp ((Original.Q (2 ^ n)).subtype_injective.comp
    q.injective))

omit [Finite G] in
theorem not_hasSemidihedralSylow_and_wreathed {n m : ℕ} (hSD : HasSemidihedralSylow G n)
    (hW : HasWreathedSylow G m) : False := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨f⟩ := hSD.2 S
  obtain ⟨e⟩ := hW.2 S
  have hstr := wreath_center_involution_and_quaternion_coordinates m hW.1
  let ψ : SemidihedralGroup n ≃* Wreath (2 ^ m) := f.trans e
  have hc1 : Nat.card (Subgroup.center (SemidihedralGroup n)) = 2 := center_card n hSD.1
  have hc2 : Nat.card (Subgroup.center (Wreath (2 ^ m))) = 2 ^ m := by
    rw [hstr.center, Original.Z, Nat.card_zpowers, Original.orderOf_a]
  have hc : Nat.card (Subgroup.center (SemidihedralGroup n)) =
      Nat.card (Subgroup.center (Wreath (2 ^ m))) := by
    rw [← Subgroup.map_center_eq ψ, Subgroup.card_map_of_injective ψ.injective]
  rw [hc1, hc2] at hc
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hW.1
  omega

omit [Finite G] in
theorem IsMaximalQuaternionIn.exists_quaternion_equiv {R Y : Subgroup G}
    (h : IsMaximalQuaternionIn R Y) :
    ∃ k : ℕ, 1 ≤ k ∧ Nonempty (Y ≃* QuaternionGroup (2 ^ k)) := by
  obtain ⟨hYR, hpos⟩ := h
  have eY : Y ≃* Y.subgroupOf R := (Subgroup.subgroupOfEquivOfLe hYR).symm
  rcases hpos with ⟨n, hn, ι, hι, himg⟩ | ⟨n, hn, ι, hι, himg⟩
  · exact ⟨n - 3, by omega, ⟨eY.trans (((Y.subgroupOf R).equivMapOfInjective ι hι).trans
      ((MulEquiv.subgroupCongr himg).trans (quaternionEquiv n hn).symm))⟩⟩
  · obtain ⟨eQ⟩ := (wreath_center_involution_and_quaternion_coordinates n hn).quaternion
    have hhalf : 2 ^ n / 2 = 2 ^ (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, Nat.mul_div_cancel _ two_pos]
      rfl
    rw [hhalf] at eQ
    exact ⟨n - 1, by omega, ⟨eY.trans (((Y.subgroupOf R).equivMapOfInjective ι hι).trans
      ((MulEquiv.subgroupCongr himg).trans eQ.symm))⟩⟩

theorem card_quaternionGroup_two_pow (k : ℕ) :
    Nat.card (QuaternionGroup (2 ^ k)) = 4 * 2 ^ k := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

end SylowTypes

end CFSG.QuasiDihedralFusion
