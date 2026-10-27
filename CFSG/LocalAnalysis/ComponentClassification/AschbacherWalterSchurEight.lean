module

public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentNormalization
public import CFSG.Walter.JRFacts

public section

namespace CFSG.ComponentClassification.WalterSchur

open scoped MatrixGroups

section Eight

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem sq_ne_one_of_orderOf_eq_four {x : A} (hx : orderOf x = 4) : x ^ 2 ≠ 1 := by
  intro h
  have := orderOf_le_of_pow_eq_one (by norm_num) h
  omega

theorem sq_eq_sq_of_orderOf_eq_four (hA : Nat.card A = 8) {x y : A} (hx : orderOf x = 4)
    (hy : orderOf y = 4) : y ^ 2 = x ^ 2 := by
  classical
  set H := Subgroup.zpowers x with hHdef
  have hH4 : Nat.card H = 4 := by rw [hHdef, Nat.card_zpowers, hx]
  have hidx : H.index = 2 := by
    have h := H.card_mul_index
    rw [hH4, hA] at h
    omega
  have hmem : y ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hidx y
  rw [hHdef, mem_zpowers_iff_mem_range_orderOf, Finset.mem_image, hx] at hmem
  obtain ⟨k, hk, hky⟩ := hmem
  have hy4 : (y ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = orderOf y by rw [hy], pow_orderOf_eq_one]
  have hy2 := sq_ne_one_of_orderOf_eq_four hy
  have hx4 : x ^ 4 = 1 := by rw [← hx, pow_orderOf_eq_one]
  rw [Finset.mem_range] at hk
  interval_cases k
  · exact absurd hky.symm (by simpa using hy2)
  · exfalso
    rw [pow_one] at hky
    rw [← hky] at hy4
    exact sq_ne_one_of_orderOf_eq_four hx hy4
  · exact hky.symm
  · exfalso
    rw [← hky, ← pow_mul, show 3 * 2 = 4 + 2 by norm_num, pow_add, hx4, one_mul] at hy4
    exact sq_ne_one_of_orderOf_eq_four hx hy4

omit [Finite A] in
theorem exists_orderOf_eq_four (hA : Nat.card A = 8) {x : A} (hx : x * x ≠ 1) :
    ∃ w : A, orderOf w = 4 := by
  have hdvd : orderOf x ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hA]
    exact orderOf_dvd_natCard x
  obtain ⟨k, hk, hxk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · exfalso
    rw [pow_zero, orderOf_eq_one_iff] at hxk
    exact hx (by rw [hxk, one_mul])
  · exfalso
    apply hx
    rw [← sq, ← pow_one 2, ← hxk, pow_orderOf_eq_one]
  · exact ⟨x, hxk⟩
  · refine ⟨x ^ 2, ?_⟩
    rw [orderOf_pow' x (by norm_num), hxk]
    norm_num

theorem dihedral_or_quaternion_of_card_eq_eight (hA : Nat.card A = 8)
    (hnc : ∃ a b : A, a * b ≠ b * a) :
    Nonempty (A ≃* DihedralGroup 4) ∨ Nonempty (A ≃* QuaternionGroup 2) := by
  classical
  have hexp : ∃ x : A, x * x ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have hinv : ∀ g : A, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  obtain ⟨x₀, hx₀⟩ := hexp
  obtain ⟨x, hx⟩ := exists_orderOf_eq_four hA hx₀
  have hx4 : x ^ 4 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hx2 : x ^ 2 ≠ 1 := sq_ne_one_of_orderOf_eq_four hx
  set H := Subgroup.zpowers x with hHdef
  have hH4 : Nat.card H = 4 := by rw [hHdef, Nat.card_zpowers, hx]
  have hidx : H.index = 2 := by
    have h := H.card_mul_index
    rw [hH4, hA] at h
    omega
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨y, hyH⟩ : ∃ y : A, y ∉ H := by
    by_contra h
    push Not at h
    have htop : H = ⊤ := eq_top_iff.mpr fun g _ => h g
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ := by
    set K := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hKdef
    have hHK : H ≤ K := le_sup_left
    have hyK : y ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hdvd : H.relIndex K ∣ 2 := hidx ▸ Subgroup.relIndex_dvd_index_of_le hHK
    have hne1 : H.relIndex K ≠ 1 := fun h => hyH (Subgroup.relIndex_eq_one.mp h hyK)
    have h2 : H.relIndex K = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hKi := Subgroup.relIndex_mul_index hHK
    rw [h2, hidx] at hKi
    exact Subgroup.index_eq_one.mp (by omega)
  have hcen : ∀ z : A, z * x = x * z → z * y = y * z → z ∈ Subgroup.center A := by
    intro z hzx hzy
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer {z} := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hzx.symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hzy.symm
    rw [hgen] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hnab : y * x * y⁻¹ ≠ x := by
    intro hyx
    have hxy : x * y = y * x := by
      calc x * y = y * x * y⁻¹ * y := by rw [hyx]
        _ = y * x := by group
    have hxc : x ∈ Subgroup.center A := hcen x rfl hxy
    have hyc : y ∈ Subgroup.center A := hcen y hxy.symm rfl
    have htop : Subgroup.center A = ⊤ := by
      rw [eq_top_iff, ← hgen]
      exact sup_le (Subgroup.zpowers_le.mpr hxc) (Subgroup.zpowers_le.mpr hyc)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)
  have hconj : y * x * y⁻¹ = x ^ 3 := by
    have hmem : y * x * y⁻¹ ∈ H := hHn.conj_mem x (Subgroup.mem_zpowers x) y
    have hord : orderOf (y * x * y⁻¹) = 4 := by
      rw [show y * x * y⁻¹ = MulAut.conj y x from rfl, MulEquiv.orderOf_eq, hx]
    rw [hHdef, mem_zpowers_iff_mem_range_orderOf, Finset.mem_image, hx] at hmem
    obtain ⟨k, hk, hkx⟩ := hmem
    rw [Finset.mem_range] at hk
    interval_cases k
    · exfalso
      rw [pow_zero] at hkx
      rw [← hkx, orderOf_one] at hord
      omega
    · exact absurd (by rw [← hkx, pow_one]) hnab
    · exfalso
      rw [← hkx] at hord
      exact sq_ne_one_of_orderOf_eq_four hord (by rw [← pow_mul, hx4])
    · exact hkx.symm
  have hx3 : x ^ 3 = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx4])
  have hrel : y * x * y⁻¹ = x⁻¹ := hconj.trans hx3
  have hy2mem : y ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hidx y
  rw [hHdef, mem_zpowers_iff_mem_range_orderOf, Finset.mem_image, hx] at hy2mem
  obtain ⟨j, hj, hjy⟩ := hy2mem
  rw [Finset.mem_range] at hj
  have hy2c : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
  have hclos : Subgroup.closure ({x, y} : Set A) = ⊤ := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, hgen]
  interval_cases j
  ·
    left
    rw [pow_zero] at hjy
    have hd := GorensteinWalter.dihedral_of_generators_of_not_mem x y hgen.symm hjy.symm hrel hyH
    rwa [hx] at hd
  · exfalso
    rw [pow_one] at hjy
    apply hnab
    rw [hjy]
    exact hy2c
  ·
    right
    obtain ⟨⟨e, -⟩, -⟩ := Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2)
      (by norm_num) hclos (by rw [hx]) hyH hjy.symm hrel
    exact ⟨e.symm⟩
  · exfalso
    have h1 : y * x ^ 3 * y⁻¹ = x ^ 3 := by rw [hjy]; exact hy2c
    have h2 : y * x ^ 3 * y⁻¹ = x := by
      rw [← conj_pow, hconj, ← pow_mul, show 3 * 3 = 4 * 2 + 1 by norm_num, pow_add, pow_mul,
        hx4, one_pow, one_mul, pow_one]
    apply hx2
    have h3 : x ^ 3 = x := h1.symm.trans h2
    have h4 : x ^ 2 * x = 1 * x := by rw [← pow_succ, h3, one_mul]
    exact mul_right_cancel h4

end Eight

section Simple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem mul_self_eq_one_of_abelian_card_eight (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) (hPc : IsMulCommutative (P : Subgroup G))
    (hP8 : Nat.card (P : Subgroup G) = 8) : ∀ x ∈ (P : Subgroup G), x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hc
  push Not at hc
  obtain ⟨x₀, hx₀P, hx₀⟩ := hc
  obtain ⟨w, hw⟩ := exists_orderOf_eq_four hP8 (x := ⟨x₀, hx₀P⟩)
    (fun h => hx₀ (congrArg Subtype.val h))
  set u : G := (w : G) ^ 2 with hudef
  have huP : u ∈ (P : Subgroup G) := Subgroup.pow_mem _ w.2 2
  have hu1 : u ≠ 1 := by
    intro h
    apply sq_ne_one_of_orderOf_eq_four hw
    exact Subtype.ext (by simpa [hudef] using h)
  have hcomm : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n * u = u * n := by
    intro n hn
    set w' : (P : Subgroup G) :=
      ⟨n * w * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn w).mp w.2⟩ with hw'def
    have hw' : orderOf w' = 4 := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (n * (w : G) * n⁻¹) = 4
      rw [show n * (w : G) * n⁻¹ = MulAut.conj n (w : G) from rfl, MulEquiv.orderOf_eq,
        Subgroup.orderOf_coe, hw]
    have hsq := congrArg Subtype.val (sq_eq_sq_of_orderOf_eq_four hP8 hw hw')
    simp only [Subgroup.coe_pow, hw'def] at hsq
    rw [conj_pow] at hsq
    calc n * u = n * u * n⁻¹ * n := by group
      _ = u * n := by rw [hudef, hsq]
  exact hu1 (Walter.eq_one_of_mem_sylow_of_commute_normalizer_of_simple hnonab P huP hcomm)

theorem isMulCommutative_of_card_eight
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (hP8 : Nat.card (P : Subgroup G) = 8) (hA7 : Nat.card G ≠ 2520)
    (hL2 : ∀ p k : ℕ, p.Prime → Odd p → 1 ≤ k → Nat.card G ≠ p ^ k * ((p ^ k) ^ 2 - 1) / 2) :
    IsMulCommutative (P : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnc
  have hnc' : ∃ a b : (P : Subgroup G), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnc ⟨⟨h⟩⟩
  rcases dihedral_or_quaternion_of_card_eq_eight hP8 hnc' with hD | hQ
  ·
    obtain ⟨e⟩ := hD
    rcases GorensteinWalter.gorenstein_walter G hnonab P ⟨4, ⟨e⟩⟩ with h7 |
      ⟨p, k, hp, hpodd, h5, hL⟩
    · obtain ⟨e7⟩ := h7
      apply hA7
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · obtain ⟨eL⟩ := hL
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h5
        · exact hk
      apply hL2 p k hp.out hpodd hk
      have hK : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by omega)
      rw [Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula _
        ⟨p, k, hp.out, hpodd, hk, hK⟩, hK]
  ·
    obtain ⟨e⟩ := hQ
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup G)) 2
      (by rw [hP8]; norm_num)
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have hbs := BrauerSuzuki.brauer_suzuki 3 le_rfl P ⟨e⟩ t t.2 ht2
    have heven : Even (Nat.card G) := by
      have h := orderOf_dvd_natCard (t : G)
      rw [ht2] at h
      exact even_iff_two_dvd.mpr h
    have hO : CFSG.oddCore G = ⊥ :=
      CFSG.QuasithinUnique.oddCore_eq_bot_of_isSimpleGroup_of_even heven
    have htc : (t : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := Subgroup.mem_center_iff.mp hbs (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hO,
        Subgroup.mem_bot] at h
      have h' := congrArg (fun z => g * (t : G) * z) h
      simp only [mul_one] at h'
      rw [show g * (t : G) * ((g * t)⁻¹ * (t * g)) = t * g by group] at h'
      exact h'.symm
    have hZ : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    rw [hZ, Subgroup.mem_bot] at htc
    rw [htc, orderOf_one] at ht2
    omega

end Simple

end CFSG.ComponentClassification.WalterSchur
