module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupCentralizer

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open CFSG.Open AschbacherToolkit
open scoped commutatorElement

theorem exists_pow_eq_of_mem_zpowers {P : Type*} [Group P] [Finite P] {a x : P}
    (h : x ∈ Subgroup.zpowers a) : ∃ k : ℕ, a ^ k = x :=
  (Submonoid.mem_powers_iff x a).mp (mem_powers_iff_mem_zpowers.mpr h)

theorem conj_eq_or_of_sq_central {P : Type*} [Group P] {a x : P} {m : ℕ} (hm : 1 ≤ m)
    (ham : orderOf a = 2 ^ m) (ha2 : a ^ 2 ∈ Subgroup.center P)
    (hx : x * a * x⁻¹ ∈ Subgroup.zpowers a) :
    x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a * a ^ 2 ^ (m - 1) := by
  have hw : a⁻¹ * (x * a * x⁻¹) ∈ Subgroup.zpowers a :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hx
  have hu2 : (x * a * x⁻¹) ^ 2 = a ^ 2 := by
    rw [conj_pow, Subgroup.mem_center_iff.mp ha2 x, mul_inv_cancel_right]
  have hcomm : Commute a⁻¹ (x * a * x⁻¹) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    exact ((Commute.refl a).zpow_right k).inv_left
  have hw2 : (a⁻¹ * (x * a * x⁻¹)) ^ 2 = 1 := by
    rw [hcomm.mul_pow, hu2, inv_pow, inv_mul_cancel]
  rcases CyclicCentralizer.eq_of_sq_eq_one_of_mem_zpowers hm ham hw hw2 with h | h
  · exact Or.inl (inv_mul_eq_one.mp h).symm
  · exact Or.inr (by rw [← h, mul_inv_cancel_left])

theorem quotient_dihedral_or_semidihedral {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hinv : ¬ AtMostOneInvolution P) {a : P} (ha : 2 < orderOf a)
    (hcent : Subgroup.centralizer ({a} : Set P) = Subgroup.zpowers a)
    (ha2 : a ^ 2 ∈ Subgroup.center P) (Z₀ : Subgroup P) [Z₀.Normal]
    (hZ₀ : Z₀ = Subgroup.zpowers (a ^ 2)) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ⧸ Z₀ ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ⧸ Z₀ ≃* SemidihedralGroup n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, ham⟩ := CyclicCentralizer.exists_orderOf_eq_two_pow hP a
  have hm : 2 ≤ m := by
    by_contra h
    have h2 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← ham] at h2
    omega
  have hZc : Z₀ ≤ Subgroup.center P := hZ₀ ▸ Subgroup.zpowers_le.mpr ha2
  have hZa : Z₀ ≤ Subgroup.zpowers a :=
    hZ₀ ▸ Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2)
  obtain ⟨c, hc⟩ : ∃ c : P, c = a ^ 2 ^ (m - 1) := ⟨_, rfl⟩
  have hcZ : c ∈ Z₀ := by
    have h : c = (a ^ 2) ^ 2 ^ (m - 2) := by
      rw [hc, ← pow_mul, ← pow_succ']
      congr 2
      omega
    rw [h, hZ₀]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hcz : ∀ g : P, g * c = c * g := Subgroup.mem_center_iff.mp (hZc hcZ)
  have hc1 : c ≠ 1 := by
    intro h
    rw [hc] at h
    have h1 := Nat.le_of_dvd (by positivity) (ham ▸ orderOf_dvd_of_pow_eq_one h)
    have h2 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcsq : c * c = 1 := by
    rw [← sq, hc, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m), ← ham,
      pow_orderOf_eq_one]
  have hact : ∀ x : P, x * a * x⁻¹ ∈ Subgroup.zpowers a →
      x ∈ Subgroup.zpowers a ∨ x * a * x⁻¹ = a * c := by
    intro x hx
    rcases conj_eq_or_of_sq_central (by omega) ham ha2 hx with h | h
    · left
      rw [← hcent]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
    · right
      rw [hc]
      exact h
  obtain ⟨t, ht⟩ : ∃ t : P ⧸ Z₀, t = (a : P ⧸ Z₀) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup P,
      D = (Subgroup.centralizer ({t} : Set (P ⧸ Z₀))).comap (QuotientGroup.mk' Z₀) :=
    ⟨_, rfl⟩
  have hmemD : ∀ x : P, x ∈ D ↔ ⁅x, a⁆ ∈ Z₀ := by
    intro x
    rw [hD, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ht,
      ← QuotientGroup.mk'_apply, ← commutatorElement_eq_one_iff_mul_comm,
      ← map_commutatorElement]
    exact QuotientGroup.eq_one_iff _
  have hDconj : ∀ x ∈ D, x * a * x⁻¹ ∈ Subgroup.zpowers a := by
    intro x hx
    have h := Subgroup.mul_mem _ (hZa ((hmemD x).mp hx)) (Subgroup.mem_zpowers a)
    rwa [commutatorElement_def, inv_mul_cancel_right] at h
  have hD_of : ∀ x : P, x * a * x⁻¹ = a * c → x ∈ D := by
    intro x hx
    rw [hmemD, commutatorElement_def, hx, hcz a, mul_inv_cancel_right]
    exact hcZ
  have haD : Subgroup.zpowers a ≤ D := by
    rw [Subgroup.zpowers_le, hmemD, commutatorElement_self]
    exact Subgroup.one_mem _
  have hZD : Z₀ ≤ D := hZa.trans haD
  have hout : ∀ x ∈ D, x ∉ Subgroup.zpowers a → x * a * x⁻¹ = a * c :=
    fun x hx hxa => (hact x (hDconj x hx)).resolve_left hxa
  have hatop : Subgroup.zpowers a ≠ ⊤ := by
    intro h
    have : IsCyclic P := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, h⟩
    exact hinv atMostOneInvolution_of_isCyclic
  have : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨x₀, hx₀N, hx₀a⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hatop))
  have hx₀c : x₀ * a * x₀⁻¹ = a * c :=
    (hact x₀ ((Subgroup.mem_normalizer_iff.mp hx₀N a).mp (Subgroup.mem_zpowers a))).resolve_left
      hx₀a
  have hx₀D : x₀ ∈ D := hD_of x₀ hx₀c
  have hindex : ((Subgroup.zpowers a).subgroupOf D).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨x₀, hx₀D⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hx₀a
    · rintro ⟨b, hb⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      by_cases hba : b ∈ Subgroup.zpowers a
      · exact Or.inr hba
      · left
        have h1 := hout b hb hba
        rw [← hcent, Subgroup.mem_centralizer_singleton_iff]
        show b * x₀ * a = a * (b * x₀)
        calc b * x₀ * a = b * (x₀ * a * x₀⁻¹) * x₀ := by group
          _ = b * (a * c) * x₀ := by rw [hx₀c]
          _ = (b * a * b⁻¹) * (b * c) * x₀ := by group
          _ = (a * c) * (c * b) * x₀ := by rw [h1, hcz b]
          _ = a * (c * c) * b * x₀ := by group
          _ = a * (b * x₀) := by rw [hcsq]; group
  have hcardD : Nat.card D = 2 * 2 ^ m := by
    have h := Subgroup.card_mul_index ((Subgroup.zpowers a).subgroupOf D)
    rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe haD).toEquiv, Nat.card_zpowers,
      ham] at h
    omega
  have hcardZ : Nat.card Z₀ = 2 ^ (m - 1) := by
    rw [hZ₀, Nat.card_zpowers, orderOf_pow' a two_ne_zero, ham,
      Nat.gcd_eq_right (dvd_pow_self 2 (by omega : m ≠ 0))]
    have h : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [h, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have hDmap : D.map (QuotientGroup.mk' Z₀) = Subgroup.centralizer ({t} : Set (P ⧸ Z₀)) := by
    rw [hD]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z₀) _
  have hcardC : Nat.card (Subgroup.centralizer ({t} : Set (P ⧸ Z₀))) = 4 := by
    have h := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' Z₀).domRestrict D)
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', MonoidHom.domRestrict_range, hDmap,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, hcardZ, hcardD] at h
    have h2 : 2 * 2 ^ m = 2 ^ (m - 1) * 4 := by
      have : 2 ^ m = 2 ^ (m - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      rw [this]
      ring
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hexp : ∀ w ∈ Subgroup.centralizer ({t} : Set (P ⧸ Z₀)), w ^ 2 = 1 := by
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z₀ w
    have hxD : x ∈ D := by
      rw [hD]
      exact hw
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    by_cases hxa : x ∈ Subgroup.zpowers a
    · obtain ⟨k, rfl⟩ := exists_pow_eq_of_mem_zpowers hxa
      rw [hZ₀, ← pow_mul, mul_comm, pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · have h1 := hout x hxD hxa
      have hx2 : x ^ 2 ∈ Subgroup.zpowers a := by
        rw [← hcent, Subgroup.mem_centralizer_singleton_iff, sq]
        calc x * x * a = x * (x * a * x⁻¹) * x⁻¹ * (x * x) := by group
          _ = x * (a * c) * x⁻¹ * (x * x) := by rw [h1]
          _ = (x * a * x⁻¹) * (x * c * x⁻¹) * (x * x) := by group
          _ = a * c * c * (x * x) := by rw [h1, hcz x, mul_inv_cancel_right]
          _ = a * (x * x) := by rw [mul_assoc a c c, hcsq, mul_one]
      obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers hx2
      have hck : c ^ k = 1 := by
        have h2 : a ^ k * c ^ k = a ^ k := by
          calc a ^ k * c ^ k = (a * c) ^ k := (Commute.mul_pow (hcz a) k).symm
            _ = (x * a * x⁻¹) ^ k := by rw [h1]
            _ = x * a ^ k * x⁻¹ := conj_pow
            _ = x * x ^ 2 * x⁻¹ := by rw [hk]
            _ = x ^ 2 := by rw [(Commute.self_pow x 2).eq, mul_inv_cancel_right]
            _ = a ^ k := hk.symm
        exact mul_eq_left.mp h2
      have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hcsq) hc1
      obtain ⟨i, rfl⟩ : 2 ∣ k := hc2 ▸ orderOf_dvd_of_pow_eq_one hck
      rw [← hk, pow_mul, hZ₀]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact suzuki_two_group (hP.to_quotient Z₀) hcardC hexp

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
