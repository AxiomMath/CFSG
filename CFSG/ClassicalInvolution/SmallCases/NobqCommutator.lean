module

public import CFSG.ClassicalInvolution.SmallCases.NobqTransfer

public section

namespace CFSG.ClassicalInvolution.Nobq

theorem commutator_mem_of_datum {G : Type*} [Group G] {N R : Subgroup G} [N.Normal] {t : G}
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (huniq : ∀ u ∈ R, orderOf u = 2 → u = t)
    (hW : ∀ c ∈ N, c * t = t * c → c * c = t → ∃ g ∈ N, g * t = t * g ∧
      (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧ c * (g * c * g⁻¹) ≠ 1 ∧
        c * (g * c * g⁻¹) ≠ t)
    (hO : ∀ m ∈ N, m * t = t * m → ∃ j : ℕ, orderOf m = 2 ^ j)
    {s : G} (hs : s ∈ R) {u : G} (huN : u ∈ N) (hut : u * t = t * u) :
    s * u * s⁻¹ * u⁻¹ = 1 ∨ s * u * s⁻¹ * u⁻¹ = t := by
  classical
  have hconj : ∀ g : G, g * t = t * g → ∀ x ∈ R, g * x * g⁻¹ ∈ R := by
    intro g hg x hx
    have hgC : g ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hg
    have h1 := hRn.conj_mem ⟨x, hRC hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hgC⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  have hmN : s * u * s⁻¹ * u⁻¹ ∈ N :=
    N.mul_mem (Subgroup.Normal.conj_mem inferInstance u huN s) (N.inv_mem huN)
  have hmR : s * u * s⁻¹ * u⁻¹ ∈ R := by
    have h1 := hconj u hut s⁻¹ (R.inv_mem hs)
    have h2 : s * u * s⁻¹ * u⁻¹ = s * (u * s⁻¹ * u⁻¹) := by simp only [mul_assoc]
    rw [h2]
    exact R.mul_mem hs h1
  have hmt : s * u * s⁻¹ * u⁻¹ * t = t * (s * u * s⁻¹ * u⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.1 (hRC hmR)
  by_contra hne
  push Not at hne
  obtain ⟨hm1, hmt'⟩ := hne
  set m := s * u * s⁻¹ * u⁻¹ with hm
  obtain ⟨j, hj⟩ := hO m hmN hmt
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hm1 hj
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hmt' (huniq m hmR (by rw [hj]; norm_num))
  have hj2 : 2 ≤ j := by omega
  set m' := m ^ (2 ^ (j - 2)) with hm'
  have hm'o : orderOf m' = 4 := by
    rw [hm', orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hj]; exact pow_dvd_pow 2 (by omega)), hj, Nat.pow_div (by omega) (by norm_num)]
    have : j - (j - 2) = 2 := by omega
    norm_num [this]
  have hm'R : m' ∈ R := R.pow_mem hmR _
  have hm'N : m' ∈ N := N.pow_mem hmN _
  have hm't : m' * t = t * m' := by
    have := Commute.pow_left (show Commute m t from hmt) (2 ^ (j - 2))
    exact this
  have hm'sq : m' * m' = t := by
    have h2 : orderOf (m' * m') = 2 := by
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hm'o]; norm_num), hm'o]
    exact huniq _ (R.mul_mem hm'R hm'R) h2
  obtain ⟨g, hgN, hgt, hy2, hy1, hyt⟩ := hW m' hm'N hm't hm'sq
  have hyR : m' * (g * m' * g⁻¹) ∈ R := R.mul_mem hm'R (hconj g hgt m' hm'R)
  have hyo : orderOf (m' * (g * m' * g⁻¹)) = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  exact hyt (huniq _ hyR hyo)

theorem exists_orderOf_eq_four_of_datum {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (S : Sylow 2 R)
    {n : ℕ} [NeZero n] (e : (S : Subgroup R) ≃* QuaternionGroup n) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (ht2 : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ s ∈ R, orderOf s = 4 ∧ s * s = t := by
  let a : (S : Subgroup R) := e.symm (QuaternionGroup.xa 0)
  have ha : orderOf a = 4 := by
    rw [MulEquiv.orderOf_eq e.symm, QuaternionGroup.orderOf_xa]
  let s : G := ((a : R) : G)
  have hsR : s ∈ R := (a : R).2
  have hs4 : orderOf s = 4 := by
    show orderOf (((a : R)) : G) = 4
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact ha
  refine ⟨s, hsR, hs4, ?_⟩
  have h2 : orderOf (s * s) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hs4]; norm_num), hs4]
  have hsq : s * s ∈ R := R.mul_mem hsR hsR
  exact eq_of_orderOf_eq_two_of_datum S e ht ht2 hRC hsq h2

end CFSG.ClassicalInvolution.Nobq
