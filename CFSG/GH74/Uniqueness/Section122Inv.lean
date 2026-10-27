module

public import CFSG.GH74.Uniqueness.Lemma31gh

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem card_closure_pair_eq_two_mul_orderOf {u z : X} (hu : u * u = 1) (hz : z * z = 1)
    (hu1 : u ≠ 1) (hz1 : z ≠ 1) :
    Nat.card ↥(closure ({u, z} : Set X)) = 2 * orderOf (u * z) := by
  set D := closure ({u, z} : Set X) with hD
  have huD : u ∈ D := subset_closure (Set.mem_insert u _)
  have hzD : z ∈ D := subset_closure (Set.mem_insert_of_mem u rfl)
  have hrD : u * z ∈ D := mul_mem huD hzD
  have hnot : u ∉ zpowers (u * z) := by
    intro hmem
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
    have hc : Commute (u * z) ((u * z) ^ i) := (Commute.refl (u * z)).zpow_right i
    rw [hi] at hc
    have h1 : u * z * u = u * (u * z) := hc.eq
    rw [← mul_assoc u u z, hu, one_mul] at h1
    have huz' : u * z = z * u := by
      calc u * z = u * z * u * u := by rw [mul_assoc (u * z) u u, hu, mul_one]
        _ = z * u := by rw [h1]
    have hsq' : (u * z) ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      calc u * z * (u * z) = u * (z * u) * z := by group
        _ = u * (u * z) * z := by rw [huz']
        _ = (u * u) * (z * z) := by group
        _ = 1 := by rw [hu, hz, one_mul]
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
    · rw [hk, zpow_mul, hsq', one_zpow] at hi
      exact hu1 hi.symm
    · rw [hk, zpow_add_one, zpow_mul, hsq', one_zpow, one_mul] at hi
      exact hz1 (by simpa using hi)
  have hDA : D = zpowers (u * z) ⊔ zpowers u := by
    apply le_antisymm
    · refine (closure_le _).mpr ?_
      intro x hx
      have hu_mem : u ∈ zpowers (u * z) ⊔ zpowers u := mem_sup_right (mem_zpowers _)
      have hr_mem : u * z ∈ zpowers (u * z) ⊔ zpowers u := mem_sup_left (mem_zpowers _)
      rcases hx with hx | hx
      · rw [hx]
        exact hu_mem
      · rw [Set.mem_singleton_iff.mp hx]
        have h1 := mul_mem hu_mem hr_mem
        rwa [← mul_assoc, hu, one_mul] at h1
    · exact sup_le (zpowers_le.mpr hrD) (zpowers_le.mpr huD)
  have hgen : (⊤ : Subgroup D) = zpowers (⟨u * z, hrD⟩ : D) ⊔ zpowers (⟨u, huD⟩ : D) := by
    apply map_injective D.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    exact hDA
  have hσ2 : (⟨u, huD⟩ : D) ^ 2 = 1 := Subtype.ext (by simp [pow_two, hu])
  have hrel : (⟨u, huD⟩ : D) * ⟨u * z, hrD⟩ * (⟨u, huD⟩ : D)⁻¹ = (⟨u * z, hrD⟩ : D)⁻¹ := by
    apply Subtype.ext
    show u * (u * z) * u⁻¹ = (u * z)⁻¹
    rw [mul_inv_eq_iff_eq_mul]
    exact (semiconj_mul_of_sq hu hz).eq
  have hσρ : (⟨u, huD⟩ : D) ∉ zpowers (⟨u * z, hrD⟩ : D) := by
    intro hmem
    apply hnot
    have h1 := mem_map_of_mem D.subtype hmem
    rwa [MonoidHom.map_zpowers] at h1
  obtain ⟨eD⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem _ _ hgen hσ2 hrel hσρ
  rw [Subgroup.orderOf_mk] at eD
  rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]

theorem IsProductDisconnected.productInvolutions_eq (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M)
    (hcomm : ∀ x ∈ zHull Z M, ∀ y ∈ zHull Z M, x * y = y * x)
    (hzM : Z ∩ (M : Set X) = (zHull Z M : Set X) \ {1})
    (hcard : 4 ≤ Nat.card ↥(zHull Z M)) :
    productInvolutions Z = Z := by
  have hconj : ∀ w ∈ Z, ∀ g : X, g * w * g⁻¹ ∈ Z := fun w hw g => by
    have := hZ.2 w hw g⁻¹
    rwa [inv_inv] at this
  have hsub : ∀ w ∈ Z, w ∈ M → w ∈ zHull Z M := fun w hw hwM => subset_closure ⟨hw, hwM⟩
  have hZM_of : ∀ a ∈ zHull Z M, a ≠ 1 → a ∈ Z := fun a ha ha1 => by
    have : a ∈ Z ∩ (M : Set X) := by
      rw [hzM]
      exact ⟨ha, ha1⟩
    exact this.1
  apply Set.Subset.antisymm
  ·
    rintro u ⟨hu2, x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, hg⟩ := h.exists_conj_mem_subgroup hZ hx
    have hx' : g⁻¹ * x * g ∈ Z := hZ.2 x hx g
    have hy' : g⁻¹ * y * g ∈ Z := hZ.2 y hy g
    have hxy' : g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * x * g * (g⁻¹ * y * g) := by
      calc g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
        _ = g⁻¹ * (x * y) * g := by rw [hxy]
        _ = g⁻¹ * x * g * (g⁻¹ * y * g) := by group
    have hy'M : g⁻¹ * y * g ∈ M :=
      h.centralizer_le_of_mem hx' hg (Subgroup.mem_centralizer_singleton_iff.mpr hxy')
    have hu' : g⁻¹ * x * g * (g⁻¹ * y * g) ∈ zHull Z M :=
      mul_mem (hsub _ hx' hg) (hsub _ hy' hy'M)
    have hne : g⁻¹ * x * g * (g⁻¹ * y * g) ≠ 1 := by
      intro h1
      have h2 : x * y = 1 := by
        calc x * y = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [h1]
          _ = 1 := by group
      rw [h2, orderOf_one] at hu2
      omega
    have hmem := hconj _ (hZM_of _ hu' hne) g
    have heq : g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ = x * y := by group
    rwa [heq] at hmem
  ·
    intro y hy
    refine ⟨hZ.1 y hy, ?_⟩
    obtain ⟨g, hg⟩ := h.exists_conj_mem_subgroup hZ hy
    have hy' : g⁻¹ * y * g ∈ Z := hZ.2 y hy g
    have hy'H : g⁻¹ * y * g ∈ zHull Z M := hsub _ hy' hg
    have hy'2 : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 := hZ.mul_self_eq_one hy'
    obtain ⟨a, haH, ha1, hay⟩ : ∃ a ∈ zHull Z M, a ≠ 1 ∧ a ≠ g⁻¹ * y * g := by
      by_contra hno
      have hsubset : ((zHull Z M : Subgroup X) : Set X) ⊆ {1, g⁻¹ * y * g} := by
        intro a ha
        by_cases ha1 : a = 1
        · exact Or.inl ha1
        · by_cases hay : a = g⁻¹ * y * g
          · exact Or.inr hay
          · exact absurd ⟨a, ha, ha1, hay⟩ hno
      have h1 := Set.ncard_le_ncard hsubset (Set.toFinite _)
      have h2 := Set.ncard_insert_le (1 : X) {g⁻¹ * y * g}
      rw [Set.ncard_singleton] at h2
      have h3 : Nat.card ↥(zHull Z M) = ((zHull Z M : Subgroup X) : Set X).ncard :=
        Nat.card_coe_set_eq _
      omega
    have haZ : a ∈ Z := hZM_of a haH ha1
    have hbH : a * (g⁻¹ * y * g) ∈ zHull Z M := mul_mem haH hy'H
    have hb1 : a * (g⁻¹ * y * g) ≠ 1 := by
      intro h1
      apply hay
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_eq_of_mul_eq_one_right hy'2
    have hbZ : a * (g⁻¹ * y * g) ∈ Z := hZM_of _ hbH hb1
    have haa : a * a = 1 := hZ.mul_self_eq_one haZ
    have hab : a * (a * (g⁻¹ * y * g)) = a * (g⁻¹ * y * g) * a := hcomm a haH _ hbH
    refine ⟨g * a * g⁻¹, hconj a haZ g, g * (a * (g⁻¹ * y * g)) * g⁻¹, hconj _ hbZ g, ?_, ?_⟩
    · calc g * a * g⁻¹ * (g * (a * (g⁻¹ * y * g)) * g⁻¹)
          = g * (a * (a * (g⁻¹ * y * g))) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * y * g) * a) * g⁻¹ := by rw [hab]
        _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ * (g * a * g⁻¹) := by group
    · calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = g * (a * (a * (g⁻¹ * y * g))) * g⁻¹ := by rw [← mul_assoc a a, haa, one_mul]
        _ = g * a * g⁻¹ * (g * (a * (g⁻¹ * y * g)) * g⁻¹) := by group

theorem IsProductDisconnected.lemma122e (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hV : productInvolutions Z = Z)
    (hab : Open.IsElemAbelian 2 (zHull Z M)) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    ∀ u : X, orderOf u = 2 → u ∉ Z →
      (Nat.card ↥(closure ({u, z} : Set X)) = 8 ∨
        ∃ k : ℕ, Odd k ∧ Nat.card ↥(closure ({u, z} : Set X)) = 4 * k) ∧
      ∀ w ∈ zpowers (u * z), orderOf w = 2 → Nat.card ↥(closure ({u, z} : Set X)) = 8 →
        closure ({w, z} : Set X) ≤ zHull Z M ∧ u ∈ M ∧ u ∉ centralizer (zHull Z M : Set X) := by
  intro u hu2 huZ
  have hu1 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  have hz1 : z * z = 1 := hZ.mul_self_eq_one hz
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
  have hu_ne : u ≠ 1 := fun h1 => by simp [h1] at hu2
  have hz_ne : z ≠ 1 := fun h1 => by
    have := hZ.1 z hz
    simp [h1] at this
  have hcard : Nat.card ↥(closure ({u, z} : Set X)) = 2 * orderOf (u * z) :=
    card_closure_pair_eq_two_mul_orderOf hu1 hz1 hu_ne hz_ne
  have hzH : z ∈ zHull Z M := subset_closure ⟨hz, hzM⟩
  have heven : Even (orderOf (u * z)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨x, -, hx⟩ := exists_mem_closure_conj_of_odd hu1 hz1 hodd
    have hxZ := hZ.2 z hz x
    rw [hx] at hxZ
    exact huZ hxZ
  obtain ⟨m, hm⟩ := heven
  have hord : orderOf (u * z) = 2 * m := by omega
  have hmpos : 0 < m := by
    have := orderOf_pos (u * z)
    omega
  have hzr : ∀ n : ℕ, z * (u * z) ^ n = ((u * z) ^ n)⁻¹ * z := fun n => by
    have := (semiconj_mul_of_sq' hu1 hz1).pow_right n
    rw [SemiconjBy, inv_pow] at this
    exact this
  have claimA : Even m → m = 2 ∧ u ∈ M ∧ (u * z) ^ 2 ∈ zHull Z M := by
    rintro ⟨j, hj⟩
    obtain ⟨hw₀sq, hw₀1, huw₀, hzw₀, -⟩ := dihedral_even hu1 hz1 hmpos hord
    have hvinv : ((u * z) ^ m)⁻¹ = (u * z) ^ m := inv_eq_of_mul_eq_one_right hw₀sq
    have hconj1 : ((u * z) ^ j)⁻¹ * z * (u * z) ^ j = (u * z) ^ m * z := by
      calc ((u * z) ^ j)⁻¹ * z * (u * z) ^ j
          = ((u * z) ^ j)⁻¹ * (z * (u * z) ^ j) := by rw [mul_assoc]
        _ = ((u * z) ^ j)⁻¹ * (((u * z) ^ j)⁻¹ * z) := by rw [hzr j]
        _ = ((u * z) ^ (j + j))⁻¹ * z := by rw [← mul_assoc, ← mul_inv_rev, ← pow_add]
        _ = ((u * z) ^ m)⁻¹ * z := by rw [hj]
        _ = (u * z) ^ m * z := by rw [hvinv]
    have hz2 : (u * z) ^ m * z ∈ Z := by
      have := hZ.2 z hz ((u * z) ^ j)
      rwa [hconj1] at this
    have hw₀P : (u * z) ^ m ∈ productInvolutions Z := by
      refine ⟨?_, z, hz, (u * z) ^ m * z, hz2, ?_, ?_⟩
      · exact orderOf_eq_prime (by rw [pow_two]; exact hw₀sq) hw₀1
      · calc z * ((u * z) ^ m * z) = (z * (u * z) ^ m) * z := (mul_assoc _ _ _).symm
          _ = ((u * z) ^ m * z) * z := by rw [hzw₀]
      · calc (u * z) ^ m = (u * z) ^ m * (z * z) := by rw [hz1, mul_one]
          _ = ((u * z) ^ m * z) * z := (mul_assoc _ _ _).symm
          _ = (z * (u * z) ^ m) * z := by rw [hzw₀]
          _ = z * ((u * z) ^ m * z) := mul_assoc _ _ _
    have hw₀Z : (u * z) ^ m ∈ Z := hV.subset hw₀P
    have hw₀M : (u * z) ^ m ∈ M :=
      h.centralizer_le_of_mem hz hzM (Subgroup.mem_centralizer_singleton_iff.mpr hzw₀.symm)
    have huM : u ∈ M :=
      h.centralizer_le_of_mem hw₀Z hw₀M (Subgroup.mem_centralizer_singleton_iff.mpr huw₀)
    have hconj2 : u * z * u ∈ zHull Z M := by
      have h1 : u * z * u ∈ Z := by
        have := hZ.2 z hz u
        rwa [hu'] at this
      exact subset_closure ⟨h1, M.mul_mem (M.mul_mem huM hzM) huM⟩
    have hr2 : (u * z) ^ 2 ∈ zHull Z M := by
      have : (u * z) ^ 2 = u * z * u * z := by
        rw [pow_two]
        group
      rw [this]
      exact mul_mem hconj2 hzH
    have hr4 : (u * z) ^ 4 = 1 := by
      have h1 := hab.2 _ hr2
      rw [← pow_mul] at h1
      exact h1
    have hdvd : 2 * m ∣ 4 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hr4
    have hle : 2 * m ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    exact ⟨by omega, huM, hr2⟩
  refine ⟨?_, ?_⟩
  · rcases Nat.even_or_odd m with hme | hmo
    · left
      obtain ⟨hm2, -, -⟩ := claimA hme
      omega
    · right
      exact ⟨m, hmo, by omega⟩
  · intro w hw hw2 hc8
    have hm2 : m = 2 := by omega
    obtain ⟨-, huM, hr2⟩ := claimA ⟨1, by omega⟩
    have hord4 : orderOf (u * z) = 4 := by omega
    refine ⟨?_, huM, ?_⟩
    · have hwH : w ∈ zHull Z M := by
        obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hw)
        have hw2' : (u * z) ^ k * (u * z) ^ k = 1 := by
          have := pow_orderOf_eq_one ((u * z) ^ k)
          rwa [hw2, pow_two] at this
        have hk : (u * z) ^ (k + k) = 1 := by
          rw [pow_add]
          exact hw2'
        have hdvd := orderOf_dvd_of_pow_eq_one hk
        rw [hord4] at hdvd
        obtain ⟨l, hl⟩ : ∃ l, k = 2 * l := ⟨k / 2, by omega⟩
        rw [hl, pow_mul]
        exact Subgroup.pow_mem _ hr2 l
      refine (closure_le _).mpr ?_
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        exact hwH
      · rw [Set.mem_singleton_iff.mp hx]
        exact hzH
    · intro hcen
      have hcomm : z * u = u * z := Subgroup.mem_centralizer_iff.mp hcen z hzH
      have hsq : u * z * (u * z) = 1 := by
        calc u * z * (u * z) = u * (z * u) * z := by group
          _ = u * (u * z) * z := by rw [hcomm]
          _ = (u * u) * (z * z) := by group
          _ = 1 := by rw [hu1, hz1, one_mul]
      have hdvd := orderOf_dvd_of_pow_eq_one (show (u * z) ^ 2 = 1 by rw [pow_two]; exact hsq)
      rw [hord4] at hdvd
      omega

end CFSG.GH74.Uniqueness
