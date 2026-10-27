module

public import CFSG.GH74.GLS.C3.Layer1.P34Cfg
public import CFSG.GH74.Uniqueness.SU.SU1MaxClassShape

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup

namespace QShape

variable {G : Type} [Group G]

theorem cyclic_involution_unique {H : Type*} [Group H] [Finite H] [IsCyclic H] {u v : H}
    (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  classical
  have := Fintype.ofFinite H
  by_contra hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  have hsub : ({1, u, v} : Finset H) ⊆ Finset.univ.filter (fun a : H => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact hu
    · rw [pow_two]; exact hv
  have h3 : ({1, u, v} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp [Ne.symm hu1, Ne.symm hv1]
  have := Finset.card_le_card hsub
  omega

structure MaxData (G : Type) [Group G] (a x : G) : Prop where
  index_two : (zpowers a).index = 2
  order_ge : 4 ≤ orderOf a
  x_sq : x * x = 1
  x_ne : x ≠ 1
  x_central : ∀ y, x * y = y * x
  center_eq : ∀ z : G, (∀ y, z * y = y * z) → z = 1 ∨ z = x

namespace MaxData

variable {a x : G}

theorem normal (S : MaxData G a x) : (zpowers a).Normal :=
  Subgroup.normal_of_index_eq_two S.index_two

theorem sq_ne_one (S : MaxData G a x) : a * a ≠ 1 := by
  intro h
  have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h2 := Nat.le_of_dvd (by norm_num) h1
  have h3 := S.order_ge
  omega

theorem central_of_centralizes (S : MaxData G a x) {g m : G} (hg : g ∉ zpowers a)
    (hm : m ∈ zpowers a) (hgm : m * g = g * m) (h : G) : m * h = h * m := by
  by_cases hh : h ∈ zpowers a
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_zpow_self a i j).eq
  · have hgh : g⁻¹ * h ∈ zpowers a := by
      rw [Subgroup.mul_mem_iff_of_index_two S.index_two, inv_mem_iff]
      exact iff_of_false hg hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgh
    have hh' : h = g * a ^ j := by rw [hj]; group
    have hcomm : a ^ i * a ^ j = a ^ j * a ^ i := (Commute.zpow_zpow_self a i j).eq
    rw [hh']
    calc a ^ i * (g * a ^ j) = (a ^ i * g) * a ^ j := by rw [mul_assoc]
      _ = (g * a ^ i) * a ^ j := by rw [hgm]
      _ = g * (a ^ i * a ^ j) := by rw [mul_assoc]
      _ = g * (a ^ j * a ^ i) := by rw [hcomm]
      _ = (g * a ^ j) * a ^ i := by rw [mul_assoc]

theorem invol_central [Finite G] (S : MaxData G a x) {v : G} (hv : v ∈ zpowers a)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (g : G) : v * g = g * v := by
  have hn := S.normal
  have hconj : g * v * g⁻¹ ∈ zpowers a := hn.conj_mem v hv g
  have key : (⟨g * v * g⁻¹, hconj⟩ : zpowers a) = ⟨v, hv⟩ := by
    apply cyclic_involution_unique (H := zpowers a)
    · apply Subtype.ext
      show g * v * g⁻¹ * (g * v * g⁻¹) = 1
      calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv2]; group
    · apply Subtype.ext
      exact hv2
    · intro h
      apply hv1
      have := congrArg Subtype.val h
      have h' : g * v * g⁻¹ = 1 := this
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    · intro h
      apply hv1
      exact congrArg Subtype.val h
  have h' : g * v * g⁻¹ = v := congrArg Subtype.val key
  calc v * g = (g * v * g⁻¹) * g := by rw [h']
    _ = g * v := by group

theorem not_mem_of_noncentral [Finite G] (S : MaxData G a x) {u : G} (hu2 : u * u = 1)
    (hnc : ∃ y, u * y ≠ y * u) : u ∉ zpowers a := by
  intro h
  obtain ⟨y, hy⟩ := hnc
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hy (by simp)
  exact hy (S.invol_central h hu2 hu1 y)

theorem false_of_noncentral [Finite G] (S : MaxData G a x) {u : G} (hu2 : u * u = 1)
    (hnc : ∃ y, u * y ≠ y * u) (H : ∀ q : G, q * q = 1 → q * u = u * q) : False := by
  have hx2 := S.x_sq
  have hxc := S.x_central
  have huM : u ∉ zpowers a := S.not_mem_of_noncentral hu2 hnc
  have ha_mem : a ∈ zpowers a := Subgroup.mem_zpowers a
  have hn := S.normal
  obtain ⟨v, hv⟩ : ∃ v : G, v = a⁻¹ * u * a := ⟨_, rfl⟩
  have hv2 : v * v = 1 := by
    calc v * v = a⁻¹ * (u * u) * a := by rw [hv]; group
      _ = 1 := by rw [hu2]; group
  have hvu : v * u = u * v := H v hv2
  have hvM : v ∉ zpowers a := by
    intro h
    apply huM
    have h1 : a * v * a⁻¹ ∈ zpowers a := hn.conj_mem v h a
    have e : a * v * a⁻¹ = u := by rw [hv]; group
    rwa [e] at h1
  have hcM : u * v ∈ zpowers a := by
    rw [Subgroup.mul_mem_iff_of_index_two S.index_two]
    exact iff_of_false huM hvM
  have hcu : (u * v) * u = u * (u * v) := by
    calc (u * v) * u = u * (v * u) := by rw [mul_assoc]
      _ = u * (u * v) := by rw [hvu]
  have hcc := S.central_of_centralizes huM hcM hcu
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rcases S.center_eq _ hcc with hc | hc
  · exfalso
    have hvu' : v = u := by
      have : v = u⁻¹ := eq_inv_of_mul_eq_one_right hc
      rw [this, hu_inv]
    have hua : a * u = u * a := by
      have h1 : a⁻¹ * u * a = u := by rw [← hv]; exact hvu'
      calc a * u = a * (a⁻¹ * u * a) := by rw [h1]
        _ = u * a := by group
    have hac := S.central_of_centralizes huM ha_mem hua
    rcases S.center_eq a hac with h | h
    · exact S.sq_ne_one (by rw [h, mul_one])
    · exact S.sq_ne_one (by rw [h, hx2])
  · have hv' : v = u * x := by
      calc v = u * (u * v) := by rw [← mul_assoc, hu2, one_mul]
        _ = u * x := by rw [hc]
    have h6 : u * a = a * (u * x) := by
      calc u * a = a * (a⁻¹ * u * a) := by group
        _ = a * (u * x) := by rw [← hv, hv']
    have h7 : a * u = u * a * x := by
      calc a * u = a * (u * x) * x := by rw [mul_assoc, mul_assoc, hx2, mul_one]
        _ = (u * a) * x := by rw [← h6]
    have hxa : x * a = a * x := hxc a
    have h8 : u * (a * a) = (a * a) * u := by
      calc u * (a * a) = (u * a) * a := by rw [mul_assoc]
        _ = (a * (u * x)) * a := by rw [h6]
        _ = a * u * (x * a) := by simp only [mul_assoc]
        _ = a * u * (a * x) := by rw [hxa]
        _ = a * (u * a) * x := by simp only [mul_assoc]
        _ = a * (a * (u * x)) * x := by rw [h6]
        _ = a * a * u * (x * x) := by simp only [mul_assoc]
        _ = a * a * u := by rw [hx2, mul_one]
    have hAM : a * a ∈ zpowers a := Subgroup.mul_mem _ ha_mem ha_mem
    have haac := S.central_of_centralizes huM hAM h8.symm
    have haax : a * a = x := by
      rcases S.center_eq _ haac with h | h
      · exact absurd h S.sq_ne_one
      · exact h
    have hq2 : (u * a) * (u * a) = 1 := by
      calc (u * a) * (u * a) = u * (a * u) * a := by simp only [mul_assoc]
        _ = u * (u * a * x) * a := by rw [h7]
        _ = (u * u) * a * (x * a) := by simp only [mul_assoc]
        _ = a * (a * x) := by rw [hu2, one_mul, hxa]
        _ = (a * a) * x := by rw [mul_assoc]
        _ = 1 := by rw [haax, hx2]
    have hqu := H (u * a) hq2
    apply S.x_ne
    have e1 : (u * a) * u = a * x := by
      calc (u * a) * u = u * (a * u) := by rw [mul_assoc]
        _ = u * (u * a * x) := by rw [h7]
        _ = (u * u) * a * x := by simp only [mul_assoc]
        _ = a * x := by rw [hu2, one_mul]
    have e2 : u * (u * a) = a := by rw [← mul_assoc, hu2, one_mul]
    rw [e1, e2] at hqu
    exact mul_eq_left.mp hqu

theorem x_mem_of_commuting [Finite G] (S : MaxData G a x) {b₁ b₂ : G} (h1 : b₁ * b₁ = 1)
    (h2 : b₂ * b₂ = 1) (h1' : b₁ ≠ 1) (h2' : b₂ ≠ 1) (hne : b₁ ≠ b₂) (hc : b₁ * b₂ = b₂ * b₁) :
    x = b₁ ∨ x = b₂ ∨ x = b₁ * b₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hx2, hx3⟩ := hcon
  have hnotM : ∀ b : G, b * b = 1 → b ≠ 1 → b ≠ x → b ∉ zpowers a := by
    intro b hb2 hb1 hbx hbM
    rcases S.center_eq b (S.invol_central hbM hb2 hb1) with h | h
    · exact hb1 h
    · exact hbx h
  have hb1M := hnotM b₁ h1 h1' (Ne.symm hx1)
  have hb2M := hnotM b₂ h2 h2' (Ne.symm hx2)
  have hprodM : b₁ * b₂ ∈ zpowers a := by
    rw [Subgroup.mul_mem_iff_of_index_two S.index_two]
    exact iff_of_false hb1M hb2M
  have hprod2 : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    calc (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by simp only [mul_assoc]
      _ = b₁ * (b₁ * b₂) * b₂ := by rw [hc]
      _ = (b₁ * b₁) * (b₂ * b₂) := by simp only [mul_assoc]
      _ = 1 := by rw [h1, h2, one_mul]
  have hprod1 : b₁ * b₂ ≠ 1 := by
    intro h
    apply hne
    have : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right h1]
  rcases S.center_eq _ (S.invol_central hprodM hprod2 hprod1) with h | h
  · exact hprod1 h
  · exact hx3 h.symm

theorem inv_lemma [Finite G] (S : MaxData G a x) (h4 : orderOf a = 4) {g : G} (hg : g ∉ zpowers a) :
    g * a * g⁻¹ = a⁻¹ := by
  have hn := S.normal
  have hmem : g * a * g⁻¹ ∈ zpowers a := hn.conj_mem a (Subgroup.mem_zpowers a) g
  obtain ⟨r, hr⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_pow_eq_of_mem_zpowers hmem
  have ha4 : a ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one a
  have hr' : g * a * g⁻¹ = a ^ (r % 4) := by
    rw [← hr, ← h4, pow_mod_orderOf]
  have hlt : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize r % 4 = s at hr' hlt
  interval_cases s
  · exfalso
    have h1 : g * a * g⁻¹ = 1 := by rw [hr', pow_zero]
    have : a = 1 := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at h4
    exact absurd h4 (by norm_num)
  · exfalso
    have h1 : a * g = g * a := by
      calc a * g = (g * a * g⁻¹) * g := by rw [hr', pow_one]
        _ = g * a := by group
    have hac := S.central_of_centralizes hg (Subgroup.mem_zpowers a) h1
    rcases S.center_eq a hac with h | h
    · exact S.sq_ne_one (by rw [h, mul_one])
    · exact S.sq_ne_one (by rw [h, S.x_sq])
  · exfalso
    have hAM : a * a ∈ zpowers a :=
      Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    have hAA : (a * a) * (a * a) = 1 := by
      calc (a * a) * (a * a) = a ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := ha4
    have hcen := S.invol_central hAM hAA S.sq_ne_one
    have h1 : g * a * g⁻¹ = a * a := by rw [hr', pow_two]
    have h2 : a = a * a := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * (a * a) * g := by rw [h1]
        _ = g⁻¹ * (g * (a * a)) := by rw [← hcen g]; group
        _ = a * a := by group
    exact S.sq_ne_one (by
      have : a = 1 := mul_eq_left.mp h2.symm
      rw [this, mul_one])
  · rw [hr']
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact ha4

theorem inv_of_mem [Finite G] (S : MaxData G a x) (h4 : orderOf a = 4) {g : G} (hg : g ∉ zpowers a)
    {m : G} (hm : m ∈ zpowers a) : g * m * g⁻¹ = m⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  rw [← conj_zpow, S.inv_lemma h4 hg, inv_zpow]

theorem phi_mem [Finite G] (S : MaxData G a x) {u : G} (hu2 : u * u = 1)
    (hnc : ∃ y, u * y ≠ y * u) (φ : G →* G) (hφ : Function.Injective φ) : φ a ∈ zpowers a := by
  by_contra hφa
  have huM : u ∉ zpowers a := S.not_mem_of_noncentral hu2 hnc
  have hbb : φ a * φ a ∈ zpowers a := Subgroup.mul_self_mem_of_index_two S.index_two (φ a)
  have hcen := S.central_of_centralizes hφa hbb (by rw [mul_assoc])
  have hb4 : φ a ^ 4 = 1 := by
    have e : φ a ^ 4 = (φ a * φ a) * (φ a * φ a) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rcases S.center_eq _ hcen with h | h
    · rw [e, h, mul_one]
    · rw [e, h, S.x_sq]
  have hord : orderOf (φ a) = orderOf a := orderOf_injective φ hφ a
  have h4 : orderOf a = 4 := by
    have h1 : orderOf a ∣ 4 := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hb4
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := S.order_ge
    omega
  have hmM : u * φ a ∈ zpowers a := by
    rw [Subgroup.mul_mem_iff_of_index_two S.index_two]
    exact iff_of_false huM hφa
  have hinv := S.inv_of_mem h4 huM hmM
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rw [hu_inv] at hinv
  have hbb1 : φ a * φ a = 1 := by
    have e1 : u * (u * φ a) * u = φ a * u := by
      calc u * (u * φ a) * u = (u * u) * φ a * u := by simp only [mul_assoc]
        _ = φ a * u := by rw [hu2, one_mul]
    have e2 : (u * φ a)⁻¹ = (φ a)⁻¹ * u := by rw [mul_inv_rev, hu_inv]
    rw [e1, e2] at hinv
    have h5 := mul_right_cancel hinv
    calc φ a * φ a = (φ a)⁻¹ * φ a := by rw [← h5]
      _ = 1 := inv_mul_cancel _
  have h6 : orderOf (φ a) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h7 := Nat.le_of_dvd (by norm_num) h6
  rw [hord] at h7
  have := S.order_ge
  omega

theorem central_of_centralizes_M [Finite G] (S : MaxData G a x) {q : G} (hq2 : q * q = 1)
    (hqc : ∀ c ∈ zpowers a, q * c = c * q) (y : G) : q * y = y * q := by
  by_cases hq1 : q = 1
  · rw [hq1]; simp
  by_cases hqM : q ∈ zpowers a
  · exact S.invol_central hqM hq2 hq1 y
  · by_cases hy : y ∈ zpowers a
    · exact hqc y hy
    · have hm : q⁻¹ * y ∈ zpowers a := by
        rw [Subgroup.mul_mem_iff_of_index_two S.index_two, inv_mem_iff]
        exact iff_of_false hqM hy
      have h1 := hqc _ hm
      have h2 : y = q⁻¹ * y * q := by rw [← h1]; group
      calc q * y = q * (q⁻¹ * y * q) := by rw [← h2]
        _ = y * q := by group

end MaxData

theorem exists_cyclic_of_all_central (x : G)
    (hall : ∀ q : G, q * q = 1 → ∀ y : G, q * y = y * q) :
    ∃ M₀ : Subgroup G, IsCyclic M₀ ∧
      (∀ φ : G →* G, Function.Injective φ → φ x = x → ∀ c ∈ M₀, φ c ∈ M₀) ∧
      ∀ q : G, q * q = 1 → (∀ c ∈ M₀, q * c = c * q) → ∀ y : G, q * y = y * q := by
  refine ⟨zpowers x, inferInstance, ?_, fun q hq2 _ y => hall q hq2 y⟩
  intro φ _ hφx c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [map_zpow, hφx]
  exact Subgroup.zpow_mem_zpowers x k

theorem x_mem_of_card_four [Finite G] {x : G} (hx1 : x ≠ 1) (h4 : Nat.card G = 4) {b₁ b₂ : G}
    (h1 : b₁ * b₁ = 1) (h1' : b₁ ≠ 1) (h2' : b₂ ≠ 1) (hne : b₁ ≠ b₂) :
    x = b₁ ∨ x = b₂ ∨ x = b₁ * b₂ := by
  classical
  have := Fintype.ofFinite G
  have hb12 : b₁ * b₂ ≠ 1 := by
    intro h
    apply hne
    have : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right h1]
  have hS : ({1, b₁, b₂, b₁ * b₂} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      intro h
      exact h1' (mul_eq_right.mp h.symm)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, fun h => h2' (mul_eq_left.mp h.symm)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm h1', Ne.symm h2', Ne.symm hb12⟩
  have huniv : ({1, b₁, b₂, b₁ * b₂} : Finset G) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hS, ← Nat.card_eq_fintype_card, h4])
  have hxmem : x ∈ ({1, b₁, b₂, b₁ * b₂} : Finset G) := by rw [huniv]; exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with h | h | h | h
  · exact absurd h hx1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem card_center_two {n : ℕ} (hn : 3 ≤ n) {P : Type} [Group P] [Finite P]
    (hP : Nat.card P = 2 ^ n) (hcl : n - 1 ≤ Group.nilpotencyClass P) :
    Nat.card (center P) = 2 := by
  by_cases h4 : 4 ≤ n
  · exact CFSG.GH74.Uniqueness.SU.SU1.card_center_of_maxClass Nat.prime_two h4 hP hcl
  · have hn3 : n = 3 := by omega
    subst hn3
    have hPp : IsPGroup 2 P := IsPGroup.of_card hP
    have hnil : Group.IsNilpotent P := hPp.isNilpotent
    have hnc : ¬ IsMulCommutative P := by
      intro hcomm
      have := (Group.IsNilpotent.nilpotencyClass_le_one_iff).mpr hcomm
      omega
    have hnt : Nontrivial P := by
      rw [← Finite.one_lt_card_iff_nontrivial, hP]
      norm_num
    have := Fact.mk Nat.prime_two
    have hZnt : Nontrivial (center P) := hPp.center_nontrivial
    have hdvd : Nat.card (center P) ∣ 2 ^ 3 := hP ▸ Subgroup.card_subgroup_dvd_card (center P)
    obtain ⟨s, hs3, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hZ1 : 1 < Nat.card (center P) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    have hs1 : 1 ≤ s := by
      by_contra hcon
      have : s = 0 := by omega
      rw [hs, this, pow_zero] at hZ1
      exact lt_irrefl _ hZ1
    have hQZ : Nat.card (P ⧸ center P) = 2 ^ (3 - s) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
      rw [hs, hP] at h1
      have h2 : 2 ^ 3 = 2 ^ (3 - s) * 2 ^ s := by
        rw [← pow_add, Nat.sub_add_cancel hs3]
      rw [h2] at h1
      exact (Nat.eq_of_mul_eq_mul_right (pow_pos two_pos s) h1).symm
    by_contra hne
    have hs2 : 2 ≤ s := by
      by_contra hlt
      have : s = 1 := by omega
      exact hne (by rw [hs, this, pow_one])
    have hcyc : IsCyclic (P ⧸ center P) :=
      CFSG.GH74.Uniqueness.SU.SU1.isCyclic_of_card_le_prime Nat.prime_two hQZ (by omega)
    exact hnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (center P)) (by simp))

theorem classify [Finite G] {x : G} (hx2 : orderOf x = 2) (hxc : ∀ y, x * y = y * x)
    (hG : IsCyclic G ∨ IsMaximalClassTwoGroup G) :
    IsCyclic G ∨ (Nat.card G = 4 ∧ ∀ y z : G, y * z = z * y) ∨ ∃ a : G, MaxData G a x := by
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  right
  obtain ⟨hp, hnil, hcard⟩ := hG.resolve_left hcyc
  obtain ⟨c, hc⟩ : ∃ c, c = Group.nilpotencyClass G := ⟨_, rfl⟩
  rw [← hc] at hcard
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · left
    have hcomm : IsMulCommutative G :=
      (Group.IsNilpotent.nilpotencyClass_le_one_iff).mp (by omega)
    interval_cases c
    · exfalso
      have h2 : Nat.card G = 2 := by simpa using hcard.symm
      have := Fact.mk Nat.prime_two
      exact hcyc (isCyclic_of_prime_card h2)
    · exact ⟨by simpa using hcard.symm, fun y z => hcomm.is_comm.comm y z⟩
  · right
    have hn3 : 3 ≤ c + 1 := by omega
    obtain ⟨M, hMidx, hMcyc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_cyclic_index_two (c + 1) hn3 G
      hcard.symm (by omega)
    have hZ : Nat.card (center G) = 2 := card_center_two hn3 hcard.symm (by omega)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
    set a : G := (g : G) with ha_def
    have hzM : zpowers a = M := by
      refine le_antisymm (Subgroup.zpowers_le.mpr g.2) (fun m hm => ?_)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨m, hm⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hMcard : Nat.card M = 2 ^ c := by
      have h1 := Subgroup.card_mul_index M
      rw [hMidx, ← hcard, pow_succ] at h1
      exact Nat.eq_of_mul_eq_mul_right two_pos h1
    have ha : orderOf a = Nat.card M := by
      rw [ha_def, Subgroup.orderOf_coe]
      exact orderOf_eq_card_of_forall_mem_zpowers hg
    have h4 : 4 ≤ orderOf a := by
      rw [ha, hMcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ c := Nat.pow_le_pow_right two_pos hc2
    have hx_sq : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx2, pow_two] at this
    have hx_ne : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    have hxcen : x ∈ center G := Subgroup.mem_center_iff.mpr (fun y => (hxc y).symm)
    have hcenter : ∀ z : G, (∀ y, z * y = y * z) → z = 1 ∨ z = x := by
      intro z hz
      have hzc : z ∈ center G := Subgroup.mem_center_iff.mpr (fun y => (hz y).symm)
      have hle : zpowers x ≤ center G := Subgroup.zpowers_le.mpr hxcen
      have hcx : Nat.card (zpowers x) = 2 := by rw [Nat.card_zpowers, hx2]
      have heq : zpowers x = center G :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcx, hZ])
      rw [← heq] at hzc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzc
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · left
        rw [hm, zpow_mul, zpow_two, hx_sq, one_zpow]
      · right
        rw [hm, zpow_add, zpow_mul, zpow_two, hx_sq, one_zpow, one_mul, zpow_one]
    exact ⟨a, ⟨hzM ▸ hMidx, h4, hx_sq, hx_ne, hxc, hcenter⟩⟩

theorem qshape_abstract [Finite G] {x : G} (hx2 : orderOf x = 2) (hxc : ∀ y, x * y = y * x)
    (hG : IsCyclic G ∨ IsMaximalClassTwoGroup G) :
    (∀ z₁ z₂ : G, z₁ ≠ 1 → z₂ ≠ 1 → z₁ ≠ z₂ → z₁ * z₁ = 1 → z₂ * z₂ = 1 → z₁ * z₂ = z₂ * z₁ →
      (∀ q : G, q * q = 1 → q * z₁ = z₁ * q ∧ q * z₂ = z₂ * q) → Nat.card G = 4) ∧
    (∃ M₀ : Subgroup G, IsCyclic M₀ ∧
      (∀ φ : G →* G, Function.Injective φ → φ x = x → ∀ c ∈ M₀, φ c ∈ M₀) ∧
      ∀ q : G, q * q = 1 → (∀ c ∈ M₀, q * c = c * q) → ∀ y : G, q * y = y * q) ∧
    (∀ q : G, (∀ y : G, q * y = y * q) → q * q = 1 → q ≠ 1 → q ≠ x → Nat.card G = 4) ∧
    (∀ b₁ b₂ : G, b₁ * b₁ = 1 → b₂ * b₂ = 1 → b₁ ≠ 1 → b₂ ≠ 1 → b₁ ≠ b₂ → b₁ * b₂ = b₂ * b₁ →
      x = b₁ ∨ x = b₂ ∨ x = b₁ * b₂) := by
  have hx_sq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hx_ne : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  rcases classify hx2 hxc hG with hcyc | ⟨h4, hcomm⟩ | ⟨a, S⟩
  · have := hcyc
    have hcomm : ∀ y z : G, y * z = z * y := fun y z => IsMulCommutative.is_comm.comm y z
    refine ⟨?_, exists_cyclic_of_all_central x (fun q _ y => hcomm q y), ?_, ?_⟩
    · intro z₁ z₂ h1 h2 hne hz1 hz2 _ _
      exact absurd (cyclic_involution_unique hz1 hz2 h1 h2) hne
    · intro q _ hq2 hq1 hqx
      exact absurd (cyclic_involution_unique hq2 hx_sq hq1 hx_ne) hqx
    · intro b₁ b₂ h1 h2 h1' h2' hne _
      exact absurd (cyclic_involution_unique h1 h2 h1' h2') hne
  · refine ⟨fun _ _ _ _ _ _ _ _ _ => h4,
      exists_cyclic_of_all_central x (fun q _ y => hcomm q y), fun _ _ _ _ _ => h4, ?_⟩
    intro b₁ b₂ h1 _ h1' h2' hne _
    exact x_mem_of_card_four hx_ne h4 h1 h1' h2' hne
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro z₁ z₂ h1 h2 hne hz1 hz2 _ hall
      exfalso
      by_cases hnc1 : ∃ y, z₁ * y ≠ y * z₁
      · exact S.false_of_noncentral hz1 hnc1 (fun q hq => (hall q hq).1)
      · push Not at hnc1
        have hz1x : z₁ = x := (S.center_eq z₁ hnc1).resolve_left h1
        by_cases hnc2 : ∃ y, z₂ * y ≠ y * z₂
        · exact S.false_of_noncentral hz2 hnc2 (fun q hq => (hall q hq).2)
        · push Not at hnc2
          have hz2x : z₂ = x := (S.center_eq z₂ hnc2).resolve_left h2
          exact hne (hz1x.trans hz2x.symm)
    · by_cases hall : ∀ q : G, q * q = 1 → ∀ y : G, q * y = y * q
      · exact exists_cyclic_of_all_central x hall
      · push Not at hall
        obtain ⟨u, hu2, y, hy⟩ := hall
        refine ⟨zpowers a, inferInstance, ?_,
          fun q hq2 hqc y => S.central_of_centralizes_M hq2 hqc y⟩
        intro φ hφ _ c hc
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        rw [map_zpow]
        exact Subgroup.zpow_mem _ (S.phi_mem hu2 ⟨y, hy⟩ φ hφ) k
    · intro q hqc _ hq1 hqx
      exact absurd ((S.center_eq q hqc).resolve_left hq1) hqx
    · intro b₁ b₂ h1 h2 h1' h2' hne hc
      exact S.x_mem_of_commuting h1 h2 h1' h2' hne hc

def conjEnd {X : Type} [Group X] (Q : Subgroup X) (t : X) (h : ∀ a ∈ Q, t * a * t⁻¹ ∈ Q) :
    ↥Q →* ↥Q where
  toFun a := ⟨t * a * t⁻¹, h a a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

end QShape

theorem qShapeFacts : QShapeFacts := by
  intro X _ _ T Q x _hT hQT hnorm hxQ hx2 hxc hshape
  let x' : ↥Q := ⟨x, hxQ⟩
  have hx2' : orderOf x' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hx2
  have hxc' : ∀ y : ↥Q, x' * y = y * x' := fun y => Subtype.ext (hxc y (hQT y.2)).symm
  obtain ⟨A1, A2, A3, A4⟩ := QShape.qshape_abstract hx2' hxc' hshape
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h1 h2 hne hs1 hs2 hcomm hall
    refine A1 ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun h => h1 (congrArg Subtype.val h)
    · exact fun h => h2 (congrArg Subtype.val h)
    · exact fun h => hne (congrArg Subtype.val h)
    · exact Subtype.ext hs1
    · exact Subtype.ext hs2
    · exact Subtype.ext hcomm
    · intro q hq
      have := hall q q.2 (congrArg Subtype.val hq)
      exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  · obtain ⟨M₀, hMc, hMφ, hMq⟩ := A2
    refine ⟨M₀.map Q.subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨m, _, rfl⟩
      exact m.2
    · intro t ht c hc
      obtain ⟨m, hm, rfl⟩ := hc
      have hφinj : Function.Injective (QShape.conjEnd Q t (hnorm t ht)) := by
        intro a b hab
        have := congrArg Subtype.val hab
        have h' : t * (a : X) * t⁻¹ = t * (b : X) * t⁻¹ := this
        exact Subtype.ext (by simpa using h')
      have hφx : QShape.conjEnd Q t (hnorm t ht) x' = x' := by
        apply Subtype.ext
        show t * x * t⁻¹ = x
        calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hxc t ht]
          _ = x := by group
      exact ⟨QShape.conjEnd Q t (hnorm t ht) m, hMφ _ hφinj hφx m hm, rfl⟩
    · have : IsCyclic ↥M₀ := hMc
      exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective M₀ Q.subtype Subtype.val_injective) (MulEquiv.surjective _)
    · intro q hq hq2 hqc y hy
      have := hMq ⟨q, hq⟩ (Subtype.ext hq2)
        (fun c hc => Subtype.ext (hqc c ⟨c, hc, rfl⟩)) ⟨y, hy⟩
      exact congrArg Subtype.val this
  · intro q hq hqc hq2 hq1 hqx
    refine A3 ⟨q, hq⟩ (fun y => Subtype.ext (hqc y y.2)) (Subtype.ext hq2) ?_ ?_
    · exact fun h => hq1 (congrArg Subtype.val h)
    · exact fun h => hqx (congrArg Subtype.val h)
  · intro a ha b hb h1 h2 h1' h2' hne hc
    rcases A4 ⟨a, ha⟩ ⟨b, hb⟩ (Subtype.ext h1) (Subtype.ext h2)
        (fun h => h1' (congrArg Subtype.val h)) (fun h => h2' (congrArg Subtype.val h))
        (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hc) with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))

end CFSG.GH74.GLS.C3.Layer1.P34
