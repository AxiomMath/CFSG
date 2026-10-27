module

public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

open CFSG CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n (card_conjSubgroup conjSubgroup_eq_self_iff conjSubgroup_eq_of_isTI
  inf_conjSubgroup_eq_bot_of_isTI isTI_conjSubgroup)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem forall_mul_comm_of_isCyclic {A : Subgroup G} (hcyc : IsCyclic ↥A) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  intro a ha b hb
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h1 := congrArg Subtype.val hm
  have h2 := congrArg Subtype.val hn
  simp only [Subgroup.coe_zpow] at h1 h2
  rw [← h1, ← h2]
  exact (zpow_mul_comm _ m n).symm.symm

theorem eq_of_card_eq_of_le_of_isCyclic {A : Subgroup G} (hcyc : IsCyclic ↥A) {X Y : Subgroup G}
    (hX : X ≤ A) (hY : Y ≤ A) (h : Nat.card ↥X = Nat.card ↥Y) : X = Y := by
  have hX' : Nat.card ↥(X.subgroupOf A) = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hY' : Nat.card ↥(Y.subgroupOf A) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have := (IsCyclic.subgroup_eq_iff_card_eq (H := X.subgroupOf A) (K := Y.subgroupOf A)).mpr
    (by rw [hX', hY', h])
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hX, inf_of_le_left hY] at this
  exact this

theorem centralizer_le_normalizer_of_isTI {A : Subgroup G} (hA : IsTI A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {y : G} (hy : y * a = a * y) : y ∈ Subgroup.normalizer (A : Set G) := by
  have hmem : a ∈ A ⊓ conjSubgroup y A :=
    ⟨ha, mem_conjSubgroup.mpr (by
      have : y⁻¹ * a * y = a := by
        calc y⁻¹ * a * y = y⁻¹ * (a * y) := by simp only [mul_assoc]
          _ = y⁻¹ * (y * a) := by rw [hy]
          _ = a := by group
      rw [this]; exact ha)⟩
  have hne : A ⊓ conjSubgroup y A ≠ ⊥ := fun h => ha1 (by
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem)
  exact conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI hA hne)

theorem isTI_of_le_cyclic {A : Subgroup G} (hcyc : IsCyclic ↥A) (hTI : IsTI A)
    {K₂ : Subgroup G} (hK₂ : K₂ ≤ A) : IsTI K₂ := by
  intro h
  by_cases hh : h ∈ Subgroup.normalizer (A : Set G)
  · right
    have hle : conjSubgroup h K₂ ≤ A :=
      (Subgroup.map_mono hK₂).trans (conjSubgroup_eq_self_iff.mpr hh).le
    have heq : K₂ = conjSubgroup h K₂ :=
      eq_of_card_eq_of_le_of_isCyclic hcyc hK₂ hle (by rw [card_conjSubgroup])
    rw [← heq, inf_idem]
  · left
    have hbot : A ⊓ conjSubgroup h A = ⊥ :=
      inf_conjSubgroup_eq_bot_of_isTI hTI fun h' => hh (conjSubgroup_eq_self_iff.mp h')
    exact eq_bot_iff.mpr ((inf_le_inf hK₂ (Subgroup.map_mono hK₂)).trans hbot.le)

theorem two_pow_pred_dvd_sq_sub_one_of_two_pow_dvd_pow_four_sub_one (a : ℕ) (ha : 1 ≤ a)
    (k : ℤ) (h : (2 : ℤ) ^ a ∣ k ^ 4 - 1) : (2 : ℤ) ^ (a - 1) ∣ k ^ 2 - 1 := by
  have hodd : Odd k := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have h2 : (2 : ℤ) ∣ k ^ 4 - 1 := (dvd_pow_self 2 (by omega)).trans h
    have h3 : (2 : ℤ) ∣ k ^ 4 := ⟨8 * m ^ 4, by rw [hm]; ring⟩
    have := dvd_sub h3 h2
    simp at this
  obtain ⟨m, hm⟩ := hodd
  set w : ℤ := 2 * m ^ 2 + 2 * m + 1 with hw
  have hwodd : Odd w := ⟨m ^ 2 + m, by rw [hw]; ring⟩
  have hk2 : k ^ 2 + 1 = 2 * w := by rw [hm, hw]; ring
  have hk4 : k ^ 4 - 1 = 2 * (w * (k ^ 2 - 1)) := by
    have : k ^ 4 - 1 = (k ^ 2 - 1) * (k ^ 2 + 1) := by ring
    rw [this, hk2]; ring
  rw [hk4] at h
  have h1 : (2 : ℤ) ^ (a - 1) ∣ w * (k ^ 2 - 1) := by
    have : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this] at h
    exact (mul_dvd_mul_iff_left (by norm_num)).mp h
  have hcop : IsCoprime ((2 : ℤ) ^ (a - 1)) w := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨c, hc⟩ := hwodd
    rw [hc]
    simp [Int.gcd_comm]
  exact hcop.dvd_of_dvd_mul_left h1

theorem two_pow_dvd_sq_sub_one_of_two_pow_pred_dvd_sub_one (a : ℕ) (ha : 2 ≤ a) (k : ℤ)
    (h : (2 : ℤ) ^ (a - 1) ∣ k - 1) : (2 : ℤ) ^ a ∣ k ^ 2 - 1 := by
  obtain ⟨c, hc⟩ := h
  have h2 : (2 : ℤ) ∣ k - 1 := by
    rw [hc]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) c
  obtain ⟨d, hd⟩ := h2
  have : k ^ 2 - 1 = (k - 1) * ((k - 1) + 2) := by ring
  rw [this, hc]
  have e : (2 : ℤ) ^ a = 2 ^ (a - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [e]
  have h3 : (2 : ℤ) ∣ ((2 : ℤ) ^ (a - 1) * c + 2) := by
    have : (2 : ℤ) ∣ (2 : ℤ) ^ (a - 1) * c := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) c
    exact dvd_add this (dvd_refl 2)
  obtain ⟨e', he'⟩ := h3
  rw [he']
  exact ⟨c * e', by ring⟩

theorem le_normalizer_conj_and_commute_of_orderOf_four {A : Subgroup G} (hcyc : IsCyclic ↥A)
    (hA2 : IsPGroup 2 A) (hTI : IsTI A) (h4 : 4 ≤ Nat.card ↥A)
    {g : G} (hg : g ∉ Subgroup.normalizer (A : Set G)) {u : G} (hu : u ∈ conjSubgroup g A)
    (huM : u ∈ Subgroup.normalizer (A : Set G)) (hu4 : orderOf u = 4) :
    A ≤ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) ∧
      ∀ r ∈ A, r * u = u * r := by
  have hB : IsTI (conjSubgroup g A) := isTI_conjSubgroup hTI g
  have hAB : A ⊓ conjSubgroup g A = ⊥ :=
    inf_conjSubgroup_eq_bot_of_isTI hTI fun h => hg (conjSubgroup_eq_self_iff.mp h)
  have htB : u ^ 2 ∈ conjSubgroup g A := (conjSubgroup g A).pow_mem hu 2
  have ht1 : u ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hu4] at this
    omega
  have hct : ∀ y : G, y * u ^ 2 = u ^ 2 * y →
      y ∈ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) :=
    fun y hy => centralizer_le_normalizer_of_isTI hB htB ht1 hy
  have hcomm : ∀ r ∈ A,
      r ∈ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) → r * u = u * r := by
    intro r hr hrN
    have h1 : r * u * r⁻¹ * u⁻¹ ∈ conjSubgroup g A := by
      have h2 : r * u * r⁻¹ ∈ conjSubgroup g A := (Subgroup.mem_normalizer_iff.mp hrN u).mp hu
      exact mul_mem h2 (inv_mem hu)
    have h3 : r * u * r⁻¹ * u⁻¹ ∈ A := by
      have h4' : u * r⁻¹ * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp huM r⁻¹).mp (inv_mem hr)
      have := mul_mem hr h4'
      simpa [mul_assoc] using this
    have h5 : r * u * r⁻¹ * u⁻¹ = 1 := by
      have : r * u * r⁻¹ * u⁻¹ ∈ A ⊓ conjSubgroup g A := ⟨h3, h1⟩
      rw [hAB, Subgroup.mem_bot] at this
      exact this
    calc r * u = r * u * r⁻¹ * u⁻¹ * (u * r) := by group
      _ = u * r := by rw [h5, one_mul]
  by_cases hA : ∀ r ∈ A, r * u ^ 2 = u ^ 2 * r
  · exact ⟨fun r hr => hct r (hA r hr), fun r hr => hcomm r hr (hct r (hA r hr))⟩
  · exfalso
    push Not at hA
    obtain ⟨r₀, hr₀A, hr₀⟩ := hA
    obtain ⟨r, hr⟩ := hcyc.exists_generator
    have hrt : (r : G) * u ^ 2 ≠ u ^ 2 * r := by
      intro hc
      apply hr₀
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨r₀, hr₀A⟩)
      have : r₀ = (r : G) ^ m := by simpa using (congrArg Subtype.val hm).symm
      rw [this]
      exact (Commute.zpow_left (show Commute (r : G) (u ^ 2) from hc) m).eq
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hA2
    have ha2 : 2 ≤ a := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hord : orderOf (r : G) = 2 ^ a := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hr, ha]
    have hur : u * (r : G) * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp huM r).mp r.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨_, hur⟩)
    have hk' : u * (r : G) * u⁻¹ = (r : G) ^ k := by simpa using (congrArg Subtype.val hk).symm
    have hconj : ∀ m : ℤ, u * (r : G) ^ m * u⁻¹ = (r : G) ^ (k * m) := by
      intro m
      have h1 : u * (r : G) ^ m * u⁻¹ = (u * (r : G) * u⁻¹) ^ m := by
        simp
      rw [h1, hk', ← zpow_mul, mul_comm]
    have hconj2 : ∀ m : ℤ, u ^ 2 * (r : G) ^ m * (u ^ 2)⁻¹ = (r : G) ^ (k * (k * m)) := by
      intro m
      have : u ^ 2 * (r : G) ^ m * (u ^ 2)⁻¹ = u * (u * (r : G) ^ m * u⁻¹) * u⁻¹ := by
        rw [sq]; group
      rw [this, hconj, hconj]
    have hdvd : (2 : ℤ) ^ a ∣ k ^ 4 - 1 := by
      have hu4' : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
      have h1 : u ^ 2 * (u ^ 2 * (r : G) * (u ^ 2)⁻¹) * (u ^ 2)⁻¹ = (r : G) := by
        have e : u ^ 2 * (u ^ 2 * (r : G) * (u ^ 2)⁻¹) * (u ^ 2)⁻¹ =
            u ^ 4 * (r : G) * (u ^ 4)⁻¹ := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]; group
        rw [e, hu4']; group
      have h2 : u ^ 2 * (r : G) * (u ^ 2)⁻¹ = (r : G) ^ (k * k) := by
        have := hconj2 1
        simpa [mul_one] using this
      have h3 : (r : G) ^ (k * (k * (k * k))) = (r : G) := by
        rw [h2, hconj2 (k * k)] at h1
        exact h1
      have h4 : (r : G) ^ (k * (k * (k * k)) - 1) = 1 := by
        rw [zpow_sub_one, h3]; group
      have h5 := (orderOf_dvd_iff_zpow_eq_one).mpr h4
      rw [hord] at h5
      have e : k * (k * (k * k)) - 1 = k ^ 4 - 1 := by ring
      rw [e] at h5
      exact_mod_cast h5
    have h6 := two_pow_pred_dvd_sq_sub_one_of_two_pow_dvd_pow_four_sub_one a (by omega) k hdvd
    have hpow2 : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hr2t : (r : G) ^ 2 * u ^ 2 = u ^ 2 * (r : G) ^ 2 := by
      have e := hconj2 2
      have e2 : (r : G) ^ (k * (k * 2)) = (r : G) ^ (2 : ℤ) := by
        have h0 : (r : G) ^ (k * (k * 2) - 2) = 1 := by
          apply (orderOf_dvd_iff_zpow_eq_one).mp
          rw [hord]
          have e3 : k * (k * 2) - 2 = 2 * (k ^ 2 - 1) := by ring
          rw [e3]
          have h7 : (2 : ℤ) ^ a ∣ 2 * (k ^ 2 - 1) := by
            rw [hpow2]; exact mul_dvd_mul_left 2 h6
          exact_mod_cast h7
        rw [zpow_sub, mul_inv_eq_one] at h0
        exact h0
      rw [e2] at e
      have e4 : u ^ 2 * (r : G) ^ 2 = (r : G) ^ 2 * u ^ 2 := by
        have : u ^ 2 * (r : G) ^ (2 : ℤ) * (u ^ 2)⁻¹ = (r : G) ^ (2 : ℤ) := e
        have e5 : u ^ 2 * (r : G) ^ 2 = u ^ 2 * (r : G) ^ (2 : ℤ) := by simp
        rw [e5]
        calc u ^ 2 * (r : G) ^ (2 : ℤ) = u ^ 2 * (r : G) ^ (2 : ℤ) * (u ^ 2)⁻¹ * u ^ 2 := by group
          _ = (r : G) ^ (2 : ℤ) * u ^ 2 := by rw [this]
          _ = (r : G) ^ 2 * u ^ 2 := by simp
      exact e4.symm
    have hr2N := hct _ hr2t
    have hr2u : (r : G) ^ 2 * u = u * (r : G) ^ 2 :=
      hcomm _ (A.pow_mem r.2 2) hr2N
    have hk2 : (r : G) ^ (k * 2) = (r : G) ^ (2 : ℤ) := by
      have h1 := hconj 2
      have h2 : u * (r : G) ^ (2 : ℤ) * u⁻¹ = (r : G) ^ (2 : ℤ) := by
        have e5 : (r : G) ^ (2 : ℤ) = (r : G) ^ 2 := by simp
        rw [e5]
        calc u * (r : G) ^ 2 * u⁻¹ = (r : G) ^ 2 * u * u⁻¹ := by rw [← hr2u]
          _ = (r : G) ^ 2 := by group
      rw [h2] at h1
      exact h1.symm
    have h8 : (2 : ℤ) ^ (a - 1) ∣ k - 1 := by
      have h0 : (r : G) ^ (k * 2 - 2) = 1 := by
        rw [zpow_sub, mul_inv_eq_one]; exact hk2
      have h9 := (orderOf_dvd_iff_zpow_eq_one).mpr h0
      rw [hord] at h9
      have e3 : k * 2 - 2 = 2 * (k - 1) := by ring
      rw [e3] at h9
      have h10 : (2 : ℤ) ^ a ∣ 2 * (k - 1) := by exact_mod_cast h9
      rw [hpow2] at h10
      exact (mul_dvd_mul_iff_left (by norm_num)).mp h10
    have h11 := two_pow_dvd_sq_sub_one_of_two_pow_pred_dvd_sub_one a ha2 k h8
    have h12 : (r : G) ^ (k * k) = (r : G) := by
      have h0 : (r : G) ^ (k ^ 2 - 1) = 1 := by
        apply (orderOf_dvd_iff_zpow_eq_one).mp
        rw [hord]
        exact_mod_cast h11
      rw [zpow_sub_one, mul_inv_eq_one] at h0
      rw [sq] at h0
      exact h0
    have h13 : u ^ 2 * (r : G) * (u ^ 2)⁻¹ = (r : G) := by
      have := hconj2 1
      simpa [mul_one, h12] using this
    apply hrt
    calc (r : G) * u ^ 2 = (u ^ 2 * (r : G) * (u ^ 2)⁻¹) * u ^ 2 := by rw [h13]
      _ = u ^ 2 * r := by group

omit [Finite G] in
theorem conj_inv_le_normalizer_of_le_normalizer_conj {A : Subgroup G} (g : G) :
    A ≤ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) →
      conjSubgroup g⁻¹ A ≤ Subgroup.normalizer (A : Set G) := by
  intro h x hx
  have hx' : g * x * g⁻¹ ∈ A := by simpa using mem_conjSubgroup.mp hx
  have hN := Subgroup.mem_normalizer_iff.mp (h hx')
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have e1 := hN (g * z * g⁻¹)
  rw [mem_conjSubgroup, mem_conjSubgroup] at e1
  have e2 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
  have e3 : g⁻¹ * (g * x * g⁻¹ * (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹) * g = x * z * x⁻¹ := by group
  rw [e2, e3] at e1
  exact e1

theorem conj_le_normalizer_of_card_four_conj_le_normalizer {A : Subgroup G} (hcyc : IsCyclic ↥A)
    (hA2 : IsPGroup 2 A) (hTI : IsTI A) (h8 : 8 ≤ Nat.card ↥A)
    {K₂ : Subgroup G} (hK₂ : K₂ ≤ A) (hK₂4 : Nat.card ↥K₂ = 4)
    {g : G} (hg : g ∉ Subgroup.normalizer (A : Set G))
    (hK₂g : conjSubgroup g K₂ ≤ Subgroup.normalizer (A : Set G)) :
    conjSubgroup g A ≤ Subgroup.normalizer (A : Set G) ∧
      conjSubgroup g⁻¹ A ≤ Subgroup.normalizer (A : Set G) := by
  have := hcyc
  have : IsCyclic ↥K₂ := Subgroup.isCyclic_of_le hK₂
  obtain ⟨x, hx⟩ := (inferInstance : IsCyclic ↥K₂).exists_generator
  have hxo : orderOf (x : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx, hK₂4]
  have h4 : 4 ≤ Nat.card ↥A := by omega
  have hA1 : A ≤ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) := by
    refine (le_normalizer_conj_and_commute_of_orderOf_four hcyc hA2 hTI h4 hg
      (u := g * (x : G) * g⁻¹) ?_ ?_ ?_).1
    · exact (Subgroup.map_mono hK₂) ⟨x, x.2, rfl⟩
    · exact hK₂g ⟨x, x.2, rfl⟩
    · rw [← hxo]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
  have h1 : conjSubgroup g⁻¹ A ≤ Subgroup.normalizer (A : Set G) :=
    conj_inv_le_normalizer_of_le_normalizer_conj g hA1
  refine ⟨?_, h1⟩
  have hg' : g⁻¹ ∉ Subgroup.normalizer (A : Set G) := fun h' => hg (by simpa using inv_mem h')
  have hA2' : A ≤ Subgroup.normalizer ((conjSubgroup g⁻¹ A : Subgroup G) : Set G) := by
    refine (le_normalizer_conj_and_commute_of_orderOf_four hcyc hA2 hTI h4 hg'
      (u := g⁻¹ * (x : G) * g⁻¹⁻¹) ?_ ?_ ?_).1
    · exact (Subgroup.map_mono hK₂) ⟨x, x.2, rfl⟩
    · exact h1 ((Subgroup.map_mono hK₂) ⟨x, x.2, rfl⟩)
    · rw [← hxo]
      exact orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective _
  have := conj_inv_le_normalizer_of_le_normalizer_conj g⁻¹ hA2'
  simpa using this

end CFSG.CGT.PushingUpLit.SolKAb
