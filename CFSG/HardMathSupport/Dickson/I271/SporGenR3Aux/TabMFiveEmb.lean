module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenEmb

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open Subgroup

section Subtype

variable {G : Type*} [Group G]

theorem card_centralizer_subtype {C : Subgroup G} (u : C) :
    Nat.card (centralizer ({u} : Set C)) =
      Nat.card (C ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun k => ⟨(k.1 : G), k.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp k.2))⟩
      invFun := fun m => ⟨⟨m.1, m.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2.2))⟩
      left_inv := fun k => rfl
      right_inv := fun m => rfl }

theorem eq_of_involutions [Finite G] {C D : Subgroup G} (hDC : D ≤ C)
    (hcent : ∀ t ∈ D, orderOf t = 2 → C ⊓ centralizer ({t} : Set G) ≤ D)
    (hconj : ∀ t ∈ D, ∀ u ∈ D, orderOf t = 2 → orderOf u = 2 →
      Nat.card ↥(C ⊓ centralizer ({t} : Set G)) = Nat.card ↥(C ⊓ centralizer ({u} : Set G)) →
        ∃ g ∈ D, g * u * g⁻¹ = t)
    {t₀ t₁ : G} (ht₀ : t₀ ∈ D) (ht₁ : t₁ ∈ D) (ho₀ : orderOf t₀ = 2) (ho₁ : orderOf t₁ = 2)
    (hne : Nat.card ↥(C ⊓ centralizer ({t₀} : Set G)) ≠
      Nat.card ↥(C ⊓ centralizer ({t₁} : Set G))) : D = C := by
  have key : D.subgroupOf C = ⊤ := by
    refine TabMSeven.eq_top_of_involutions (C := ↥C) (D := D.subgroupOf C) ?_ ?_
      (t₀ := ⟨t₀, hDC ht₀⟩) (t₁ := ⟨t₁, hDC ht₁⟩) (Subgroup.mem_subgroupOf.2 ht₀)
      (Subgroup.mem_subgroupOf.2 ht₁) (by rw [← Subgroup.orderOf_coe]; exact ho₀)
      (by rw [← Subgroup.orderOf_coe]; exact ho₁) ?_
    · intro t ht ho c hc
      have hc' : (c : G) ∈ C ⊓ centralizer ({(t : G)} : Set G) :=
        ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))⟩
      exact Subgroup.mem_subgroupOf.2 (hcent (t : G) (Subgroup.mem_subgroupOf.1 ht)
        ((Subgroup.orderOf_coe t).trans ho) hc')
    · intro t ht u hu hto huo hcard
      rw [card_centralizer_subtype, card_centralizer_subtype] at hcard
      obtain ⟨g, hg, hgu⟩ := hconj (t : G) (Subgroup.mem_subgroupOf.1 ht) (u : G)
        (Subgroup.mem_subgroupOf.1 hu) ((Subgroup.orderOf_coe t).trans hto)
        ((Subgroup.orderOf_coe u).trans huo) hcard
      exact ⟨⟨g, hDC hg⟩, Subgroup.mem_subgroupOf.2 hg, Subtype.ext hgu⟩
    · show Nat.card (centralizer ({(⟨t₀, hDC ht₀⟩ : C)} : Set C)) ≠
        Nat.card (centralizer ({(⟨t₁, hDC ht₁⟩ : C)} : Set C))
      rw [card_centralizer_subtype, card_centralizer_subtype]
      exact hne
  exact le_antisymm hDC (Subgroup.subgroupOf_eq_top.1 key)

end Subtype

section Prod

variable {G : Type*} [Group G]

@[expose] def prodSub (k : G) (H : Subgroup G) (hHk : H ≤ centralizer ({k} : Set G)) :
    Subgroup G where
  carrier := {g | ∃ (i : ℤ) (h : G), h ∈ H ∧ g = k ^ i * h}
  one_mem' := ⟨0, 1, H.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, h, hh, rfl⟩ ⟨j, h', hh', rfl⟩
    refine ⟨i + j, h * h', H.mul_mem hh hh', ?_⟩
    have hc : h * k ^ j = k ^ j * h :=
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hHk hh) : Commute h k) j).eq
    calc k ^ i * h * (k ^ j * h') = k ^ i * (h * k ^ j) * h' := by simp only [mul_assoc]
      _ = k ^ i * (k ^ j * h) * h' := by rw [hc]
      _ = k ^ (i + j) * (h * h') := by rw [zpow_add]; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨i, h, hh, rfl⟩
    refine ⟨-i, h⁻¹, H.inv_mem hh, ?_⟩
    have hc : h⁻¹ * k ^ (-i) = k ^ (-i) * h⁻¹ :=
      (Commute.inv_left (Commute.zpow_right
        (Subgroup.mem_centralizer_singleton_iff.1 (hHk hh) : Commute h k) (-i))).eq
    rw [mul_inv_rev, ← zpow_neg, hc]

variable {k : G} {H : Subgroup G} {hHk : H ≤ centralizer ({k} : Set G)}

theorem le_prodSub : H ≤ prodSub k H hHk := fun h hh => ⟨0, h, hh, by simp⟩

theorem prodSub_le {C : Subgroup G} (hkC : k ∈ C) (hHC : H ≤ C) : prodSub k H hHk ≤ C := by
  rintro _ ⟨i, h, hh, rfl⟩
  exact C.mul_mem (C.zpow_mem hkC i) (hHC hh)

variable {p : ℕ}

theorem eq_one_of_mem_zpowers (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {α : G}
    (hα : α * k * α⁻¹ = k⁻¹) {H' : Subgroup G} (hH'α : H' ≤ centralizer ({α} : Set G)) {g : G}
    (hg : g ∈ Subgroup.zpowers k) (hgH : g ∈ H') : g = 1 := by
  have hinv : ∀ g ∈ Subgroup.zpowers k, α * g * α⁻¹ = g⁻¹ := by
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← conj_zpow, hα, inv_zpow]
  have hc : g * α = α * g := Subgroup.mem_centralizer_singleton_iff.1 (hH'α hgH)
  have h1 : α * g * α⁻¹ = g := by rw [← hc]; simp
  have h2 : g * g = 1 := by
    have h3 := hinv g hg
    rw [h1] at h3
    exact mul_eq_one_iff_eq_inv.2 h3
  have h4 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have h5 : orderOf g ∣ p := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk, pow_orderOf_eq_one,
      one_zpow]
  have h6 : orderOf g ∣ Nat.gcd 2 p := Nat.dvd_gcd h4 h5
  have h7 : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  rw [h7] at h6
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)

theorem prod_injective (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {α : G}
    (hα : α * k * α⁻¹ = k⁻¹) {H' : Subgroup G} (hH'α : H' ≤ centralizer ({α} : Set G)) :
    Function.Injective (fun x : Fin p × ↥H' => k ^ (x.1 : ℕ) * (x.2 : G)) := by
  rintro ⟨i, h⟩ ⟨j, h'⟩ hij
  have hij' : k ^ (i : ℕ) * (h : G) = k ^ (j : ℕ) * (h' : G) := hij
  have h1 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) = (h' : G) * (h : G)⁻¹ := by
    calc (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ)
        = (k ^ (j : ℕ))⁻¹ * (k ^ (i : ℕ) * (h : G)) * (h : G)⁻¹ := by group
      _ = (k ^ (j : ℕ))⁻¹ * (k ^ (j : ℕ) * (h' : G)) * (h : G)⁻¹ := by rw [hij']
      _ = (h' : G) * (h : G)⁻¹ := by group
  have h2 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) ∈ Subgroup.zpowers k :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _))
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _)
  have h3 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) ∈ H' := by
    rw [h1]
    exact H'.mul_mem h'.2 (H'.inv_mem h.2)
  have h4 := eq_one_of_mem_zpowers hp hp2 hk hα hH'α h2 h3
  have h5 : k ^ (j : ℕ) = k ^ (i : ℕ) := inv_mul_eq_one.1 h4
  have h6 : (i : ℕ) = (j : ℕ) := by
    have hi : (i : ℕ) ∈ Set.Iio (orderOf k) := by rw [hk]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf k) := by rw [hk]; exact j.2
    exact (pow_injOn_Iio_orderOf hi hj h5.symm)
  have h7 : (h' : G) * (h : G)⁻¹ = 1 := by rw [← h1, h6]; simp
  have hij2 : i = j := Fin.ext h6
  subst hij2
  have : (h' : G) = h := mul_inv_eq_one.1 h7
  exact Prod.ext rfl (Subtype.ext this.symm)

theorem mul_card_le_of_prod [Finite G] (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {α : G}
    (hα : α * k * α⁻¹ = k⁻¹) {H' X : Subgroup G} (hH'α : H' ≤ centralizer ({α} : Set G))
    (hkX : k ∈ X) (hH'X : H' ≤ X) : p * Nat.card ↥H' ≤ Nat.card ↥X := by
  let f : Fin p × ↥H' → ↥X := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), X.mul_mem (X.pow_mem hkX _) (hH'X x.2.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact prod_injective hp hp2 hk hα hH'α (congrArg Subtype.val hxy)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this

theorem eq_prod_of_card_le [Finite G] (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {α : G}
    (hα : α * k * α⁻¹ = k⁻¹) {H' X : Subgroup G} (hH'α : H' ≤ centralizer ({α} : Set G))
    (hkX : k ∈ X) (hH'X : H' ≤ X) (hX : Nat.card ↥X ≤ p * Nat.card ↥H') :
    ∀ x ∈ X, ∃ (i : ℕ) (h : G), h ∈ H' ∧ x = k ^ i * h := by
  let f : Fin p × ↥H' → ↥X := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), X.mul_mem (X.pow_mem hkX _) (hH'X x.2.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact prod_injective hp hp2 hk hα hH'α (congrArg Subtype.val hxy)
  have hbij : Function.Bijective f := by
    refine hf.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]
    exact hX
  intro x hx
  obtain ⟨⟨i, h⟩, hih⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨i, h, h.2, (congrArg Subtype.val hih).symm⟩

theorem mem_of_orderOf_two (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {α : G}
    (hα : α * k * α⁻¹ = k⁻¹) (hHα : H ≤ centralizer ({α} : Set G)) {t : G}
    (ht : t ∈ prodSub k H hHk) (ho : orderOf t = 2) : t ∈ H := by
  obtain ⟨i, h, hh, rfl⟩ := ht
  have hc : h * k ^ i = k ^ i * h :=
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hHk hh) : Commute h k) i).eq
  have hsq : (k ^ i * h) ^ 2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hsq' : k ^ (2 * i) = (h ^ 2)⁻¹ := by
    have h1 : (k ^ i * h) ^ 2 = k ^ i * k ^ i * (h * h) := by
      calc (k ^ i * h) ^ 2 = k ^ i * h * (k ^ i * h) := sq _
        _ = k ^ i * (h * k ^ i) * h := by simp only [mul_assoc]
        _ = k ^ i * (k ^ i * h) * h := by rw [hc]
        _ = k ^ i * k ^ i * (h * h) := by simp only [mul_assoc]
    rw [h1] at hsq
    rw [two_mul, zpow_add, sq h]
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using hsq)
  have hz : k ^ (2 * i) ∈ Subgroup.zpowers k := Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) _
  have hH : k ^ (2 * i) ∈ H := by
    rw [hsq']
    exact H.inv_mem (H.pow_mem hh 2)
  have h1 := eq_one_of_mem_zpowers hp hp2 hk hα hHα hz hH
  have h2 : k ^ i = 1 := by
    have hodd : orderOf (k ^ i) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      simpa using h1
    have hdv : orderOf (k ^ i) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk,
        pow_orderOf_eq_one, one_zpow]
    have h6 : orderOf (k ^ i) ∣ Nat.gcd 2 p := Nat.dvd_gcd hodd hdv
    have h7 : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rw [h7] at h6
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)
  rw [h2, one_mul]
  exact hh

theorem mul_card_le_cent_inf [Finite G] (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p)
    {α : G} (hα : α * k * α⁻¹ = k⁻¹) (hHα : H ≤ centralizer ({α} : Set G))
    (hHk : H ≤ centralizer ({k} : Set G)) {t : G} (ht : t ∈ H) :
    p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) ≤
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) :=
  mul_card_le_of_prod hp hp2 hk hα (H' := H ⊓ centralizer ({t} : Set G))
    (fun x hx => hHα hx.1)
    ⟨Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hHk ht)).symm,
      Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    (fun x hx => ⟨hx.2, hHk hx.1⟩)

theorem card_centralizer_le_of_involutions [Finite G] (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : orderOf k = p) {α : G} (hα : α * k * α⁻¹ = k⁻¹)
    (hHα : H ≤ centralizer ({α} : Set G)) (hHk : H ≤ centralizer ({k} : Set G))
    (hup : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) ≤
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)))
    (hconj : ∀ t ∈ H, ∀ u ∈ H, orderOf t = 2 → orderOf u = 2 →
      Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = Nat.card ↥(H ⊓ centralizer ({u} : Set G)) →
        ∃ g ∈ H, g * u * g⁻¹ = t)
    {t₀ t₁ : G} (ht₀ : t₀ ∈ H) (ht₁ : t₁ ∈ H) (ho₀ : orderOf t₀ = 2) (ho₁ : orderOf t₁ = 2)
    (hne : Nat.card ↥(H ⊓ centralizer ({t₀} : Set G)) ≠
      Nat.card ↥(H ⊓ centralizer ({t₁} : Set G))) :
    centralizer ({k} : Set G) = prodSub k H hHk ∧
      Nat.card ↥(centralizer ({k} : Set G)) ≤ p * Nat.card ↥H := by
  set D := prodSub k H hHk with hD
  have hkC : k ∈ centralizer ({k} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hDC : D ≤ centralizer ({k} : Set G) := prodSub_le hkC hHk
  have hHD : H ≤ D := le_prodSub
  have hkt : ∀ t ∈ H, k ∈ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := fun t ht =>
    ⟨Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hHk ht)).symm, hkC⟩
  have hHt : ∀ t ∈ H, H ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := fun t _ x hx =>
    ⟨hx.2, hHk hx.1⟩
  have heq : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) =
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) := fun t ht ho =>
    le_antisymm (hup t ht ho)
      (mul_card_le_of_prod hp hp2 hk hα (H' := H ⊓ centralizer ({t} : Set G))
        (fun x hx => hHα hx.1) (hkt t ht) (hHt t ht))
  have heq' : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({k} : Set G) ⊓ centralizer ({t} : Set G)) =
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) := fun t ht ho => by
    rw [inf_comm]
    exact heq t ht ho
  have hsub : ∀ t ∈ H, orderOf t = 2 →
      centralizer ({k} : Set G) ⊓ centralizer ({t} : Set G) ≤ D := by
    intro t ht ho x hx
    have hx' : x ∈ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := ⟨hx.2, hx.1⟩
    obtain ⟨i, h, hh, rfl⟩ := eq_prod_of_card_le hp hp2 hk hα (H' := H ⊓ centralizer ({t} : Set G))
      (fun x hx => hHα hx.1) (hkt t ht) (hHt t ht) (hup t ht ho) x hx'
    exact ⟨(i : ℤ), h, hh.1, by rw [zpow_natCast]⟩
  have hDeq : D = centralizer ({k} : Set G) := by
    refine eq_of_involutions hDC ?_ ?_ (hHD ht₀) (hHD ht₁) ho₀ ho₁ ?_
    · intro t ht ho
      exact hsub t (mem_of_orderOf_two hp hp2 hk hα hHα ht ho) ho
    · intro t ht u hu hto huo hcard
      have ht' := mem_of_orderOf_two hp hp2 hk hα hHα ht hto
      have hu' := mem_of_orderOf_two hp hp2 hk hα hHα hu huo
      rw [heq' t ht' hto, heq' u hu' huo] at hcard
      obtain ⟨g, hg, hgu⟩ := hconj t ht' u hu' hto huo (Nat.eq_of_mul_eq_mul_left hp.pos hcard)
      exact ⟨g, hHD hg, hgu⟩
    · rw [heq' t₀ ht₀ ho₀, heq' t₁ ht₁ ho₁]
      exact fun h => hne (Nat.eq_of_mul_eq_mul_left hp.pos h)
  refine ⟨hDeq.symm, ?_⟩
  rw [← hDeq]
  let f : Fin p × ↥H → ↥D := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), ⟨((x.1 : ℕ) : ℤ), x.2, x.2.2, by rw [zpow_natCast]⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨d, i, h, hh, rfl⟩
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hk' : (orderOf k : ℤ) = p := by rw [hk]
    have hnn : 0 ≤ i % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
    have hlt : (i % (p : ℤ)).toNat < p := by
      have := Int.emod_lt_of_pos i hp0
      omega
    have h1 : k ^ i = k ^ ((i % (p : ℤ)).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← hk', zpow_mod_orderOf]
    refine ⟨(⟨(i % (p : ℤ)).toNat, hlt⟩, ⟨h, hh⟩), Subtype.ext ?_⟩
    show k ^ ((i % (p : ℤ)).toNat) * h = k ^ i * h
    rw [h1]
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this

end Prod

end CFSG.HardMathSupport.Dickson.I271.TabMFive
