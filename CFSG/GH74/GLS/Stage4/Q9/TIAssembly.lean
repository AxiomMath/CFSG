module

public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section Defs

variable {G : Type*} [Group G]

@[expose] def S2set (z : G) : Set G :=
  {x | x ∈ Subgroup.centralizer {z} ∧ z ∈ Subgroup.zpowers x}

@[expose] def S3set (z : G) : Set G :=
  {x | x ∈ Subgroup.centralizer {z} ∧ 3 ∣ orderOf x}

@[expose] def S5set (K₁ K₂ : Subgroup G) : Set G :=
  {x | (x ∈ K₁ ∨ x ∈ K₂) ∧ orderOf x = 5}

@[expose] def Sset (z : G) (K₁ K₂ : Subgroup G) : Set G :=
  S2set z ∪ S3set z ∪ S5set K₁ K₂

end Defs

section Helpers

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g
    (show SemiconjBy g x (g * x * g⁻¹) by simp [SemiconjBy, mul_assoc])).symm

private theorem conj_mem_zpowers' {g s z : G} (h : z ∈ zpowers s) :
    g * z * g⁻¹ ∈ zpowers (g * s * g⁻¹) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [conj_zpow]⟩

private theorem conj_commute_iff' (g a b : G) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) ↔ a * b = b * a := by
  constructor
  · intro h
    have h' : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  · intro h
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

private theorem conj_mem_centralizer_conj' {g s c : G} :
    g * c * g⁻¹ ∈ Subgroup.centralizer {g * s * g⁻¹} ↔ c ∈ Subgroup.centralizer {s} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact conj_commute_iff' g c s

private theorem mem_centralizer_of_conj_eq' {z g : G} (h : g * z * g⁻¹ = z) :
    g ∈ Subgroup.centralizer {z} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h]

private theorem conj_eq_of_mem_centralizer' {z g : G} (h : g ∈ Subgroup.centralizer {z}) :
    g * z * g⁻¹ = z := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h]
    _ = z := by group

private theorem eq_of_orderOf_eq_two_of_mem_zpowers' [Finite G] {x a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hax : a ∈ zpowers x) (hbx : b ∈ zpowers x) : a = b := by
  classical
  by_contra hne
  have : Fintype (zpowers x) := Fintype.ofFinite _
  have ha2 : a ^ 2 = 1 ∧ a ≠ 1 := orderOf_eq_prime_iff.mp ha
  have hb2 : b ^ 2 = 1 ∧ b ≠ 1 := orderOf_eq_prime_iff.mp hb
  have h1a : (1 : zpowers x) ≠ ⟨a, hax⟩ := fun h => ha2.2 (congrArg Subtype.val h).symm
  have h1b : (1 : zpowers x) ≠ ⟨b, hbx⟩ := fun h => hb2.2 (congrArg Subtype.val h).symm
  have hab : (⟨a, hax⟩ : zpowers x) ≠ ⟨b, hbx⟩ := fun h => hne (congrArg Subtype.val h)
  have hcard : ({1, ⟨a, hax⟩, ⟨b, hbx⟩} : Finset (zpowers x)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, ⟨a, hax⟩, ⟨b, hbx⟩, h1a, h1b, hab, rfl⟩
  have hsub : ({1, ⟨a, hax⟩, ⟨b, hbx⟩} : Finset (zpowers x)) ⊆
      Finset.univ.filter (fun h : zpowers x => h ^ 2 = 1) := by
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hh with rfl | rfl | rfl
    · simp
    · exact Subtype.ext ha2.1
    · exact Subtype.ext hb2.1
  have hle := IsCyclic.card_pow_eq_one_le (α := zpowers x) (n := 2) (by norm_num)
  have := Finset.card_le_card hsub
  omega

private theorem exists_pow_orderOf_eq_three' [Finite G] {x : G} (h3 : 3 ∣ orderOf x) :
    ∃ m : ℕ, orderOf (x ^ m) = 3 := by
  obtain ⟨k, hk⟩ := h3
  have hpos : 0 < orderOf x := orderOf_pos x
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  refine ⟨k, ?_⟩
  rw [orderOf_pow_of_dvd hk0 ⟨3, by rw [hk]; ring⟩, hk]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)

end Helpers

section Key

variable {G : Type*} [Group G]

private theorem eq_of_mem_zpowers_Sset [Finite G] {z : G} (hz : orderOf z = 2) {K₁ K₂ : Subgroup G}
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    {x e : G} (hx : x ∈ Sset z K₁ K₂) (he : e ∈ zpowers x) (he2 : orderOf e = 2) : e = z := by
  rcases hx with (⟨hxC, hzx⟩ | ⟨hxC, h3x⟩) | ⟨_, h5⟩
  · exact eq_of_orderOf_eq_two_of_mem_zpowers' he2 hz he hzx
  · obtain ⟨m, hm⟩ := exists_pow_orderOf_eq_three' h3x
    refine hK3 (x ^ m) (pow_mem hxC m) hm e he2 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (((Commute.refl x).zpow_left k).pow_right m).eq
  · exfalso
    have h := orderOf_dvd_of_mem_zpowers he
    rw [he2, h5] at h
    omega

private theorem mem_centralizer_of_S2 [Finite G] {z : G} (hz : orderOf z = 2) {K₁ K₂ : Subgroup G}
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    {s g : G} (hs : s ∈ S2set z) (hs' : g * s * g⁻¹ ∈ Sset z K₁ K₂) :
    g ∈ Subgroup.centralizer {z} :=
  mem_centralizer_of_conj_eq'
    (eq_of_mem_zpowers_Sset hz hK3 hs' (conj_mem_zpowers' hs.2) (by rw [orderOf_conj_eq', hz]))

private theorem mem_centralizer_of_S3 [Finite G] {z : G} (hz : orderOf z = 2)
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    {s g : G} (hs : s ∈ S3set z) (hs' : g * s * g⁻¹ ∈ S3set z) :
    g ∈ Subgroup.centralizer {z} := by
  obtain ⟨hsC, h3s⟩ := hs
  obtain ⟨hsC', -⟩ := hs'
  obtain ⟨m, hm⟩ := exists_pow_orderOf_eq_three' h3s
  have hy'eq : (g * s * g⁻¹) ^ m = g * s ^ m * g⁻¹ := conj_pow
  have hy'3 : orderOf ((g * s * g⁻¹) ^ m) = 3 := by rw [hy'eq, orderOf_conj_eq', hm]
  have hcomm : s ^ m * z = z * s ^ m :=
    Subgroup.mem_centralizer_singleton_iff.mp (pow_mem hsC m)
  refine mem_centralizer_of_conj_eq' (hK3 _ (pow_mem hsC' m) hy'3 (g * z * g⁻¹)
    (by rw [orderOf_conj_eq', hz]) ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, hy'eq]
  calc g * z * g⁻¹ * (g * s ^ m * g⁻¹) = g * (z * s ^ m) * g⁻¹ := by group
    _ = g * (s ^ m * z) * g⁻¹ := by rw [← hcomm]
    _ = g * s ^ m * g⁻¹ * (g * z * g⁻¹) := by group

private theorem mem_centralizer_of_S5 {z : G} (hz : orderOf z = 2) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
      ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
        (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z)
    {s g : G} (hs : s ∈ S5set K₁ K₂) (hs' : g * s * g⁻¹ ∈ S5set K₁ K₂) :
    g ∈ Subgroup.centralizer {z} := by
  obtain ⟨hsK, hs5⟩ := hs
  obtain ⟨hsK', hs5'⟩ := hs'
  have hsC : s ∈ Subgroup.centralizer {z} := hsK.elim (fun h => hK₁ h) (fun h => hK₂ h)
  have hzs : z ∈ Subgroup.centralizer {s} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hsC ⊢
    exact hsC.symm
  have hcent := (hK5 s hsK hs5).1
  refine mem_centralizer_of_conj_eq' ((hK5 _ hsK' hs5').2 (g * z * g⁻¹)
    (conj_mem_centralizer_conj'.2 hzs) (by rw [orderOf_conj_eq', hz]) ?_)
  intro c' hc'
  have hd : g⁻¹ * c' * g ∈ Subgroup.centralizer {s} := by
    have hc'eq : g * (g⁻¹ * c' * g) * g⁻¹ = c' := by group
    refine (conj_mem_centralizer_conj' (g := g) (s := s) (c := g⁻¹ * c' * g)).1 ?_
    rwa [hc'eq]
  have hdz : (g⁻¹ * c' * g) * z = z * (g⁻¹ * c' * g) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcent hd)
  calc g * z * g⁻¹ * c' = g * (z * (g⁻¹ * c' * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * c' * g) * z) * g⁻¹ := by rw [← hdz]
    _ = c' * (g * z * g⁻¹) := by group

private theorem mem_centralizer_of_conj_mem_Sset [Finite G] {z : G} (hz : orderOf z = 2)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
      ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
        (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z)
    {s g : G} (hs : s ∈ Sset z K₁ K₂) (hs' : g * s * g⁻¹ ∈ Sset z K₁ K₂) :
    g ∈ Subgroup.centralizer {z} := by
  by_cases h2 : s ∈ S2set z
  · exact mem_centralizer_of_S2 hz hK3 h2 hs'
  by_cases h2' : g * s * g⁻¹ ∈ S2set z
  · have hs'' : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ ∈ Sset z K₁ K₂ := by
      rw [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group]
      exact hs
    exact inv_mem_iff.1 (mem_centralizer_of_S2 hz hK3 h2' hs'')
  rcases hs with (hs2 | hs3) | hs5
  · exact absurd hs2 h2
  · rcases hs' with (hs2' | hs3') | hs5'
    · exact absurd hs2' h2'
    · exact mem_centralizer_of_S3 hz hK3 hs3 hs3'
    · exfalso
      have h := hs3.2
      rw [← orderOf_conj_eq' g s, hs5'.2] at h
      omega
  · rcases hs' with (hs2' | hs3') | hs5'
    · exact absurd hs2' h2'
    · exfalso
      have h := hs3'.2
      rw [orderOf_conj_eq', hs5.2] at h
      omega
    · exact mem_centralizer_of_S5 hz hK₁ hK₂ hK5 hs5 hs5'

private theorem conj_mem_Sset {z : G} {K₁ K₂ : Subgroup G}
    (hn₁ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    {c : G} (hc : c ∈ Subgroup.centralizer {z}) {s : G} (hs : s ∈ Sset z K₁ K₂) :
    c * s * c⁻¹ ∈ Sset z K₁ K₂ := by
  rcases hs with (⟨hsC, hzs⟩ | ⟨hsC, h3⟩) | ⟨hK, h5⟩
  · refine Or.inl (Or.inl ⟨mul_mem (mul_mem hc hsC) (inv_mem hc), ?_⟩)
    have h := conj_mem_zpowers' (g := c) hzs
    rwa [conj_eq_of_mem_centralizer' hc] at h
  · exact Or.inl (Or.inr ⟨mul_mem (mul_mem hc hsC) (inv_mem hc), by rwa [orderOf_conj_eq']⟩)
  · exact Or.inr ⟨hK.imp (hn₁ c hc s) (hn₂ c hc s), by rwa [orderOf_conj_eq']⟩

end Key

section Main

variable {G : Type*} [Group G]

theorem Sset_subset_centralizer {z : G} {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z}) {s : G}
    (hs : s ∈ Sset z K₁ K₂) : s ∈ Subgroup.centralizer {z} := by
  rcases hs with (⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩
  · exact h
  · exact h
  · exact h.elim (fun h => hK₁ h) (fun h => hK₂ h)

theorem inv_mem_Sset {z : G} {K₁ K₂ : Subgroup G} {s : G} (hs : s ∈ Sset z K₁ K₂) :
    s⁻¹ ∈ Sset z K₁ K₂ := by
  rcases hs with (⟨hC, hz⟩ | ⟨hC, h3⟩) | ⟨hK, h5⟩
  · exact Or.inl (Or.inl ⟨inv_mem hC, by rwa [Subgroup.zpowers_inv]⟩)
  · exact Or.inl (Or.inr ⟨inv_mem hC, by rwa [orderOf_inv]⟩)
  · exact Or.inr ⟨hK.imp (fun h => inv_mem h) (fun h => inv_mem h), by rwa [orderOf_inv]⟩

theorem eq_of_orderOf_eq_two_of_mem_Sset [Finite G] {z : G} (hz : orderOf z = 2)
    {K₁ K₂ : Subgroup G}
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    {s : G} (hs : s ∈ Sset z K₁ K₂) (hs2 : orderOf s = 2) : s = z :=
  eq_of_mem_zpowers_Sset hz hK3 hs (Subgroup.mem_zpowers s) hs2

theorem isTISubset_Sset [Finite G] {z : G} (hz : orderOf z = 2) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hn₁ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
      ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
        (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z) :
    CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}) := by
  have hzC : z ∈ Subgroup.centralizer {z} := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzS : z ∈ Sset z K₁ K₂ := Or.inl (Or.inl ⟨hzC, Subgroup.mem_zpowers z⟩)
  refine ⟨⟨z, hzS⟩, ?_, ?_, ?_⟩
  · rintro ((⟨-, h1⟩ | ⟨-, h3⟩) | ⟨-, h5⟩)
    · rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1
      rw [h1, orderOf_one] at hz
      omega
    · rw [orderOf_one] at h3
      omega
    · rw [orderOf_one] at h5
      omega
  · ext g
    constructor
    · intro hg
      have h1 : g * z * g⁻¹ ∈ Sset z K₁ K₂ := (Subgroup.mem_set_normalizer_iff.mp hg z).mp hzS
      exact mem_centralizer_of_conj_mem_Sset hz hK₁ hK₂ hK3 hK5 hzS h1
    · intro hg
      refine Subgroup.mem_set_normalizer_iff.mpr fun n => ⟨fun hn => conj_mem_Sset hn₁ hn₂ hg hn,
        fun hn => ?_⟩
      have h := conj_mem_Sset hn₁ hn₂ (inv_mem hg) hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at h
  · intro g hg
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, x, hx, rfl⟩
    refine hg (mem_centralizer_of_conj_mem_Sset hz hK₁ hK₂ hK3 hK5 hy ?_)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]

theorem ti_of_key {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2) (K₁ K₂ : Subgroup G)
    (hK₁ : K₁ ≤ Subgroup.centralizer {z}) (hK₂ : K₂ ≤ Subgroup.centralizer {z})
    (hn₁ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ Subgroup.centralizer {z}, ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    (hK3 : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      Subgroup.centralizer {y} ≤ Subgroup.centralizer {z} ∧
        ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      Subgroup.centralizer {x} ≤ Subgroup.centralizer {z} ∧
        ∀ e : G, e ∈ Subgroup.centralizer {x} → orderOf e = 2 →
          (∀ c ∈ Subgroup.centralizer {x}, e * c = c * e) → e = z) :
    CFSG.IsTISubset (Sset z K₁ K₂) (Subgroup.centralizer {z}) ∧
      (∀ s ∈ Sset z K₁ K₂, s⁻¹ ∈ Sset z K₁ K₂) ∧
      (∀ s ∈ Sset z K₁ K₂, orderOf s = 2 → s = z) ∧
      ∀ s ∈ Sset z K₁ K₂, s ∈ Subgroup.centralizer {z} := by
  have hK3' : ∀ y : G, y ∈ Subgroup.centralizer {z} → orderOf y = 3 →
      ∀ e : G, orderOf e = 2 → e ∈ Subgroup.centralizer {y} → e = z :=
    fun y hy h3 => (hK3 y hy h3).2
  exact ⟨isTISubset_Sset hz hK₁ hK₂ hn₁ hn₂ hK3' hK5, fun s hs => inv_mem_Sset hs,
    fun s hs hs2 => eq_of_orderOf_eq_two_of_mem_Sset hz hK3' hs hs2,
    fun s hs => Sset_subset_centralizer hK₁ hK₂ hs⟩

end Main

end CFSG.GH74.GLS.Stage4.Q9
