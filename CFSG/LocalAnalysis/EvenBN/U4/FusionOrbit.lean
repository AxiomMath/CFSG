module

public import CFSG.LocalAnalysis.EvenBN.U4.Fusion
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OrbitCounts
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.BangOrbit

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Orbits

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem ncard_of_I1N1_invariant {X : Set (GL (Fin 4) K)}
    (hXsub : X ⊆ (miyamotoA1 h : Set (GL (Fin 4) K)) \ {1})
    (hXinv : ∀ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    X.ncard = 0 ∨ X.ncard = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) ∨
      X.ncard = (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) ∨ X.ncard = (2 ^ f) ^ 4 - 1 := by
  have := h.finite
  set O₁ : Set (GL (Fin 4) K) :=
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * miyamotoZ1 K * g = y} with hO₁
  set O₂ : Set (GL (Fin 4) K) :=
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y} with hO₂
  have hfull : ∀ z : GL (Fin 4) K, (∃ x ∈ X, ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h,
      g⁻¹ * z * g = x) → {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * z * g = y} ⊆ X := by
    rintro z ⟨_, hx, g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    have := hXinv (g⁻¹ * g') (mul_mem (inv_mem hg) hg') _ hx
    rwa [show (g⁻¹ * g')⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * g') = g'⁻¹ * z * g' by group] at this
  have hcover : X ⊆ O₁ ∪ O₂ := by
    intro x hx
    have := miyamoto_two_orbits_A1 h (hXsub hx).1 (hXsub hx).2
    by_cases h1 : x ∈ O₁
    · exact Or.inl h1
    · exact Or.inr (by tauto)
  have hdisj : Disjoint O₁ O₂ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have hx1' := hx1
    rw [hO₁, miyamoto_orbit_z1_I1N1 h] at hx1'
    exact (miyamoto_two_orbits_A1 h hx1'.1 hx1'.2.1).1 hx1 hx2
  have hc1 : O₁.ncard = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := ncard_orbit_z1 h
  have hc2 : O₂.ncard = (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) := ncard_orbit_z2 h
  have hsplit : ∀ O : Set (GL (Fin 4) K), (O = O₁ ∨ O = O₂) →
      (X ∩ O = ∅ ∨ X ∩ O = O) := by
    rintro O (rfl | rfl)
    · by_cases hne : (X ∩ O₁).Nonempty
      · obtain ⟨x, hxX, ⟨g, hg, e⟩⟩ := hne
        exact Or.inr (Set.inter_eq_right.2 (hfull _ ⟨x, hxX, g, hg, e⟩))
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)
    · by_cases hne : (X ∩ O₂).Nonempty
      · obtain ⟨x, hxX, ⟨g, hg, e⟩⟩ := hne
        exact Or.inr (Set.inter_eq_right.2 (hfull _ ⟨x, hxX, g, hg, e⟩))
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)
  have hX : X = (X ∩ O₁) ∪ (X ∩ O₂) := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hcover]
  have hsum : (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) + (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) =
      (2 ^ f) ^ 4 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 :=
      ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
    rw [hk]
    simp only [Nat.add_sub_cancel]
    have e : (k + 1) ^ 4 = k * ((k + 1) ^ 2 + 1) + k * (k + 1) * ((k + 1) ^ 2 + 1) + 1 := by
      ring
    omega
  rcases hsplit O₁ (Or.inl rfl) with h1 | h1 <;> rcases hsplit O₂ (Or.inr rfl) with h2 | h2
  · left
    rw [hX, h1, h2, Set.empty_union, Set.ncard_empty]
  · right; right; left
    rw [hX, h1, h2, Set.empty_union, hc2]
  · right; left
    rw [hX, h1, h2, Set.union_empty, hc1]
  · right; right; right
    rw [hX, h1, h2, Set.ncard_union_eq hdisj, hc1, hc2, hsum]

end Orbits

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem exists_of_mem_B1 (hS : Setting h L η t Q T) {z : G} (hz : z ∈ miyamotoB1 h L η t) :
    ∃ a ∈ miyamotoA1G h L η, z = a ∨ z = t * a := by
  obtain ⟨x, hx, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => mem_centralizer_iff.1 (hS.A1_le_centralizer_zpowers hy) x hx) hz
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
  refine ⟨a, ha, ?_⟩
  rcases hS.zpow_t_eq i with h1 | h1
  · left
    rw [h1, one_mul]
  · right
    rw [h1]

theorem conj_mem_A1G_of_mem_I1_sup_N1 (_hS : Setting h L η t Q T) {g : GL (Fin 4) K}
    (hg : g ∈ miyamotoI1 h ⊔ miyamotoN1 h) (hgS : g ∈ gramSU h (miyamotoJ4 K)) {a : G}
    (ha : a ∈ miyamotoA1G h L η) :
    ((η.symm ⟨g, hgS⟩ : L) : G) * a * ((η.symm ⟨g, hgS⟩ : L) : G)⁻¹ ∈ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨a₀, ha₀, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  have e : ((η.symm ⟨g, hgS⟩ : L) : G) * ((η.symm a₀ : L) : G) *
      ((η.symm ⟨g, hgS⟩ : L) : G)⁻¹ = ((η.symm (⟨g, hgS⟩ * a₀ * ⟨g, hgS⟩⁻¹) : L) : G) := by
    simp only [map_mul, map_inv, L.coe_mul, L.coe_inv]
  rw [e, symm_mem_miyamotoPull_iff h L η]
  have := (conj_mem_A1_and_Q_of_mem_I1_sup_N1 h (inv_mem hg) ha₀).1
  rwa [inv_inv] at this

theorem symm_mem_normalizer_B1_of_mem_I1_sup_N1 (hS : Setting h L η t Q T) {g : GL (Fin 4) K}
    (hg : g ∈ miyamotoI1 h ⊔ miyamotoN1 h) (hgS : g ∈ gramSU h (miyamotoJ4 K)) :
    ((η.symm ⟨g, hgS⟩ : L) : G) ∈ normalizer (miyamotoB1 h L η t : Set G) := by
  set ℓ : G := ((η.symm ⟨g, hgS⟩ : L) : G)
  have hℓt : ℓ * t = t * ℓ := hS.comm_t_of_mem_L (η.symm _).2
  refine mem_normalizer_of_conj_le fun b hb => ?_
  obtain ⟨a, ha, rfl | rfl⟩ := hS.exists_of_mem_B1 hb
  · exact mem_sup_right (hS.conj_mem_A1G_of_mem_I1_sup_N1 hg hgS ha)
  · rw [show ℓ * (t * a) * ℓ⁻¹ = (ℓ * t) * a * ℓ⁻¹ by group, hℓt,
      show t * ℓ * a * ℓ⁻¹ = t * (ℓ * a * ℓ⁻¹) by group]
    exact mul_mem hS.t_mem_B1 (mem_sup_right (hS.conj_mem_A1G_of_mem_I1_sup_N1 hg hgS ha))

theorem conj_set_B1_eq (hS : Setting h L η t Q T) :
    {x | ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), x = n⁻¹ * t * n} =
      {x | ∃ a ∈ miyamotoA1G h L η, x = t * a} := by
  have : CharP K 2 := h.charP
  set Ω : Set G := {x | ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), x = n⁻¹ * t * n}
    with hΩ
  set tA : Set G := {x | ∃ a ∈ miyamotoA1G h L η, x = t * a} with htA
  have hΩtA : Ω ⊆ tA := by
    rintro _ ⟨n, hn, rfl⟩
    have hB : n⁻¹ * t * n ∈ miyamotoB1 h L η t := by
      have := (mem_normalizer_iff.1 (inv_mem hn) t).1 hS.t_mem_B1
      rwa [inv_inv] at this
    obtain ⟨a, ha, h1 | h1⟩ := hS.exists_of_mem_B1 hB
    · exfalso
      apply hS.conj_not_mem_L n
      rw [h1]
      exact miyamotoPull_le h L η _ ha
    · exact ⟨a, ha, h1⟩
  have hcard_tA : tA.ncard = (2 ^ f) ^ 4 := by
    have : tA = (fun a => t * a) '' (miyamotoA1G h L η : Set G) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, rfl⟩
    rw [this, Set.ncard_image_of_injective _ (mul_right_injective t), ← Nat.card_coe_set_eq]
    exact card_miyamotoA1G h L η
  have hA1S := miyamotoUnipotent_le_SU h true false
  set X : Set (GL (Fin 4) K) := {v | ∃ hv : v ∈ miyamotoA1 h, v ≠ 1 ∧
    t * ((η.symm ⟨v, hA1S hv⟩ : L) : G) ∈ Ω} with hX
  have hXsub : X ⊆ (miyamotoA1 h : Set (GL (Fin 4) K)) \ {1} :=
    fun _ hv => ⟨hv.fst, hv.snd.1⟩
  have hXinv : ∀ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, ∀ v ∈ X, g⁻¹ * v * g ∈ X := by
    rintro g hg v ⟨hvA, hv1, n, hn, hnv⟩
    have hgS : g ∈ gramSU h (miyamotoJ4 K) :=
      sup_le (miyamotoI1_le_gramSU h) (miyamotoN1_le_gramSU h) hg
    have hgv : g⁻¹ * v * g ∈ miyamotoA1 h := (conj_mem_A1_and_Q_of_mem_I1_sup_N1 h hg hvA).1
    refine ⟨hgv, fun h1 => hv1 ?_, ?_⟩
    · calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · set ℓ : G := ((η.symm ⟨g, hgS⟩ : L) : G)
      have hℓt : ℓ * t = t * ℓ := hS.comm_t_of_mem_L (η.symm _).2
      have hconj : ((η.symm ⟨g⁻¹ * v * g, hA1S hgv⟩ : L) : G) =
          ℓ⁻¹ * ((η.symm ⟨v, hA1S hvA⟩ : L) : G) * ℓ := by
        have e : (⟨g⁻¹ * v * g, hA1S hgv⟩ : gramSU h (miyamotoJ4 K)) =
            (⟨g, hgS⟩ : gramSU h (miyamotoJ4 K))⁻¹ * ⟨v, hA1S hvA⟩ * ⟨g, hgS⟩ := rfl
        rw [e]
        simp only [map_mul, map_inv, L.coe_mul, L.coe_inv]
        rfl
      refine ⟨n * ℓ, mul_mem hn (hS.symm_mem_normalizer_B1_of_mem_I1_sup_N1 hg hgS), ?_⟩
      rw [hconj]
      have hℓt' : ℓ⁻¹ * t = t * ℓ⁻¹ := (Commute.inv_left (hℓt : Commute ℓ t)).eq
      calc t * (ℓ⁻¹ * ((η.symm ⟨v, hA1S hvA⟩ : L) : G) * ℓ) =
          (t * ℓ⁻¹) * ((η.symm ⟨v, hA1S hvA⟩ : L) : G) * ℓ := by group
        _ = (ℓ⁻¹ * t) * ((η.symm ⟨v, hA1S hvA⟩ : L) : G) * ℓ := by rw [hℓt']
        _ = ℓ⁻¹ * (t * ((η.symm ⟨v, hA1S hvA⟩ : L) : G)) * ℓ := by group
        _ = ℓ⁻¹ * (n⁻¹ * t * n) * ℓ := by rw [hnv]
        _ = (n * ℓ)⁻¹ * t * (n * ℓ) := by group
  have htΩ : t ∈ Ω := ⟨1, one_mem _, by group⟩
  have hXΩ : X.ncard = (Ω \ {t}).ncard := by
    refine Set.ncard_congr (fun v hv => t * ((η.symm ⟨v, hA1S hv.fst⟩ : L) : G))
      (fun v ⟨hv, hv1, hvΩ⟩ => ⟨hvΩ, fun e => hv1 ?_⟩) (fun v w hv hw e => ?_) fun x hx => ?_
    · have e' : ((η.symm ⟨v, hA1S hv⟩ : L) : G) = 1 := mul_eq_left.1 e
      have e'' : η.symm ⟨v, hA1S hv⟩ = η.symm 1 := by
        rw [map_one]
        exact Subtype.ext e'
      exact congrArg Subtype.val (η.symm.injective e'')
    · have e' := mul_left_cancel e
      exact congrArg Subtype.val (η.symm.injective (Subtype.ext e'))
    · obtain ⟨hxΩ, hxt⟩ := hx
      obtain ⟨a, ha, rfl⟩ := hΩtA hxΩ
      obtain ⟨y, hy, rfl⟩ := (mem_miyamotoPull h L η).1 ha
      refine ⟨y, ⟨hy, fun hy1 => hxt ?_, hxΩ⟩, rfl⟩
      have : y = 1 := Subtype.ext hy1
      rw [this, map_one, OneMemClass.coe_one, mul_one]
      rfl
  have hΩcard : Ω.ncard = X.ncard + 1 := by
    rw [hXΩ, Set.ncard_sdiff_singleton_add_one htΩ (Set.toFinite _)]
  have hXne : X.ncard ≠ 0 := by
    obtain ⟨g, hgB, hgne⟩ := hS.exists_conj_mem_B1
    obtain ⟨n, hn, hnt⟩ := hS.exists_normalizer_B1_conj_eq hgB
    have hgΩ : g⁻¹ * t * g ∈ Ω \ {t} := ⟨⟨n, hn, hnt.symm⟩, hgne⟩
    rw [hXΩ]
    exact ((Set.ncard_pos (Set.toFinite _)).2 ⟨_, hgΩ⟩).ne'
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hΩ3 : Nat.card Ω = (2 ^ f) ^ 3 - (2 ^ f) ^ 2 + 2 ^ f ∨
      Nat.card Ω = (2 ^ f) ^ 4 - (2 ^ f) ^ 3 + (2 ^ f) ^ 2 - 2 ^ f + 1 ∨
      Nat.card Ω = (2 ^ f) ^ 4 := by
    rw [Nat.card_coe_set_eq, hΩcard, pow_three_sub_eq_one_add hq1, pow_four_sub_eq_one_add hq1]
    rcases ncard_of_I1N1_invariant h hXsub hXinv with h0 | h1 | h2 | h3
    · exact absurd h0 hXne
    · left
      rw [h1]
      ring
    · right; left
      rw [h2]
      ring
    · right; right
      rw [h3]
      have : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by positivity)
      omega
  have hB₁card : Nat.card (miyamotoB1 h L η t) = 2 ^ (4 * f + 1) := by
    rw [hS.card_B1]
    ring
  have hBang := card_conj_set_eq_of_bang hS.two_le hB₁card le_rfl hS.t_mem_B1 hΩ3
  rw [Nat.card_coe_set_eq] at hBang
  exact Set.eq_of_subset_of_ncard_le hΩtA (by rw [hcard_tA, hBang]) (Set.toFinite _)

theorem conj_inter_B1 (hS : Setting h L η t Q T) :
    {x | ∃ g : G, x = g⁻¹ * t * g} ∩ (miyamotoB1 h L η t : Set G) =
      {x | ∃ a ∈ miyamotoA1G h L η, x = t * a} := by
  rw [← hS.conj_set_B1.1, hS.conj_set_B1_eq]

theorem inf_zpowers_eq_bot (hS : Setting h L η t Q T) {H : Subgroup G} (hH : H ≤ L) :
    H ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxt⟩ := mem_inf.1 hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hxt
  rcases hS.zpow_t_eq i with h1 | h1
  · rw [h1]
    exact one_mem _
  · rw [h1] at hxH
    exact absurd (hH hxH) hS.t_not_mem_L

theorem zpowers_comm_of_le_L (hS : Setting h L η t Q T) {H : Subgroup G} (hH : H ≤ L) :
    ∀ a ∈ zpowers t, ∀ b ∈ H, a * b = b * a := fun a ha b hb => by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
  exact (Commute.zpow_left (hS.comm_t_of_mem_L (hH hb)).symm i).eq

theorem zpowers_sup_inf_L (hS : Setting h L η t Q T) {H : Subgroup G} (hH : H ≤ L) :
    (zpowers t ⊔ H) ⊓ L = H := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hH)
  obtain ⟨hxB, hxL⟩ := mem_inf.1 hx
  obtain ⟨u, hu, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute (hS.zpowers_comm_of_le_L hH) hxB
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
  rcases hS.zpow_t_eq i with h1 | h1
  · rw [h1, one_mul]
    exact ha
  · exfalso
    rw [h1] at hxL
    apply hS.t_not_mem_L
    have := mul_mem hxL (inv_mem (hH ha))
    rwa [mul_inv_cancel_right] at this

theorem card_zpowers_sup (hS : Setting h L η t Q T) {H : Subgroup G} (hH : H ≤ L) :
    Nat.card (zpowers t ⊔ H : Subgroup G) = 2 * Nat.card H := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers t) H
    (hS.zpowers_comm_of_le_L hH)
  rwa [inf_comm, hS.inf_zpowers_eq_bot hH, Subgroup.card_bot, mul_one, hS.card_zpowers_t] at hc

theorem B1_inf_L (hS : Setting h L η t Q T) : miyamotoB1 h L η t ⊓ L = miyamotoA1G h L η :=
  hS.zpowers_sup_inf_L (miyamotoPull_le h L η _)

theorem card_Q (hS : Setting h L η t Q T) : Nat.card Q = 2 * (2 ^ f) ^ 6 := by
  rw [hS.Q_eq, sup_comm, hS.card_zpowers_sup (miyamotoPull_le h L η _), card_miyamotoPG]

theorem zpowers_comm (_hS : Setting h L η t Q T) {u u' : G} (hu : u ∈ zpowers t)
    (hu' : u' ∈ zpowers t) : u * u' = u' * u := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu'
  exact (Commute.zpow_zpow_self t i j).eq

theorem P_mod_A1 (_hS : Setting h L η t Q T) :
    (∀ x ∈ miyamotoPG h L η, x * x ∈ miyamotoA1G h L η) ∧
      ∀ x ∈ miyamotoPG h L η, ∀ y ∈ miyamotoPG h L η, ⁅x, y⁆ ∈ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨hsq, hcomm⟩ := miyamotoP_mod_A1 h
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    rw [← L.coe_mul, ← map_mul, symm_mem_miyamotoPull_iff h L η]
    exact hsq _ hg
  · obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
    have e : ⁅((η.symm g : L) : G), ((η.symm k : L) : G)⁆ = ((η.symm ⁅g, k⁆ : L) : G) := by
      simp only [commutatorElement_def, map_mul, map_inv, L.coe_mul, L.coe_inv]
    rw [e, symm_mem_miyamotoPull_iff h L η]
    have := hcomm _ hg _ hk
    simpa [commutatorElement_def] using this

theorem Q_mod_B1 (hS : Setting h L η t Q T) :
    (∀ x ∈ Q, x * x ∈ miyamotoB1 h L η t) ∧ ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ miyamotoB1 h L η t := by
  obtain ⟨hsq, hcomm⟩ := hS.P_mod_A1
  have hdec : ∀ x ∈ Q, ∃ p ∈ miyamotoPG h L η, ∃ u ∈ zpowers t, x = p * u := fun x hx => by
    rw [hS.Q_eq] at hx
    exact exists_mul_of_mem_sup_of_commute hS.P_comm_zpowers hx
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨p, hp, u, hu, rfl⟩ := hdec x hx
    have hup : u * p = p * u := (hS.P_comm_zpowers p hp u hu).symm
    have e : p * u * (p * u) = (p * p) * (u * u) := by
      calc p * u * (p * u) = p * (u * p) * u := by group
        _ = p * (p * u) * u := by rw [hup]
        _ = (p * p) * (u * u) := by group
    rw [e]
    exact mul_mem (mem_sup_right (hsq p hp)) (mem_sup_left (mul_mem hu hu))
  · obtain ⟨p, hp, u, hu, rfl⟩ := hdec x hx
    obtain ⟨p', hp', u', hu', rfl⟩ := hdec y hy
    rw [commutatorElement_mul_mul_eq_of_commute (hS.P_comm_zpowers p' hp' u hu).symm
      (hS.zpowers_comm hu hu') (hS.P_comm_zpowers p hp u' hu').symm]
    exact mem_sup_right (hcomm p hp p' hp')

theorem B1_le_ker (hS : Setting h L η t Q T) :
    miyamotoB1 h L η t ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :=
  sup_le ((zpowers_le).2 (mem_sup_right hS.t_mem_kernel))
    ((miyamotoPull_le h L η _).trans le_sup_left)

theorem card_le_of_mod_B1 (hS : Setting h L η t Q T) {Y : Subgroup G} (hYT : Y ≤ T)
    (hsq : ∀ y ∈ Y, y * y ∈ miyamotoB1 h L η t)
    (hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, ⁅y, y'⁆ ∈ miyamotoB1 h L η t) :
    Nat.card Y ≤ 2 * (2 ^ f) ^ 6 ∧ (Nat.card Y = 2 * (2 ^ f) ^ 6 → Y = Q) := by
  have : CharP K 2 := h.charP
  set N := L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) with hN
  have hTN : ∀ y ∈ T, y ∈ N → y ∈ Q := by
    intro y hyT hyN
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hS.L_comm_kernel hyN
    have hlP := hS.mem_P_of_mul hyT hl hc rfl
    rw [hS.kernel_eq_zpowers'] at hc
    rw [hS.Q_eq]
    exact mul_mem (mem_sup_left hlP) (mem_sup_right hc)
  by_cases hA : Y ≤ N
  · have hYQ : Y ≤ Q := fun y hy => hTN y (hYT hy) (hA hy)
    have h1 := card_le_of_le hYQ
    rw [hS.card_Q] at h1
    exact ⟨h1, fun hcard => eq_of_le_of_card_ge hYQ (by rw [hS.card_Q, hcard])⟩
  obtain ⟨y₀, hy₀Y, hy₀N⟩ := Set.not_subset.1 hA
  have hσ₀ : hS.fieldFactor ⟨y₀, hS.T_le (hYT hy₀Y)⟩ ≠ 1 := fun h1 => hy₀N (by
    obtain ⟨l, hl, c, hc, e⟩ := (hS.fieldFactor_eq_one_iff _).1 h1
    rw [show y₀ = l * c from e]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hc))
  have hker : ∀ x : centralizer ({t} : Set G), (x : G) ∈ N → hS.fieldFactor x = 1 :=
    fun x hx => by rw [← MonoidHom.mem_ker, hS.ker_fieldFactor, mem_subgroupOf]; exact hx
  have h1 := hS.card_le_two_mul_card_inf_ker (H := Y) (hYT.trans hS.T_le) fun y hy => by
    rw [← map_mul]
    exact hker _ (hS.B1_le_ker (hsq y hy))
  rw [← hN] at h1
  have hY₀Q : Y ⊓ N ≤ miyamotoPG h L η ⊔ zpowers t := fun y hy => by
    rw [← hS.Q_eq]
    exact hTN y (hYT (mem_inf.1 hy).1) (mem_inf.1 hy).2
  have h2 := hS.card_le_two_mul_card_inf_P hY₀Q
  have h3 := hS.two_mul_card_lt_of_commute_mod_A1 (hYT hy₀Y) hσ₀
    (inf_le_right : Y ⊓ N ⊓ miyamotoPG h L η ≤ _) fun w hw => by
      have hwY := (mem_inf.1 (mem_inf.1 hw).1).1
      have hwL := miyamotoPull_le h L η _ (mem_inf.1 hw).2
      rw [← hS.B1_inf_L]
      refine mem_inf.2 ⟨hcomm y₀ hy₀Y w hwY, ?_⟩
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hS.T_le_normalizer (hYT hy₀Y)) w).1 hwL)
        (inv_mem hwL)
  exact ⟨by omega, fun hcard => by omega⟩

theorem centerIn_Q (hS : Setting h L η t Q T) :
    CFSG.centerIn Q = zpowers t ⊔ miyamotoZG h L η := by
  have hZP : miyamotoZG h L η = CFSG.centerIn (miyamotoPG h L η) := (centerIn_miyamotoPG h L η).symm
  have hdec : ∀ x ∈ Q, ∃ p ∈ miyamotoPG h L η, ∃ u ∈ zpowers t, x = p * u := fun x hx => by
    rw [hS.Q_eq] at hx
    exact exists_mul_of_mem_sup_of_commute hS.P_comm_zpowers hx
  refine le_antisymm (fun z hz => ?_) (sup_le ?_ fun z hz => ?_)
  · obtain ⟨hzQ, hzC⟩ := mem_inf.1 hz
    obtain ⟨p, hp, u, hu, rfl⟩ := hdec z hzQ
    have hpZ : p ∈ CFSG.centerIn (miyamotoPG h L η) := by
      refine mem_inf.2 ⟨hp, mem_centralizer_iff.2 fun p' hp' => ?_⟩
      have h1 := mem_centralizer_iff.1 hzC p' (hS.P_le_Q hp')
      have h2 : u * p' = p' * u := (hS.P_comm_zpowers p' hp' u hu).symm
      have h3 : p' * p * u = p * p' * u := by
        calc p' * p * u = p' * (p * u) := by group
          _ = p * u * p' := h1
          _ = p * (u * p') := by group
          _ = p * (p' * u) := by rw [h2]
          _ = p * p' * u := by group
      exact mul_right_cancel h3
    rw [← hZP] at hpZ
    rw [(hS.P_comm_zpowers p hp u hu)]
    exact mul_mem (mem_sup_left hu) (mem_sup_right hpZ)
  · rw [zpowers_le]
    exact mem_inf.2 ⟨hS.t_mem_Q, mem_centralizer_iff.2 fun q hq =>
      mem_centralizer_singleton_iff.1 (hS.Q_le_centralizer hq)⟩
  · rw [hZP] at hz
    obtain ⟨hzP, hzC⟩ := mem_inf.1 hz
    refine mem_inf.2 ⟨hS.P_le_Q hzP, mem_centralizer_iff.2 fun q hq => ?_⟩
    obtain ⟨p, hp, u, hu, rfl⟩ := hdec q hq
    have h1 : p * z = z * p := mem_centralizer_iff.1 hzC p hp
    have h2 : u * z = z * u := (hS.P_comm_zpowers z hzP u hu).symm
    calc p * u * z = p * (u * z) := by group
      _ = p * (z * u) := by rw [h2]
      _ = (p * z) * u := by group
      _ = (z * p) * u := by rw [h1]
      _ = z * (p * u) := by group

theorem B2_le_Q (hS : Setting h L η t Q T) : miyamotoB2 h L η t ≤ Q :=
  sup_le ((zpowers_le).2 hS.t_mem_Q)
    ((miyamotoPull_mono h L η (miyamotoA2_le_P h)).trans hS.P_le_Q)

theorem card_B2 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoB2 h L η t) = 2 * (2 ^ f) ^ 5 := by
  rw [miyamotoB2, hS.card_zpowers_sup (miyamotoPull_le h L η _), card_miyamotoA2G]

theorem A2_mod_Z (_hS : Setting h L η t Q T) :
    (∀ x ∈ miyamotoA2G h L η, x * x ∈ miyamotoZG h L η) ∧
      ∀ x ∈ miyamotoA2G h L η, ∀ y ∈ miyamotoA2G h L η, ⁅x, y⁆ ∈ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    rw [← L.coe_mul, ← map_mul, symm_mem_miyamotoPull_iff h L η]
    exact (miyamotoA2_mod_Z h).1 _ hg
  · have := commutator_mem_commutator hx hy
    rwa [commutator_miyamotoA2G h L η] at this

theorem card_le_and_eq_A2G_of_mod_Z (_hS : Setting h L η t Q T) {W : Subgroup G}
    (hWP : W ≤ miyamotoPG h L η) (hsq : ∀ x ∈ W, x * x ∈ miyamotoZG h L η)
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ miyamotoZG h L η) :
    Nat.card W ≤ (2 ^ f) ^ 5 ∧ ((2 ^ f) ^ 5 ≤ Nat.card W → W = miyamotoA2G h L η) := by
  have : CharP K 2 := h.charP
  obtain ⟨M, hMS, rfl⟩ := exists_eq_miyamotoPull h L η (hWP.trans (miyamotoPull_le h L η _))
  have hMP : M ≤ miyamotoP h := (miyamotoPull_le_miyamotoPull_iff h L η hMS).1 hWP
  have hsqM : ∀ x ∈ M, x * x ∈ miyamotoZ h := by
    intro x hx
    have := hsq _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨x, hMS hx⟩)).2 hx)
    rw [← L.coe_mul, ← map_mul, symm_mem_miyamotoPull_iff h L η] at this
    exact this
  have hcommM : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ miyamotoZ h := by
    intro x hx y hy
    have := hcomm _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨x, hMS hx⟩)).2 hx)
      _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨y, hMS hy⟩)).2 hy)
    have e : ⁅((η.symm ⟨x, hMS hx⟩ : L) : G), ((η.symm ⟨y, hMS hy⟩ : L) : G)⁆ =
        ((η.symm ⁅(⟨x, hMS hx⟩ : gramSU h (miyamotoJ4 K)), ⟨y, hMS hy⟩⁆ : L) : G) := by
      simp only [commutatorElement_def, map_mul, map_inv, L.coe_mul, L.coe_inv]
    rw [e, symm_mem_miyamotoPull_iff h L η] at this
    simpa [commutatorElement_def] using this
  have key := card_le_and_eq_A2_of_mod_Z h hMP hsqM hcommM
  rw [card_miyamotoPull h L η hMS]
  exact ⟨key.1, fun hge => by rw [key.2 hge]⟩

theorem characteristic_B1 (hS : Setting h L η t Q T) :
    ((miyamotoB1 h L η t).subgroupOf T).Characteristic := by
  refine characteristic_iff_map_eq.2 fun φ => ?_
  set H := ((miyamotoB1 h L η t).subgroupOf T).map φ.toMonoidHom with hH
  have hHT : H.map T.subtype ≤ T := map_subtype_le _
  have hHe : CFSG.IsElementaryAbelian 2 (H.map T.subtype) := by
    refine isElementaryAbelian_two_of_forall ?_ ?_
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have e : a * b = b * a := Subtype.ext (hS.B1_comm _ ha _ hb)
      simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
      rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, e]
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have e : a * a = 1 :=
        Subtype.ext (hS.mul_self_of_isElementaryAbelian hS.isElementaryAbelian_B1 _ ha)
      simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
      rw [← coe_mul, ← map_mul, e, map_one, coe_one]
  have hcard : Nat.card (H.map T.subtype) = 2 * (2 ^ f) ^ 4 := by
    rw [card_map_of_injective T.subtype_injective, hH, card_map_of_injective φ.injective,
      ← hS.card_B1]
    exact Nat.card_congr (subgroupOfEquivOfLe hS.B1_le_T).toEquiv
  rw [← comap_map_eq_self_of_injective T.subtype_injective H,
    (hS.card_le_of_le_T hHT hHe).2 hcard]
  rfl

theorem normalizer_T_le_normalizer_Q (hS : Setting h L η t Q T) :
    normalizer (T : Set G) ≤ normalizer (Q : Set G) := by
  intro n hn
  have hB : (miyamotoB1 h L η t).map (MulAut.conj n).toMonoidHom = miyamotoB1 h L η t := by
    have hXT : (miyamotoB1 h L η t).map (MulAut.conj n).toMonoidHom ≤ T := by
      rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.1 hn b).1 (hS.B1_le_T hb)
    have := hS.isElementaryAbelian_B1
    have hcard : Nat.card ((miyamotoB1 h L η t).map (MulAut.conj n).toMonoidHom) =
        2 * (2 ^ f) ^ 4 := by
      rw [card_map_of_injective (MulAut.conj n).injective, hS.card_B1]
    exact (hS.card_le_of_le_T hXT (CFSG.IsElementaryAbelian.map _)).2 hcard
  have hnB : ∀ b ∈ miyamotoB1 h L η t, n * b * n⁻¹ ∈ miyamotoB1 h L η t := fun b hb => by
    rw [← hB]
    exact ⟨b, hb, rfl⟩
  have hYT : Q.map (MulAut.conj n).toMonoidHom ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    exact (mem_normalizer_iff.1 hn q).1 (hS.Q_le_T hq)
  obtain ⟨hsq, hcomm⟩ := hS.Q_mod_B1
  have hcard : Nat.card (Q.map (MulAut.conj n).toMonoidHom) = 2 * (2 ^ f) ^ 6 := by
    rw [card_map_of_injective (MulAut.conj n).injective, hS.card_Q]
  have hY := (hS.card_le_of_mod_B1 hYT ?_ ?_).2 hcard
  · refine mem_normalizer_of_conj_le fun q hq => ?_
    rw [← hY]
    exact ⟨q, hq, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show n * q * n⁻¹ * (n * q * n⁻¹) = n * (q * q) * n⁻¹ by group]
    exact hnB _ (hsq q hq)
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show ⁅n * q * n⁻¹, n * q' * n⁻¹⁆ = n * ⁅q, q'⁆ * n⁻¹ by
      simp only [commutatorElement_def]
      group]
    exact hnB _ (hcomm q hq q' hq')

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
