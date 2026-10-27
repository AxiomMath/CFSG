module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_left_of_le_normalizer {K A : Subgroup G}
    (h : A ≤ normalizer (K : Set G)) : ⁅K, A⁆ ≤ K := by
  rw [commutator_le]
  intro k hk a ha
  rw [show ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) by rw [commutatorElement_def]; group]
  exact mul_mem hk ((mem_normalizer_iff.mp (h ha) k⁻¹).mp (inv_mem hk))

theorem le_normalizer_commutator (K A : Subgroup G) :
    K ≤ normalizer ((⁅K, A⁆ : Subgroup G) : Set G) := by
  have key : ∀ u ∈ K, ∀ x ∈ ⁅K, A⁆, u * x * u⁻¹ ∈ ⁅K, A⁆ := by
    intro u hu x hx
    have hle : ⁅K, A⁆ ≤ ⁅K, A⁆.comap (MulAut.conj u).toMonoidHom := by
      rw [commutator_le]
      intro v hv a ha
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show u * ⁅v, a⁆ * u⁻¹ = ⁅u * v, a⁆ * ⁅u, a⁆⁻¹ by simp only [commutatorElement_def]; group]
      exact mul_mem (commutator_mem_commutator (mul_mem hu hv) ha)
        (inv_mem (commutator_mem_commutator hu ha))
    have h1 := mem_comap.mp (hle hx)
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  intro u hu
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key u hu x, fun hx => ?_⟩
  have h := key u⁻¹ (inv_mem hu) _ hx
  rwa [show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x by group] at h

theorem commutator_eq_self_or_eq_bot {K A : Subgroup G} (hK : IsComponent K)
    (h : A ≤ normalizer (K : Set G)) : ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ := by
  have hle := commutator_le_left_of_le_normalizer h
  have hn : (⁅K, A⁆.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).mpr (le_normalizer_commutator K A)
  rcases quasisimple_normal_subgroups hK.1 hn with htop | hcen
  · exact Or.inl (le_antisymm hle (subgroupOf_eq_top.mp htop))
  · right
    apply perfect_double_commutator hK.1.1
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro k hk
    have hxc := hcen (show (⟨x, hle hx⟩ : K) ∈ ⁅K, A⁆.subgroupOf K from hx)
    exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨k, hk⟩)

variable [Finite G]

theorem exists_two_element_not_mem_center {K : Subgroup G}
    (heven : Even (Nat.card (K ⧸ center K))) : ∃ k : K, k ∉ center K ∧ ∃ a : ℕ, k ^ 2 ^ a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  obtain ⟨k, hkv, a, hka⟩ := exists_two_power_lift hv
  refine ⟨k, fun hk => ?_, a, hka⟩
  have h1 : QuotientGroup.mk' (center K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
  rw [hkv] at h1
  rw [h1, orderOf_one] at hv
  omega

theorem commutator_eq_bot_of_hom {s : G} {D : Subgroup G} (hDC : D ≤ centralizer ({s} : Set G))
    (hDn : (D.subgroupOf (centralizer ({s} : Set G))).Normal) (hDodd : Odd (Nat.card D))
    {K : Subgroup G} (hK : IsComponent K) (heven : Even (Nat.card (K ⧸ center K)))
    (hDK : D ≤ normalizer (K : Set G)) (φ : K →* G)
    (hφC : ∀ k : K, φ k ∈ centralizer ({s} : Set G))
    (hφcomm : ∀ k₁ k₂ : K, ∀ d ∈ D, (k₂ : G) = ⁅(k₁ : G), d⁆ → φ k₂ = ⁅φ k₁, d⁆)
    (hφker : ∀ k : K, φ k = 1 → k ∈ center K) : ⁅K, D⁆ = ⊥ := by
  let M : Subgroup K := D.comap φ
  have hMn : M.Normal := ⟨fun m hm k => by
    change φ (k * m * k⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_of_normal_subgroupOf hDC hDn (hφC k) hm⟩
  rcases quasisimple_normal_subgroups hK.1 hMn with hM | hM
  · exfalso
    obtain ⟨k, hk, a, hka⟩ := exists_two_element_not_mem_center heven
    have hkM : k ∈ M := hM ▸ mem_top k
    have hpow : φ k ^ 2 ^ a = 1 := by rw [← map_pow, hka, map_one]
    exact hk (hφker k (eq_one_of_mem_of_pow_two_pow hDodd hkM hpow))
  · apply perfect_double_commutator hK.1.1
    rw [commutator_eq_bot_iff_le_centralizer]
    have hcen : ⁅K, D⁆ ≤ (center K).map K.subtype := by
      rw [commutator_le]
      intro k hk d hd
      have hkd : ⁅k, d⁆ ∈ K :=
        commutator_le_left_of_le_normalizer hDK (commutator_mem_commutator hk hd)
      have hmem : (⟨⁅k, d⁆, hkd⟩ : K) ∈ M := by
        change φ ⟨⁅k, d⁆, hkd⟩ ∈ D
        rw [hφcomm ⟨k, hk⟩ ⟨⁅k, d⁆, hkd⟩ d hd rfl, commutatorElement_def]
        exact mul_mem (conj_mem_of_normal_subgroupOf hDC hDn (hφC _) hd) (inv_mem hd)
      exact ⟨_, hM hmem, rfl⟩
    intro x hx
    rw [mem_centralizer_iff]
    intro k hk
    obtain ⟨z, hz, rfl⟩ := hcen hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)

theorem commutator_eq_bot_of_le_centralizer {s : G} {D : Subgroup G}
    (hDC : D ≤ centralizer ({s} : Set G))
    (hDn : (D.subgroupOf (centralizer ({s} : Set G))).Normal) (hDodd : Odd (Nat.card D))
    {K : Subgroup G} (hK : IsComponent K) (heven : Even (Nat.card (K ⧸ center K)))
    (hDK : D ≤ normalizer (K : Set G)) (hKs : K ≤ centralizer ({s} : Set G)) : ⁅K, D⁆ = ⊥ :=
  commutator_eq_bot_of_hom hDC hDn hDodd hK heven hDK K.subtype (fun k => hKs k.2)
    (fun _ _ _ _ h => h) (fun k hk => by
      rw [show k = 1 from Subtype.ext hk]
      exact one_mem _)

theorem commutator_eq_bot_of_conjugate_ne {s : G} (hs : s * s = 1) {D : Subgroup G}
    (hDC : D ≤ centralizer ({s} : Set G))
    (hDn : (D.subgroupOf (centralizer ({s} : Set G))).Normal) (hDodd : Odd (Nat.card D))
    {K : Subgroup G} (hK : IsComponent K) (heven : Even (Nat.card (K ⧸ center K)))
    (hDK : D ≤ normalizer (K : Set G)) (hDKs : D ≤ normalizer (conjugate K s : Set G))
    (hne : conjugate K s ≠ K) : ⁅K, D⁆ = ⊥ := by
  have hcomm : ⁅conjugate K s, K⁆ = ⊥ :=
    (distinct_components_commute (isComponent_conjugate hK s) hK).resolve_left hne
  have hc : ∀ x ∈ conjugate K s, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hx) y hy).symm
  have hsK : ∀ k ∈ K, s⁻¹ * k * s ∈ conjugate K s := fun k hk => conj_mem_conjugate hk s
  let φ : K →* G := MonoidHom.mk' (fun k => (k : G) * (s⁻¹ * k * s)) (by
    intro a b
    simp only [Subgroup.coe_mul]
    have h1 : (b : G) * (s⁻¹ * a * s) = (s⁻¹ * a * s) * b := (hc _ (hsK a a.2) b b.2).symm
    calc (a : G) * b * (s⁻¹ * (a * b) * s) = a * (b * (s⁻¹ * a * s)) * (s⁻¹ * b * s) := by
          group
      _ = a * ((s⁻¹ * a * s) * b) * (s⁻¹ * b * s) := by rw [h1]
      _ = a * (s⁻¹ * a * s) * (b * (s⁻¹ * b * s)) := by group)
  have hφ : ∀ k : K, φ k = (k : G) * (s⁻¹ * k * s) := fun _ => rfl
  have hφC : ∀ k : K, φ k ∈ centralizer ({s} : Set G) := by
    intro k
    rw [mem_centralizer_singleton_iff_conj, hφ]
    calc s⁻¹ * ((k : G) * (s⁻¹ * k * s)) * s = (s⁻¹ * k * s) * ((s * s)⁻¹ * k * (s * s)) := by
          group
      _ = (s⁻¹ * k * s) * k := by rw [hs, inv_one, one_mul, mul_one]
      _ = (k : G) * (s⁻¹ * k * s) := hc _ (hsK k k.2) k k.2
  have hφcomm : ∀ k₁ k₂ : K, ∀ d ∈ D, (k₂ : G) = ⁅(k₁ : G), d⁆ → φ k₂ = ⁅φ k₁, d⁆ := by
    intro k₁ k₂ d hd hk₂
    rw [hφ, hφ, hk₂]
    have hds : s⁻¹ * d * s = d := mem_centralizer_singleton_iff_conj.mp (hDC hd)
    set k : G := (k₁ : G) with hkdef
    have hk : k ∈ K := k₁.2
    set k' : G := s⁻¹ * k * s with hk'def
    have hk' : k' ∈ conjugate K s := hsK k hk
    have ha : d * k⁻¹ * d⁻¹ ∈ K := (mem_normalizer_iff.mp (hDK hd) k⁻¹).mp (inv_mem hk)
    have hb : d * k'⁻¹ * d⁻¹ ∈ conjugate K s :=
      (mem_normalizer_iff.mp (hDKs hd) k'⁻¹).mp (inv_mem hk')
    have hconj : s⁻¹ * ⁅k, d⁆ * s = ⁅k', d⁆ := by
      rw [conj_commutatorElement, hds, hk'def]
    rw [hconj]
    have h1 : (d * k⁻¹ * d⁻¹) * k' = k' * (d * k⁻¹ * d⁻¹) := (hc _ hk' _ ha).symm
    have h2 : (d * k⁻¹ * d⁻¹) * (d * k'⁻¹ * d⁻¹) = (d * k'⁻¹ * d⁻¹) * (d * k⁻¹ * d⁻¹) :=
      (hc _ hb _ ha).symm
    calc ⁅k, d⁆ * ⁅k', d⁆ = k * ((d * k⁻¹ * d⁻¹) * k') * (d * k'⁻¹ * d⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = k * (k' * (d * k⁻¹ * d⁻¹)) * (d * k'⁻¹ * d⁻¹) := by rw [h1]
      _ = k * k' * ((d * k⁻¹ * d⁻¹) * (d * k'⁻¹ * d⁻¹)) := by group
      _ = k * k' * ((d * k'⁻¹ * d⁻¹) * (d * k⁻¹ * d⁻¹)) := by rw [h2]
      _ = ⁅k * k', d⁆ := by
          simp only [commutatorElement_def]
          group
  have hφker : ∀ k : K, φ k = 1 → k ∈ center K := by
    intro k hk1
    rw [hφ] at hk1
    have hkK : (k : G) ∈ conjugate K s := by
      rw [eq_inv_of_mul_eq_one_left hk1]
      exact inv_mem (hsK k k.2)
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hc _ hkK g g.2).symm
  exact commutator_eq_bot_of_hom hDC hDn hDodd hK heven hDK φ hφC hφcomm hφker

theorem active_component {s : G} (hs : s * s = 1) {D : Subgroup G}
    (hDC : D ≤ centralizer ({s} : Set G))
    (hDn : (D.subgroupOf (centralizer ({s} : Set G))).Normal) (hDodd : Odd (Nat.card D))
    {K : Subgroup G} (hK : IsComponent K) (heven : Even (Nat.card (K ⧸ center K)))
    (hDK : D ≤ normalizer (K : Set G)) (hDKs : D ≤ normalizer (conjugate K s : Set G))
    (hne : ⁅K, D⁆ ≠ ⊥) : s ∈ normalizer (K : Set G) ∧ ⁅K, D⁆ = K ∧ ⁅K, zpowers s⁆ = K := by
  have hKs : conjugate K s = K := by
    by_contra h
    exact hne (commutator_eq_bot_of_conjugate_ne hs hDC hDn hDodd hK heven hDK hDKs h)
  have hsN : s ∈ normalizer (K : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    rw [← mem_conjugate_iff, hKs]
  refine ⟨hsN, (commutator_eq_self_or_eq_bot hK hDK).resolve_right hne, ?_⟩
  refine (commutator_eq_self_or_eq_bot hK (zpowers_le.mpr hsN)).resolve_right fun hbot => hne ?_
  apply commutator_eq_bot_of_le_centralizer hDC hDn hDodd hK heven hDK
  rw [← centralizer_zpowers_eq, ← commutator_eq_bot_iff_le_centralizer]
  exact hbot

end CFSG.ComponentClassification.UnbalancedLayer
