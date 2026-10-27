module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H]

theorem inv_mul_mul_pow (g u : H) (n : ℕ) : (g⁻¹ * u * g) ^ n = g⁻¹ * u ^ n * g := by
  have h := conj_pow (a := g⁻¹) (b := u) (i := n)
  rwa [inv_inv] at h

theorem eq_one_of_mem_of_pow_two_pow {D : Subgroup H} (hD : Odd (Nat.card D)) {x : H}
    (hx : x ∈ D) {a : ℕ} (h : x ^ 2 ^ a = 1) : x = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hD.coprime_two_right.pow_right a)
    (D.orderOf_dvd_natCard hx) (orderOf_dvd_of_pow_eq_one h))

theorem conj_mem_of_normal_subgroupOf {D C : Subgroup H} (hDC : D ≤ C)
    (hDn : (D.subgroupOf C).Normal) {c x : H} (hc : c ∈ C) (hx : x ∈ D) : c * x * c⁻¹ ∈ D :=
  mem_subgroupOf.mp (hDn.conj_mem ⟨x, hDC hx⟩ (mem_subgroupOf.mpr hx) ⟨c, hc⟩)

theorem conjugate_sup (A B : Subgroup H) (g : H) :
    conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g := by
  unfold conjugate
  exact map_sup A B _

theorem conjugate_injective {A B : Subgroup H} {g : H} (h : conjugate A g = conjugate B g) :
    A = B := by
  rw [← conjugate_conjugate_inv A g, h, conjugate_conjugate_inv]

theorem conjugate_conjugate_comm (X : Subgroup H) {d t : H} (h : d * t = t * d) :
    conjugate (conjugate X t) d = conjugate (conjugate X d) t := by
  rw [conjugate_conjugate, conjugate_conjugate, h]

theorem conjugate_conjugate_self_of_mul_self {X : Subgroup H} {t : H} (ht : t * t = 1) :
    conjugate (conjugate X t) t = X := by
  rw [conjugate_conjugate, ht, conjugate_one]

theorem conjugate_mul_mem_pair {X : Subgroup H} {t g h : H} (ht : t * t = 1)
    (hht : h * t = t * h) (hg : conjugate X g = X ∨ conjugate X g = conjugate X t)
    (hh : conjugate X h = X ∨ conjugate X h = conjugate X t) :
    conjugate X (g * h) = X ∨ conjugate X (g * h) = conjugate X t := by
  rw [← conjugate_conjugate]
  rcases hg with hg | hg <;> rw [hg]
  · exact hh
  · rw [conjugate_conjugate_comm X hht]
    rcases hh with hh | hh <;> rw [hh]
    · exact Or.inr rfl
    · exact Or.inl (conjugate_conjugate_self_of_mul_self ht)

theorem exists_pow_mul_self_eq {d : H} (hd : Odd (orderOf d)) : ∃ n : ℕ, (d * d) ^ n = d := by
  obtain ⟨j, hj⟩ := hd
  refine ⟨j + 1, ?_⟩
  rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf d + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

variable [Finite H]

theorem pair_le_centralizer_pair {X Y : Subgroup H} (hX : IsComponent X) (hY : IsComponent Y)
    {t : H} (ht : t * t = 1) (h1 : Y ≠ X) (h2 : Y ≠ conjugate X t) :
    X ⊔ conjugate X t ≤ centralizer ((Y ⊔ conjugate Y t : Subgroup H) : Set H) := by
  have h := sSup_le_centralizer_sSup (S := {X, conjugate X t}) (S' := {Y, conjugate Y t})
    (by
      intro N hN
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
      rcases hN with hN | hN <;> rw [hN]
      · exact hX
      · exact isComponent_conjugate hX t)
    (by
      intro N hN
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
      rcases hN with hN | hN <;> rw [hN]
      · exact hY
      · exact isComponent_conjugate hY t)
    (by
      intro N hN hN'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN hN'
      rcases hN with hN | hN <;> rcases hN' with h | h <;> rw [hN] at h
      · exact h1 h.symm
      · exact h2 (by rw [h, conjugate_conjugate_self_of_mul_self ht])
      · exact h2 h.symm
      · exact h1 (conjugate_injective h).symm)
  rwa [sSup_pair, sSup_pair] at h

theorem exists_two_power_lift {K : Type*} [Group K] [Finite K] {N : Subgroup K} [N.Normal]
    {v : K ⧸ N} (hv : orderOf v = 2) :
    ∃ k : K, QuotientGroup.mk' N k = v ∧ ∃ a : ℕ, k ^ 2 ^ a = 1 := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N v
  obtain ⟨a, m, hm, hw⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  refine ⟨w ^ m, ?_, a, ?_⟩
  · obtain ⟨j, rfl⟩ := hm
    have h2 : QuotientGroup.mk' N w ^ 2 = 1 := by
      rw [← hv]
      exact pow_orderOf_eq_one _
    rw [map_pow, pow_succ, pow_mul, h2, one_pow, one_mul]
  · rw [← pow_mul, mul_comm, ← hw, pow_orderOf_eq_one]

omit [Finite H] in
theorem exists_not_commute_of_mk_ne_one {K : Subgroup H} {k : K}
    (hk : QuotientGroup.mk' (center K) k ≠ 1) : ∃ k' ∈ K, (k : H) * k' ≠ k' * k := by
  by_contra hall
  push Not at hall
  apply hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
  intro g
  exact Subtype.ext (hall g g.2).symm

theorem exists_two_element_witness {K : Subgroup H} (hK : IsComponent K)
    (heven : Even (Nat.card (K ⧸ center K))) {t : H} (ht : t * t = 1) :
    ∃ u ∈ K ⊔ conjugate K t, (∃ a : ℕ, u ^ 2 ^ a = 1) ∧ (∃ k ∈ K, u * k ≠ k * u) ∧
      u⁻¹ * (t⁻¹ * u * t) ∈ (center K).map K.subtype := by
  have hdvd : 2 ∣ Nat.card (K ⧸ center K) := even_iff_two_dvd.mp heven
  have hne : ∀ {v : K ⧸ center K}, orderOf v = 2 → v ≠ 1 := by
    rintro v hv rfl
    rw [orderOf_one] at hv
    omega
  by_cases heq : conjugate K t = K
  ·
    have heq' : K.map ((MulAut.conj t⁻¹ : MulAut H) : H →* H) = K := heq
    let φ : MulAut K := ((MulAut.conj t⁻¹).subgroupMap K).trans (MulEquiv.subgroupCongr heq')
    have hφ : ∀ k : K, (φ k : H) = t⁻¹ * k * t := fun k => by
      change t⁻¹ * (k : H) * t⁻¹⁻¹ = _
      rw [inv_inv]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hφinv : Function.Involutive φ := fun k => Subtype.ext (by
      rw [hφ, hφ, htinv]
      calc t * (t * (k : H) * t) * t = (t * t) * k * (t * t) := by group
        _ = k := by rw [ht, one_mul, mul_one])
    have hα : Function.Involutive (PerfectAutomorphisms.onCenterQuotient φ) := by
      intro x
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
      rw [PerfectAutomorphisms.onCenterQuotient_apply_mk,
        PerfectAutomorphisms.onCenterQuotient_apply_mk, hφinv]
    obtain ⟨v, hv, hαv⟩ := InvolutionFixedPoints.exists_fixed_involution hdvd _ hα
    obtain ⟨k, hkv, a, hka⟩ := exists_two_power_lift hv
    have hk1 : QuotientGroup.mk' (center K) k ≠ 1 := by
      rw [hkv]
      exact hne hv
    obtain ⟨k', hk', hkk'⟩ := exists_not_commute_of_mk_ne_one hk1
    have hcen : k⁻¹ * φ k ∈ center K := by
      rw [← QuotientGroup.ker_mk' (center K), MonoidHom.mem_ker, map_mul, map_inv,
        ← PerfectAutomorphisms.onCenterQuotient_apply_mk, hkv, hαv, inv_mul_cancel]
    refine ⟨k, mem_sup_left k.2, ⟨a, ?_⟩, ⟨k', hk', hkk'⟩, ⟨k⁻¹ * φ k, hcen, ?_⟩⟩
    · have h := congrArg Subtype.val hka
      simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using h
    · change ((k⁻¹ * φ k : K) : H) = _
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    obtain ⟨k, hkv, a, hka⟩ := exists_two_power_lift hv
    have hk1 : QuotientGroup.mk' (center K) k ≠ 1 := by
      rw [hkv]
      exact hne hv
    obtain ⟨k₀, hk₀, hkk₀⟩ := exists_not_commute_of_mk_ne_one hk1
    have hcomm := (distinct_components_commute (isComponent_conjugate hK t) hK).resolve_left heq
    have hk' : t⁻¹ * (k : H) * t ∈ conjugate K t := conj_mem_conjugate k.2 t
    have hk'c : t⁻¹ * (k : H) * t ∈ centralizer (K : Set H) :=
      commutator_eq_bot_iff_le_centralizer.mp hcomm hk'
    have hkk' : Commute (k : H) (t⁻¹ * k * t) := mem_centralizer_iff.mp hk'c k k.2
    have hka' : (k : H) ^ 2 ^ a = 1 := by
      have h := congrArg Subtype.val hka
      simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using h
    refine ⟨(k : H) * (t⁻¹ * k * t), mul_mem_sup k.2 hk', ⟨a, ?_⟩,
      ⟨k₀, hk₀, fun h => hkk₀ ?_⟩, ?_⟩
    · rw [hkk'.mul_pow, inv_mul_mul_pow, hka', mul_one, inv_mul_cancel, one_mul]
    · have hk₀' : Commute k₀ (t⁻¹ * (k : H) * t) := mem_centralizer_iff.mp hk'c k₀ hk₀
      calc (k : H) * k₀ = (k : H) * (k₀ * (t⁻¹ * k * t)) * (t⁻¹ * k * t)⁻¹ := by group
        _ = (k : H) * ((t⁻¹ * k * t) * k₀) * (t⁻¹ * k * t)⁻¹ := by rw [hk₀'.eq]
        _ = (k * (t⁻¹ * k * t)) * k₀ * (t⁻¹ * k * t)⁻¹ := by group
        _ = k₀ * (k * (t⁻¹ * k * t)) * (t⁻¹ * k * t)⁻¹ := by rw [h]
        _ = k₀ * k := by group
    · have hfix : t⁻¹ * ((k : H) * (t⁻¹ * k * t)) * t = (k : H) * (t⁻¹ * k * t) := by
        calc t⁻¹ * ((k : H) * (t⁻¹ * k * t)) * t
            = (t⁻¹ * k * t) * ((t * t)⁻¹ * k * (t * t)) := by group
          _ = (t⁻¹ * k * t) * k := by rw [ht, inv_one, one_mul, mul_one]
          _ = (k : H) * (t⁻¹ * k * t) := hkk'.eq.symm
      rw [hfix, inv_mul_cancel]
      exact one_mem _

omit [Finite H] in
theorem inv_mul_conj_eq {u u₁ u₂ d : H} (h₁ : u₁ = d⁻¹ * u * d) (h₂ : u₂ = d⁻¹ * u₁ * d) :
    (u⁻¹ * u₁)⁻¹ * (d⁻¹ * (u⁻¹ * u₁) * d) = u₁⁻¹ * u * u₁⁻¹ * u₂ := by
  subst h₁ h₂
  group

theorem odd_fixed_centralizer_normalizes_even_layer_components {t : H} (ht : orderOf t = 2)
    {D : Subgroup H} (hDC : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal) (hDodd : Odd (Nat.card D))
    (hDZ : ⁅D, (center (layer H)).map (layer H).subtype⁆ = ⊥)
    (heven : ∀ K : Subgroup H, IsComponent K → Even (Nat.card (K ⧸ center K))) :
    ∀ K : Subgroup H, IsComponent K → D ≤ normalizer (K : Set H) := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hdt : ∀ d ∈ D, d * t = t * d := fun d hd => mem_centralizer_singleton_iff.mp (hDC hd)
  have hodd : ∀ X : Subgroup H, ∀ d ∈ D,
      (conjugate X (d * d) = X ∨ conjugate X (d * d) = conjugate X t) →
      conjugate X d = X ∨ conjugate X d = conjugate X t := by
    intro X d hd h2
    have hdd : d * d * t = t * (d * d) := by
      rw [mul_assoc, hdt d hd, ← mul_assoc, hdt d hd, mul_assoc]
    have hpow : ∀ n : ℕ, conjugate X ((d * d) ^ n) = X ∨
        conjugate X ((d * d) ^ n) = conjugate X t := by
      intro n
      induction n with
      | zero => exact Or.inl (by rw [pow_zero, conjugate_one])
      | succ n ih =>
        rw [pow_succ]
        exact conjugate_mul_mem_pair htt hdd ih h2
    obtain ⟨n, hn⟩ := exists_pow_mul_self_eq (hDodd.of_dvd_nat (D.orderOf_dvd_natCard hd))
    rw [← hn]
    exact hpow n
  have hpair : ∀ X : Subgroup H, IsComponent X → ∀ d ∈ D,
      conjugate X d = X ∨ conjugate X d = conjugate X t := by
    intro X hX d hd
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    obtain ⟨u, huX, ⟨a, hua⟩, ⟨k₀, hk₀, hk₀u⟩, hz⟩ :=
      exists_two_element_witness hX (heven X hX) htt
    have hzE := center_component_le_center_layer hX hz
    obtain ⟨-, hzc⟩ := (mem_map_center_iff _).mp hzE
    have hdz : u⁻¹ * (t⁻¹ * u * t) * d = d * (u⁻¹ * (t⁻¹ * u * t)) :=
      mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDZ hd) _ hzE
    set z := u⁻¹ * (t⁻¹ * u * t) with hzdef
    have hX₁ := isComponent_conjugate hX d
    have hX₂ := isComponent_conjugate hX₁ d
    have hne3 : conjugate (conjugate X d) d ≠ X := by
      intro h
      apply hne1
      have h' := hodd X d hd (Or.inl (by rw [← conjugate_conjugate, h]))
      exact h'.resolve_right hne2
    have hne4 : conjugate (conjugate X d) d ≠ conjugate X t := by
      intro h
      apply hne1
      have h' := hodd X d hd (Or.inr (by rw [← conjugate_conjugate, h]))
      exact h'.resolve_right hne2
    have hne5 : conjugate (conjugate X d) d ≠ conjugate X d := fun h =>
      hne1 (conjugate_injective h)
    have hne6 : conjugate (conjugate X d) d ≠ conjugate (conjugate X d) t := fun h =>
      hne2 (conjugate_injective (h.trans (conjugate_conjugate_comm X (hdt d hd)).symm))
    have hc01 := pair_le_centralizer_pair hX hX₁ htt hne1 hne2
    have hc02 := pair_le_centralizer_pair hX hX₂ htt hne3 hne4
    have hc12 := pair_le_centralizer_pair hX₁ hX₂ htt hne5 hne6
    have hu₁ : d⁻¹ * u * d ∈ conjugate X d ⊔ conjugate (conjugate X d) t := by
      rw [← conjugate_conjugate_comm X (hdt d hd), ← conjugate_sup]
      exact conj_mem_conjugate huX d
    have hu₂ : d⁻¹ * (d⁻¹ * u * d) * d ∈
        conjugate (conjugate X d) d ⊔ conjugate (conjugate (conjugate X d) d) t := by
      rw [← conjugate_conjugate_comm (conjugate X d) (hdt d hd), ← conjugate_sup]
      exact conj_mem_conjugate hu₁ d
    set u₁ := d⁻¹ * u * d with hu₁def
    set u₂ := d⁻¹ * u₁ * d with hu₂def
    have hcu₁ : Commute u u₁ := (mem_centralizer_iff.mp (hc01 huX) u₁ hu₁).symm
    have hcu₂ : Commute u u₂ := (mem_centralizer_iff.mp (hc02 huX) u₂ hu₂).symm
    have hc₁₂ : Commute u₁ u₂ := (mem_centralizer_iff.mp (hc12 hu₁) u₂ hu₂).symm
    have hk₀X : k₀ ∈ X ⊔ conjugate X t := mem_sup_left hk₀
    have hk₁ : Commute k₀ u₁ := (mem_centralizer_iff.mp (hc01 hk₀X) u₁ hu₁).symm
    have hk₂ : Commute k₀ u₂ := (mem_centralizer_iff.mp (hc02 hk₀X) u₂ hu₂).symm
    have hu₁a : u₁ ^ 2 ^ a = 1 := by
      rw [hu₁def, inv_mul_mul_pow, hua, mul_one, inv_mul_cancel]
    have hu₂a : u₂ ^ 2 ^ a = 1 := by
      rw [hu₂def, inv_mul_mul_pow, hu₁a, mul_one, inv_mul_cancel]
    have hEsup : ∀ Y : Subgroup H, IsComponent Y → Y ⊔ conjugate Y t ≤ layer H := fun Y hY =>
      sup_le (component_le_layer hY) (component_le_layer (isComponent_conjugate hY t))
    have hwE : u⁻¹ * u₁ ∈ layer H :=
      mul_mem (inv_mem (hEsup X hX huX)) (hEsup _ hX₁ hu₁)
    have hw : u⁻¹ * u₁ ∈ centralizer ({t} : Set H) := by
      rw [mem_centralizer_singleton_iff_conj]
      have h1 : t⁻¹ * u * t = u * z := by rw [hzdef]; group
      have hdt' := hdt d hd
      have h2 : t⁻¹ * u₁ * t = u₁ * z := by
        calc t⁻¹ * u₁ * t = (d * t)⁻¹ * u * (d * t) := by rw [hu₁def]; group
          _ = (t * d)⁻¹ * u * (t * d) := by rw [hdt']
          _ = d⁻¹ * (t⁻¹ * u * t) * d := by group
          _ = d⁻¹ * u * d * (d⁻¹ * (z * d)) := by rw [h1]; group
          _ = d⁻¹ * u * d * (d⁻¹ * (d * z)) := by rw [hdz]
          _ = u₁ * z := by rw [inv_mul_cancel_left, hu₁def]
      have hzw : Commute z (u⁻¹ * u₁) := (mem_centralizer_iff.mp hzc _ hwE).symm
      calc t⁻¹ * (u⁻¹ * u₁) * t = (t⁻¹ * u * t)⁻¹ * (t⁻¹ * u₁ * t) := by group
        _ = z⁻¹ * ((u⁻¹ * u₁) * z) := by rw [h1, h2]; group
        _ = z⁻¹ * (z * (u⁻¹ * u₁)) := by rw [← hzw.eq]
        _ = u⁻¹ * u₁ := by group
    have hxD : (u⁻¹ * u₁)⁻¹ * (d⁻¹ * (u⁻¹ * u₁) * d) ∈ D := by
      have h := mul_mem (conj_mem_of_normal_subgroupOf hDC hDn (inv_mem hw) (inv_mem hd)) hd
      rwa [show (u⁻¹ * u₁)⁻¹ * d⁻¹ * (u⁻¹ * u₁)⁻¹⁻¹ * d =
        (u⁻¹ * u₁)⁻¹ * (d⁻¹ * (u⁻¹ * u₁) * d) by group] at h
    rw [inv_mul_conj_eq hu₁def hu₂def] at hxD
    have hx : u₁⁻¹ * u * u₁⁻¹ * u₂ = u * (u₁⁻¹ * u₁⁻¹ * u₂) := by
      rw [hcu₁.inv_right.symm.eq]
      group
    rw [hx] at hxD
    have hy : Commute u (u₁⁻¹ * u₁⁻¹ * u₂) :=
      (hcu₁.inv_right.mul_right hcu₁.inv_right).mul_right hcu₂
    have hxa : (u * (u₁⁻¹ * u₁⁻¹ * u₂)) ^ 2 ^ a = 1 := by
      rw [hy.mul_pow, (hc₁₂.inv_left.mul_left hc₁₂.inv_left).mul_pow,
        (Commute.refl u₁⁻¹).mul_pow, inv_pow, hua, hu₁a, hu₂a]
      simp
    have hone := eq_one_of_mem_of_pow_two_pow hDodd hxD hxa
    apply hk₀u
    have hky : Commute k₀ (u₁⁻¹ * u₁⁻¹ * u₂) :=
      (hk₁.inv_right.mul_right hk₁.inv_right).mul_right hk₂
    rw [eq_inv_of_mul_eq_one_left hone]
    exact hky.inv_right.eq.symm
  intro K hK d hd
  have hKd : conjugate K d = K := by
    rcases hpair K hK d hd with h | h
    · exact h
    · have h2 : conjugate K (d * d) = K := by
        rw [← conjugate_conjugate, h, conjugate_conjugate_comm K (hdt d hd), h,
          conjugate_conjugate_self_of_mul_self htt]
      have hpow : ∀ n : ℕ, conjugate K ((d * d) ^ n) = K := by
        intro n
        induction n with
        | zero => rw [pow_zero, conjugate_one]
        | succ n ih => rw [pow_succ, ← conjugate_conjugate, ih, h2]
      obtain ⟨n, hn⟩ := exists_pow_mul_self_eq (hDodd.of_dvd_nat (D.orderOf_dvd_natCard hd))
      rw [← hn]
      exact hpow n
  rw [mem_normalizer_iff]
  intro h
  rw [← mem_conjugate_iff, hKd]

end CFSG.ComponentClassification.UnbalancedLayer
