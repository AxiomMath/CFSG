module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Inn

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem mem_normalizer_of_conjugate_eq {A : Type} [Group A] {S : Subgroup A} {x : A}
    (h : CFSG.conjugate S x = S) : x ∈ normalizer (S : Set A) := by
  have h' : x⁻¹ ∈ normalizer (S : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show CFSG.conjugate S x = S
    exact h
  simpa using (Subgroup.inv_mem _ h')

private theorem l34g_pk2_central {A : Type} [Group A] [Finite A] {S : Subgroup A}
    (hS : SimpleFStarQuotient ↥S) {x g : A} (hcent : S ≤ centralizer ({x} : Set A))
    (hgc : ∀ c ∈ S ⊓ centralizer ({x} : Set A), Odd (orderOf c) → g * c = c * g) :
    ∀ s ∈ S, g * s = s * g := by
  intro s hs
  have hT : (centralizer ({g} : Set A)).subgroupOf S = ⊤ := by
    rw [eq_top_iff, ← l34g_closure_odd_eq_top hS, Subgroup.closure_le]
    intro y hy
    change y ∈ (centralizer ({g} : Set A)).subgroupOf S
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have hoddA : Odd (orderOf (y : A)) := by rwa [Subgroup.orderOf_coe]
    exact (hgc (y : A) ⟨y.2, hcent y.2⟩ hoddA).symm
  have hmem : (⟨s, hs⟩ : ↥S) ∈ (centralizer ({g} : Set A)).subgroupOf S := by
    rw [hT]; exact Subgroup.mem_top _
  exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hmem)).symm

private theorem l34g_pk2_orderOf_x {A : Type} [Group A] {S : Subgroup A} {x : A}
    (hx : x * x = 1) (hxN : x ∈ normalizer (S : Set A))
    (hcent : ¬ S ≤ centralizer ({x} : Set A)) :
    orderOf (S.normalizerMonoidHom ⟨x, hxN⟩) = 2 := by
  rw [orderOf_eq_prime_iff]
  constructor
  · rw [pow_two]
    change S.normalizerMonoidHom ⟨x, hxN⟩ * S.normalizerMonoidHom ⟨x, hxN⟩ = 1
    rw [← map_mul]
    have hxx : (⟨x, hxN⟩ : normalizer (S : Set A)) * ⟨x, hxN⟩ = 1 := by
      apply Subtype.ext
      simpa using hx
    rw [hxx, map_one]
  · intro ha1
    obtain ⟨s, hs, hsc⟩ : ∃ s ∈ S, s ∉ centralizer ({x} : Set A) := by
      by_contra h
      apply hcent
      intro t ht
      by_contra htc
      exact h ⟨t, ht, htc⟩
    apply hsc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * (s : A) * x⁻¹ = (s : A) := by
      have h : ((S.normalizerMonoidHom ⟨x, hxN⟩) ⟨s, hs⟩ : ↥S) = ⟨s, hs⟩ := by
        rw [ha1]; rfl
      have h' := congrArg (fun u : ↥S => (u : A)) h
      change ((S.normalizerMonoidHom ⟨x, hxN⟩) ⟨s, hs⟩ : A) = (s : A) at h'
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨x, hxN⟩ ⟨s, hs⟩] at h'
      exact h'
    calc (s : A) * x = (x * (s : A) * x⁻¹) * x := by rw [h1]
      _ = x * (s : A) := by group

private theorem l34g_pk2_fix_of_odd {A : Type} [Group A] {S : Subgroup A} {x g : A}
    (hxN : x ∈ normalizer (S : Set A)) (hgN : g ∈ normalizer (S : Set A))
    (hgc : ∀ c ∈ S ⊓ centralizer ({x} : Set A), Odd (orderOf c) → g * c = c * g) :
    ∀ t : ↥S, (S.normalizerMonoidHom ⟨x, hxN⟩) t = t → Odd (orderOf t) →
      (S.normalizerMonoidHom ⟨g, hgN⟩) t = t := by
  intro t hfix hodd
  have htA : (t : A) ∈ centralizer ({x} : Set A) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun u : ↥S => (u : A)) hfix
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨x, hxN⟩ t] at h
    calc (t : A) * x = (x * (t : A) * x⁻¹) * x := by rw [h]
      _ = x * (t : A) := by group
  have hoddA : Odd (orderOf (t : A)) := by rwa [Subgroup.orderOf_coe]
  have hgct : g * (t : A) = (t : A) * g := hgc (t : A) ⟨t.2, htA⟩ hoddA
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨g, hgN⟩ t]
  calc g * (t : A) * g⁻¹ = (t : A) * g * g⁻¹ := by rw [hgct]
    _ = (t : A) := by group

private theorem l34g_pk2_pow3 {G : Type} [Group G] [Finite G] {a g' : G} {m : ℕ}
    (hga : g' * a = a * g') (hg'm : g' ^ 3 ^ m = 1) (hg' : g' ≠ 1) :
    orderOf (g' ^ (orderOf g' / 3)) = 3 ∧
      g' ^ (orderOf g' / 3) * a = a * g' ^ (orderOf g' / 3) := by
  have hord_dvd : orderOf g' ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hg'm
  obtain ⟨j, _hjm, hord_eq⟩ :=
    (Nat.dvd_prime_pow (p := 3) (by norm_num : Nat.Prime 3)).mp hord_dvd
  have hj : j ≠ 0 := by
    intro hj0
    exact hg' (orderOf_eq_one_iff.mp (by rw [hord_eq, hj0, pow_zero]))
  have h3dvd : 3 ∣ orderOf g' := by
    rw [hord_eq]
    exact dvd_pow_self 3 hj
  have hx0 : orderOf g' ≠ 0 := ne_of_gt (orderOf_pos g')
  exact ⟨orderOf_pow_orderOf_div hx0 h3dvd, Commute.pow_left hga (orderOf g' / 3)⟩

private theorem l34g_pk2_core {G : Type} [Group G] [Finite G] (hC3 : Asc82FactCent3)
    {Inn : Subgroup G} (hInnNormal : Inn.Normal) (hInnCent : centralizer (Inn : Set G) = ⊥)
    (hInnSimple : SimpleFStarQuotient ↥Inn) {a : G} (ha2 : orderOf a = 2)
    {g'' : G} (hg''3 : orderOf g'' = 3) (hcomm : g'' * a = a * g'')
    (hcentral : ∀ c ∈ Inn ⊓ centralizer ({a} : Set G), Odd (orderOf c) → g'' * c = c * g'') :
    False :=
  (hC3 G Inn hInnNormal hInnCent hInnSimple a ha2 g'' hg''3 hcomm) hcentral

private theorem l34g_pk2_aut_eq_one (hC3 : Asc82FactCent3) {S : Type} [Group S] [Finite S]
    (hc0 : center S = ⊥) (hS : SimpleFStarQuotient S) {a g' : MulAut S} {m : ℕ}
    (ha2 : orderOf a = 2) (hga : g' * a = a * g') (hg'm : g' ^ 3 ^ m = 1)
    (hfix : ∀ t : S, a t = t → Odd (orderOf t) → g' t = t) : g' = 1 := by
  by_contra hg'
  let g'' : MulAut S := g' ^ (orderOf g' / 3)
  have hpow := l34g_pk2_pow3 hga hg'm hg'
  have hg''3 : orderOf g'' = 3 := hpow.1
  have hcomm : g'' * a = a * g'' := hpow.2
  let Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range
  have hInnNormal : Inn.Normal := l34g_inn_normal S
  have hInnCent : centralizer (Inn : Set (MulAut S)) = ⊥ := l34g_inn_centralizer hc0
  have hInnSimple : SimpleFStarQuotient Inn := l34g_inn_simpleFStar hS
  have hcentral : ∀ c ∈ Inn ⊓ centralizer ({a} : Set (MulAut S)),
      Odd (orderOf c) → g'' * c = c * g'' := by
    intro c hc hodd
    obtain ⟨hcInn, hcCent⟩ := Subgroup.mem_inf.mp hc
    change c ∈ (MulAut.conj : S →* MulAut S).range at hcInn
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hcInn
    rw [← ht] at hcCent hodd ⊢
    have hca : MulAut.conj t * a = a * MulAut.conj t :=
      Subgroup.mem_centralizer_singleton_iff.mp hcCent
    have hfix_t : a t = t := (l34g_inn_commute_iff hc0 a t).mp hca
    have hodd_t : Odd (orderOf t) := by
      rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (l34g_conj_injective hc0) t]
      exact hodd
    have hg't : g' t = t := hfix t hfix_t hodd_t
    have hcomm_t : MulAut.conj t * g' = g' * MulAut.conj t :=
      (l34g_inn_commute_iff hc0 g' t).mpr hg't
    exact Commute.pow_left hcomm_t.symm (orderOf g' / 3)
  exact l34g_pk2_core hC3 hInnNormal hInnCent hInnSimple ha2 hg''3 hcomm hcentral

private theorem l34g_pk2_noncentral (hC3 : Asc82FactCent3) {A : Type} [Group A] [Finite A]
    {S : Subgroup A} (hS : SimpleFStarQuotient ↥S) {x : A} (hx : x * x = 1)
    (hxS : CFSG.conjugate S x = S) {g : A} {m : ℕ} (hg : g ^ 3 ^ m = 1)
    (hgS : CFSG.conjugate S g = S) (hgx : g * x = x * g)
    (hgc : ∀ c ∈ S ⊓ centralizer ({x} : Set A), Odd (orderOf c) → g * c = c * g)
    (hcent : ¬ S ≤ centralizer ({x} : Set A)) :
    ∀ s ∈ S, g * s = s * g := by
  have hc0 : center ↥S = ⊥ := (l34g_simple_of_simpleFStar hS).2
  have hxN : x ∈ normalizer (S : Set A) := mem_normalizer_of_conjugate_eq hxS
  have hgN : g ∈ normalizer (S : Set A) := mem_normalizer_of_conjugate_eq hgS
  have ha2 : orderOf (S.normalizerMonoidHom ⟨x, hxN⟩) = 2 := l34g_pk2_orderOf_x hx hxN hcent
  have hga : S.normalizerMonoidHom ⟨g, hgN⟩ * S.normalizerMonoidHom ⟨x, hxN⟩ =
      S.normalizerMonoidHom ⟨x, hxN⟩ * S.normalizerMonoidHom ⟨g, hgN⟩ := by
    rw [← map_mul, ← map_mul]
    have huv : (⟨g, hgN⟩ : normalizer (S : Set A)) * ⟨x, hxN⟩ =
        ⟨x, hxN⟩ * ⟨g, hgN⟩ := by
      apply Subtype.ext
      simpa using hgx
    rw [huv]
  have hg'm : (S.normalizerMonoidHom ⟨g, hgN⟩) ^ 3 ^ m = 1 := by
    rw [← map_pow]
    have hgg : (⟨g, hgN⟩ : normalizer (S : Set A)) ^ (3 ^ m) = 1 := by
      apply Subtype.ext
      simpa using hg
    rw [hgg, map_one]
  have hfix : ∀ t : ↥S, (S.normalizerMonoidHom ⟨x, hxN⟩) t = t → Odd (orderOf t) →
      (S.normalizerMonoidHom ⟨g, hgN⟩) t = t := l34g_pk2_fix_of_odd hxN hgN hgc
  have hg'1 : S.normalizerMonoidHom ⟨g, hgN⟩ = 1 :=
    l34g_pk2_aut_eq_one hC3 hc0 hS ha2 hga hg'm hfix
  intro s hs
  have h1 : ((S.normalizerMonoidHom ⟨g, hgN⟩) ⟨s, hs⟩ : ↥S) = ⟨s, hs⟩ := by rw [hg'1]; rfl
  have h2 : (((S.normalizerMonoidHom ⟨g, hgN⟩) ⟨s, hs⟩ : ↥S) : A) = (s : A) :=
    congrArg (fun t : ↥S => (t : A)) h1
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨g, hgN⟩ ⟨s, hs⟩] at h2
  calc g * s = g * s * g⁻¹ * g := by group
    _ = s * g := by rw [h2]

theorem l34g_pk2 (hC3 : Asc82FactCent3) {A : Type} [Group A] [Finite A] {S : Subgroup A}
    (hS : SimpleFStarQuotient ↥S) {x : A} (hx : x * x = 1) (hxS : CFSG.conjugate S x = S)
    {g : A} {m : ℕ} (hg : g ^ 3 ^ m = 1) (hgS : CFSG.conjugate S g = S) (hgx : g * x = x * g)
    (hgc : ∀ c ∈ S ⊓ centralizer ({x} : Set A), Odd (orderOf c) → g * c = c * g) :
    ∀ s ∈ S, g * s = s * g := by
  by_cases hcent : S ≤ centralizer ({x} : Set A)
  · exact l34g_pk2_central hS hcent hgc
  · exact l34g_pk2_noncentral hC3 hS hx hxS hg hgS hgx hgc hcent

end CFSG.OddStandard.SmallF3.Omega
