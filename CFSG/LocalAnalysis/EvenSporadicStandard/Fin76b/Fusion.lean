module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem z_ne_t : z ≠ t := fun hzt => h.z_not_mem_A (hzt ▸ h.t_mem_A)

include h in
theorem t_comm_z : t * z = z * t := h.z_comm_of_mem_A h.t_mem_A

include h in
theorem z_mul_t_sq : (z * t) * (z * t) = 1 := by
  calc z * t * (z * t) = z * (t * z) * t := by group
    _ = z * (z * t) * t := by rw [h.t_comm_z]
    _ = (z * z) * (t * t) := by group
    _ = 1 := by rw [h.z_sq, h.t_sq, one_mul]

include h in
theorem z_not_square : ¬ ∃ g : G, g * g = z := by
  rintro ⟨g, hg⟩
  have hgz : g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * (g * g) := by rw [hg]
      _ = (g * g) * g := by group
      _ = z * g := by rw [hg]
  rw [h.cent_eq] at hgz
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.z_cent) hgz
  have hcz : c * a = a * c := by
    rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl
    · simp
    · exact (h.z_comm_of_mem_A ha).symm
  have hsq : (a * c) * (a * c) = a * a * (c * c) := by
    calc (a * c) * (a * c) = a * (c * a) * c := by group
      _ = a * (a * c) * c := by rw [hcz]
      _ = a * a * (c * c) := by group
  have hcc : c * c = 1 := by
    rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl
    · simp
    · exact h.z_sq
  rw [hsq, hcc, mul_one] at hg
  exact h.z_not_mem_A (hg ▸ mul_mem ha ha)

include h in
theorem conj_t_ne_z (x : G) : x * t * x⁻¹ ≠ z := by
  intro hx
  obtain ⟨g, hgA, hg⟩ := h.t_square
  refine h.z_not_square ⟨x * g * x⁻¹, ?_⟩
  calc x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ := by group
    _ = z := by rw [hg, hx]

include h in
theorem conj_z_ne_t (x : G) : x * z * x⁻¹ ≠ t := by
  intro hx
  obtain ⟨g, hgA, hg⟩ := h.t_square
  refine h.z_not_square ⟨x⁻¹ * g * x, ?_⟩
  calc x⁻¹ * g * x * (x⁻¹ * g * x) = x⁻¹ * (g * g) * x := by group
    _ = z := by rw [hg, ← hx]; group

include h in
theorem z_central_T : ∀ y ∈ T₀ ⊔ zpowers z, y * z = z * y := by
  intro y hy
  obtain ⟨s, hs, hy | hy⟩ := (h.mem_T_iff).1 hy
  · rw [hy]; exact h.z_comm_of_mem_A (h.T₀_le hs)
  · rw [hy]
    calc s * z * z = s := by rw [mul_assoc, h.z_sq, mul_one]
      _ = z * (s * z) := by
        rw [← mul_assoc, ← h.z_comm_of_mem_A (h.T₀_le hs), mul_assoc, h.z_sq, mul_one]

include h in
theorem t_central_T : ∀ y ∈ T₀ ⊔ zpowers z, y * t = t * y := by
  intro y hy
  obtain ⟨s, hs, hy | hy⟩ := (h.mem_T_iff).1 hy
  · rw [hy]; exact h.t_central s hs
  · rw [hy]
    calc s * z * t = s * (z * t) := by group
      _ = s * (t * z) := by rw [h.t_comm_z]
      _ = (s * t) * z := by group
      _ = (t * s) * z := by rw [h.t_central s hs]
      _ = t * (s * z) := by group

include h in
theorem center_T {x : G} (hx : x ∈ T₀ ⊔ zpowers z)
    (hc : ∀ y ∈ T₀ ⊔ zpowers z, y * x = x * y) : x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  obtain ⟨s, hs, hxs | hxs⟩ := (h.mem_T_iff).1 hx
  · have hsc : ∀ y ∈ T₀, y * s = s * y := fun y hy => by
      have := hc y (mem_sup_left hy)
      rwa [hxs] at this
    rcases h.center_le s hs hsc with h1 | h1
    · exact Or.inl (hxs.trans h1)
    · exact Or.inr (Or.inr (Or.inl (hxs.trans h1)))
  · have hsc : ∀ y ∈ T₀, y * s = s * y := fun y hy => by
      have h1 := hc y (mem_sup_left hy)
      rw [hxs] at h1
      have h2 : y * s * z = s * y * z := by
        calc y * s * z = y * (s * z) := by group
          _ = (s * z) * y := h1
          _ = s * (z * y) := by group
          _ = s * (y * z) := by rw [← h.z_comm_of_mem_A (h.T₀_le hy)]
          _ = s * y * z := by group
      exact mul_right_cancel h2
    rcases h.center_le s hs hsc with h1 | h1
    · refine Or.inr (Or.inl ?_)
      rw [hxs, h1, one_mul]
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hxs, h1, h.t_comm_z]

end InnerConfig

theorem conj_central_of_normalizer {G : Type*} [Group G] {T : Subgroup G} {x u : G}
    (hx : x ∈ normalizer (T : Set G)) (hu : u ∈ T) (hc : ∀ y ∈ T, y * u = u * y) :
    x * u * x⁻¹ ∈ T ∧ ∀ y ∈ T, y * (x * u * x⁻¹) = (x * u * x⁻¹) * y := by
  have hmem : ∀ k : G, k ∈ T ↔ x * k * x⁻¹ ∈ T := fun k => mem_normalizer_iff.1 hx k
  refine ⟨(hmem u).1 hu, fun y hy => ?_⟩
  have hy' : x⁻¹ * y * x ∈ T := by
    rw [hmem (x⁻¹ * y * x)]
    have : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [this]
  have := hc (x⁻¹ * y * x) hy'
  calc y * (x * u * x⁻¹) = x * ((x⁻¹ * y * x) * u) * x⁻¹ := by group
    _ = x * (u * (x⁻¹ * y * x)) * x⁻¹ := by rw [this]
    _ = (x * u * x⁻¹) * y := by group

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem normalizer_dichotomy {x : G} (hx : x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G)) :
    (x * z * x⁻¹ = z ∧ x * t * x⁻¹ = t) ∨ (x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t) := by
  have hzT : z ∈ T₀ ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have htT : t ∈ T₀ ⊔ zpowers z := mem_sup_left h.t_mem
  obtain ⟨hz1, hz2⟩ := conj_central_of_normalizer hx hzT (h.z_central_T)
  obtain ⟨ht1, ht2⟩ := conj_central_of_normalizer hx htT (h.t_central_T)
  have hz1' := h.center_T hz1 hz2
  have ht1' := h.center_T ht1 ht2
  have hxz_ne : x * z * x⁻¹ ≠ 1 := fun e => h.z_ne (by
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, e]; group)
  have hxt_ne : x * t * x⁻¹ ≠ 1 := fun e => h.t_ne (by
    have : t = x⁻¹ * (x * t * x⁻¹) * x := by group
    rw [this, e]; group)
  have hxz : x * z * x⁻¹ = z ∨ x * z * x⁻¹ = z * t := by
    rcases hz1' with e | e | e | e
    · exact absurd e hxz_ne
    · exact Or.inl e
    · exact absurd e (h.conj_z_ne_t x)
    · exact Or.inr e
  have hxt : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t := by
    rcases ht1' with e | e | e | e
    · exact absurd e hxt_ne
    · exact absurd e (h.conj_t_ne_z x)
    · exact Or.inl e
    · exact Or.inr e
  rcases hxz with e1 | e1 <;> rcases hxt with e2 | e2
  · exact Or.inl ⟨e1, e2⟩
  · exfalso
    have hxc : x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have : z * x = (x * z * x⁻¹) * x := by rw [e1]
      rw [this]; group
    rw [h.cent_eq] at hxc
    obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 h.z_cent) hxc
    have hct : c * t * c⁻¹ = t := by
      rcases mem_zpowers_sq_eq_one h.z_sq hc with hc1 | hc1
      · rw [hc1]; simp
      · have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
        rw [hc1, hzi, ← h.t_comm_z, mul_assoc, h.z_sq, mul_one]
    have : a * c * t * (a * c)⁻¹ = a * t * a⁻¹ := by
      calc a * c * t * (a * c)⁻¹ = a * (c * t * c⁻¹) * a⁻¹ := by group
        _ = a * t * a⁻¹ := by rw [hct]
    rw [this] at e2
    have hat : a * t * a⁻¹ ∈ A := mul_mem (mul_mem ha h.t_mem_A) (inv_mem ha)
    rw [e2] at hat
    exact h.z_not_mem_A (by simpa using mul_mem hat (inv_mem h.t_mem_A))
  · exact Or.inr ⟨e1, e2⟩
  · exfalso
    have h3 : x * z * x⁻¹ = x * t * x⁻¹ := e1.trans e2.symm
    have : z = t := mul_left_cancel (mul_right_cancel h3)
    exact h.z_ne_t this

end InnerConfig

theorem exists_odd_pow_mem {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : ¬ 2 ∣ T.index) {x : G} (hx : x ∈ normalizer (T : Set G)) :
    ∃ k : ℕ, x ^ (2 * k + 1) ∈ T := by
  have hN : (T.subgroupOf (normalizer (T : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_normalizer).2 le_rfl
  have hmem := Subgroup.pow_index_mem (T.subgroupOf (normalizer (T : Set G))) ⟨x, hx⟩
  have hodd : Odd (T.subgroupOf (normalizer (T : Set G))).index := by
    have hd : (T.subgroupOf (normalizer (T : Set G))).index ∣ T.index :=
      Subgroup.relIndex_dvd_index_of_le le_normalizer
    by_contra hne
    exact hT (dvd_trans (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)) hd)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  have := (mem_subgroupOf.1 hmem)
  rw [hk] at this
  simpa using this

theorem exists_normalizer_conj {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT : ¬ 2 ∣ T.index) {u w g : G} (hu : ∀ y ∈ T, y * u = u * y)
    (hw : ∀ y ∈ T, y * w = w * y) (hg : g * u * g⁻¹ = w) :
    ∃ n ∈ normalizer (T : Set G), n * u * n⁻¹ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := hT2.toSylow hT
  have hP : (P : Subgroup G) = T := rfl
  have hu' : g⁻¹ * w * g = u := by rw [← hg]; group
  obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P w g
    (mem_centralizer_iff.2 fun y hy => hw y hy)
    (by rw [hu']; exact mem_centralizer_iff.2 fun y hy => hu y hy)
  refine ⟨n, hn, ?_⟩
  rw [hu'] at hn'
  rw [hn']
  group

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem T_pgroup [Finite G] : IsPGroup 2 (T₀ ⊔ zpowers z : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h.T₀_pgroup.exists_card_eq
  refine IsPGroup.of_card (n := k + 1) ?_
  rw [h.T_card, hk, pow_succ]
  ring

include h in
theorem T₀_relIndex_T [Finite G] : T₀.relIndex (T₀ ⊔ zpowers z) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := T₀) (K := T₀ ⊔ zpowers z)
  rw [inf_eq_left.2 le_sup_left, h.T_card] at h1
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

include h in
theorem central_zt : ∀ y ∈ T₀ ⊔ zpowers z, y * (z * t) = (z * t) * y := by
  intro y hy
  calc y * (z * t) = (y * z) * t := by group
    _ = (z * y) * t := by rw [h.z_central_T y hy]
    _ = z * (y * t) := by group
    _ = z * (t * y) := by rw [h.t_central_T y hy]
    _ = (z * t) * y := by group

include h in
theorem normalizer_fixes_of_sylow [Finite G] (hT : ¬ 2 ∣ (T₀ ⊔ zpowers z).index) {x : G}
    (hx : x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G)) :
    x * z * x⁻¹ = z ∧ x * t * x⁻¹ = t := by
  rcases h.normalizer_dichotomy hx with h1 | ⟨h1, h2⟩
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ := exists_odd_pow_mem hT hx
    have hsq : x ^ 2 * z * (x ^ 2)⁻¹ = z := by
      have e1 : x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
      calc x ^ 2 * z * (x ^ 2)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * (z * t) * x⁻¹ := by rw [h1]
        _ = (x * z * x⁻¹) * (x * t * x⁻¹) := e1
        _ = (z * t) * t := by rw [h1, h2]
        _ = z * (t * t) := by group
        _ = z := by rw [h.t_sq, mul_one]
    have hc2 : Commute (x ^ 2) z := by
      have : x ^ 2 * z = z * x ^ 2 := by
        calc x ^ 2 * z = (x ^ 2 * z * (x ^ 2)⁻¹) * x ^ 2 := by simp [mul_assoc]
          _ = z * x ^ 2 := by rw [hsq]
      exact this
    have hcm : Commute (x ^ (2 * k + 1)) z := (h.z_central_T _ hk)
    have hx_eq : x = ((x ^ 2) ^ k)⁻¹ * x ^ (2 * k + 1) := by
      have : (x ^ 2) ^ k * x = x ^ (2 * k + 1) := by rw [← pow_mul, ← pow_succ]
      rw [← this]; group
    have hcx : Commute x z := by
      rw [hx_eq]
      exact (hc2.pow_left k).inv_left.mul_left hcm
    have h4 : x * z * x⁻¹ = z := by
      have : x * z = z * x := hcx
      calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [this]
        _ = z := by group
    rw [h4] at h1
    have : t = 1 := by
      have h3 : z * t = z * 1 := by rw [mul_one]; exact h1.symm
      exact mul_left_cancel h3
    exact h.t_ne this

end InnerConfig

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem not_conj_of_sylow [Finite G] (hT : ¬ 2 ∣ (T₀ ⊔ zpowers z).index) {u w : G}
    (hu : u = z ∨ u = t ∨ u = z * t) (hw : w = z ∨ w = t ∨ w = z * t) {g : G}
    (hg : g * u * g⁻¹ = w) : w = u := by
  have hcen : ∀ v : G, (v = z ∨ v = t ∨ v = z * t) → ∀ y ∈ T₀ ⊔ zpowers z, y * v = v * y := by
    intro v hv
    rcases hv with hv | hv | hv
    · rw [hv]; exact h.z_central_T
    · rw [hv]; exact h.t_central_T
    · rw [hv]; exact h.central_zt
  obtain ⟨n, hn, hn'⟩ := exists_normalizer_conj h.T_pgroup hT (hcen u hu) (hcen w hw) hg
  obtain ⟨hz, ht⟩ := h.normalizer_fixes_of_sylow hT hn
  have hfix : ∀ v : G, (v = z ∨ v = t ∨ v = z * t) → n * v * n⁻¹ = v := by
    intro v hv
    rcases hv with hv | hv | hv
    · rw [hv]; exact hz
    · rw [hv]; exact ht
    · rw [hv]
      calc n * (z * t) * n⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) := by group
        _ = z * t := by rw [hz, ht]
  rw [← hn', hfix u hu]

include h in
theorem z_mul_t_ne_one : z * t ≠ 1 := fun e => h.z_ne_t (by
  have h1 : z = t⁻¹ := eq_inv_of_mul_eq_one_left e
  rw [h1]; exact inv_eq_of_mul_eq_one_right h.t_sq)

include h in
theorem z_mul_t_order : orderOf (z * t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.z_mul_t_sq) h.z_mul_t_ne_one

include h in
theorem false_of_sylow [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hT : ¬ 2 ∣ (T₀ ⊔ zpowers z).index) : False := by
  have hT2 := h.T_pgroup
  have hrel := h.T₀_relIndex_T
  have hzT : z ∈ T₀ ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hztT : z * t ∈ T₀ ⊔ zpowers z := mul_mem hzT (mem_sup_left h.t_mem)
  have hztT₀ : z * t ∉ T₀ := fun hm => h.z_not_mem_T₀ (by
    simpa [h.t_sq] using mul_mem hm (inv_mem h.t_mem))
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hT2 hT le_sup_left hrel hzT
    h.z_not_mem_T₀ h.z_order
  obtain ⟨g', hg'⟩ := exists_conj_mem_complement hnonab hT2 hT le_sup_left hrel hztT hztT₀
    h.z_mul_t_order
  obtain ⟨b, hbA, hcls⟩ := h.classes
  have ha2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [h.z_sq]; group
  have ha1 : g⁻¹ * z * g ≠ 1 := fun e => h.z_ne (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have ha2' : (g'⁻¹ * (z * t) * g') * (g'⁻¹ * (z * t) * g') = 1 := by
    calc (g'⁻¹ * (z * t) * g') * (g'⁻¹ * (z * t) * g') = g'⁻¹ * ((z * t) * (z * t)) * g' := by
          group
      _ = 1 := by rw [h.z_mul_t_sq]; group
  have ha1' : g'⁻¹ * (z * t) * g' ≠ 1 := fun e => h.z_mul_t_ne_one (by
    calc z * t = g' * (g'⁻¹ * (z * t) * g') * g'⁻¹ := by group
      _ = 1 := by rw [e]; group)
  rcases hcls _ (h.T₀_le hg) ha2 ha1 with ⟨c, hcA, hc⟩ | ⟨c, hcA, hc⟩
  · refine h.conj_t_ne_z (g * c) ?_
    calc (g * c) * t * (g * c)⁻¹ = g * (c * t * c⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hc]
      _ = z := by group
  · rcases hcls _ (h.T₀_le hg') ha2' ha1' with ⟨c', hcA', hc'⟩ | ⟨c', hcA', hc'⟩
    · have hk : (g' * c') * t * (g' * c')⁻¹ = z * t := by
        calc (g' * c') * t * (g' * c')⁻¹ = g' * (c' * t * c'⁻¹) * g'⁻¹ := by group
          _ = g' * (g'⁻¹ * (z * t) * g') * g'⁻¹ := by rw [hc']
          _ = z * t := by group
      have := h.not_conj_of_sylow hT (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hk
      exact h.z_ne (mul_right_cancel (this.trans (one_mul t).symm))
    · have e1 : z = (g * c) * b * (g * c)⁻¹ := by
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = g * (c * b * c⁻¹) * g⁻¹ := by rw [hc]
          _ = (g * c) * b * (g * c)⁻¹ := by group
      have e2 : z * t = (g' * c') * b * (g' * c')⁻¹ := by
        calc z * t = g' * (g'⁻¹ * (z * t) * g') * g'⁻¹ := by group
          _ = g' * (c' * b * c'⁻¹) * g'⁻¹ := by rw [hc']
          _ = (g' * c') * b * (g' * c')⁻¹ := by group
      have hk : ((g' * c') * (g * c)⁻¹) * z * ((g' * c') * (g * c)⁻¹)⁻¹ = z * t := by
        calc ((g' * c') * (g * c)⁻¹) * z * ((g' * c') * (g * c)⁻¹)⁻¹
            = ((g' * c') * (g * c)⁻¹) * ((g * c) * b * (g * c)⁻¹) *
                ((g' * c') * (g * c)⁻¹)⁻¹ := by rw [← e1]
          _ = (g' * c') * b * (g' * c')⁻¹ := by group
          _ = z * t := e2.symm
      have := h.not_conj_of_sylow hT (Or.inl rfl) (Or.inr (Or.inr rfl)) hk
      exact h.t_ne (mul_left_cancel (this.trans (mul_one z).symm))

end InnerConfig

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem mem_T_of_two_group [Finite G] {x : G} (hx : x ∈ centralizer ({z} : Set G))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hTQ : T₀ ⊔ zpowers z ≤ Q) (hxQ : x ∈ Q) :
    x ∈ T₀ ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hAm⟩ := h.T₀_odd
  set T := T₀ ⊔ zpowers z with hTdef
  set T' := T ⊔ zpowers x with hT'def
  have hT'Q : T' ≤ Q := sup_le hTQ (zpowers_le.2 hxQ)
  have hT'2 : IsPGroup 2 T' := hQ.to_le hT'Q
  have hH : centralizer ({z} : Set G) = A ⊔ zpowers z := h.cent_eq
  have hT'H : T' ≤ A ⊔ zpowers z := by
    refine sup_le (sup_le (le_trans h.T₀_le le_sup_left) le_sup_right) ?_
    rw [zpowers_le, ← hH]; exact hx
  have hcardH : Nat.card (A ⊔ zpowers z : Subgroup G) = Nat.card A * 2 := by
    rw [Nat.card_congr (mulEquivProdSup (zpowers_le.2 h.z_cent) h.disjoint).toEquiv.symm,
      Nat.card_prod, Nat.card_zpowers, h.z_order]
  have hdvd : Nat.card T' ∣ Nat.card T * m := by
    have h1 : Nat.card T' ∣ Nat.card (A ⊔ zpowers z : Subgroup G) := Subgroup.card_dvd_of_le hT'H
    rw [hcardH, hAm] at h1
    have hTc : Nat.card T = 2 * Nat.card T₀ := h.T_card
    rw [hTc]
    refine h1.trans (dvd_of_eq ?_)
    ring
  obtain ⟨j, hj⟩ := hT'2.exists_card_eq
  obtain ⟨i, hi⟩ := (h.T_pgroup).exists_card_eq
  have hcop : Nat.Coprime (2 ^ j) m := by
    apply Nat.Coprime.pow_left
    exact Nat.coprime_two_left.2 hm
  have hdvd2 : 2 ^ j ∣ 2 ^ i := by
    rw [hj, hi] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hle : Nat.card T' ≤ Nat.card T := by
    rw [hj, hi]; exact Nat.le_of_dvd (by positivity) hdvd2
  have heq : T = T' := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [heq]
  exact mem_sup_right (mem_zpowers x)

end InnerConfig

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem exists_swap [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ (P : Subgroup G) (x : G), IsPGroup 2 P ∧ T₀ ⊔ zpowers z ≤ P ∧ x ∈ P ∧
      x ∉ T₀ ⊔ zpowers z ∧ x ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G) ∧
      x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.T_pgroup.exists_le_sylow
  by_cases hTQ : (T₀ ⊔ zpowers z : Subgroup G) = Q
  · exfalso
    exact h.false_of_sylow hnonab (by rw [hTQ]; exact Q.not_dvd_index)
  · let TQ : Subgroup (Q : Subgroup G) := (T₀ ⊔ zpowers z).subgroupOf (Q : Subgroup G)
    have hTQne : TQ < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hTQ ?_
      refine le_antisymm hQ (fun q hq => ?_)
      have : (⟨q, hq⟩ : (Q : Subgroup G)) ∈ TQ := by rw [htop]; trivial
      exact mem_subgroupOf.1 this
    have : Group.IsNilpotent (Q : Subgroup G) := Q.isPGroup'.isNilpotent
    have hnc : NormalizerCondition (Q : Subgroup G) := Group.normalizerCondition_of_isNilpotent
    obtain ⟨y, hyN, hyn⟩ := IsConcreteLE.exists_of_lt (hnc TQ hTQne)
    have hxN : (y : G) ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G) := by
      have : y ∈ (normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G)).subgroupOf
          (Q : Subgroup G) := by
        rw [Subgroup.subgroupOf_normalizer_eq hQ]; exact hyN
      exact mem_subgroupOf.1 this
    have hxT : (y : G) ∉ T₀ ⊔ zpowers z := fun hyT => hyn (mem_subgroupOf.2 hyT)
    rcases h.normalizer_dichotomy hxN with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      refine hxT (h.mem_T_of_two_group ?_ Q.isPGroup' hQ y.2)
      rw [mem_centralizer_singleton_iff]
      calc (y : G) * z = ((y : G) * z * (y : G)⁻¹) * (y : G) := by group
        _ = z * (y : G) := by rw [h1]
    · exact ⟨Q, y, Q.isPGroup', hQ, y.2, hxT, hxN, h1, h2⟩

end InnerConfig

end CFSG.EvenSporadicStandard.Fin76b
