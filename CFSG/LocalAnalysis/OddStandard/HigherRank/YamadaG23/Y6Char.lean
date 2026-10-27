module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Inv
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6KFacts

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

private lemma y6c_t_sq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t * t = 1 := by
  have hpow := pow_orderOf_eq_one t
  rw [h.t_ord] at hpow
  simpa [pow_two] using hpow

private lemma y6c_t_inv_eq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (y6c_t_sq h)

private lemma y6c_z_sq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : z * z = 1 := by
  simpa [pow_two] using h.rel.z_sq

private lemma y6c_z_inv_eq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (y6c_z_sq h)

private lemma y6c_t_ne_z (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t ≠ z := by
  intro htz
  have h1 := h.t_inv
  rw [htz, ← h.u_sq] at h1
  have h2 : u ^ 2 * u * (u ^ 2)⁻¹ = u := by group
  rw [h2] at h1
  have h3 : u ^ 2 = 1 := by
    have h4 : u * u = 1 := by
      calc u * u = u * u⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel u
    simpa [pow_two] using h4
  have h5 := orderOf_dvd_of_pow_eq_one h3
  rw [h.u_ord] at h5
  exact absurd h5 (by decide)

private lemma y6c_t_conj_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    t * v * t⁻¹ = v⁻¹ := by
  rw [h.hV] at hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← conj_zpow, h.t_inv, inv_zpow]

private lemma y6c_mem_normalizer_of_conj {H : Subgroup G} {x : G}
    (h1 : ∀ c ∈ H, x * c * x⁻¹ ∈ H) (h2 : ∀ c ∈ H, x⁻¹ * c * x ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨h1 c, fun hc => ?_⟩
  have := h2 (x * c * x⁻¹) hc
  rwa [show x⁻¹ * (x * c * x⁻¹) * x = c by group] at this

private lemma y6c_conj_mem_closure {S : Set G} {K : Subgroup G} {x : G}
    (hgen : ∀ y ∈ S, x * y * x⁻¹ ∈ K) :
    ∀ c ∈ Subgroup.closure S, x * c * x⁻¹ ∈ K := by
  have hle : Subgroup.closure S ≤ K.comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_comap.mpr (show x * y * x⁻¹ ∈ K from hgen y hy)
  intro c hc
  exact Subgroup.mem_comap.mp (hle hc)

private lemma y6c_conj_t_order (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) (x : G) :
    orderOf (x * t * x⁻¹) = 2 := by
  have h1 := MulEquiv.orderOf_eq (MulAut.conj x) t
  rw [MulAut.conj_apply] at h1
  rw [h1, h.t_ord]

theorem y6_mem_NC0_iff (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx : x ∈ normalizer (V : Set G)) :
    x ∈ normalizer (C0 : Set G) ↔ t⁻¹ * (x * t * x⁻¹) ∈ V := by
  have hVC0 : V ≤ C0 := y6_V_le_C0 h
  have htC0 : t ∈ C0 := y6_t_mem_C0 h
  have hC0' : C0 = closure ({u, t} : Set G) := h.hC0
  have hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hx v).mp hv
  have hxiV : ∀ v ∈ V, x⁻¹ * v * x ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) v).mp hv
    simpa using this
  constructor
  · intro hxN
    have hy : x * t * x⁻¹ ∈ C0 := (Subgroup.mem_normalizer_iff.mp hxN t).mp htC0
    have hy' : x * t * x⁻¹ ∈ (closure ({u, t} : Set G) : Subgroup G) := by rwa [hC0'] at hy
    rcases y6_d8_invol h.u_ord h.t_ord h.t_inv (x * t * x⁻¹) hy' (y6c_conj_t_order h x) with
      hz | ⟨i, hi⟩
    · exfalso
      have hxz : x * z * x⁻¹ = z := y6_fix_z h hx
      have h1 : x * t * x⁻¹ = x * z * x⁻¹ := by rw [hz, h.u_sq, hxz]
      have h2 : t = z := by
        have := congrArg (fun w => x⁻¹ * w * x) h1
        simpa [mul_assoc] using this
      exact y6c_t_ne_z h h2
    · rw [hi, y6c_t_inv_eq h]
      have hui : u ^ i ∈ V := by rw [h.hV]; exact Subgroup.npow_mem_zpowers u i
      have h3 : t * (u ^ i * t) = t * u ^ i * t⁻¹ := by rw [y6c_t_inv_eq h, mul_assoc]
      rw [h3, y6c_t_conj_V h hui]
      exact Subgroup.inv_mem _ hui
  · intro hv
    set v : G := t⁻¹ * (x * t * x⁻¹) with hvdef
    have hxt : x * t * x⁻¹ = t * v := by rw [hvdef]; group
    have hxit : x⁻¹ * t * x = t * (x⁻¹ * v * x)⁻¹ := by
      have h1 : t = (x⁻¹ * t * x) * (x⁻¹ * v * x) := by
        calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
          _ = x⁻¹ * (t * v) * x := by rw [hxt]
          _ = (x⁻¹ * t * x) * (x⁻¹ * v * x) := by group
      rw [eq_mul_inv_iff_mul_eq]
      exact h1.symm
    have hgen : ∀ y ∈ ({u, t} : Set G), x * y * x⁻¹ ∈ C0 := by
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact hVC0 (hxV u (by rw [h.hV]; exact Subgroup.mem_zpowers u))
      · rw [hy, hxt]
        exact Subgroup.mul_mem _ htC0 (hVC0 hv)
    have hgen' : ∀ y ∈ ({u, t} : Set G), x⁻¹ * y * x⁻¹⁻¹ ∈ C0 := by
      intro y hy
      rw [inv_inv]
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact hVC0 (hxiV u (by rw [h.hV]; exact Subgroup.mem_zpowers u))
      · rw [hy, hxit]
        exact Subgroup.mul_mem _ htC0 (Subgroup.inv_mem _ (hVC0 (hxiV v hv)))
    refine y6c_mem_normalizer_of_conj ?_ ?_
    · intro c hc
      rw [hC0'] at hc
      exact y6c_conj_mem_closure hgen c hc
    · intro c hc
      rw [hC0'] at hc
      have := y6c_conj_mem_closure hgen' c hc
      rwa [inv_inv] at this

theorem y6_cen_At (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ w ∈ A ⊔ zpowers t, (∀ y ∈ A ⊔ zpowers t, w * y = y * w) →
      w = 1 ∨ w = z ∨ w = t ∨ w = z * t := by
  intro w hw hcen
  have ht2 : t ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one t
    rwa [h.t_ord] at hpow
  have hcomm : ∀ a ∈ A, ∀ c ∈ zpowers t, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute a t from h.t_cent a ha) k).eq
  obtain ⟨a, ha, c, hc, rfl⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcomm hw
  have hc12 : c = 1 ∨ c = t := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hmod := zpow_eq_zpow_emod' k ht2
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; rw [hmod]; simp [hk]
    · right; rw [hmod]; simp [hk]
  have hAcen : a = 1 ∨ a = z := by
    refine y6q8_cen h.rel h.z_ne (h.hA ▸ h.card_A) a (h.hA ▸ ha) ?_
    intro b hb
    have hbA : b ∈ A := by rwa [h.hA]
    have hb' : b ∈ A ⊔ zpowers t := Subgroup.mem_sup_left hbA
    have h1 := hcen b hb'
    rcases hc12 with rfl | rfl
    · simpa using h1
    · have hbt : b * c = c * b := h.t_cent b hbA
      have h2 : (a * b) * c = (b * a) * c := by
        calc (a * b) * c = a * (b * c) := by group
          _ = a * (c * b) := by rw [hbt]
          _ = (a * c) * b := by group
          _ = b * (a * c) := h1
          _ = (b * a) * c := by group
      exact mul_right_cancel h2
  rcases hAcen with rfl | rfl <;> rcases hc12 with rfl | rfl <;> simp

private lemma y6c_conj_At_mem (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G))
    (hxt : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t) :
    ∀ c ∈ A ⊔ zpowers t, x * c * x⁻¹ ∈ A ⊔ zpowers t := by
  intro c hc
  have hzC : ∀ w ∈ A ⊔ C0, w * z = z * w := by
    intro w hw
    obtain ⟨a, ha, c0, hc0, rfl⟩ := y6_C1_elems h w hw
    have haz : a * z = z * a := y6q8_z_central h.rel a (by rw [← h.hA]; exact ha)
    have hc0z : c0 * z = z * c0 := by
      have hc0' : c0 ∈ closure ({u, t} : Set G) := by rwa [h.hC0] at hc0
      obtain ⟨i, hi | hi⟩ := y6_d8_elems h.u_ord h.t_ord h.t_inv c0 hc0'
      · have huz : u ^ i * z = z * u ^ i := by
          rw [← h.u_sq]; group
        rw [hi]; exact huz
      · have huz : u ^ i * z = z * u ^ i := by
          rw [← h.u_sq]; group
        have htz : t * z = z * t := by
          have hz_t : t * z * t⁻¹ = z := by
            have hzV : z ∈ V := y6_z_mem_V h
            rw [y6c_t_conj_V h hzV, y6c_z_inv_eq h]
          rw [y6c_t_inv_eq h] at hz_t
          calc t * z = (t * z * t) * t := by rw [mul_assoc, mul_assoc, y6c_t_sq h, mul_one]
            _ = z * t := by rw [hz_t]
        rw [hi]
        calc u ^ i * t * z = u ^ i * (t * z) := by group
          _ = u ^ i * (z * t) := by rw [htz]
          _ = (u ^ i * z) * t := by group
          _ = (z * u ^ i) * t := by rw [huz]
          _ = z * (u ^ i * t) := by group
    calc a * c0 * z = a * (c0 * z) := by group
      _ = a * (z * c0) := by rw [hc0z]
      _ = (a * z) * c0 := by group
      _ = (z * a) * c0 := by rw [haz]
      _ = z * (a * c0) := by group
  have hcC1 : c ∈ (A ⊔ C0) ⊓ centralizer ({t} : Set G) := by
    refine ⟨sup_le_sup_left (Subgroup.zpowers_le.mpr (y6_t_mem_C0 h)) _ hc, ?_⟩
    have hle : A ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (h.t_cent a ha).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
    exact hle hc
  rw [← y6_cent_C1_t h]
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hx1 c).mp hcC1.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hct : t * c = c * t := Subgroup.mem_centralizer_iff.mp hcC1.2 t (Set.mem_singleton t)
  have hxc1 : x * c * x⁻¹ ∈ A ⊔ C0 := (Subgroup.mem_normalizer_iff.mp hx1 c).mp hcC1.1
  rcases hxt with hxt | hxt
  · have h1 : (x * t * x⁻¹) * (x * c * x⁻¹) = (x * c * x⁻¹) * (x * t * x⁻¹) := by
      calc (x * t * x⁻¹) * (x * c * x⁻¹) = x * (t * c) * x⁻¹ := by group
        _ = x * (c * t) * x⁻¹ := by rw [hct]
        _ = (x * c * x⁻¹) * (x * t * x⁻¹) := by group
    rw [hxt] at h1
    exact h1
  · have h1 : (x * t * x⁻¹) * (x * c * x⁻¹) = (x * c * x⁻¹) * (x * t * x⁻¹) := by
      calc (x * t * x⁻¹) * (x * c * x⁻¹) = x * (t * c) * x⁻¹ := by group
        _ = x * (c * t) * x⁻¹ := by rw [hct]
        _ = (x * c * x⁻¹) * (x * t * x⁻¹) := by group
    rw [hxt] at h1
    have h2 : z * (t * (x * c * x⁻¹)) = z * ((x * c * x⁻¹) * t) := by
      calc z * (t * (x * c * x⁻¹)) = (z * t) * (x * c * x⁻¹) := by group
        _ = (x * c * x⁻¹) * (z * t) := h1
        _ = ((x * c * x⁻¹) * z) * t := by group
        _ = (z * (x * c * x⁻¹)) * t := by rw [hzC _ hxc1]
        _ = z * ((x * c * x⁻¹) * t) := by group
    exact mul_left_cancel h2

theorem y6_mem_NAt_iff (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G)) :
    x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ↔
      (x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t) := by
  constructor
  · intro hxN
    have htA : t ∈ A ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hy : x * t * x⁻¹ ∈ A ⊔ zpowers t := (Subgroup.mem_normalizer_iff.mp hxN t).mp htA
    have hcen : ∀ w ∈ A ⊔ zpowers t, (x * t * x⁻¹) * w = w * (x * t * x⁻¹) := by
      intro w hw
      have hxiN : x⁻¹ ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ hxN
      have hw' : x⁻¹ * w * x ∈ A ⊔ zpowers t := by
        have := (Subgroup.mem_normalizer_iff.mp hxiN w).mp hw
        simpa using this
      have htcen : t * (x⁻¹ * w * x) = (x⁻¹ * w * x) * t := by
        have hsup : ∀ c ∈ A ⊔ zpowers t, t * c = c * t := by
          intro c hc
          have hcomm : ∀ a ∈ A, ∀ c ∈ zpowers t, a * c = c * a := by
            intro a ha c hc
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
            exact (Commute.zpow_right (show Commute a t from h.t_cent a ha) k).eq
          obtain ⟨a, ha, c', hc', rfl⟩ :=
            CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcomm hc
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
          have hta : t * a = a * t := (h.t_cent a ha).symm
          have htk : t * t ^ k = t ^ k * t := (Commute.zpow_right (Commute.refl t) k).eq
          calc t * (a * t ^ k) = (t * a) * t ^ k := by group
            _ = (a * t) * t ^ k := by rw [hta]
            _ = a * (t * t ^ k) := by group
            _ = a * (t ^ k * t) := by rw [htk]
            _ = (a * t ^ k) * t := by group
        exact hsup _ hw'
      calc (x * t * x⁻¹) * w = x * (t * (x⁻¹ * w * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * w * x) * t) * x⁻¹ := by rw [htcen]
        _ = w * (x * t * x⁻¹) := by group
    have hcases := y6_cen_At h (x * t * x⁻¹) hy hcen
    rcases hcases with h1 | hz | ht | hzt
    · exfalso
      have := y6c_conj_t_order h x
      rw [h1] at this
      simp at this
    · exfalso
      have hxz : x * z * x⁻¹ = z := y6_fix_z h hx2
      have h1 : x * t * x⁻¹ = x * z * x⁻¹ := by rw [hz, hxz]
      have h2 : t = z := by
        have := congrArg (fun w => x⁻¹ * w * x) h1
        simpa [mul_assoc] using this
      exact y6c_t_ne_z h h2
    · exact Or.inl ht
    · exact Or.inr hzt
  · intro hxt
    have hxit : x⁻¹ * t * x = t ∨ x⁻¹ * t * x = z * t := by
      rcases hxt with hxt | hxt
      · left
        have := congrArg (fun w => x⁻¹ * w * x) hxt
        simpa [mul_assoc] using this.symm
      · right
        have hxiz : x⁻¹ * z * x = z := by
          have := y6_fix_z h (Subgroup.inv_mem _ hx2)
          simpa using this
        have h1 : t = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by
          calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
            _ = x⁻¹ * (z * t) * x := by rw [hxt]
            _ = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by group
        rw [hxiz] at h1
        have h2 : z * t = z * (z * (x⁻¹ * t * x)) := by rw [← h1]
        calc x⁻¹ * t * x = (z * z) * (x⁻¹ * t * x) := by rw [y6c_z_sq h, one_mul]
          _ = z * (z * (x⁻¹ * t * x)) := by group
          _ = z * t := by rw [← h1]
    refine y6c_mem_normalizer_of_conj (y6c_conj_At_mem h hx1 hxt) ?_
    have hx1i : x⁻¹ ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) := Subgroup.inv_mem _ hx1
    have hc := y6c_conj_At_mem h hx1i (x := x⁻¹) (by simpa using hxit)
    intro c hc'
    simpa using hc c hc'

theorem y6_mem_NAt_of_cent (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hxt : x * t * x⁻¹ = t) :
    x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) := by
  have hxit : x⁻¹ * t * x = t := by
    have := congrArg (fun w => x⁻¹ * w * x) hxt
    simpa [mul_assoc] using this.symm
  refine y6c_mem_normalizer_of_conj (y6c_conj_At_mem h hx1 (Or.inl hxt)) ?_
  have hx1i : x⁻¹ ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) := Subgroup.inv_mem _ hx1
  have hc := y6c_conj_At_mem h hx1i (x := x⁻¹) (Or.inl (by simpa using hxit))
  intro c hc'
  simpa using hc c hc'

end CFSG.OddStandard.HigherRank.YamadaG23
