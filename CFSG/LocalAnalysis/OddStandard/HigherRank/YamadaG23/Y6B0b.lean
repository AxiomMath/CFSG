module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B0a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

private lemma y6_t_sq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t * t = 1 := by
  have hpow := pow_orderOf_eq_one t
  rw [h.t_ord] at hpow
  simpa [pow_two] using hpow

private lemma y6_t_inv_eq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (y6_t_sq h)

private lemma y6_t_conj_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    t * v * t⁻¹ = v⁻¹ := by
  rw [h.hV] at hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← conj_zpow, h.t_inv, inv_zpow]

private lemma y6_t_mul_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    t * v = v⁻¹ * t := by
  have hc := congrArg (· * t) (y6_t_conj_V h hv)
  simpa [mul_assoc] using hc

private lemma y6_V_ab (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : x * y = y * x := by
  rw [h.hV] at hx hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self u m n).eq

private lemma y6_V_sq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    v ^ 2 ∈ zpowers z := by
  rw [h.hV] at hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  rw [← h.u_sq]
  have hthis : (u ^ k) ^ 2 = (u ^ 2) ^ k := by
    rw [← zpow_natCast (u ^ k) 2, ← zpow_mul]
    rw [show (↑(2 : ℕ) : ℤ) = (2 : ℤ) by norm_num, ← zpow_natCast u 2]
    exact zpow_mul' u k (2 : ℤ)
  rw [hthis]

private lemma y6_comm_A_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ a ∈ A, ∀ v ∈ V, a * v = v * a := by
  intro a ha v hv
  rw [h.hV] at hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hcomm : Commute a u := h.u_cent a ha
  exact (hcomm.zpow_right k).eq

private lemma y6_C0_elems (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ c ∈ C0, c ∈ V ∨ ∃ v ∈ V, c = v * t := by
  intro c hc
  rw [h.hC0] at hc
  rcases y6_d8_elems h.u_ord h.t_ord h.t_inv c hc with ⟨i, hi | hi⟩
  · left
    rw [h.hV, hi]
    exact Subgroup.npow_mem_zpowers u i
  · exact Or.inr ⟨u ^ i, by rw [h.hV]; exact Subgroup.npow_mem_zpowers u i, hi⟩

private lemma y6_comm_V_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v : G} (hv : v ∈ V) :
    ⁅v, t⁆ = v ^ 2 := by
  have hconj : t * v⁻¹ * t⁻¹ = v := by
    simpa using y6_t_conj_V h (V.inv_mem hv)
  rw [commutatorElement_def]
  calc v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
    _ = v * v := by rw [hconj]
    _ = v ^ 2 := by rw [pow_two]

private lemma y6_comm_V_Vt (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v v' : G} (hv : v ∈ V)
    (hv' : v' ∈ V) : ⁅v, v' * t⁆ = v ^ 2 := by
  have hcomm : Commute v v' := y6_V_ab h hv hv'
  rw [commutatorElement_mul_right_eq_mul_conj, hcomm.commutator_eq, one_mul,
    y6_comm_V_t h hv]
  rw [y6_V_ab h hv' (V.pow_mem hv 2)]
  group

private lemma y6_comm_Vt_Vt (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {v v' : G} (hv : v ∈ V)
    (hv' : v' ∈ V) : ⁅v * t, v' * t⁆ = (v * v'⁻¹) ^ 2 := by
  have htinv : t⁻¹ = t := y6_t_inv_eq h
  have ht2 : t * t = 1 := y6_t_sq h
  have htv' : t * v' = v'⁻¹ * t := y6_t_mul_V h hv'
  have htvinv : t * v⁻¹ = v * t := by simpa using y6_t_mul_V h (V.inv_mem hv)
  have htv'inv : t * v'⁻¹ = v' * t := by simpa using y6_t_mul_V h (V.inv_mem hv')
  calc ⁅v * t, v' * t⁆
      = (v * t) * (v' * t) * (t * v⁻¹) * (t * v'⁻¹) := by
          rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, htinv]
    _ = (v * v'⁻¹) ^ 2 := by
          rw [htvinv, htv'inv]
          rw [show (v * t) * (v' * t) * (v * t) * (v' * t)
                = ((v * t) * (v' * t)) * ((v * t) * (v' * t)) by group]
          rw [show (v * t) * (v' * t) = v * (t * v') * t by group]
          rw [htv']
          rw [show v * (v'⁻¹ * t) * t = v * v'⁻¹ * (t * t) by group]
          rw [ht2, mul_one, pow_two]

private lemma y6_comm_C0 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ c ∈ C0, ∀ c' ∈ C0, ⁅c, c'⁆ ∈ zpowers z := by
  intro c hc c' hc'
  rcases y6_C0_elems h c hc with hcV | ⟨v, hv, rfl⟩
  · rcases y6_C0_elems h c' hc' with hc'V | ⟨v', hv', rfl⟩
    · have hcomm : Commute c c' := y6_V_ab h hcV hc'V
      rw [hcomm.commutator_eq]
      exact Subgroup.one_mem _
    · rw [y6_comm_V_Vt h hcV hv']
      exact y6_V_sq h hcV
  · rcases y6_C0_elems h c' hc' with hc'V | ⟨v', hv', rfl⟩
    · have h3 : ⁅v * t, c'⁆ = (c' ^ 2)⁻¹ := by
        rw [← commutatorElement_inv, y6_comm_V_Vt h hc'V hv]
      rw [h3]
      exact Subgroup.inv_mem _ (y6_V_sq h hc'V)
    · rw [y6_comm_Vt_Vt h hv hv']
      exact y6_V_sq h (V.mul_mem hv (V.inv_mem hv'))

private lemma y6_comm_A (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ zpowers z := by
  intro a ha a' ha'
  rw [h.hA] at ha ha'
  rcases y6q8_comm_mem h.rel a ha a' ha' with hh | hh
  · rw [hh]; exact Subgroup.one_mem _
  · rw [hh]; exact Subgroup.mem_zpowers z

private lemma y6_comm_mul_mul (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a a' c c' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hc : c ∈ C0) (hc' : c' ∈ C0) :
    ⁅a * c, a' * c'⁆ = ⁅a, a'⁆ * ⁅c, c'⁆ := by
  let f : ↥A × ↥C0 →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := by
        rintro ⟨a1, c1⟩ ⟨a2, c2⟩
        change (a1 : G) * (a2 : G) * ((c1 : G) * (c2 : G)) =
          ((a1 : G) * (c1 : G)) * ((a2 : G) * (c2 : G))
        rw [show (a1 : G) * (a2 : G) * ((c1 : G) * (c2 : G)) =
              (a1 : G) * ((a2 : G) * (c1 : G)) * (c2 : G) by group]
        rw [y6_C0_comm h a2 a2.2 c1 c1.2]
        group }
  have hmap := map_commutatorElement f (⟨a, ha⟩, ⟨c, hc⟩) (⟨a', ha'⟩, ⟨c', hc'⟩)
  simpa [f, commutatorElement_def] using hmap.symm

theorem y6_C1_elems (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ A ⊔ C0, ∃ a ∈ A, ∃ c ∈ C0, x = a * c := by
  intro x hx
  exact CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute (y6_C0_comm h) hx

theorem y6_AV_elems (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ A ⊔ V, ∃ a ∈ A, ∃ v ∈ V, x = a * v := by
  intro x hx
  exact CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute (y6_comm_A_V h) hx

theorem y6_C1_le_N_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    A ⊔ C0 ≤ normalizer (V : Set G) := by
  apply sup_le
  · rw [Subgroup.le_set_normalizer_iff]
    intro a ha v hv
    rw [y6_comm_A_V h a ha v hv]
    simpa [mul_assoc] using hv
  · rw [h.hC0, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have huV : u ∈ V := by rw [h.hV]; exact Subgroup.mem_zpowers u
      exact Subgroup.le_normalizer huV
    · rw [hx]
      intro v
      constructor
      · intro hv
        rw [y6_t_conj_V h hv]
        exact V.inv_mem hv
      · intro hv
        have h1 : t * (t * v * t⁻¹) * t⁻¹ = v := by
          rw [y6_t_inv_eq h]
          rw [show t * (t * v * t) * t = (t * t) * v * (t * t) by group]
          rw [y6_t_sq h]
          group
        have h2 := y6_t_conj_V h hv
        rw [h1] at h2
        rw [h2]
        exact V.inv_mem hv

theorem y6_comm_C1 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ c ∈ A ⊔ C0, ∀ x ∈ A ⊔ C0, ⁅c, x⁆ ∈ zpowers z := by
  intro c hc x hx
  obtain ⟨a, ha, c0, hc0, rfl⟩ := y6_C1_elems h c hc
  obtain ⟨a', ha', c0', hc0', rfl⟩ := y6_C1_elems h x hx
  rw [y6_comm_mul_mul h ha ha' hc0 hc0']
  exact Subgroup.mul_mem _ (y6_comm_A h a ha a' ha') (y6_comm_C0 h c0 hc0 c0' hc0')

theorem y6_cent_C1_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ A ⊔ C0, ((∀ v ∈ V, x * v = v * x) ↔ x ∈ A ⊔ V) := by
  intro x hx
  constructor
  · intro hcomm
    obtain ⟨a, ha, c0, hc0, hxeq⟩ := y6_C1_elems h x hx
    have huV : u ∈ V := by rw [h.hV]; exact Subgroup.mem_zpowers u
    have hxu : (a * c0) * u = u * (a * c0) := by
      rw [← hxeq]
      exact hcomm u huV
    have ha_u : a * u = u * a := h.u_cent a ha
    have hc0u : c0 * u = u * c0 := by
      have hstep : a * (c0 * u) = a * (u * c0) := by
        calc a * (c0 * u) = (a * c0) * u := by group
          _ = u * (a * c0) := hxu
          _ = a * (u * c0) := by
                rw [show u * (a * c0) = (u * a) * c0 by group, ← ha_u]
                group
      exact mul_left_cancel hstep
    rcases y6_C0_elems h c0 hc0 with hc0V | ⟨v', hv', hc0eq⟩
    · rw [hxeq]
      exact Subgroup.mul_mem_sup ha hc0V
    · exfalso
      have hv'u : v' * u = u * v' := y6_V_ab h hv' huV
      have htu : t * u = u * t := by
        have h1 : (v' * t) * u = u * (v' * t) := by
          rw [← hc0eq]
          exact hc0u
        have h2 : v' * (t * u) = v' * (u * t) := by
          calc v' * (t * u) = (v' * t) * u := by group
            _ = u * (v' * t) := h1
            _ = v' * (u * t) := by
                  rw [show u * (v' * t) = (u * v') * t by group, ← hv'u]
                  group
        exact mul_left_cancel h2
      have hu_eq : u = u⁻¹ := by
        have h' := h.t_inv
        rw [htu, mul_assoc, mul_inv_cancel, mul_one] at h'
        exact h'
      have h2 : u ^ 2 = 1 := by
        rw [pow_two]
        exact (mul_eq_one_iff_eq_inv).mpr hu_eq
      exact h.z_ne (by rw [← h.u_sq, h2])
  · intro hxAV
    obtain ⟨a, ha, v0, hv0, hxeq⟩ := y6_AV_elems h x hxAV
    intro v hv
    rw [hxeq]
    calc (a * v0) * v = a * (v0 * v) := by group
      _ = a * (v * v0) := by rw [y6_V_ab h hv0 hv]
      _ = (a * v) * v0 := by group
      _ = (v * a) * v0 := by rw [y6_comm_A_V h a ha v hv]
      _ = v * (a * v0) := by group

theorem y6_cen_AV (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ x ∈ A ⊔ V, (∀ w ∈ A ⊔ V, x * w = w * x) → x ∈ V := by
  intro x hx hcen
  obtain ⟨a, ha, v, hv, hxeq⟩ := y6_AV_elems h x hx
  have hcen' : ∀ w ∈ A ⊔ V, (a * v) * w = w * (a * v) := by
    intro w hw
    rw [← hxeq]
    exact hcen w hw
  have hcomm_A : ∀ b ∈ A, a * b = b * a := by
    intro b hb
    have h1 : (a * v) * b = b * (a * v) := hcen' b (Subgroup.mem_sup_left hb)
    have hvb : v * b = b * v := (y6_comm_A_V h b hb v hv).symm
    have h2 : (a * b) * v = (b * a) * v := by
      calc (a * b) * v = a * (b * v) := by group
        _ = a * (v * b) := by rw [← hvb]
        _ = (a * v) * b := by group
        _ = b * (a * v) := h1
        _ = (b * a) * v := by group
    exact mul_right_cancel h2
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := h.hA ▸ h.card_A
  have haA : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rw [← h.hA]; exact ha
  have hcomm_A' : ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * b = b * a := by
    intro b hb
    exact hcomm_A b (by rw [h.hA]; exact hb)
  rw [hxeq]
  rcases y6q8_cen h.rel h.z_ne hA32 a haA hcomm_A' with ha1 | haz
  · rw [ha1, one_mul]
    exact hv
  · rw [haz]
    exact V.mul_mem (y6_z_mem_V h) hv

theorem y6_t_not_mem_AV (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t ∉ A ⊔ V := by
  intro ht
  obtain ⟨a, ha, v, hv, htv⟩ := y6_AV_elems h t ht
  have haC0 : a ∈ C0 := by
    have hthis : a = t * v⁻¹ := by rw [htv]; group
    rw [hthis]
    exact C0.mul_mem (y6_t_mem_C0 h) (C0.inv_mem (y6_V_le_C0 h hv))
  have haZ : a ∈ zpowers z := by
    have hthis : a ∈ A ⊓ C0 := ⟨ha, haC0⟩
    rwa [y6_A_inf_C0 h] at hthis
  have haV : a ∈ V := (Subgroup.zpowers_le.mpr (y6_z_mem_V h)) haZ
  have htV : t ∈ V := by
    rw [htv]
    exact V.mul_mem haV hv
  have htcomm : t * u = u * t := by
    rw [h.hV] at htV
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htV
    rw [← hk]
    exact (Commute.zpow_self u k).eq
  have hu_eq : u = u⁻¹ := by
    have h' := h.t_inv
    rw [htcomm, mul_assoc, mul_inv_cancel, mul_one] at h'
    exact h'
  have h2 : u ^ 2 = 1 := by
    rw [pow_two]
    exact (mul_eq_one_iff_eq_inv).mpr hu_eq
  exact h.z_ne (by rw [← h.u_sq, h2])

end CFSG.OddStandard.HigherRank.YamadaG23