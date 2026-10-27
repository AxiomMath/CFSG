module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Cfg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_t_inv (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (y7a_t_sq h)

private lemma y7a_V_ab (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {v w : G}
    (hv : v ∈ V) (hw : w ∈ V) : v * w = w * v := by
  have hgen : ∀ x ∈ ({z, d} : Set G), ∀ y ∈ ({z, d} : Set G), Commute x y := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hxz | hxd <;> rcases hy with hyz | hyd
    · rw [hxz, hyz]
    · rw [hxz, hyd]; exact y7a_d_cent h z (y7a_z_mem_A h)
    · rw [hxd, hyz]; exact (y7a_d_cent h z (y7a_z_mem_A h)).symm
    · rw [hxd, hyd]
  rw [h.hV] at hv hw
  have hmain : ∀ w ∈ Subgroup.closure ({z, d} : Set G), Commute v w := by
    refine Subgroup.closure_induction (p := fun v _ =>
      ∀ w ∈ Subgroup.closure ({z, d} : Set G), Commute v w) ?_ ?_ ?_ ?_ hv
    · intro x hx w hw
      exact Subgroup.closure_induction (p := fun w _ => Commute x w)
        (fun y hy => hgen x hx y hy) (Commute.one_right x)
        (fun y c _ _ hy hc => Commute.mul_right hy hc)
        (fun y _ hy => Commute.inv_right hy) hw
    · intro w _
      exact Commute.one_left w
    · intro x y _ _ hx hy w hw
      exact Commute.mul_left (hx w hw) (hy w hw)
    · intro x _ hx w hw
      exact Commute.inv_left (hx w hw)
  exact (hmain w hw).eq

private lemma y7a_dt_pow (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ i : ℕ, (d * t) ^ i ∈ V ∨ ∃ v ∈ V, (d * t) ^ i = v * t := by
  intro i
  induction i with
  | zero => left; rw [pow_zero]; exact V.one_mem
  | succ i ih =>
    rcases ih with hv | ⟨v, hv, hveq⟩
    · right
      refine ⟨(d * t) ^ i * d, V.mul_mem hv (y7a_d_mem_V h), ?_⟩
      rw [pow_succ]
      group
    · left
      have htdt : t * d * t = z * d := by
        have hh := y7a_tdt h
        rwa [y7a_t_inv h] at hh
      rw [pow_succ, hveq, show (v * t) * (d * t) = v * (t * d * t) by group, htdt]
      exact V.mul_mem hv (V.mul_mem (y7a_z_mem_V h) (y7a_d_mem_V h))

private lemma y7a_C0_elems (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ c ∈ C0, c ∈ V ∨ ∃ v ∈ V, c = v * t := by
  intro c hc
  rw [h.cfg.hC0] at hc
  rcases y6_d8_elems h.cfg.u_ord h.cfg.t_ord h.cfg.t_inv c hc with ⟨i, hi | hi⟩
  · rcases y7a_dt_pow h i with hv | ⟨v, hv, hveq⟩
    · left; rw [hi]; exact hv
    · right; exact ⟨v, hv, by rw [hi, hveq]⟩
  · rcases y7a_dt_pow h i with hv | ⟨v, hv, hveq⟩
    · right; exact ⟨(d * t) ^ i, hv, hi⟩
    · left; rw [hi, hveq, mul_assoc, y7a_t_sq h, mul_one]; exact hv

private lemma y7a_cent_C0_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ c ∈ C0, ((∀ v ∈ V, c * v = v * c) ↔ c ∈ V) := by
  intro c hc
  constructor
  · intro hcomm
    rcases y7a_C0_elems h c hc with hv | ⟨v, hv, rfl⟩
    · exact hv
    · exfalso
      have hcd : (v * t) * d = d * (v * t) := hcomm d (y7a_d_mem_V h)
      have hconj1 : (v * t) * d * (v * t)⁻¹ = d := by rw [hcd]; group
      have htdt : t * d * t = z * d := by
        have hh := y7a_tdt h
        rwa [y7a_t_inv h] at hh
      have hconj2 : (v * t) * d * (v * t)⁻¹ = z * d := by
        rw [mul_inv_rev, y7a_t_inv h]
        calc (v * t) * d * (t * v⁻¹) = v * (t * d * t) * v⁻¹ := by group
          _ = v * (z * d) * v⁻¹ := by rw [htdt]
          _ = z * d := by
              rw [y7a_V_ab h hv (V.mul_mem (y7a_z_mem_V h) (y7a_d_mem_V h))]
              group
      rw [hconj1] at hconj2
      have hz1 : z = 1 := by
        have h : z * d = 1 * d := by simpa using hconj2.symm
        exact mul_right_cancel h
      exact h.cfg.z_ne hz1
  · intro hv v' hv'
    exact y7a_V_ab h hv hv'

private lemma y7a_AV_inf_C0 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    (A ⊔ V) ⊓ C0 = V := by
  refine le_antisymm ?_ (le_inf le_sup_right (y7a_V_le_C0 h))
  intro x hx
  obtain ⟨hxAV, hxC0⟩ := hx
  obtain ⟨a, ha, v, hv, rfl⟩ := y7a_AV_elems h x hxAV
  have haC0 : a ∈ C0 := by
    have hthis : a = (a * v) * v⁻¹ := by group
    rw [hthis]
    exact C0.mul_mem hxC0 (C0.inv_mem (y7a_V_le_C0 h hv))
  have haZ : a ∈ zpowers z := by
    have hmem : a ∈ A ⊓ C0 := ⟨ha, haC0⟩
    rwa [y6_A_inf_C0 h.cfg] at hmem
  exact V.mul_mem ((Subgroup.zpowers_le.mpr (y7a_z_mem_V h)) haZ) hv

private lemma y7a_t_conj_dt (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) (j : ℕ) :
    t * (d * t) ^ j * t = ((d * t) ^ j)⁻¹ := by
  have h1 : t * (d * t) ^ j * t⁻¹ = ((d * t) ^ j)⁻¹ := by
    rw [← conj_pow, h.cfg.t_inv, inv_pow]
  simpa [y7a_t_inv h] using h1

private lemma y7a_C0_sq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ c ∈ C0, c * c ∈ V := by
  intro c hc
  rw [h.cfg.hC0] at hc
  rcases y6_d8_elems h.cfg.u_ord h.cfg.t_ord h.cfg.t_inv c hc with ⟨i, hi | hi⟩
  · rw [hi]
    have hsq : (d * t) ^ i * (d * t) ^ i = z ^ i := by
      rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, h.cfg.u_sq]
    rw [hsq]
    exact (Subgroup.zpowers_le.mpr (y7a_z_mem_V h)) (Subgroup.npow_mem_zpowers z i)
  · rw [hi]
    have hsq : ((d * t) ^ i * t) * ((d * t) ^ i * t) = 1 := by
      rw [show ((d * t) ^ i * t) * ((d * t) ^ i * t)
            = (d * t) ^ i * (t * (d * t) ^ i * t) by group, y7a_t_conj_dt h i]
      exact mul_inv_cancel _
    rw [hsq]
    exact V.one_mem

private lemma y7a_mem_zpowers_z (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {w : G} :
    w ∈ zpowers z ↔ w = 1 ∨ w = z := by
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h2 : z ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
      exact y7a_z_sq h
    rw [zpow_eq_zpow_emod k (n := (2 : ℤ)) h2]
    have hge : 0 ≤ k % 2 := Int.emod_nonneg k (show (2 : ℤ) ≠ 0 by norm_num)
    have hlt : k % 2 < 2 := Int.emod_lt_of_pos k (show (0 : ℤ) < 2 by norm_num)
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (hw1 | hwz)
    · rw [hw1]; exact Subgroup.one_mem _
    · rw [hwz]; exact Subgroup.mem_zpowers z

theorem y7a_cent_C1_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ C0, ((∀ v ∈ V, x * v = v * x) ↔ x ∈ A ⊔ V) := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := y6_C1_elems h.cfg x hx
  have hacomm : ∀ v ∈ V, a * v = v * a := fun v hv =>
    y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hxc : ((∀ v ∈ V, (a * c) * v = v * (a * c)) ↔ (∀ v ∈ V, c * v = v * c)) := by
    constructor
    · intro hh v hv
      have h1 : a * (c * v) = a * (v * c) := by
        calc a * (c * v) = (a * c) * v := by group
          _ = v * (a * c) := hh v hv
          _ = (v * a) * c := by group
          _ = (a * v) * c := by rw [← hacomm v hv]
          _ = a * (v * c) := by group
      exact mul_left_cancel h1
    · intro hh v hv
      calc (a * c) * v = a * (c * v) := by group
        _ = a * (v * c) := by rw [hh v hv]
        _ = (a * v) * c := by group
        _ = (v * a) * c := by rw [hacomm v hv]
        _ = v * (a * c) := by group
  have hmem : (a * c ∈ A ⊔ V) ↔ c ∈ V := by
    constructor
    · intro hm
      have hcAV : c ∈ A ⊔ V := by
        have hthis : c = a⁻¹ * (a * c) := by group
        rw [hthis]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem ha)) hm
      have hmem' : c ∈ (A ⊔ V) ⊓ C0 := ⟨hcAV, hc⟩
      rwa [y7a_AV_inf_C0 h] at hmem'
    · intro hv
      exact Subgroup.mul_mem_sup ha hv
  rw [hxc, y7a_cent_C0_V h c hc, hmem]

theorem y7a_cen_AV (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ V, (∀ w ∈ A ⊔ V, x * w = w * x) → x ∈ V := by
  intro x hx hcen
  obtain ⟨a, ha, v, hv, rfl⟩ := y7a_AV_elems h x hx
  have hcomm_A : ∀ b ∈ A, a * b = b * a := by
    intro b hb
    have h1 : (a * v) * b = b * (a * v) := hcen b (Subgroup.mem_sup_left hb)
    have hvb : v * b = b * v := (y6_C0_comm h.cfg b hb v (y7a_V_le_C0 h hv)).symm
    have h2 : (a * b) * v = (b * a) * v := by
      calc (a * b) * v = a * (b * v) := by group
        _ = a * (v * b) := by rw [hvb]
        _ = (a * v) * b := by group
        _ = b * (a * v) := h1
        _ = (b * a) * v := by group
    exact mul_right_cancel h2
  have haA : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
    rw [← h.cfg.hA]; exact ha
  have hcomm_A' : ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * b = b * a :=
    fun b hb => hcomm_A b (by rw [h.cfg.hA]; exact hb)
  rcases y6q8_cen h.cfg.rel h.cfg.z_ne (h.cfg.hA ▸ h.cfg.card_A) a haA hcomm_A' with ha1 | haz
  · rw [ha1, one_mul]; exact hv
  · rw [haz]; exact V.mul_mem (y7a_z_mem_V h) hv

theorem y7a_t_not_mem_AV (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t ∉ A ⊔ V := by
  intro ht
  obtain ⟨a, ha, v, hv, htav⟩ := y7a_AV_elems h t ht
  have hdv : v * d = d * v := y7a_V_ab h hv (y7a_d_mem_V h)
  have had : a * d = d * a := y7a_d_cent h a ha
  have hcomm : t * d = d * t := by
    rw [htav]
    calc (a * v) * d = a * (v * d) := by group
      _ = a * (d * v) := by rw [hdv]
      _ = (a * d) * v := by group
      _ = (d * a) * v := by rw [had]
      _ = d * (a * v) := by group
  have hconj : t * d * t⁻¹ = d := by rw [hcomm]; group
  rw [y7a_tdt h] at hconj
  have hz1 : z = 1 := by
    have h : z * d = 1 * d := by simpa using hconj
    exact mul_right_cancel h
  exact h.cfg.z_ne hz1

theorem y7a_AV_le_C1 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : A ⊔ V ≤ A ⊔ C0 :=
  sup_le le_sup_left ((y7a_V_le_C0 h).trans le_sup_right)

theorem y7a_index_AV (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ C0, ∀ y ∈ A ⊔ C0, x ∉ A ⊔ V → y ∉ A ⊔ V → x * y ∈ A ⊔ V := by
  intro x hx y hy hxnot hynot
  rcases y7a_C1_elems h x hx with hx1 | hx2
  · exact absurd (by obtain ⟨a, ha, v, hv, rfl⟩ := hx1
                     exact Subgroup.mul_mem_sup ha hv) hxnot
  · rcases y7a_C1_elems h y hy with hy1 | hy2
    · exact absurd (by obtain ⟨a, ha, v, hv, rfl⟩ := hy1
                       exact Subgroup.mul_mem_sup ha hv) hynot
    · obtain ⟨a, ha, v, hv, rfl⟩ := hx2
      obtain ⟨a', ha', v', hv', rfl⟩ := hy2
      have ht_mem : t ∈ normalizer (V : Set G) :=
        y7a_C1_le_N_V h (Subgroup.mem_sup_right (y7a_t_mem_C0 h))
      have htvt : t * v * t⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.mp ht_mem v).mp hv
      have htvt' : t * v * t ∈ V := by simpa [y7a_t_inv h] using htvt
      have hprod : (a * t * v) * (a' * t * v') = (a * a') * ((t * v * t) * v') := by
        have ha'v : v * a' = a' * v := (y6_C0_comm h.cfg a' ha' v (y7a_V_le_C0 h hv)).symm
        have ha't : t * a' = a' * t := (h.cfg.t_cent a' ha').symm
        calc (a * t * v) * (a' * t * v') = a * t * (v * a') * t * v' := by group
          _ = a * t * (a' * v) * t * v' := by rw [ha'v]
          _ = a * (t * a') * v * t * v' := by group
          _ = a * (a' * t) * v * t * v' := by rw [ha't]
          _ = (a * a') * ((t * v * t) * v') := by group
      rw [hprod]
      exact Subgroup.mul_mem_sup (A.mul_mem ha ha') (V.mul_mem htvt' hv')

theorem y7a_comm_C1 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ c ∈ A ⊔ C0, ∀ x ∈ A ⊔ C0, ⁅c, x⁆ ∈ V := by
  intro c hc x hx
  exact (Subgroup.zpowers_le.mpr (y7a_z_mem_V h)) (y6_comm_C1 h.cfg c hc x hx)

theorem y7a_sq_C1 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ x ∈ A ⊔ C0, x * x ∈ V := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := y6_C1_elems h.cfg x hx
  have hac : a * c = c * a := y6_C0_comm h.cfg a ha c hc
  have haA : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rw [← h.cfg.hA]; exact ha
  have hsq : (a * c) * (a * c) = a ^ 2 * c ^ 2 := by
    calc (a * c) * (a * c) = a * (c * a) * c := by group
      _ = a * (a * c) * c := by rw [hac.symm]
      _ = a ^ 2 * c ^ 2 := by rw [pow_two, pow_two]; group
  rw [hsq]
  rcases y6q8_sq_cases h.cfg.rel a haA with ha2 | ha2
  · rw [ha2, one_mul, pow_two]; exact y7a_C0_sq h c hc
  · rw [ha2, pow_two]; exact V.mul_mem (y7a_z_mem_V h) (y7a_C0_sq h c hc)

theorem y7a_fix_z (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hx : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) : x * z * x⁻¹ = z := by
  have ha₁ : a₁ ∈ A := by rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hb₁ : b₁ ∈ A := by rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hxa : x * a₁ * x⁻¹ ∈ A ⊔ C0 :=
    (Subgroup.mem_set_normalizer_iff.mp hx a₁).mp (Subgroup.mem_sup_left ha₁)
  have hxb : x * b₁ * x⁻¹ ∈ A ⊔ C0 :=
    (Subgroup.mem_set_normalizer_iff.mp hx b₁).mp (Subgroup.mem_sup_left hb₁)
  have hcomm : ⁅x * a₁ * x⁻¹, x * b₁ * x⁻¹⁆ ∈ zpowers z :=
    y6_comm_C1 h.cfg _ hxa _ hxb
  have hconj : x * z * x⁻¹ = ⁅x * a₁ * x⁻¹, x * b₁ * x⁻¹⁆ := by
    rw [show z = ⁅a₁, b₁⁆ from h.cfg.rel.comm1.symm]
    exact conjugate_commutatorElement (g₁ := a₁) (g₂ := b₁) (g₃ := x)
  have hmem : x * z * x⁻¹ ∈ zpowers z := by rw [hconj]; exact hcomm
  rcases (y7a_mem_zpowers_z h).mp hmem with h1 | hz
  · exfalso
    have hz1 : z = 1 := by
      have := congrArg (fun y => x⁻¹ * y * x) h1
      simpa [mul_assoc] using this
    exact h.cfg.z_ne hz1
  · exact hz

theorem y7a_conj_AV (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G)) :
    ∀ w, w ∈ A ⊔ V ↔ x * w * x⁻¹ ∈ A ⊔ V := by
  intro w
  have hxw_c1 : ∀ y, y ∈ A ⊔ C0 → x * y * x⁻¹ ∈ A ⊔ C0 := fun y hy =>
    (Subgroup.mem_set_normalizer_iff.mp hx1 y).mp hy
  have hxinv1 : x⁻¹ ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) := Subgroup.inv_mem _ hx1
  have hxinv_c1 : ∀ y, y ∈ A ⊔ C0 → x⁻¹ * y * x ∈ A ⊔ C0 := fun y hy =>
    by simpa using (Subgroup.mem_set_normalizer_iff.mp hxinv1 y).mp hy
  have hxw_v : ∀ y, y ∈ V → x * y * x⁻¹ ∈ V := fun y hy =>
    (Subgroup.mem_set_normalizer_iff.mp hx2 y).mp hy
  have hxinv2 : x⁻¹ ∈ normalizer (V : Set G) := Subgroup.inv_mem _ hx2
  have hxinv_v : ∀ y, y ∈ V → x⁻¹ * y * x ∈ V := fun y hy =>
    by simpa using (Subgroup.mem_set_normalizer_iff.mp hxinv2 y).mp hy
  constructor
  · intro hw
    have hwC1 : w ∈ A ⊔ C0 := y7a_AV_le_C1 h hw
    have hwc : ∀ v ∈ V, w * v = v * w := (y7a_cent_C1_V h w hwC1).2 hw
    refine (y7a_cent_C1_V h (x * w * x⁻¹) (hxw_c1 w hwC1)).1 ?_
    intro v hv
    have hv' : x⁻¹ * v * x ∈ V := hxinv_v v hv
    have h1 : w * (x⁻¹ * v * x) = (x⁻¹ * v * x) * w := hwc (x⁻¹ * v * x) hv'
    calc (x * w * x⁻¹) * v = x * (w * (x⁻¹ * v * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * v * x) * w) * x⁻¹ := by rw [h1]
      _ = v * (x * w * x⁻¹) := by group
  · intro hw
    have hwC1 : x * w * x⁻¹ ∈ A ⊔ C0 := y7a_AV_le_C1 h hw
    have hwC1' : w ∈ A ⊔ C0 := by
      have h := hxinv_c1 (x * w * x⁻¹) hwC1
      have heq : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rwa [heq] at h
    have hwc : ∀ v ∈ V, (x * w * x⁻¹) * v = v * (x * w * x⁻¹) :=
      (y7a_cent_C1_V h (x * w * x⁻¹) hwC1).2 hw
    refine (y7a_cent_C1_V h w hwC1').1 ?_
    intro v hv
    have hv' : x * v * x⁻¹ ∈ V := hxw_v v hv
    have h1 : (x * w * x⁻¹) * (x * v * x⁻¹) = (x * v * x⁻¹) * (x * w * x⁻¹) :=
      hwc (x * v * x⁻¹) hv'
    calc w * v = x⁻¹ * ((x * w * x⁻¹) * (x * v * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * v * x⁻¹) * (x * w * x⁻¹)) * x := by rw [h1]
      _ = v * w := by group

end CFSG.OddStandard.HigherRank.YamadaG23
