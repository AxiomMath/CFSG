module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CfgB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Char

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_s_t_inv (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (y7a_t_sq h)

private lemma y7a_s_t_ne_z (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : t ≠ z := by
  intro htz
  have hcomm : t * d = d * t := y7a_d_cent h t (by rw [htz]; exact y7a_z_mem_A h)
  have htd : t * d * t⁻¹ = d := by rw [hcomm]; group
  rw [y7a_tdt h] at htd
  refine h.cfg.z_ne ?_
  have hh := congrArg (fun w => w * d⁻¹) htd
  simpa [mul_assoc] using hh

private lemma y7a_s_conj_t_order (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) (x : G) :
    orderOf (x * t * x⁻¹) = 2 := by
  have h1 := MulEquiv.orderOf_eq (MulAut.conj x) t
  rw [MulAut.conj_apply] at h1
  rw [h1, h.cfg.t_ord]

private lemma y7a_s_mem_normalizer_of_conj {H : Subgroup G} {x : G}
    (h1 : ∀ c ∈ H, x * c * x⁻¹ ∈ H) (h2 : ∀ c ∈ H, x⁻¹ * c * x ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨h1 c, fun hc => ?_⟩
  have := h2 (x * c * x⁻¹) hc
  rwa [show x⁻¹ * (x * c * x⁻¹) * x = c by group] at this

private lemma y7a_s_conj_mem_closure {S : Set G} {K : Subgroup G} {x : G}
    (hgen : ∀ y ∈ S, x * y * x⁻¹ ∈ K) :
    ∀ c ∈ Subgroup.closure S, x * c * x⁻¹ ∈ K := by
  have hle : Subgroup.closure S ≤ K.comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_comap.mpr (show x * y * x⁻¹ ∈ K from hgen y hy)
  intro c hc
  exact Subgroup.mem_comap.mp (hle hc)

private lemma y7a_s_conj_At_mem (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G))
    (hxt : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t) :
    ∀ c ∈ A ⊔ zpowers t, x * c * x⁻¹ ∈ A ⊔ zpowers t := by
  intro c hc
  have hzC : ∀ w ∈ A ⊔ C0, w * z = z * w := by
    intro w hw
    obtain ⟨a, ha, c0, hc0, rfl⟩ := y6_C1_elems h.cfg w hw
    have haz : a * z = z * a :=
      y6q8_z_central h.cfg.rel a (by rw [← h.cfg.hA]; exact ha)
    have htzeq : t * z = z * t := (h.cfg.t_cent z (y7a_z_mem_A h)).symm
    have hc0z : c0 * z = z * c0 := by
      have hc0' : c0 ∈ closure ({d * t, t} : Set G) := by rwa [h.cfg.hC0] at hc0
      obtain ⟨i, hi | hi⟩ :=
        y6_d8_elems h.cfg.u_ord h.cfg.t_ord h.cfg.t_inv c0 hc0'
      · have huz : (d * t) ^ i * z = z * (d * t) ^ i := by
          rw [← h.cfg.u_sq]; group
        rw [hi]; exact huz
      · have huz : (d * t) ^ i * z = z * (d * t) ^ i := by
          rw [← h.cfg.u_sq]; group
        rw [hi]
        calc (d * t) ^ i * t * z = (d * t) ^ i * (t * z) := by group
          _ = (d * t) ^ i * (z * t) := by rw [htzeq]
          _ = ((d * t) ^ i * z) * t := by group
          _ = (z * (d * t) ^ i) * t := by rw [huz]
          _ = z * ((d * t) ^ i * t) := by group
    calc a * c0 * z = a * (c0 * z) := by group
      _ = a * (z * c0) := by rw [hc0z]
      _ = (a * z) * c0 := by group
      _ = (z * a) * c0 := by rw [haz]
      _ = z * (a * c0) := by group
  have hcC1 : c ∈ (A ⊔ C0) ⊓ centralizer ({t} : Set G) := by
    refine ⟨sup_le_sup_left (Subgroup.zpowers_le.mpr (y7a_t_mem_C0 h)) _ hc, ?_⟩
    have hle : A ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (h.cfg.t_cent a ha).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
    exact hle hc
  rw [← y6_cent_C1_t h.cfg]
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

theorem y7a_C1_le_K (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    A ⊔ C0 ≤ CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V := by
  intro c hc
  refine ⟨Subgroup.le_normalizer hc, y7a_C1_le_N_V h hc, fun k hk => ?_⟩
  exact y7a_comm_C1 h k hk c hc

theorem y7a_K_le_NC0 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V ≤ normalizer (C0 : Set G) := by
  intro x hx
  have hx0 := hx
  obtain ⟨-, hxV, hxk⟩ := hx
  have htC1 : t ∈ A ⊔ C0 := Subgroup.mem_sup_right (y7a_t_mem_C0 h)
  have hxt_mem : x * t * x⁻¹ ∈ C0 := by
    have hv : ⁅t, x⁆ ∈ V := hxk t htC1
    have hconj : x * t * x⁻¹ = ⁅t, x⁆⁻¹ * t := by rw [commutatorElement_def]; group
    rw [hconj]
    exact C0.mul_mem (C0.inv_mem (y7a_V_le_C0 h hv)) (y7a_t_mem_C0 h)
  have hgen : ∀ y ∈ ({d * t, t} : Set G), x * y * x⁻¹ ∈ C0 := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      have hd : x * d * x⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hxV d).mp (y7a_d_mem_V h)
      have hdt : x * (d * t) * x⁻¹ = (x * d * x⁻¹) * (x * t * x⁻¹) := by group
      rw [hdt]
      exact C0.mul_mem (y7a_V_le_C0 h hd) hxt_mem
    · rw [hy]; exact hxt_mem
  have hxinv : x⁻¹ ∈ CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V :=
    (CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V).inv_mem hx0
  obtain ⟨-, hxinvV, hxinvk⟩ := hxinv
  have hxit_mem : x⁻¹ * t * x ∈ C0 := by
    have hv : ⁅t, x⁻¹⁆ ∈ V := hxinvk t htC1
    have hconj : x⁻¹ * t * x = ⁅t, x⁻¹⁆⁻¹ * t := by rw [commutatorElement_def]; group
    rw [hconj]
    exact C0.mul_mem (C0.inv_mem (y7a_V_le_C0 h hv)) (y7a_t_mem_C0 h)
  have hgen2 : ∀ y ∈ ({d * t, t} : Set G), x⁻¹ * y * x ∈ C0 := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      have hd : x⁻¹ * d * x ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp hxinvV d).mp (y7a_d_mem_V h)
        simpa using this
      have hdt : x⁻¹ * (d * t) * x = (x⁻¹ * d * x) * (x⁻¹ * t * x) := by group
      rw [hdt]
      exact C0.mul_mem (y7a_V_le_C0 h hd) hxit_mem
    · rw [hy]; exact hxit_mem
  have h1 : ∀ c ∈ C0, x * c * x⁻¹ ∈ C0 := by
    intro c hc
    rw [h.cfg.hC0] at hc
    exact y7a_s_conj_mem_closure hgen c hc
  have h2 : ∀ c ∈ C0, x⁻¹ * c * x ∈ C0 := by
    intro c hc
    rw [h.cfg.hC0] at hc
    have := y7a_s_conj_mem_closure (x := x⁻¹) (K := C0)
      (fun y hy => by simpa using hgen2 y hy) c hc
    simpa using this
  exact y7a_s_mem_normalizer_of_conj h1 h2

theorem y7a_mem_NAt_iff (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) :
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
            exact (Commute.zpow_right (show Commute a t from h.cfg.t_cent a ha) k).eq
          obtain ⟨a, ha, c', hc', rfl⟩ :=
            CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcomm hc
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
          have hta : t * a = a * t := (h.cfg.t_cent a ha).symm
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
    have hcases := y6_cen_At h.cfg (x * t * x⁻¹) hy hcen
    rcases hcases with h1 | hz | ht | hzt
    · exfalso
      have := y7a_s_conj_t_order h x
      rw [h1] at this
      simp at this
    · exfalso
      have hxz : x * z * x⁻¹ = z := y7a_fix_z h hx1
      have h1 : x * t * x⁻¹ = x * z * x⁻¹ := by rw [hz, hxz]
      have h2 : t = z := by
        have := congrArg (fun w => x⁻¹ * w * x) h1
        simpa [mul_assoc] using this
      exact y7a_s_t_ne_z h h2
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
          have := y7a_fix_z h (Subgroup.inv_mem _ hx1)
          simpa using this
        have h1 : t = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by
          calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
            _ = x⁻¹ * (z * t) * x := by rw [hxt]
            _ = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by group
        rw [hxiz] at h1
        have h2 : z * t = z * (z * (x⁻¹ * t * x)) := by rw [← h1]
        calc x⁻¹ * t * x = (z * z) * (x⁻¹ * t * x) := by rw [y7a_z_sq h, one_mul]
          _ = z * (z * (x⁻¹ * t * x)) := by group
          _ = z * t := by rw [← h1]
    refine y7a_s_mem_normalizer_of_conj (y7a_s_conj_At_mem h hx1 hxt) ?_
    have hx1i : x⁻¹ ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) := Subgroup.inv_mem _ hx1
    have hc := y7a_s_conj_At_mem h hx1i (x := x⁻¹) (by simpa using hxit)
    intro c hc'
    simpa using hc c hc'

theorem y7a_stab_iff (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) :
    t⁻¹ * (x * t * x⁻¹) ∈ V ↔ x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) := by
  have ht_inv : t⁻¹ = t := y7a_s_t_inv h
  have htz : t * z = z * t := (h.cfg.t_cent z (y7a_z_mem_A h)).symm
  have hzd_comm : z * d = d * z := y7a_d_cent h z (y7a_z_mem_A h)
  have htd_sq : (t * d) * (t * d) = z := by
    calc (t * d) * (t * d) = (t * d * t⁻¹) * d := by rw [ht_inv]; group
      _ = (z * d) * d := by rw [y7a_tdt h]
      _ = z := by rw [mul_assoc, y7a_d_sq h, mul_one]
  constructor
  · intro hw
    let w : G := t⁻¹ * (x * t * x⁻¹)
    have hwV : w ∈ V := hw
    have hxt : x * t * x⁻¹ = t * w := by
      show x * t * x⁻¹ = t * (t⁻¹ * (x * t * x⁻¹))
      group
    have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      have hp := pow_orderOf_eq_one (x * t * x⁻¹)
      rw [y7a_s_conj_t_order h x] at hp
      simpa [pow_two] using hp
    have htw : (t * w) * (t * w) = 1 := by rw [← hxt]; exact hsq
    rcases y7a_V_elems h w hwV with h1 | hz | hd | hzd
    · rw [y7a_mem_NAt_iff h hx1]
      left
      rw [hxt, h1, mul_one]
    · rw [y7a_mem_NAt_iff h hx1]
      right
      rw [hxt, hz]
      exact htz
    · exfalso
      have h1 : (t * w) * (t * w) = z := by rw [hd]; exact htd_sq
      rw [htw] at h1
      exact h.cfg.z_ne h1.symm
    · exfalso
      have hA : z * (t * d) = (t * d) * z := by
        calc z * (t * d) = (z * t) * d := by group
          _ = (t * z) * d := by rw [← htz]
          _ = t * (z * d) := by group
          _ = t * (d * z) := by rw [hzd_comm]
          _ = (t * d) * z := by group
      have he : t * (z * d) = z * (t * d) := by
        calc t * (z * d) = (t * z) * d := by group
          _ = (z * t) * d := by rw [htz]
          _ = z * (t * d) := by group
      have h1 : (t * w) * (t * w) = z := by
        rw [hzd, he]
        calc (z * (t * d)) * (z * (t * d)) = z * ((t * d) * z) * (t * d) := by group
          _ = z * (z * (t * d)) * (t * d) := by rw [← hA]
          _ = (z * z) * ((t * d) * (t * d)) := by group
          _ = z := by rw [y7a_z_sq h, one_mul, htd_sq]
      rw [htw] at h1
      exact h.cfg.z_ne h1.symm
  · intro hxN
    rcases (y7a_mem_NAt_iff h hx1).mp hxN with hxt | hxt
    · rw [hxt]
      have : t⁻¹ * t = 1 := inv_mul_cancel t
      rw [this]
      exact V.one_mem
    · rw [hxt]
      have : t⁻¹ * (z * t) = z := by
        rw [ht_inv]
        calc t * (z * t) = (t * z) * t := by group
          _ = (z * t) * t := by rw [htz]
          _ = z := by rw [mul_assoc, y7a_t_sq h, mul_one]
      rw [this]
      exact y7a_z_mem_V h

end CFSG.OddStandard.HigherRank.YamadaG23
