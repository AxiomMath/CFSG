module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B0b
public import CFSG.GH74.GLS.Basic

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

private lemma y6_t_mul_u (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t * u = u⁻¹ * t := by
  have h' := congrArg (· * t) h.t_inv
  simpa [mul_assoc] using h'

private lemma y6_t_mul_u_inv (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t * u⁻¹ = u * t := by
  have h' : u * t = t * u⁻¹ := by
    have h2 : t * (t * u * t⁻¹) = t * u⁻¹ := congrArg (fun z => t * z) h.t_inv
    calc u * t = (t * t) * u * t⁻¹ := by rw [y6_t_sq h, one_mul, y6_t_inv_eq h]
      _ = t * (t * u * t⁻¹) := by group
      _ = t * u⁻¹ := h2
  exact h'.symm

private lemma y6_u_conj_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : u * t * u⁻¹ = z * t := by
  calc u * t * u⁻¹ = u * (t * u⁻¹) := by group
    _ = u * (u * t) := by rw [y6_t_mul_u_inv h]
    _ = u ^ 2 * t := by rw [pow_two, mul_assoc]
    _ = z * t := by rw [h.u_sq]

private lemma y6_u_inv_conj_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    u⁻¹ * t * u = z * t := by
  have hzsq : z * z = 1 := by simpa [pow_two] using h.rel.z_sq
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzsq
  have hu2inv : (u⁻¹) ^ 2 = z := by
    rw [inv_pow, h.u_sq, hzinv]
  calc u⁻¹ * t * u = u⁻¹ * (t * u) := by group
    _ = u⁻¹ * (u⁻¹ * t) := by rw [y6_t_mul_u h]
    _ = (u⁻¹) ^ 2 * t := by rw [pow_two, mul_assoc]
    _ = z * t := by rw [hu2inv]

private lemma y6_mem_normalizer_of_conj {H : Subgroup G} {x : G}
    (h1 : ∀ c ∈ H, x * c * x⁻¹ ∈ H) (h2 : ∀ c ∈ H, x⁻¹ * c * x ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨h1 c, fun hc => ?_⟩
  have := h2 (x * c * x⁻¹) hc
  rwa [show x⁻¹ * (x * c * x⁻¹) * x = c by group] at this

private lemma y6_conj_mem_closure {S : Set G} {K : Subgroup G} {x : G}
    (hgen : ∀ y ∈ S, x * y * x⁻¹ ∈ K) :
    ∀ c ∈ Subgroup.closure S, x * c * x⁻¹ ∈ K := by
  have hle : Subgroup.closure S ≤ K.comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_comap.mpr (show x * y * x⁻¹ ∈ K from hgen y hy)
  intro c hc
  exact Subgroup.mem_comap.mp (hle hc)

private lemma y6_conj_mem_sup_At {x : G}
    (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (ht : x * t * x⁻¹ ∈ A ⊔ zpowers t) :
    ∀ c ∈ A ⊔ zpowers t, x * c * x⁻¹ ∈ A ⊔ zpowers t := by
  have hle : A ⊔ zpowers t ≤ (A ⊔ zpowers t).comap (MulAut.conj x).toMonoidHom := by
    apply sup_le
    · intro a ha
      exact Subgroup.mem_comap.mpr
        (show x * a * x⁻¹ ∈ A ⊔ zpowers t from Subgroup.mem_sup_left (hA a ha))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_comap.mpr (show x * t * x⁻¹ ∈ A ⊔ zpowers t from ht)
  intro c hc
  exact Subgroup.mem_comap.mp (hle hc)

private lemma y6_pow_mem_zpowers_of_eq_inv (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {i : ℕ}
    (hi : u ^ i = (u⁻¹) ^ i) : u ^ i ∈ zpowers z := by
  have hui : u ^ i = (u ^ i)⁻¹ := by
    have h := hi
    rwa [inv_pow] at h
  have hpow2 : (u ^ i) ^ 2 = 1 := by
    rw [pow_two]
    exact (mul_eq_one_iff_eq_inv).mpr hui
  have h2 : u ^ (2 * i) = 1 := by
    rw [← pow_mul] at hpow2
    simpa [Nat.mul_comm] using hpow2
  have hdvd : 4 ∣ 2 * i := by
    have := (orderOf_dvd_iff_pow_eq_one (x := u) (n := 2 * i)).mpr h2
    rwa [h.u_ord] at this
  obtain ⟨k, hk⟩ := hdvd
  have hik : i = 2 * k := by omega
  rw [hik, show u ^ (2 * k) = z ^ k by rw [pow_mul, h.u_sq]]
  exact Subgroup.npow_mem_zpowers z k

theorem y6_C1_le_K (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    A ⊔ C0 ≤ CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V := by
  intro c hc
  refine ⟨Subgroup.le_normalizer hc, y6_C1_le_N_V h hc, fun k hk => ?_⟩
  exact Subgroup.zpowers_le.mpr (y6_z_mem_V h) (y6_comm_C1 h k hk c hc)

theorem y6_K_le_NC0 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V ≤ normalizer (C0 : Set G) := by
  intro x hx
  have hx' := hx
  obtain ⟨-, hxV, hxk⟩ := hx'
  have huV : u ∈ V := by rw [h.hV]; exact Subgroup.mem_zpowers u
  have hgen : ∀ y ∈ ({u, t} : Set G), x * y * x⁻¹ ∈ C0 := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hyu | hyt
    · rw [hyu]
      exact y6_V_le_C0 h ((Subgroup.mem_normalizer_iff.mp hxV u).mp huV)
    · rw [hyt]
      have htA : t ∈ A ⊔ C0 := Subgroup.mem_sup_right (y6_t_mem_C0 h)
      have hv : ⁅t, x⁆ ∈ V := hxk t htA
      have hconj : x * t * x⁻¹ = ⁅t, x⁆⁻¹ * t := by
        rw [commutatorElement_def]; group
      rw [hconj]
      exact C0.mul_mem (C0.inv_mem (y6_V_le_C0 h hv)) (y6_t_mem_C0 h)
  have h1 : ∀ c ∈ C0, x * c * x⁻¹ ∈ C0 := by
    intro c hc
    rw [h.hC0] at hc
    exact y6_conj_mem_closure hgen c hc
  have hxinv : x⁻¹ ∈ CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V :=
    (CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V).inv_mem hx
  obtain ⟨-, hxinvV, hxinvk⟩ := hxinv
  have hgen2 : ∀ y ∈ ({u, t} : Set G), x⁻¹ * y * x ∈ C0 := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hyu | hyt
    · rw [hyu]
      exact y6_V_le_C0 h (by simpa using (Subgroup.mem_normalizer_iff.mp hxinvV u).mp huV)
    · rw [hyt]
      have htA : t ∈ A ⊔ C0 := Subgroup.mem_sup_right (y6_t_mem_C0 h)
      have hv : ⁅t, x⁻¹⁆ ∈ V := hxinvk t htA
      have hconj : x⁻¹ * t * x = ⁅t, x⁻¹⁆⁻¹ * t := by
        rw [commutatorElement_def]; group
      rw [hconj]
      exact C0.mul_mem (C0.inv_mem (y6_V_le_C0 h hv)) (y6_t_mem_C0 h)
  have h2 : ∀ c ∈ C0, x⁻¹ * c * x ∈ C0 := by
    intro c hc
    rw [h.hC0] at hc
    simpa using y6_conj_mem_closure (x := x⁻¹) (fun y hy => by simpa using hgen2 y hy) c hc
  exact y6_mem_normalizer_of_conj h1 h2

theorem y6_C1_le_NAt (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    A ⊔ C0 ≤ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) := by
  apply sup_le
  · exact le_trans le_sup_left Subgroup.le_normalizer
  · rw [h.hC0, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hyu | hyt
    · rw [hyu]
      apply y6_mem_normalizer_of_conj
      · exact y6_conj_mem_sup_At
          (fun a ha => by
            have : u * a * u⁻¹ = a := by rw [← h.u_cent a ha]; group
            rwa [this])
          (by rw [y6_u_conj_t h]
              exact Subgroup.mul_mem_sup (y6_z_mem_A h) (Subgroup.mem_zpowers t))
      · intro c hc
        have hmem : ∀ d ∈ A ⊔ zpowers t, (u⁻¹) * d * (u⁻¹)⁻¹ ∈ A ⊔ zpowers t :=
          y6_conj_mem_sup_At (x := u⁻¹)
            (fun a ha => by
              have h'au : a * u = u * a := h.u_cent a ha
              have : u⁻¹ * a * u = a := by
                calc u⁻¹ * a * u = u⁻¹ * (a * u) := by group
                  _ = u⁻¹ * (u * a) := by rw [h'au]
                  _ = a := by group
              simpa [this] using ha)
            (by
              have huit := y6_u_inv_conj_t h
              simpa [huit] using
                Subgroup.mul_mem_sup (y6_z_mem_A h) (Subgroup.mem_zpowers t))
        simpa [inv_inv] using hmem c hc
    · rw [hyt]
      exact Subgroup.le_normalizer (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem y6_cent_C1_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    (A ⊔ C0) ⊓ centralizer ({t} : Set G) = A ⊔ zpowers t := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxC1, hxcen⟩ := hx
    obtain ⟨a, ha, c0, hc0, hxeq⟩ := y6_C1_elems h x hxC1
    have hxct : t * x = x * t :=
      Subgroup.mem_centralizer_iff.mp hxcen t (Set.mem_singleton t)
    have hc0t : t * c0 = c0 * t := by
      have h1 : t * (a * c0) = (a * c0) * t := by rw [← hxeq]; exact hxct
      have hat : t * a = a * t := (h.t_cent a ha).symm
      have h2 : a * (t * c0) = a * (c0 * t) := by
        calc a * (t * c0) = (a * t) * c0 := by group
          _ = (t * a) * c0 := by rw [hat]
          _ = t * (a * c0) := by group
          _ = (a * c0) * t := h1
          _ = a * (c0 * t) := by group
      exact mul_left_cancel h2
    have hc0' : c0 ∈ Subgroup.closure ({u, t} : Set G) := by rwa [h.hC0] at hc0
    obtain ⟨i, hi | hi⟩ := y6_d8_elems h.u_ord h.t_ord h.t_inv c0 hc0'
    · have hui_eq : u ^ i = (u⁻¹) ^ i := by
        have h1 : u ^ i * t = t * u ^ i := by rw [← hi]; exact hc0t.symm
        have h2 : u ^ i = t * u ^ i * t⁻¹ := by rw [← h1]; group
        rw [h2, y6_t_conj_V h (by rw [h.hV]; exact Subgroup.npow_mem_zpowers u i), inv_pow]
      have hzA : u ^ i ∈ A :=
        Subgroup.zpowers_le.mpr (y6_z_mem_A h) (y6_pow_mem_zpowers_of_eq_inv h hui_eq)
      rw [hxeq, hi]
      exact (A ⊔ zpowers t).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_left hzA)
    · have hui_eq : u ^ i = (u⁻¹) ^ i := by
        have h1 : (u ^ i * t) * t = t * (u ^ i * t) := by rw [← hi]; exact hc0t.symm
        have ht2 : t * t = 1 := y6_t_sq h
        have h2 : u ^ i = t * u ^ i * t⁻¹ := by
          calc u ^ i = (u ^ i * t) * t := by rw [mul_assoc, ht2, mul_one]
            _ = t * (u ^ i * t) := h1
            _ = t * u ^ i * t := by group
            _ = t * u ^ i * t⁻¹ := by rw [y6_t_inv_eq h]
        rw [h2, y6_t_conj_V h (by rw [h.hV]; exact Subgroup.npow_mem_zpowers u i), inv_pow]
      have hzA : u ^ i ∈ A :=
        Subgroup.zpowers_le.mpr (y6_z_mem_A h) (y6_pow_mem_zpowers_of_eq_inv h hui_eq)
      rw [hxeq, hi]
      exact (A ⊔ zpowers t).mul_mem (Subgroup.mem_sup_left ha)
        ((A ⊔ zpowers t).mul_mem (Subgroup.mem_sup_left hzA)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  · intro x hx
    refine ⟨?_, ?_⟩
    · exact sup_le le_sup_left
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (y6_t_mem_C0 h))) hx
    · have hle : A ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
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
      exact hle hx

end CFSG.OddStandard.HigherRank.YamadaG23
