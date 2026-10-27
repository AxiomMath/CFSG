module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Cfg
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_ut (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : (d * t) * t = d := by
  rw [mul_assoc, y7a_t_sq h, mul_one]

private lemma y7a_u2t (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : (d * t) ^ 2 * t = z * t := by
  rw [h.cfg.u_sq]

private lemma y7a_u3t (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : (d * t) ^ 3 * t = z * d := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h.cfg.u_sq, mul_assoc, y7a_ut h]

private lemma y7a_u_inv_eq (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    (d * t)⁻¹ = (d * t) ^ 3 := by
  have h4 : (d * t) ^ 4 = 1 := by rw [← h.cfg.u_ord, pow_orderOf_eq_one]
  have h' : (d * t) ^ 3 * (d * t) = 1 := by
    rw [← pow_succ, show 3 + 1 = 4 by norm_num, h4]
  exact inv_eq_of_mul_eq_one_left h'

private lemma y7a_u_inv_t (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    (d * t)⁻¹ * t = z * d := by
  calc (d * t)⁻¹ * t = (d * t) ^ 3 * t := by rw [y7a_u_inv_eq h]
    _ = z * d := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h.cfg.u_sq, mul_assoc, y7a_ut h]

private lemma y7a_d_conj_mem_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hu : x * (d * t) * x⁻¹ = d * t ∨ x * (d * t) * x⁻¹ = (d * t)⁻¹)
    (hc : x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t) :
    x * d * x⁻¹ ∈ V := by
  have h4 : (d * t) ^ 4 = 1 := by rw [← h.cfg.u_ord, pow_orderOf_eq_one]
  have hxd : x * d * x⁻¹ = (x * (d * t) * x⁻¹) * (x * t * x⁻¹) := by
    calc x * d * x⁻¹ = x * ((d * t) * t) * x⁻¹ := by rw [y7a_ut h]
      _ = (x * (d * t) * x⁻¹) * (x * t * x⁻¹) := by group
  have hut : (d * t) * (z * t) = z * d := by
    calc (d * t) * (z * t) = (d * t) * ((d * t) ^ 2 * t) := by rw [← h.cfg.u_sq]
      _ = z * d := by
            rw [← mul_assoc, ← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, y7a_u3t h]
  have huit : (d * t)⁻¹ * (z * t) = d := by
    calc (d * t)⁻¹ * (z * t) = (d * t)⁻¹ * ((d * t) ^ 2 * t) := by rw [← h.cfg.u_sq]
      _ = d := by
            rw [← mul_assoc, y7a_u_inv_eq h, ← pow_add, show 3 + 2 = 4 + 1 by norm_num,
              pow_add, h4, one_mul, pow_one, y7a_ut h]
  rw [hxd]
  rcases hc with hc | hc <;> rcases hu with hu | hu
  · rw [hu, hc, y7a_ut h]; exact y7a_d_mem_V h
  · rw [hu, hc, y7a_u_inv_t h]
    exact mul_mem (y7a_z_mem_V h) (y7a_d_mem_V h)
  · rw [hu, hc, hut]
    exact mul_mem (y7a_z_mem_V h) (y7a_d_mem_V h)
  · rw [hu, hc, huit]; exact y7a_d_mem_V h

private lemma y7a_mem_normalizer_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hz : x * z * x⁻¹ = z) (hd : x * d * x⁻¹ ∈ V) :
    x ∈ normalizer (V : Set G) := by
  have hd' : x * d * x⁻¹ ∈ (closure ({z, d} : Set G) : Subgroup G) := by
    rw [← h.hV]; exact hd
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [y7a_card_V h]; norm_num)
  have hle : V.map (MulAut.conj x).toMonoidHom ≤ V := by
    rw [h.hV, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨w, hw, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hwz | hwd
    · rw [hwz]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz]
        using Subgroup.subset_closure (by simp : z ∈ ({z, d} : Set G))
    · rw [hwd]
      change x * d * x⁻¹ ∈ (closure ({z, d} : Set G) : Subgroup G)
      exact hd'
  haveI := hfin
  have hcard : Nat.card ↥(V.map (MulAut.conj x).toMonoidHom) = Nat.card ↥V :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hcard' : Nat.card ↥V ≤ Nat.card ↥(V.map (MulAut.conj x).toMonoidHom) := by
    rw [hcard]
  have hmap : V.map (MulAut.conj x).toMonoidHom = V :=
    Subgroup.eq_of_le_of_card_ge hle hcard'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hmap

theorem y7a_norm_C0 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {x : G}
    (hx : x ∈ normalizer (C0 : Set G)) :
    x * z * x⁻¹ = z ∧
      (((x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t) ∧ x ∈ normalizer (V : Set G)) ∨
        (x * t * x⁻¹ = d ∨ x * t * x⁻¹ = z * d)) := by
  have hu_ord : orderOf (d * t) = 4 := h.cfg.u_ord
  have ht_ord : orderOf t = 2 := h.cfg.t_ord
  have htu : t * (d * t) * t⁻¹ = (d * t)⁻¹ := h.cfg.t_inv
  have husq : (d * t) ^ 2 = z := h.cfg.u_sq
  have hxC : x ∈ normalizer ((closure ({d * t, t} : Set G)) : Set G) := by
    rw [← h.cfg.hC0]; exact hx
  have hxzp : x ∈ normalizer ((zpowers (d * t) : Subgroup G) : Set G) :=
    y6_d8_norm hu_ord ht_ord htu x hxC
  have hxu_zp : x * (d * t) * x⁻¹ ∈ (zpowers (d * t) : Subgroup G) :=
    (Subgroup.mem_set_normalizer_iff.mp hxzp (d * t)).mp (Subgroup.mem_zpowers (d * t))
  have hxu_mem : x * (d * t) * x⁻¹ ∈ (closure ({d * t, t} : Set G) : Subgroup G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp : d * t ∈ ({d * t, t} : Set G))))
      hxu_zp
  have hxu4 : orderOf (x * (d * t) * x⁻¹) = 4 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu_ord]
  have hxu : x * (d * t) * x⁻¹ = d * t ∨ x * (d * t) * x⁻¹ = (d * t)⁻¹ :=
    y6_d8_ord4 hu_ord ht_ord htu _ hxu_mem hxu4
  have hzconj : x * z * x⁻¹ = z := by
    have h4 : (d * t) ^ 4 = 1 := by rw [← hu_ord, pow_orderOf_eq_one]
    have hinv3 : (d * t)⁻¹ = (d * t) ^ 3 := y7a_u_inv_eq h
    rcases hxu with hc | hc
    · calc x * z * x⁻¹ = (x * (d * t) * x⁻¹) * (x * (d * t) * x⁻¹) := by
              rw [← husq, pow_two]; group
        _ = (d * t) * (d * t) := by rw [hc]
        _ = z := by rw [← pow_two, husq]
    · calc x * z * x⁻¹ = (x * (d * t) * x⁻¹) * (x * (d * t) * x⁻¹) := by
              rw [← husq, pow_two]; group
        _ = (d * t)⁻¹ * (d * t)⁻¹ := by rw [hc]
        _ = (d * t) ^ 3 * (d * t) ^ 3 := by rw [hinv3]
        _ = (d * t) * (d * t) := by
              rw [← pow_add, show 3 + 3 = 4 + 2 by norm_num, pow_add, h4, one_mul, pow_two]
        _ = z := by rw [← pow_two, husq]
  have ht_C0 : t ∈ C0 := by
    rw [h.cfg.hC0]
    exact Subgroup.subset_closure (by simp : t ∈ ({d * t, t} : Set G))
  have hxt_C0 : x * t * x⁻¹ ∈ C0 :=
    (Subgroup.mem_set_normalizer_iff.mp hx t).mp ht_C0
  have hxt_mem : x * t * x⁻¹ ∈ (closure ({d * t, t} : Set G) : Subgroup G) := by
    rw [h.cfg.hC0] at hxt_C0; exact hxt_C0
  have hxt_ord : orderOf (x * t * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht_ord]
  have hxt_inv := y6_d8_invol hu_ord ht_ord htu (x * t * x⁻¹) hxt_mem hxt_ord
  have hxt_ne : x * t * x⁻¹ ≠ (d * t) ^ 2 := by
    intro hz'
    have ht_z : t = z := by
      have h1 : t = x⁻¹ * z * x := by
        calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
          _ = x⁻¹ * (d * t) ^ 2 * x := by rw [hz']
          _ = x⁻¹ * z * x := by rw [husq]
      have h2 : x⁻¹ * z * x = z := by
        have hb := congrArg (fun y => x⁻¹ * y * x) hzconj
        rw [show x⁻¹ * (x * z * x⁻¹) * x = z by group] at hb
        exact hb.symm
      rw [h1, h2]
    have hzu : z * (d * t) = (d * t) * z := by
      rw [← husq, ← pow_succ, ← pow_succ']
    have hzu' : z * (d * t) * z⁻¹ = d * t := by
      rw [hzu, mul_assoc, mul_inv_cancel, mul_one]
    have huu : d * t = (d * t)⁻¹ := by
      have h1 : z * (d * t) * z⁻¹ = (d * t)⁻¹ := by
        rw [← ht_z]; exact htu
      rwa [hzu'] at h1
    have hsq : (d * t) ^ 2 = 1 := by
      rw [pow_two]
      exact (mul_eq_one_iff_eq_inv).mpr huu
    exact h.cfg.z_ne (by rw [← husq]; exact hsq)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, x * t * x⁻¹ = (d * t) ^ i * t := by
    rcases hxt_inv with h' | h'
    · exact absurd h' hxt_ne
    · exact h'
  have hmod : (d * t) ^ i = (d * t) ^ (i % 4) := by
    simpa [hu_ord] using (pow_mod_orderOf (d * t) i).symm
  have hi4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by
    have := Nat.mod_lt i (by norm_num : 0 < 4); omega
  refine ⟨hzconj, ?_⟩
  rcases hi4 with h0 | h1 | h2 | h3
  · left
    have hc : x * t * x⁻¹ = t := by rw [hi, hmod, h0]; simp
    exact ⟨Or.inl hc, y7a_mem_normalizer_V h hzconj (y7a_d_conj_mem_V h hxu (Or.inl hc))⟩
  · right
    have hc : x * t * x⁻¹ = d := by rw [hi, hmod, h1]; simpa using y7a_ut h
    exact Or.inl hc
  · left
    have hc : x * t * x⁻¹ = z * t := by rw [hi, hmod, h2]; simpa using y7a_u2t h
    exact ⟨Or.inr hc, y7a_mem_normalizer_V h hzconj (y7a_d_conj_mem_V h hxu (Or.inr hc))⟩
  · right
    have hc : x * t * x⁻¹ = z * d := by rw [hi, hmod, h3]; simpa using y7a_u3t h
    exact Or.inr hc

theorem y7a_not_conj_of_rank {M : Subgroup G} {t d : G} (hM : IsElemAbelian 2 M) (hd : d ∈ M)
    (hbig : 32 < Nat.card ↥M)
    (hrank : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E →
      Nat.card ↥E ≤ 32) (x : G) : x * t * x⁻¹ ≠ d := by
  intro hconj
  let E : Subgroup G := M.map (MulAut.conj x⁻¹).toMonoidHom
  have hEcard : Nat.card ↥E = Nat.card ↥M := by
    change Nat.card ↥(M.map (MulAut.conj x⁻¹).toMonoidHom) = Nat.card ↥M
    exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have hEcent : E ≤ centralizer ({t} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e ∈ M.map (MulAut.conj x⁻¹).toMonoidHom at he
    obtain ⟨m, hm, hem⟩ := Subgroup.mem_map.mp he
    have hm_d : m * d = d * m := by
      simpa using congrArg Subtype.val
        (hM.1.is_comm.comm (⟨m, hm⟩ : M) (⟨d, hd⟩ : M))
    have ht_eq : t = x⁻¹ * d * x := by rw [← hconj]; group
    rw [← hem]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ht_eq]
    calc (x⁻¹ * m * x) * (x⁻¹ * d * x) = x⁻¹ * (m * d) * x := by group
      _ = x⁻¹ * (d * m) * x := by rw [hm_d]
      _ = (x⁻¹ * d * x) * (x⁻¹ * m * x) := by group
  have hEea : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨m, hm, ham⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨n, hn, hbn⟩ := Subgroup.mem_map.mp b.2
      have hmn : m * n = n * m := by
        simpa using congrArg Subtype.val
          (hM.1.is_comm.comm (⟨m, hm⟩ : M) (⟨n, hn⟩ : M))
      change (a : G) * (b : G) = (b : G) * (a : G)
      rw [← ham, ← hbn, ← map_mul, ← map_mul, hmn]
    · obtain ⟨m, hm, hem⟩ := Subgroup.mem_map.mp he
      have hm2 : m ^ 2 = 1 := hM.2 m hm
      rw [← hem, ← map_pow, hm2, map_one]
  have hle := hrank E hEcent hEea
  rw [hEcard] at hle
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
