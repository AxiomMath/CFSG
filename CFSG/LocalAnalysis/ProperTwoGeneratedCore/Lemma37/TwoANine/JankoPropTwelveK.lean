module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveM

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {fr : JankoFrame G z}

theorem card_I_sup_z (h : Hyp fr) :
    Nat.card (fr.I ⊔ zpowers z : Subgroup G) = 2 * Nat.card fr.I := by
  have hz2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, h.set.orderOf_z]
  have hzI : zpowers z ⊓ fr.I = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [hz2, h.p11.card_I]; norm_num))
  rw [sup_comm, card_sup_of_inf_eq_bot (Subgroup.zpowers_le.mpr h.z_mem_normalizer_I) hzI, hz2]

theorem K_le_normalizer_I (h : Hyp fr) : fr.K ≤ normalizer (fr.I : Set G) := by
  intro k hk
  refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
  have hkC := mem_normalizer_centralizer (fr.K_le_normalizer hk)
  rw [h.p11.centralizer_E] at hkC
  have hV : fr.I ⊔ zpowers z ≤ normalizer (fr.I : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.z_mem_normalizer_I)
  have hle : fr.I.map (MulAut.conj k).toMonoidHom ≤ fr.I ⊔ zpowers z := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hkC w).mp ((le_sup_left : fr.I ≤ fr.I ⊔ zpowers z) hw)
  have hodd : Odd (Nat.card (fr.I.map (MulAut.conj k).toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, h.p11.card_I]
    decide
  exact le_of_odd_of_card_eq_two_mul le_sup_left hV h.card_I_sup_z hle hodd ⟨x, hx, rfl⟩

theorem I_eq_E_sup_S (h : Hyp fr) : fr.I = fr.E ⊔ fr.S := by
  rw [JankoFrame.I, h.p11.ZN_eq, ← sup_assoc, sup_eq_left.mpr h.P₁_le_E]

theorem E_le_normalizer_S (h : Hyp fr) : fr.E ≤ normalizer (fr.S : Set G) :=
  le_normalizer_of_commute fun e he s hs =>
    h.p11.I_comm e ((le_sup_left : fr.E ≤ fr.I) he) s
      ((le_sup_right : fr.ZN ≤ fr.I) (h.S_le_ZN hs))

theorem mem_S_of_mem_I_of_inv (h : Hyp fr) {x : G} (hx : x ∈ fr.I) (hxz : z * x * z⁻¹ = x⁻¹) :
    x ∈ fr.S := by
  rw [h.I_eq_E_sup_S] at hx
  obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup h.E_le_normalizer_S hx
  have hze : z * e * z⁻¹ = e := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (fr.E_le he)).symm
  have hcomm : e * s = s * e := h.p11.I_comm e ((le_sup_left : fr.E ≤ fr.I) he) s
    ((le_sup_right : fr.ZN ≤ fr.I) (h.S_le_ZN hs))
  have h1 : z * (e * s) * z⁻¹ = e * s⁻¹ := by
    rw [show z * (e * s) * z⁻¹ = (z * e * z⁻¹) * (z * s * z⁻¹) by group, hze, h.z_inv_of_mem_S hs]
  rw [h1, mul_inv_rev] at hxz
  have he2 : e ^ 2 = 1 := by
    have : e = e⁻¹ := by
      calc e = e * s⁻¹ * s := by group
        _ = s⁻¹ * e⁻¹ * s := by rw [hxz]
        _ = e⁻¹ := by
          rw [show s⁻¹ * e⁻¹ * s = s⁻¹ * (e⁻¹ * s) by group,
            show e⁻¹ * s = s * e⁻¹ by
              calc e⁻¹ * s = e⁻¹ * (s * e) * e⁻¹ := by group
                _ = e⁻¹ * (e * s) * e⁻¹ := by rw [hcomm]
                _ = s * e⁻¹ := by group]
          group
    rw [sq]
    nth_rewrite 2 [this]
    exact mul_inv_cancel e
  rw [eq_one_of_sq_of_cube he2 (fr.E_pow_three e he), one_mul]
  exact hs

theorem K_le_normalizer_S (h : Hyp fr) : fr.K ≤ normalizer (fr.S : Set G) := by
  intro k hk
  refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun s hs => ?_
  have hsI : s ∈ fr.I := (le_sup_right : fr.ZN ≤ fr.I) (h.S_le_ZN hs)
  have hkI := (Subgroup.mem_normalizer_iff.mp (h.K_le_normalizer_I hk) s).mp hsI
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (fr.K_le hk)
  refine h.mem_S_of_mem_I_of_inv hkI ?_
  have hz : z * k = k * z := hkz.symm
  calc z * (k * s * k⁻¹) * z⁻¹ = (z * k) * s * (z * k)⁻¹ := by group
    _ = (k * z) * s * (k * z)⁻¹ := by rw [hz]
    _ = k * (z * s * z⁻¹) * k⁻¹ := by group
    _ = (k * s * k⁻¹)⁻¹ := by rw [h.z_inv_of_mem_S hs]; group

theorem t_mem_centralizer_of_mem_P3bar (_h : Hyp fr) {y : G} (hy : y ∈ fr.P3bar) :
    fr.t ∈ centralizer ({y} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2).symm

theorem L_inf_centralizer_le (h : Hyp fr) {y : G} (hy : y ∈ fr.P3bar) (hy1 : y ≠ 1) :
    fr.L ⊓ centralizer ({y} : Set G) ≤ zpowers fr.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hys : IsConj y fr.s₃ := h.isConj_s₃_of_mem_S ((le_sup_left : fr.P3bar ≤ fr.S) hy) hy1
  have hle : zpowers fr.t ≤ fr.L ⊓ centralizer ({y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨h.t_mem_L, h.t_mem_centralizer_of_mem_P3bar hy⟩)
  have h2 := h.p7.card_le_two y hys _ inf_le_right (h.isPGroup_L.to_le inf_le_left)
  rw [Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, fr.orderOf_t]; exact h2)]

theorem t_not_mem_centralizer_S (h : Hyp fr) : fr.t ∉ centralizer (fr.S : Set G) := by
  intro ht
  obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bbar (by norm_num)
  have h1 := h.t_inv_of_mem_P3bbar hy
  rw [← Subgroup.mem_centralizer_iff.mp ht y ((le_sup_right : fr.P3bbar ≤ fr.S) hy),
    mul_inv_cancel_right] at h1
  have hy3 := h.pow_three_of_mem_M (h.p11.ZN_le_M (h.P3bbar_le_ZN hy))
  refine hy1 (eq_one_of_sq_of_cube ?_ hy3)
  rw [sq]
  nth_rewrite 2 [h1]
  exact mul_inv_cancel y

theorem K_inf_centralizer_S (h : Hyp fr) : fr.K ⊓ centralizer (fr.S : Set G) = ⊥ := by
  set K₀ := fr.K ⊓ centralizer (fr.S : Set G)
  obtain ⟨y, hy, hy1⟩ := CFSG.Walter.J1.exists_ne_one_of_card h.p11.card_P3bar (by norm_num)
  have hyS : y ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy
  have hK₀L : fr.L ⊓ K₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxK₀⟩ := Subgroup.mem_inf.mp hx
    have hxC := (Subgroup.mem_inf.mp hxK₀).2
    have hxy : x ∈ centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxC y hyS).symm
    have hxt := h.L_inf_centralizer_le hy hy1 (Subgroup.mem_inf.mpr ⟨hxL, hxy⟩)
    rcases (CFSG.Walter.J1.mem_zpowers_of_orderOf_eq_two fr.orderOf_t).mp hxt with h1 | h1
    · exact h1 ▸ Subgroup.one_mem _
    · exact absurd (h1 ▸ hxC) h.t_not_mem_centralizer_S
  have hKK₀ : fr.K ≤ normalizer (K₀ : Set G) := fun k hk =>
    inf_mem_normalizer (Subgroup.le_normalizer hk)
      (mem_normalizer_centralizer (h.K_le_normalizer_S hk))
  have hprod := card_sup_of_inf_eq_bot (fr.L_le_K.trans hKK₀) hK₀L
  have hd : Nat.card (fr.L ⊔ K₀ : Subgroup G) ∣ 48 :=
    fr.card_K ▸ Subgroup.card_dvd_of_le (sup_le fr.L_le_K inf_le_left)
  rw [hprod, fr.card_L] at hd
  have hd3 : Nat.card K₀ ∣ 3 := by
    rw [show (48 : ℕ) = 16 * 3 by norm_num] at hd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd h3 (fr.card_ne_three K₀ inf_le_left hKK₀)

theorem eq_one_of_le_centralizer (h : Hyp fr) {k : G} (hk : k ∈ fr.K)
    (hS : fr.S ≤ centralizer ({k} : Set G)) : k = 1 := by
  have hkC : k ∈ centralizer (fr.S : Set G) := Subgroup.mem_centralizer_iff.mpr fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
  have : k ∈ fr.K ⊓ centralizer (fr.S : Set G) := Subgroup.mem_inf.mpr ⟨hk, hkC⟩
  rwa [h.K_inf_centralizer_S, Subgroup.mem_bot] at this

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
