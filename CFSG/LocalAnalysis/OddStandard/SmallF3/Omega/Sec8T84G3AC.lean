module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 : Subgroup G}

private theorem sec8t84g3a_ac_odd_card_oddCoreIn (X : Subgroup G) :
    Odd (Nat.card (oddCoreIn X)) := by
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card X

private theorem sec8t84g3a_ac_conj_mem_oddCoreIn {X : Subgroup G} {g : G} (hg : g ∈ X)
    {y : G} (hy : y ∈ oddCoreIn X) : g * y * g⁻¹ ∈ oddCoreIn X := by
  rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map] at hy ⊢
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, ?_, rfl⟩
  exact (CFSG.oddCore_normal ↥X).conj_mem y' hy' ⟨g, hg⟩

private theorem sec8t84g3a_ac_le_normalizer_oddCoreIn (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oddCoreIn X : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg y hy
  exact sec8t84g3a_ac_conj_mem_oddCoreIn hg hy

private theorem sec8t84g3a_ac_inf_oddCore_bot (hE : IsElemAb2 E 8) :
    E ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥ := by
  rw [← disjoint_iff]
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hE.2]
  exact (Nat.coprime_pow_left_iff (n := 8) (by norm_num) 2 _).mpr
    (Nat.coprime_two_left.mpr (sec8t84g3a_ac_odd_card_oddCoreIn (normalizer (E : Set G))))

private theorem sec8t84g3a_ac_pow_decomp {e n : G} (he : e ∈ E)
    (hn : n ∈ oddCoreIn (normalizer (E : Set G))) (k : ℕ) :
    ∃ nk ∈ oddCoreIn (normalizer (E : Set G)), (e * n) ^ k = e ^ k * nk := by
  induction k with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ k ih =>
      obtain ⟨nk, hnk, hk⟩ := ih
      have hconj : e⁻¹ * nk * e ∈ oddCoreIn (normalizer (E : Set G)) := by
        simpa using sec8t84g3a_ac_conj_mem_oddCoreIn
          (X := normalizer (E : Set G)) (Subgroup.le_normalizer (E.inv_mem he)) hnk
      refine ⟨(e⁻¹ * nk * e) * n, Subgroup.mul_mem _ hconj hn, ?_⟩
      rw [pow_succ, hk, pow_succ]
      group

private theorem sec8t84g3a_ac_conj_Y1 (h : Sec8XO G t E Y1 Y2) :
    ∀ b ∈ Y2, ∀ a ∈ Y1, b * a * b⁻¹ ∈ Y1 := by
  intro b hb a ha
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := h.comm a ha b hb
  have h2 : b * a * b⁻¹ * a⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
    have hinv := (oddCoreIn (normalizer (E : Set G))).inv_mem h1
    simpa [mul_inv_rev, inv_inv, mul_assoc] using hinv
  have h3 : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
  rw [h3]
  exact Y1.mul_mem (h.o_le1 h2) ha

private theorem sec8t84g3a_ac_Y2_le_normalizer (h : Sec8XO G t E Y1 Y2) :
    Y2 ≤ Subgroup.normalizer (Y1 : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => sec8t84g3a_ac_conj_Y1 h b hb a ha, fun ha => ?_⟩
  have h3 : b⁻¹ * (b * a * b⁻¹) * (b⁻¹)⁻¹ = a := by group
  have h4 := sec8t84g3a_ac_conj_Y1 h b⁻¹ (Y2.inv_mem hb) (b * a * b⁻¹) ha
  rwa [h3] at h4

private theorem sec8t84g3a_ac_mem_sup_of_left {A K : Subgroup G}
    (hle : A ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ k ∈ K, x = a * k := by
  have hset : (↑(A ⊔ K) : Set G) = (A : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A K hle
  have hx' : x ∈ (A : Set G) * (K : Set G) := hset ▸ hx
  rcases hx' with ⟨a, ha, k, hk, hak⟩
  exact ⟨a, ha, k, hk, hak.symm⟩

private theorem sec8t84g3a_ac_mem_sup_of_right {A K : Subgroup G}
    (hle : K ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ k ∈ K, x = a * k := by
  have hset : (↑(A ⊔ K) : Set G) = (A : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A K hle
  have hx' : x ∈ (A : Set G) * (K : Set G) := hset ▸ hx
  rcases hx' with ⟨a, ha, k, hk, hak⟩
  exact ⟨a, ha, k, hk, hak.symm⟩

private theorem sec8t84g3a_ac_mem_sup_decomp (h : Sec8XO G t E Y1 Y2) {x : G}
    (hx : x ∈ Y1 ⊔ Y2) : ∃ y1 ∈ Y1, ∃ y2 ∈ Y2, x = y1 * y2 := by
  exact sec8t84g3a_ac_mem_sup_of_right
    (A := Y1) (K := Y2) (sec8t84g3a_ac_Y2_le_normalizer h) hx

theorem sec8t84g3a_odd_mem_Y (h : Sec8XO G t E Y1 Y2) (ht : t * t = 1) {x : G}
    (hx : x ∈ normalizer (E : Set G)) (hodd : Odd (orderOf x)) :
    ∃ y1 ∈ Y1, ∃ y2 ∈ Y2, x = y1 * y2 := by
  set Y : Subgroup G := Y1 ⊔ Y2 with hY
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconjY : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y := by
    have h1 : Y1 ≤ Subgroup.comap (MulAut.conj t).toMonoidHom Y := by
      intro a ha
      show t * a * t⁻¹ ∈ Y
      exact Subgroup.mem_sup_right (h.swap1 a ha)
    have h2 : Y2 ≤ Subgroup.comap (MulAut.conj t).toMonoidHom Y := by
      intro a ha
      show t * a * t⁻¹ ∈ Y
      exact Subgroup.mem_sup_left (h.swap2 a ha)
    exact fun a ha => sup_le h1 h2 ha
  have htY : t ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconjY a ha, fun ha => ?_⟩
    have h4 := hconjY (t * a * t⁻¹) ha
    have h3 : t * (t * a * t⁻¹) * t⁻¹ = a := by
      calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t) := by rw [htinv]; group
        _ = a := by rw [ht, one_mul, mul_one]
    rwa [h3] at h4
  have hsquare : x * x ∈ Y := by
    have hx' : x ∈ Y ⊔ Subgroup.zpowers t := by
      rw [hY, h.sup]
      exact hx
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      sec8t84g3a_ac_mem_sup_of_right (A := Y) (K := Subgroup.zpowers t)
        (Subgroup.zpowers_le.mpr htY) hx'
    have hz2 : z * z = 1 := by
      have hdvd : orderOf z ∣ orderOf t := orderOf_dvd_of_mem_zpowers hz
      have ht2 : orderOf t ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        simpa [pow_two] using ht
      have h2 : orderOf z ∣ 2 := hdvd.trans ht2
      have hzsq : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
      simpa [pow_two] using hzsq
    have hznorm : z ∈ Subgroup.normalizer (Y : Set G) := (Subgroup.zpowers_le.mpr htY) hz
    have hzy : z * y * z⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hznorm y).mp hy
    have heq : (y * z) * (y * z) = y * (z * y * z⁻¹) := by
      rw [show (y * z) * (y * z) = y * (z * y * z⁻¹) * (z * z) from by group, hz2,
        mul_one]
    rw [hyz, heq]
    exact Y.mul_mem hy hzy
  have hxY : x ∈ Y := by
    have h2 : 2 * ((orderOf x + 1) / 2) = orderOf x + 1 :=
      Nat.mul_div_cancel' (even_iff_two_dvd.mp hodd.add_one)
    have hxeq : x = (x * x) ^ ((orderOf x + 1) / 2) := by
      rw [← pow_two, ← pow_mul, h2, pow_succ, pow_orderOf_eq_one, one_mul]
    have hmem : (x * x) ^ ((orderOf x + 1) / 2) ∈ Subgroup.zpowers (x * x) :=
      Subgroup.npow_mem_zpowers (x * x) _
    rw [← hxeq] at hmem
    exact (Subgroup.zpowers_le.mpr hsquare) hmem
  have hxY' : x ∈ Y1 ⊔ Y2 := by rwa [hY] at hxY
  exact sec8t84g3a_ac_mem_sup_decomp h hxY'

theorem sec8t84g3a_Y_cent_V (hE : IsElemAb2 E 8) (h : Sec8XO G t E Y1 Y2) :
    (∀ y ∈ Y2, ∀ v ∈ E ⊓ Y1, y * v = v * y) ∧ (∀ y ∈ Y1, ∀ v ∈ E ⊓ Y2, y * v = v * y) := by
  have hinf := sec8t84g3a_ac_inf_oddCore_bot (E := E) hE
  constructor
  · intro y hy v hv
    have hcN : v * y * v⁻¹ * y⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      h.comm v hv.2 y hy
    have hyE : y * v⁻¹ * y⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (h.le2 hy) v⁻¹).mp (E.inv_mem hv.1)
    have hcE : v * y * v⁻¹ * y⁻¹ ∈ E := by
      have hmem := E.mul_mem hv.1 hyE
      simpa only [mul_assoc] using hmem
    have hc1 : v * y * v⁻¹ * y⁻¹ = 1 := by
      have hmem : v * y * v⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hinf]
        exact ⟨hcE, hcN⟩
      simpa using hmem
    have h2 : v * y * v⁻¹ = y := mul_inv_eq_one.mp hc1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro y hy v hv
    have hcN : y * v * y⁻¹ * v⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      h.comm y hy v hv.2
    have hyE : y * v * y⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (h.le1 hy) v).mp hv.1
    have hcE : y * v * y⁻¹ * v⁻¹ ∈ E := E.mul_mem hyE (E.inv_mem hv.1)
    have hc1 : y * v * y⁻¹ * v⁻¹ = 1 := by
      have hmem : y * v * y⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hinf]
        exact ⟨hcE, hcN⟩
      simpa using hmem
    have h2 : y * v * y⁻¹ = v := mul_inv_eq_one.mp hc1
    exact mul_inv_eq_iff_eq_mul.mp h2

theorem sec8t84g3a_odd_cent_mem (hE : IsElemAb2 E 8) (h : Sec8XO G t E Y1 Y2) (ht : t * t = 1)
    {x : G} (hx : x ∈ normalizer (E : Set G)) (hodd : Odd (orderOf x))
    (hc : ∀ e ∈ E, x * e = e * x) : x ∈ oddCoreIn (normalizer (E : Set G)) := by
  obtain ⟨y1, hy1, y2, hy2, hxy⟩ := sec8t84g3a_odd_mem_Y h ht hx hodd
  have hY2c : ∀ y ∈ Y2, ∀ v ∈ E ⊓ Y1, y * v = v * y := (sec8t84g3a_Y_cent_V hE h).1
  have hY1c : ∀ y ∈ Y1, ∀ v ∈ E ⊓ Y2, y * v = v * y := (sec8t84g3a_Y_cent_V hE h).2
  have hy1c : y1 ∈ Y1 ⊓ centralizer ((E ⊓ Y1 : Subgroup G) : Set G) := by
    refine ⟨hy1, ?_⟩
    intro v hv
    have hv' : y1 * v = v * y1 := by
      have h1 : (y1 * v) * y2 = (v * y1) * y2 := by
        calc (y1 * v) * y2 = y1 * (v * y2) := by group
          _ = y1 * (y2 * v) := by rw [← hY2c y2 hy2 v hv]
          _ = (y1 * y2) * v := by group
          _ = x * v := by rw [← hxy]
          _ = v * x := hc v hv.1
          _ = v * (y1 * y2) := by rw [hxy]
          _ = (v * y1) * y2 := by group
      exact mul_right_cancel h1
    exact hv'.symm
  have hy2c : y2 ∈ Y2 ⊓ centralizer ((E ⊓ Y2 : Subgroup G) : Set G) := by
    refine ⟨hy2, ?_⟩
    intro v hv
    have hv' : v * y2 = y2 * v := by
      have h1 : y1 * (y2 * v) = y1 * (v * y2) := by
        calc y1 * (y2 * v) = (y1 * y2) * v := by group
          _ = x * v := by rw [← hxy]
          _ = v * x := hc v hv.1
          _ = v * (y1 * y2) := by rw [hxy]
          _ = (v * y1) * y2 := by group
          _ = (y1 * v) * y2 := by rw [← hY1c y1 hy1 v hv]
          _ = y1 * (v * y2) := by group
      exact (mul_left_cancel h1).symm
    exact hv'
  obtain ⟨e1, he1, n1, hn1, he1n1⟩ :=
    sec8t84g3a_ac_mem_sup_of_left
      (A := E ⊓ Y1) (K := oddCoreIn (normalizer (E : Set G)))
      (le_trans inf_le_right (le_trans h.le1
        (sec8t84g3a_ac_le_normalizer_oddCoreIn (normalizer (E : Set G)))))
      (h.cent1 hy1c)
  obtain ⟨e2, he2, n2, hn2, he2n2⟩ :=
    sec8t84g3a_ac_mem_sup_of_left
      (A := E ⊓ Y2) (K := oddCoreIn (normalizer (E : Set G)))
      (le_trans inf_le_right (le_trans h.le2
        (sec8t84g3a_ac_le_normalizer_oddCoreIn (normalizer (E : Set G)))))
      (h.cent2 hy2c)
  have hconj : e2⁻¹ * n1 * e2 ∈ oddCoreIn (normalizer (E : Set G)) := by
    have hg : e2⁻¹ ∈ normalizer (E : Set G) := Subgroup.le_normalizer (E.inv_mem he2.1)
    simpa using sec8t84g3a_ac_conj_mem_oddCoreIn hg hn1
  have hxEN : x ∈ E ⊔ oddCoreIn (normalizer (E : Set G)) := by
    have hxe : x = (e1 * e2) * ((e2⁻¹ * n1 * e2) * n2) := by
      rw [hxy, he1n1, he2n2]
      group
    rw [hxe]
    exact Subgroup.mul_mem_sup (E.mul_mem he1.1 he2.1) (Subgroup.mul_mem _ hconj hn2)
  obtain ⟨e, he, n, hn, hen⟩ :=
    sec8t84g3a_ac_mem_sup_of_left (A := E) (K := oddCoreIn (normalizer (E : Set G)))
      (le_trans Subgroup.le_normalizer
        (sec8t84g3a_ac_le_normalizer_oddCoreIn (normalizer (E : Set G)))) hxEN
  obtain ⟨nr, hnr, hr⟩ := sec8t84g3a_ac_pow_decomp he hn (orderOf x)
  have heN : e ∈ oddCoreIn (normalizer (E : Set G)) := by
    have h1 : e ^ orderOf x * nr = 1 := by
      have hxr : (e * n) ^ orderOf x = 1 := by
        rw [← hen]
        exact pow_orderOf_eq_one x
      rwa [hr] at hxr
    have heq : e ^ orderOf x = nr⁻¹ := eq_inv_of_mul_eq_one_left h1
    have her : e ^ orderOf x = e := by
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hE.1.2 e he, one_pow, one_mul]
    rw [← her, heq]
    exact (oddCoreIn (normalizer (E : Set G))).inv_mem hnr
  rw [hen]
  exact (oddCoreIn (normalizer (E : Set G))).mul_mem heN hn

end CFSG.OddStandard.SmallF3.Omega
