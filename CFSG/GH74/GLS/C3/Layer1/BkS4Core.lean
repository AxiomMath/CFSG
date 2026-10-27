module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G]

@[expose] def Sec4Shape (P Q T : Subgroup G) : Prop :=
  CFSG.IsElementaryAbelian 2 ↥Q ∨
    (IsCyclic ↥Q ∧ ∀ g ∈ T, (∀ p ∈ P, g * p * g⁻¹ * p⁻¹ ∈ Q) → g * g ∈ Q)

structure Sec4Core (a : G) (P Q T S : Subgroup G) : Prop where
  T_pgroup : IsPGroup 2 ↥T
  S_pgroup : IsPGroup 2 ↥S
  T_le_S : T ≤ S
  a_mem : a ∈ S
  a_mem_norm : a ∈ normalizer (T : Set G)
  a_not_mem : a ∉ T
  a_sq_mem : a * a ∈ T
  P_le : P ≤ T
  Q_le : Q ≤ T
  P_norm : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P
  Q_norm : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q
  P_d8 : IsD8 P
  Q_shape : Sec4Shape P Q T
  Q_card : Nat.card ↥Q = 4
  PQ_comm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  PQ_disj : P ⊓ Q = ⊥
  cent6 : ∀ u ∈ Q, u ≠ 1 → (∀ t ∈ T, u * t = t * u) → ∀ s ∈ S, s * u = u * s → s ∈ T
  rank4 : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 16

theorem comm_of_normal_disjoint {T X Y : Subgroup G} (hXT : X ≤ T) (hYT : Y ≤ T)
    (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hYn : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (hd : X ⊓ Y = ⊥) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) : x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ Y := Y.mul_mem (hYn x (hXT hx) y hy) (Y.inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ X := by
    have : x * (y * x⁻¹ * y⁻¹) ∈ X := X.mul_mem hx (hXn y (hYT hy) x⁻¹ (X.inv_mem hx))
    simpa [mul_assoc] using this
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := ⟨h2, h1⟩
  rw [hd, Subgroup.mem_bot] at h3
  have h4 : x * y * x⁻¹ = y := mul_inv_eq_one.1 h3
  exact mul_inv_eq_iff_eq_mul.1 h4

theorem conj_le_of_mem_normalizer {T X : Subgroup G} {a : G}
    (ha : a ∈ normalizer (T : Set G)) (hX : X ≤ T) : conjugate X a ≤ T := by
  intro y hy
  have h1 : a * y * a⁻¹ ∈ T := hX (mem_conjugate_iff'.1 hy)
  have h2 : a⁻¹ * (a * y * a⁻¹) * a ∈ T := by
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem ha) (a * y * a⁻¹)).1 h1
  have e : a⁻¹ * (a * y * a⁻¹) * a = y := by group
  rwa [e] at h2

theorem conj_norm_of_mem_normalizer {T X : Subgroup G} {a : G}
    (ha : a ∈ normalizer (T : Set G))
    (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    ∀ t ∈ T, ∀ y ∈ conjugate X a, t * y * t⁻¹ ∈ conjugate X a := by
  intro t ht y hy
  rw [mem_conjugate_iff'] at hy ⊢
  have h1 := hXn (a * t * a⁻¹) ((Subgroup.mem_normalizer_iff.1 ha t).1 ht) _ hy
  have e : a * t * a⁻¹ * (a * y * a⁻¹) * (a * t * a⁻¹)⁻¹ = a * (t * y * t⁻¹) * a⁻¹ := by group
  rwa [e] at h1

theorem comm_conjQ_P_of_inf_ne_bot [Finite G]
    {a : G} {P Q T : Subgroup G}
    (hT2 : IsPGroup 2 ↥T)
    (haN : a ∈ normalizer (T : Set G))
    (ha2 : a * a ∈ T)
    (hPT : P ≤ T) (hQT : Q ≤ T)
    (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P)
    (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hPd8 : IsD8 P) (hPQ : P ⊓ Q = ⊥)
    (hne : P ⊓ conjugate P a ≠ ⊥) :
    ∀ q' ∈ conjugate Q a, ∀ p ∈ P, q' * p = p * q' := by
  have hPaT : conjugate P a ≤ T := conj_le_of_mem_normalizer haN hPT
  have hQaT : conjugate Q a ≤ T := conj_le_of_mem_normalizer haN hQT
  have hPaD : IsD8 (conjugate P a) := hPd8.conjugate a
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := hPd8.exists_z
  obtain ⟨z', hz'P, hz'1, hz'z', hz'c, hz'u⟩ := hPaD.exists_z
  have hPPa_n : ∀ t ∈ T, ∀ w ∈ P ⊓ conjugate P a, t * w * t⁻¹ ∈ P ⊓ conjugate P a :=
    fun t ht w hw => ⟨hPn t ht w hw.1,
      conj_norm_of_mem_normalizer haN hPn t ht w hw.2⟩
  obtain ⟨w, hwW, hw1, hwc⟩ :=
    exists_central_of_normal hT2 hPPa_n (inf_le_left.trans hPT) hne
  have hwz : w = z := (hzu w hwW.1 (fun p hp => hwc p (hPT hp))).resolve_left hw1
  have hwz' : w = z' := (hz'u w hwW.2 (fun p hp => hwc p (hPaT hp))).resolve_left hw1
  have hPaQ : conjugate P a ⊓ Q = ⊥ := by
    by_contra hne'
    have hn' : ∀ t ∈ T, ∀ w ∈ conjugate P a ⊓ Q, t * w * t⁻¹ ∈ conjugate P a ⊓ Q :=
      fun t ht w hw => ⟨conj_norm_of_mem_normalizer haN hPn t ht w hw.1, hQn t ht w hw.2⟩
    obtain ⟨w', hw'W, hw'1, hw'c⟩ :=
      exists_central_of_normal hT2 hn' (inf_le_right.trans hQT) hne'
    have hw'z' : w' = z' := (hz'u w' hw'W.1 (fun p hp => hw'c p (hPaT hp))).resolve_left hw'1
    have hzQ : z ∈ Q := by rw [← hwz, hwz', ← hw'z']; exact hw'W.2
    have : z ∈ P ⊓ Q := ⟨hzP, hzQ⟩
    rw [hPQ, Subgroup.mem_bot] at this
    exact hz1 this
  have hcommQ : ∀ q ∈ Q, ∀ g ∈ conjugate P a, q * g = g * q := fun q hq g hg =>
    comm_of_normal_disjoint hQT hPaT hQn (conj_norm_of_mem_normalizer haN hPn)
      (by rw [inf_comm]; exact hPaQ) hq hg
  intro q' hq' p hp
  have hq : a * q' * a⁻¹ ∈ Q := mem_conjugate_iff'.1 hq'
  have hg : a * p * a⁻¹ ∈ conjugate P a := by
    rw [mem_conjugate_iff']
    have := hPn (a * a) ha2 p hp
    have e : a * (a * p * a⁻¹) * a⁻¹ = a * a * p * (a * a)⁻¹ := by group
    rw [e]; exact this
  have h1 := hcommQ _ hq _ hg
  have e1 : a * q' * a⁻¹ * (a * p * a⁻¹) = a * (q' * p) * a⁻¹ := by group
  have e2 : a * p * a⁻¹ * (a * q' * a⁻¹) = a * (p * q') * a⁻¹ := by group
  rw [e1, e2] at h1
  exact mul_left_cancel (mul_right_cancel h1)

namespace Sec4Core

variable {a : G} {P Q T S : Subgroup G}

theorem a_norm (h : Sec4Core a P Q T S) {t : G} (ht : t ∈ T) : a * t * a⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.1 h.a_mem_norm t).1 ht

theorem a_inv_norm (h : Sec4Core a P Q T S) {t : G} (ht : t ∈ T) : a⁻¹ * t * a ∈ T := by
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem h.a_mem_norm) t).1 ht
  simpa using this

theorem conj_le (h : Sec4Core a P Q T S) {X : Subgroup G} (hX : X ≤ T) : conjugate X a ≤ T :=
  conj_le_of_mem_normalizer h.a_mem_norm hX

theorem conj_norm (h : Sec4Core a P Q T S) {X : Subgroup G}
    (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    ∀ t ∈ T, ∀ y ∈ conjugate X a, t * y * t⁻¹ ∈ conjugate X a :=
  conj_norm_of_mem_normalizer h.a_mem_norm hXn

theorem conj_inv_mem (h : Sec4Core a P Q T S) {X : Subgroup G}
    (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) {y : G} (hy : y ∈ conjugate X a) :
    a⁻¹ * y * a ∈ X := by
  rw [mem_conjugate_iff'] at hy
  have h1 := hXn (a * a)⁻¹ (T.inv_mem h.a_sq_mem) _ hy
  have e : (a * a)⁻¹ * (a * y * a⁻¹) * (a * a)⁻¹⁻¹ = a⁻¹ * y * a := by group
  rwa [e] at h1

theorem mem_conj_of (X : Subgroup G) {x : G} (hx : x ∈ X) : a⁻¹ * x * a ∈ conjugate X a := by
  rw [mem_conjugate_iff']
  have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
  rwa [e]

theorem Q_inf_conj [Finite G] (h : Sec4Core a P Q T S) : Q ⊓ conjugate Q a = ⊥ := by
  by_contra hne
  have hHS : T ⊔ zpowers a ≤ S := sup_le h.T_le_S (zpowers_le.2 h.a_mem)
  have hH : IsPGroup 2 ↥(T ⊔ zpowers a) := h.S_pgroup.to_le hHS
  have hWn : ∀ t ∈ T, ∀ w ∈ Q ⊓ conjugate Q a, t * w * t⁻¹ ∈ Q ⊓ conjugate Q a :=
    fun t ht w hw => ⟨h.Q_norm t ht w hw.1, h.conj_norm h.Q_norm t ht w hw.2⟩
  have hTnorm : T ≤ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_of_two_sided (hWn t ht)
      (fun w hw => by simpa using hWn t⁻¹ (T.inv_mem ht) w hw)
  have haW : a ∈ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) := by
    refine mem_normalizer_of_two_sided (fun w hw => Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      (fun w hw => Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact mem_conjugate_iff'.1 hw.2
    · rw [mem_conjugate_iff']
      have := h.Q_norm (a * a) h.a_sq_mem w hw.1
      have e : a * (a * w * a⁻¹) * a⁻¹ = a * a * w * (a * a)⁻¹ := by group
      rw [e]; exact this
    · exact h.conj_inv_mem h.Q_norm hw.2
    · exact mem_conj_of (a := a) Q hw.1
  have hHn : T ⊔ zpowers a ≤ normalizer ((Q ⊓ conjugate Q a : Subgroup G) : Set G) :=
    sup_le hTnorm (zpowers_le.2 haW)
  obtain ⟨w, hwW, hw1, hwc⟩ := exists_central_of_normal hH
    (fun x hx w hw => (Subgroup.mem_normalizer_iff.1 (hHn hx) w).1 hw)
    (inf_le_left.trans (h.Q_le.trans le_sup_left)) hne
  exact h.a_not_mem (h.cent6 w hwW.1 hw1 (fun t ht => (hwc t (Subgroup.mem_sup_left ht)).symm) a
    h.a_mem (hwc a (Subgroup.mem_sup_right (mem_zpowers a))))

theorem P_inf_conj [Finite G] (h : Sec4Core a P Q T S) : P ⊓ conjugate P a = ⊥ := by
  by_contra hne
  have hA1 := h.Q_inf_conj
  have hQaT : conjugate Q a ≤ T := h.conj_le h.Q_le
  have hcommQa : ∀ q' ∈ conjugate Q a, ∀ p ∈ P, q' * p = p * q' :=
    comm_conjQ_P_of_inf_ne_bot h.T_pgroup h.a_mem_norm h.a_sq_mem
      h.P_le h.Q_le h.P_norm h.Q_norm h.P_d8 h.PQ_disj hne
  rcases h.Q_shape with hQel | ⟨hcyc, hsq⟩
  ·
    have hQa_el : CFSG.IsElementaryAbelian 2 ↥(conjugate Q a) :=
      isElementaryAbelian_conjugate hQel a
    have hQQa_comm : ∀ q ∈ Q, ∀ q' ∈ conjugate Q a, q * q' = q' * q := fun q hq q' hq' =>
      comm_of_normal_disjoint h.Q_le hQaT h.Q_norm (h.conj_norm h.Q_norm) hA1 hq hq'
    have hE_el := isElementaryAbelian_sup_of_commute hQel hQa_el hQQa_comm
    have hE_card : Nat.card ↥(Q ⊔ conjugate Q a) = 16 := by
      rw [card_sup_of_commute_of_disjoint hQQa_comm hA1, card_conjugate', h.Q_card]
    obtain ⟨d, hdP, hd2, hdn⟩ := h.P_d8.exists_noncentral_involution
    have hdQ : ∀ q ∈ Q, d * q = q * d := fun q hq => h.PQ_comm d hdP q hq
    have hdQa : ∀ q' ∈ conjugate Q a, q' * d = d * q' := fun q' hq' => hcommQa q' hq' d hdP
    have hdE : ∀ e ∈ Q ⊔ conjugate Q a, e * d = d * e := by
      intro e he
      have hle : Q ⊔ conjugate Q a ≤ centralizer ({d} : Set G) := sup_le
        (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hdQ q hq).symm)
        (fun q' hq' => Subgroup.mem_centralizer_singleton_iff.2 (hdQa q' hq'))
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
    have hdnE : d ∉ Q ⊔ conjugate Q a := by
      intro hd
      obtain ⟨p, hp, hdp⟩ := hdn
      apply hdp
      have hle : Q ⊔ conjugate Q a ≤ centralizer ({p} : Set G) := sup_le
        (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (h.PQ_comm p hp q hq).symm)
        (fun q' hq' => Subgroup.mem_centralizer_singleton_iff.2 (hcommQa q' hq' p hp))
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
    have hE'_el : CFSG.IsElementaryAbelian 2 ↥((Q ⊔ conjugate Q a) ⊔ zpowers d) :=
      isElementaryAbelian_sup_of_commute hE_el (isElementaryAbelian_zpowers_of_sq hd2) (by
        intro e he b hb
        have hle : zpowers d ≤ centralizer ({e} : Set G) := zpowers_le.2
          (Subgroup.mem_centralizer_singleton_iff.2 (hdE e he).symm)
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm)
    have h16 := h.rank4 _ hE'_el
    have hle : Q ⊔ conjugate Q a ≤ (Q ⊔ conjugate Q a) ⊔ zpowers d := le_sup_left
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hE_card]; exact h16)
    apply hdnE
    rw [heq]
    exact Subgroup.mem_sup_right (mem_zpowers d)

  ·
    have hQaT' : ∀ q' ∈ conjugate Q a, q' * q' = 1 := by
      intro q' hq'
      have h1 : q' * q' ∈ Q := hsq q' (hQaT hq') (fun p hp => by
        rw [hcommQa q' hq' p hp]; group; exact one_mem _)
      have h2 : q' * q' ∈ conjugate Q a := Subgroup.mul_mem _ hq' hq'
      have h3 : q' * q' ∈ Q ⊓ conjugate Q a := ⟨h1, h2⟩
      rw [hA1, Subgroup.mem_bot] at h3
      exact h3
    have hcycQa : IsCyclic ↥(conjugate Q a) := (conjugateEquiv Q a).isCyclic.1 hcyc
    have hexp : Monoid.exponent ↥(conjugate Q a) = Nat.card ↥(conjugate Q a) :=
      IsCyclic.exponent_eq_card
    have hdvd : Monoid.exponent ↥(conjugate Q a) ∣ 2 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
      apply Subtype.ext
      simp [sq, hQaT' g g.2]
    rw [hexp, card_conjugate', h.Q_card] at hdvd
    omega

theorem central_of_normal_unique {T X : Subgroup G} (hXn : ∀ t ∈ T, ∀ p ∈ X, t * p * t⁻¹ ∈ X)
    {z : G} (hz1 : z ≠ 1) (hzX : z ∈ X) (hzc : ∀ p ∈ X, p * z = z * p)
    (hzu : ∀ w ∈ X, (∀ p ∈ X, p * w = w * p) → w = 1 ∨ w = z) {t : G} (ht : t ∈ T) :
    t * z * t⁻¹ = z := by
  have h1 : t * z * t⁻¹ ∈ X := hXn t ht z hzX
  have hc : ∀ p ∈ X, p * (t * z * t⁻¹) = (t * z * t⁻¹) * p := by
    intro p hp
    have hp' : t⁻¹ * p * t ∈ X := by simpa using hXn t⁻¹ (T.inv_mem ht) p hp
    have := hzc _ hp'
    calc p * (t * z * t⁻¹) = t * ((t⁻¹ * p * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * p * t)) * t⁻¹ := by rw [this]
      _ = (t * z * t⁻¹) * p := by group
  rcases hzu _ h1 hc with h2 | h2
  · exfalso
    apply hz1
    calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
      _ = 1 := by rw [h2]; group
  · exact h2

theorem exists_z_centralizer [Finite G] (h : Sec4Core a P Q T S)
    (hK4 : Nat.card ↥(T ⊓ centralizer (P : Set G)) ≤ 16) :
    ∃ z ∈ P, z ≠ 1 ∧ z * z = 1 ∧ (∀ p ∈ P, p * z = z * p) ∧
      (∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z) ∧ (∀ t ∈ T, t * z * t⁻¹ = z) ∧
      T ⊓ centralizer (P : Set G) = zpowers z ⊔ conjugate P a := by
  have hA2 := h.P_inf_conj
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  have hPPa : ∀ p ∈ P, ∀ g ∈ conjugate P a, p * g = g * p := fun p hp g hg =>
    comm_of_normal_disjoint h.P_le hPaT h.P_norm (h.conj_norm h.P_norm) hA2 hp hg
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := h.P_d8.exists_z
  have hzT : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht =>
    central_of_normal_unique h.P_norm hz1 hzP hzc hzu ht
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hzcard : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hzPa : zpowers z ⊓ conjugate P a = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases mem_zpowers_of_sq hzz hy.1 with rfl | rfl
    · exact one_mem _
    · exfalso
      have : y ∈ P ⊓ conjugate P a := ⟨hzP, hy.2⟩
      rw [hA2, Subgroup.mem_bot] at this
      exact hz1 this
  have hzP' : zpowers z ≤ P := zpowers_le.2 hzP
  have hzPaComm : ∀ x ∈ zpowers z, ∀ y ∈ conjugate P a, x * y = y * x := fun x hx y hy =>
    hPPa x (hzP' hx) y hy
  have hCcard : Nat.card ↥(zpowers z ⊔ conjugate P a) = 16 := by
    rw [card_sup_of_commute_of_disjoint hzPaComm hzPa, hzcard, card_conjugate', h.P_d8.card_eq]
  have hCle : zpowers z ⊔ conjugate P a ≤ T ⊓ centralizer (P : Set G) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · refine ⟨h.P_le (hzP' hy), Subgroup.mem_centralizer_iff.2 (fun p hp => ?_)⟩
      rcases mem_zpowers_of_sq hzz hy with rfl | rfl
      · simp
      · exact hzc p hp
    · exact ⟨hPaT hy, Subgroup.mem_centralizer_iff.2 (fun p hp => hPPa p hp y hy)⟩
  exact ⟨z, hzP, hz1, hzz, hzc, hzu, hzT,
    (Subgroup.eq_of_le_of_card_ge hCle (by rw [hCcard]; exact hK4)).symm⟩

theorem T_le_sup [Finite G] (h : Sec4Core a P Q T S) (hQel : CFSG.IsElementaryAbelian 2 ↥Q)
    (hK4 : Nat.card ↥(T ⊓ centralizer (P : Set G)) ≤ 16) : T ≤ P ⊔ conjugate P a := by
  have hA2 := h.P_inf_conj
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  have hPaD : IsD8 (conjugate P a) := h.P_d8.conjugate a
  have hPPa : ∀ p ∈ P, ∀ g ∈ conjugate P a, p * g = g * p := fun p hp g hg =>
    comm_of_normal_disjoint h.P_le hPaT h.P_norm (h.conj_norm h.P_norm) hA2 hp hg
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu, hzT, hCeq⟩ := h.exists_z_centralizer hK4
  obtain ⟨z', hz'Pa, hz'1, hz'z', hz'c, hz'u⟩ := hPaD.exists_z
  have hzP' : zpowers z ≤ P := zpowers_le.2 hzP
  have hzPaComm : ∀ x ∈ zpowers z, ∀ y ∈ conjugate P a, x * y = y * x := fun x hx y hy =>
    hPPa x (hzP' hx) y hy
  have hQle : Q ≤ zpowers z ⊔ conjugate P a := by
    intro q hq
    rw [← hCeq]
    exact ⟨h.Q_le hq, Subgroup.mem_centralizer_iff.2 (fun p hp => h.PQ_comm p hp q hq)⟩
  have hQc := (forall_of_isElementaryAbelian hQel).1
  have hQs := (forall_of_isElementaryAbelian hQel).2
  have hzQ : z ∉ Q := by
    intro hzQ
    have : z ∈ P ⊓ Q := ⟨hzP, hzQ⟩
    rw [h.PQ_disj, Subgroup.mem_bot] at this
    exact hz1 this
  have hD : ∃ q ∈ Q, ∃ y ∈ zpowers z, ∃ g ∈ conjugate P a, q = y * g ∧
      ∃ p ∈ conjugate P a, g * p ≠ p * g := by
    classical
    by_contra hD
    push Not at hD
    have hsub : (Q : Set G) ⊆ (({1, z', z * z'} : Finset G) : Set G) := by
      intro q hq
      obtain ⟨y, hy, g, hg, hqyg⟩ := mem_sup_of_commute hzPaComm (hQle hq)
      have hgc : ∀ p ∈ conjugate P a, p * g = g * p := fun p hp => (hD q hq y hy g hg hqyg p hp).symm
      have hg' := hz'u g hg hgc
      rcases mem_zpowers_of_sq hzz hy with hy1 | hyz
      · rcases hg' with hg1 | hgz
        · subst hy1; subst hg1; simp [hqyg]
        · subst hy1; subst hgz; simp [hqyg]
      · rcases hg' with hg1 | hgz
        · exfalso
          subst hyz; subst hg1
          apply hzQ
          simpa [hqyg] using hq
        · subst hyz; subst hgz; simp [hqyg]
    have h3 : (Q : Set G).ncard ≤ 3 := by
      calc (Q : Set G).ncard ≤ (({1, z', z * z'} : Finset G) : Set G).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ({1, z', z * z'} : Finset G).card := Set.ncard_coe_finset _
        _ ≤ 3 := Finset.card_le_three
    have h4 : Nat.card ↥Q = (Q : Set G).ncard := Nat.card_coe_set_eq (Q : Set G)
    have h5 := h.Q_card
    omega
  obtain ⟨q, hq, y, hy, g, hg, hqyg, p0, hp0, hgp0⟩ := hD
  have hy' : y = 1 ∨ y = z := mem_zpowers_of_sq hzz hy
  have hgq : g = y * q := by
    rcases hy' with hy1 | hyz
    · subst hy1; simpa using hqyg.symm
    · rw [hyz] at hqyg ⊢
      rw [hqyg, ← mul_assoc, hzz, one_mul]
  have hyQ : ∀ x ∈ Q, y * x = x * y := by
    intro x hx
    rcases hy' with hy1 | hyz
    · subst hy1; simp
    · rw [hyz]; exact h.PQ_comm z hzP x hx
  have hgg : g * g = 1 := by
    rw [hgq]
    have h1 : y * y = 1 := by
      rcases hy' with hy1 | hyz
      · subst hy1; simp
      · rw [hyz]; exact hzz
    calc y * q * (y * q) = y * (q * y) * q := by group
      _ = y * (y * q) * q := by rw [← hyQ q hq]
      _ = (y * y) * (q * q) := by group
      _ = 1 := by rw [h1, hQs q hq, one_mul]
  have hinv : ∀ t ∈ T, (t * g * t⁻¹) * g = g * (t * g * t⁻¹) := by
    intro t ht
    have hq'' : t * q * t⁻¹ ∈ Q := h.Q_norm t ht q hq
    have hty : t * y * t⁻¹ = y := by
      rcases hy' with hy1 | hyz
      · subst hy1; simp
      · rw [hyz]; exact hzT t ht
    have htg : t * g * t⁻¹ = y * (t * q * t⁻¹) := by
      rw [hgq]
      calc t * (y * q) * t⁻¹ = (t * y * t⁻¹) * (t * q * t⁻¹) := by group
        _ = y * (t * q * t⁻¹) := by rw [hty]
    rw [htg, hgq]
    have c1 : Commute (t * q * t⁻¹) y := (hyQ _ hq'').symm
    have c2 : Commute q y := (hyQ _ hq).symm
    have c3 : t * q * t⁻¹ * q = q * (t * q * t⁻¹) := hQc _ hq'' _ hq
    calc y * (t * q * t⁻¹) * (y * q) = (y * y) * ((t * q * t⁻¹) * q) := c1.mul_mul_mul_comm y q
      _ = (y * y) * (q * (t * q * t⁻¹)) := by rw [c3]
      _ = y * q * (y * (t * q * t⁻¹)) := (c2.mul_mul_mul_comm y (t * q * t⁻¹)).symm
  have hinner : ∀ t ∈ T, ∃ g' ∈ conjugate P a,
      ∀ p ∈ conjugate P a, t * p * t⁻¹ = g' * p * g'⁻¹ := by
    intro t ht
    refine hPaD.exists_inner hg hgg ⟨p0, hp0, hgp0⟩ (fun p => ⟨fun hp => ?_, fun hp => ?_⟩)
      (hinv t ht)
    · exact h.conj_norm h.P_norm t ht p hp
    · have := h.conj_norm h.P_norm t⁻¹ (T.inv_mem ht) _ hp
      have e : t⁻¹ * (t * p * t⁻¹) * t⁻¹⁻¹ = p := by group
      rwa [e] at this
  intro t ht
  obtain ⟨g', hg', hgt⟩ := hinner t ht
  have hcT : g'⁻¹ * t ∈ T := T.mul_mem (T.inv_mem (hPaT hg')) ht
  have hcc : ∀ p ∈ conjugate P a, p * (g'⁻¹ * t) = (g'⁻¹ * t) * p := by
    intro p hp
    have h1 := hgt p hp
    have e : (g'⁻¹ * t) * p * (g'⁻¹ * t)⁻¹ = p := by
      calc (g'⁻¹ * t) * p * (g'⁻¹ * t)⁻¹ = g'⁻¹ * (t * p * t⁻¹) * g' := by group
        _ = g'⁻¹ * (g' * p * g'⁻¹) * g' := by rw [h1]
        _ = p := by group
    have : (g'⁻¹ * t) * p = p * (g'⁻¹ * t) := by
      calc (g'⁻¹ * t) * p = ((g'⁻¹ * t) * p * (g'⁻¹ * t)⁻¹) * (g'⁻¹ * t) := by group
        _ = p * (g'⁻¹ * t) := by rw [e]
    exact this.symm
  have hcP : g'⁻¹ * t ∈ P ⊔ conjugate P a := by
    set c := g'⁻¹ * t with hc
    have hc'T : a * c * a⁻¹ ∈ T := h.a_norm hcT
    have hc'C : a * c * a⁻¹ ∈ centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hgp : a⁻¹ * p * a ∈ conjugate P a := mem_conj_of (a := a) P hp
      have := hcc _ hgp
      calc p * (a * c * a⁻¹) = a * ((a⁻¹ * p * a) * c) * a⁻¹ := by group
        _ = a * (c * (a⁻¹ * p * a)) * a⁻¹ := by rw [this]
        _ = (a * c * a⁻¹) * p := by group
    have hc'mem : a * c * a⁻¹ ∈ zpowers z ⊔ conjugate P a := by
      rw [← hCeq]; exact ⟨hc'T, hc'C⟩
    obtain ⟨y', hy'', g'', hg'', hc'eq⟩ := mem_sup_of_commute hzPaComm hc'mem
    have hcdec : c = (a⁻¹ * y' * a) * (a⁻¹ * g'' * a) := by
      calc c = a⁻¹ * (a * c * a⁻¹) * a := by group
        _ = a⁻¹ * (y' * g'') * a := by rw [hc'eq]
        _ = (a⁻¹ * y' * a) * (a⁻¹ * g'' * a) := by group
    have h1 : a⁻¹ * y' * a ∈ conjugate P a := by
      rcases mem_zpowers_of_sq hzz hy'' with hy1 | hyz
      · rw [hy1]
        have : a⁻¹ * (1 : G) * a = 1 := by group
        rw [this]; exact one_mem _
      · rw [hyz]; exact mem_conj_of (a := a) P hzP
    have h2 : a⁻¹ * g'' * a ∈ P := h.conj_inv_mem h.P_norm hg''
    rw [hcdec]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)
  have : t = g' * (g'⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hg') hcP

theorem comm_P_conj [Finite G] (h : Sec4Core a P Q T S) :
    ∀ p ∈ P, ∀ g ∈ conjugate P a, p * g = g * p := fun _ hp _ hg =>
  comm_of_normal_disjoint h.P_le (h.conj_le h.P_le) h.P_norm (h.conj_norm h.P_norm) h.P_inf_conj hp hg

theorem card_P_sup_conj [Finite G] (h : Sec4Core a P Q T S) : Nat.card ↥(P ⊔ conjugate P a) = 64 := by
  rw [card_sup_of_commute_of_disjoint h.comm_P_conj h.P_inf_conj, card_conjugate', h.P_d8.card_eq]

theorem T_eq_sup_of_card_le [Finite G] (h : Sec4Core a P Q T S) (hT : Nat.card ↥T ≤ 64) :
    T = P ⊔ conjugate P a :=
  (Subgroup.eq_of_le_of_card_ge (sup_le h.P_le (h.conj_le h.P_le))
    (by rw [h.card_P_sup_conj]; exact hT)).symm

theorem exists_swap [Finite G] (h : Sec4Core a P Q T S)
    (hK4 : Nat.card ↥(T ⊓ centralizer (P : Set G)) ≤ 16) {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hxT : ∀ t ∈ T, x * t = t * x) :
    ∃ z ∈ P, z ≠ 1 ∧ (∀ p ∈ P, p * z = z * p) ∧ x ∈ conjugate P a ∧ a * x * a⁻¹ = z := by
  have hPaD : IsD8 (conjugate P a) := h.P_d8.conjugate a
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu, hzT, hCeq⟩ := h.exists_z_centralizer hK4
  obtain ⟨z', hz'Pa, hz'1, hz'z', hz'c, hz'u⟩ := hPaD.exists_z
  have hz'T : ∀ t ∈ T, t * z' * t⁻¹ = z' := fun t ht =>
    central_of_normal_unique (h.conj_norm h.P_norm) hz'1 hz'Pa hz'c hz'u ht
  have hz'' : a⁻¹ * z * a = z' := by
    have hmem : a⁻¹ * z * a ∈ conjugate P a := mem_conj_of (a := a) P hzP
    have hne : a⁻¹ * z * a ≠ 1 := by
      intro h1
      apply hz1
      have : z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      rw [this, h1]; group
    refine (hz'u _ hmem (fun g hg => ?_)).resolve_left hne
    have hga : a * g * a⁻¹ ∈ P := mem_conjugate_iff'.1 hg
    have := hzc _ hga
    calc g * (a⁻¹ * z * a) = a⁻¹ * ((a * g * a⁻¹) * z) * a := by group
      _ = a⁻¹ * (z * (a * g * a⁻¹)) * a := by rw [this]
      _ = (a⁻¹ * z * a) * g := by group
  have hza' : a * z' * a⁻¹ = z := by rw [← hz'']; group
  have hzaz : a * z * a⁻¹ = z' := by
    have e : a * z * a⁻¹ = (a * a) * z' * (a * a)⁻¹ := by
      rw [← hza']; group
    rw [e]
    exact hz'T _ h.a_sq_mem
  have hPPa := h.comm_P_conj
  have hzPaComm : ∀ y ∈ zpowers z, ∀ g ∈ conjugate P a, y * g = g * y := fun y hy g hg =>
    hPPa y ((zpowers_le.2 hzP) hy) g hg
  have hxC : x ∈ zpowers z ⊔ conjugate P a := by
    rw [← hCeq]
    exact ⟨h.Q_le hxQ, Subgroup.mem_centralizer_iff.2 (fun p hp => h.PQ_comm p hp x hxQ)⟩
  obtain ⟨y, hy, g, hg, hxyg⟩ := mem_sup_of_commute hzPaComm hxC
  have hy' := mem_zpowers_of_sq hzz hy
  have hyc : ∀ t ∈ T, y * t = t * y := by
    intro t ht
    rcases hy' with rfl | rfl
    · simp
    · have := hzT t ht
      calc y * t = (t * y * t⁻¹) * t := by rw [this]
        _ = t * y := by group
  have hgc : ∀ p ∈ conjugate P a, p * g = g * p := by
    intro p hp
    have hg_eq : g = y * x := by
      rcases hy' with rfl | rfl
      · simpa using hxyg.symm
      · rw [hxyg, ← mul_assoc, hzz, one_mul]
    have hpT := hPaT hp
    rw [hg_eq]
    calc p * (y * x) = (p * y) * x := by group
      _ = (y * p) * x := by rw [hyc p hpT]
      _ = y * (p * x) := by group
      _ = y * (x * p) := by rw [hxT p hpT]
      _ = (y * x) * p := by group
  have hzQ : z ∉ Q := by
    intro hzQ
    have : z ∈ P ⊓ Q := ⟨hzP, hzQ⟩
    rw [h.PQ_disj, Subgroup.mem_bot] at this
    exact hz1 this
  have hxz' : x = z' := by
    have hg' := hz'u g hg hgc
    rcases hy' with hy1 | hyz
    · rcases hg' with hg1 | hgz
      · exfalso
        apply hx1
        rw [hxyg, hy1, hg1]; simp
      · rw [hxyg, hy1, hgz]; simp
    · rcases hg' with hg1 | hgz
      · exfalso
        apply hzQ
        have : x = z := by rw [hxyg, hyz, hg1]; simp
        rw [← this]; exact hxQ
      · exfalso
        apply h.a_not_mem
        refine h.cent6 x hxQ hx1 hxT a h.a_mem ?_
        have hx : x = z * z' := by rw [hxyg, hyz, hgz]
        have hzz' : z * z' = z' * z := hPPa z hzP z' hz'Pa
        have e : a * x * a⁻¹ = x := by
          rw [hx]
          calc a * (z * z') * a⁻¹ = (a * z * a⁻¹) * (a * z' * a⁻¹) := by group
            _ = z' * z := by rw [hzaz, hza']
            _ = z * z' := hzz'.symm
        calc a * x = (a * x * a⁻¹) * a := by group
          _ = x * a := by rw [e]
  refine ⟨z, hzP, hz1, hzc, ?_, ?_⟩
  · rw [hxz']; exact hz'Pa
  · rw [hxz']; exact hza'

theorem card_centralizer_le_of_card_le [Finite G] (h : Sec4Core a P Q T S) (hT : Nat.card ↥T ≤ 64) :
    Nat.card ↥(T ⊓ centralizer (P : Set G)) ≤ 16 := by
  have hA2 := h.P_inf_conj
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  have hPPa := h.comm_P_conj
  have hTeq := h.T_eq_sup_of_card_le hT
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := h.P_d8.exists_z
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hzcard : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hzPa : zpowers z ⊓ conjugate P a = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases mem_zpowers_of_sq hzz hy.1 with rfl | rfl
    · exact one_mem _
    · exfalso
      have : y ∈ P ⊓ conjugate P a := ⟨hzP, hy.2⟩
      rw [hA2, Subgroup.mem_bot] at this
      exact hz1 this
  have hzPaComm : ∀ x ∈ zpowers z, ∀ y ∈ conjugate P a, x * y = y * x := fun x hx y hy =>
    hPPa x ((zpowers_le.2 hzP) hx) y hy
  have hCcard : Nat.card ↥(zpowers z ⊔ conjugate P a) = 16 := by
    rw [card_sup_of_commute_of_disjoint hzPaComm hzPa, hzcard, card_conjugate', h.P_d8.card_eq]
  have hle : T ⊓ centralizer (P : Set G) ≤ zpowers z ⊔ conjugate P a := by
    rintro c ⟨hcT, hcC⟩
    have hcm : c ∈ P ⊔ conjugate P a := hTeq ▸ hcT
    obtain ⟨p, hp, g, hg, rfl⟩ := mem_sup_of_commute hPPa hcm
    have hpc : ∀ p' ∈ P, p' * p = p * p' := by
      intro p' hp'
      have h1 := Subgroup.mem_centralizer_iff.1 hcC p' hp'
      have h2 : g * p' = p' * g := (hPPa p' hp' g hg).symm
      calc p' * p = (p' * (p * g)) * g⁻¹ := by group
        _ = ((p * g) * p') * g⁻¹ := by rw [h1]
        _ = p * (g * p') * g⁻¹ := by group
        _ = p * (p' * g) * g⁻¹ := by rw [h2]
        _ = p * p' := by group
    rcases hzu p hp hpc with rfl | rfl
    · rw [one_mul]; exact Subgroup.mem_sup_right hg
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers p)) (Subgroup.mem_sup_right hg)
  rw [← hCcard]
  exact Subgroup.card_le_of_le hle

theorem exists_swap_of_card_le [Finite G] (h : Sec4Core a P Q T S) (hT : Nat.card ↥T ≤ 64)
    {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxT : ∀ t ∈ T, x * t = t * x) :
    ∃ z ∈ P, z ≠ 1 ∧ (∀ p ∈ P, p * z = z * p) ∧ x ∈ conjugate P a ∧ a * x * a⁻¹ = z :=
  h.exists_swap (h.card_centralizer_le_of_card_le hT) hxQ hx1 hxT

theorem T_le_closure_involutions [Finite G] (h : Sec4Core a P Q T S)
    (hQel : CFSG.IsElementaryAbelian 2 ↥Q)
    (hK4 : Nat.card ↥(T ⊓ centralizer (P : Set G)) ≤ 16) :
    T ≤ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} := by
  refine (h.T_le_sup hQel hK4).trans (sup_le ?_ ?_)
  · exact h.P_d8.le_closure_involutions.trans
      (Subgroup.closure_mono (fun u hu => ⟨h.P_le hu.1, hu.2⟩))
  · exact (h.P_d8.conjugate a).le_closure_involutions.trans
      (Subgroup.closure_mono (fun u hu => ⟨h.conj_le h.P_le hu.1, hu.2⟩))

end Sec4Core

end CFSG.GH74.GLS.C3.Layer1.Bk
