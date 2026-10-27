module

public import CFSG.GH74.GLS.C3.Layer1.Back93
public import CFSG.GH74.GLS.C3.Layer1.BackConj

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG

variable {G : Type} [Group G]

@[expose] def omegaOneT (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {u : G | u ∈ T ∧ u * u = 1}

theorem omegaOneT_le (T : Subgroup G) : omegaOneT T ≤ T :=
  (Subgroup.closure_le T).2 fun _ hu => hu.1

theorem mem_omegaOneT {T : Subgroup G} {u : G} (hT : u ∈ T) (hu : u * u = 1) : u ∈ omegaOneT T :=
  Subgroup.subset_closure ⟨hT, hu⟩

@[expose] def omegaZ (W : Subgroup G) : Subgroup G where
  carrier := {e | e ∈ W ∧ (∀ w ∈ W, e * w = w * e) ∧ e * e = 1}
  one_mem' := ⟨W.one_mem, fun w _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haW, hac, ha2⟩ ⟨hbW, hbc, hb2⟩
    refine ⟨W.mul_mem haW hbW, fun w hw => ?_, ?_⟩
    · rw [mul_assoc, hbc w hw, ← mul_assoc, hac w hw, mul_assoc]
    · have hab : a * b = b * a := hac b hbW
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haW, hac, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hai]
    exact ⟨haW, hac, ha2⟩

theorem omegaZ_le (W : Subgroup G) : omegaZ W ≤ W := fun _ he => he.1

theorem omegaZ_isElementaryAbelian (W : Subgroup G) : CFSG.IsElementaryAbelian 2 ↥(omegaZ W) :=
  isElementaryAbelian_of_forall (fun _ hu _ hv => hu.2.1 _ hv.1) (fun _ hu => hu.2.2)

theorem omegaZ_conj {W : Subgroup G} {n : G} (hn : n ∈ normalizer (W : Set G)) {e : G}
    (he : e ∈ omegaZ W) : n⁻¹ * e * n ∈ omegaZ W := by
  obtain ⟨heW, hec, he2⟩ := he
  refine ⟨?_, fun w hw => ?_, ?_⟩
  · have := (mem_normalizer_iff.1 (inv_mem hn) e).1 heW
    simpa using this
  · have hw' : n * w * n⁻¹ ∈ W := (mem_normalizer_iff.1 hn w).1 hw
    have h1 := hec _ hw'
    calc n⁻¹ * e * n * w = n⁻¹ * (e * (n * w * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * w * n⁻¹) * e) * n := by rw [h1]
      _ = w * (n⁻¹ * e * n) := by group
  · calc n⁻¹ * e * n * (n⁻¹ * e * n) = n⁻¹ * (e * e) * n := by group
      _ = 1 := by rw [he2]; group

theorem omegaOneT_weakly_closed [Finite G] (T : Subgroup G) (g : G)
    (hg : conjugate (omegaOneT T) g ≤ T) : conjugate (omegaOneT T) g = omegaOneT T := by
  have hind : ∀ w ∈ omegaOneT T, g⁻¹ * w * g ∈ omegaOneT T := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      have hwW : w ∈ omegaOneT T := Subgroup.subset_closure hw
      have h1 : g⁻¹ * w * g ∈ conjugate (omegaOneT T) g := by
        rw [mem_conjugate_iff']
        have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
        rw [e]; exact hwW
      refine mem_omegaOneT (hg h1) ?_
      have e : g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      rw [e, hw.2]; group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      rw [e]; exact (omegaOneT T).mul_mem ha hb
    | inv a _ ha =>
      have e : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      rw [e]; exact (omegaOneT T).inv_mem ha
  have hle : conjugate (omegaOneT T) g ≤ omegaOneT T := by
    intro v hv
    have h1 := hind _ (mem_conjugate_iff'.1 hv)
    have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    rw [e] at h1; exact h1
  exact Subgroup.eq_of_le_of_card_ge hle (card_conjugate' _ g).ge

theorem weakly_closed_self [Finite G] (T : Subgroup G) (g : G) (hg : conjugate T g ≤ T) :
    conjugate T g = T :=
  Subgroup.eq_of_le_of_card_ge hg (card_conjugate' _ g).ge

theorem sup_zpowers_isElementaryAbelian {E : Subgroup G} (hE : CFSG.IsElementaryAbelian 2 ↥E) {u : G}
    (hu2 : u * u = 1) (hc : ∀ e ∈ E, e * u = u * e) :
    CFSG.IsElementaryAbelian 2 ↥(E ⊔ Subgroup.zpowers u) := by
  obtain ⟨hEab, hEsq⟩ := forall_of_isElementaryAbelian hE
  have hcomm : ∀ e ∈ E, ∀ q ∈ Subgroup.zpowers u, e * q = q * e := by
    intro e he q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact (Commute.zpow_right (show Commute e u from hc e he) i).eq
  have hz : ∀ q ∈ Subgroup.zpowers u, ∀ q' ∈ Subgroup.zpowers u, q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq'
    exact (Commute.zpow_zpow_self u i j).eq
  have hsq : ∀ q ∈ Subgroup.zpowers u, q * q = 1 := by
    intro q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have h2 : u ^ 2 = 1 := by rw [sq]; exact hu2
    have : (u ^ i) * (u ^ i) = (u ^ 2) ^ i := by
      rw [← zpow_add, ← two_mul, zpow_mul]
      simp
    rw [this, h2, one_zpow]
  refine isElementaryAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨e, he, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm ha
    obtain ⟨e', he', q', hq', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hb
    calc e * q * (e' * q') = e * (q * e') * q' := by group
      _ = e * (e' * q) * q' := by rw [(hcomm e' he' q hq).symm]
      _ = (e * e') * (q * q') := by group
      _ = (e' * e) * (q' * q) := by rw [hEab e he e' he', hz q hq q' hq']
      _ = e' * (e * q') * q := by group
      _ = e' * (q' * e) * q := by rw [hcomm e he q' hq']
      _ = e' * q' * (e * q) := by group
  · obtain ⟨e, he, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm ha
    calc e * q * (e * q) = e * (q * e) * q := by group
      _ = e * (e * q) * q := by rw [← hcomm e he q hq]
      _ = (e * e) * (q * q) := by group
      _ = 1 := by rw [hEsq e he, hsq q hq, one_mul]

theorem omegaZ_structure [Finite G] {T W : Subgroup G}
    (hinv : ∀ u ∈ T, u * u = 1 → u ∈ W)
    (hrk : ∀ A : Subgroup G, CFSG.IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 16)
    (h9 : 8 < Nat.card ↥(omegaZ W)) :
    Nat.card ↥(omegaZ W) = 16 ∧ ∀ u ∈ T, u * u = 1 → u ∈ omegaZ W := by
  have hEab := omegaZ_isElementaryAbelian W
  have hcard : Nat.card ↥(omegaZ W) = 16 := by
    have h1 := hrk _ hEab
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.IsElementaryAbelian.isPGroup 2 ↥(omegaZ W))
    rw [hk] at h1 h9
    have hk4 : k ≤ 4 := by
      by_contra hk5
      push Not at hk5
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
      omega
    have hk3 : 3 < k := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    have : k = 4 := by omega
    rw [hk, this]; norm_num
  refine ⟨hcard, fun u hu hu2 => ?_⟩
  have huW : u ∈ W := hinv u hu hu2
  have hcu : ∀ e ∈ omegaZ W, e * u = u * e := fun e he => he.2.1 u huW
  have hE' := sup_zpowers_isElementaryAbelian hEab hu2 hcu
  have hle : omegaZ W ≤ omegaZ W ⊔ Subgroup.zpowers u := le_sup_left
  have heq : omegaZ W = omegaZ W ⊔ Subgroup.zpowers u :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hrk _ hE')
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

end CFSG.GH74.GLS.C3.Layer1.Back
