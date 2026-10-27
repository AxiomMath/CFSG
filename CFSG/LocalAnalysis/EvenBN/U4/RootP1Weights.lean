module

public import CFSG.LocalAnalysis.EvenBN.U4.RootP1Coord

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf)
open scoped commutatorElement

theorem conj_mem_of_odd_orderOf {Γ : Type*} [Group Γ] {X M N : Subgroup Γ} {j : Γ}
    (hodd : Odd (orderOf j)) (hMX : M ≤ X) (hsq : ∀ x ∈ X, x * x = 1)
    (hjN : ∀ n ∈ N, j * n * j⁻¹ ∈ N) (h1 : ∀ x ∈ X, j * x * j⁻¹ * x⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, j * m * j⁻¹ * m⁻¹ ∈ N) : ∀ x ∈ X, j * x * j⁻¹ * x⁻¹ ∈ N := by
  have hA : ∀ x ∈ X, (j * j) * x * (j * j)⁻¹ * x⁻¹ ∈ N := by
    intro x hx
    set δ := j * x * j⁻¹ * x⁻¹ with hδ
    have hδM := h1 x hx
    have hδ2 : δ * δ = 1 := hsq δ (hMX hδM)
    have e : (j * j) * x * (j * j)⁻¹ * x⁻¹ = (j * δ * j⁻¹ * δ⁻¹) * (δ * δ) := by
      rw [hδ]
      group
    rw [e, hδ2, mul_one]
    exact h2 δ hδM
  have hjjN : ∀ n ∈ N, (j * j) * n * (j * j)⁻¹ ∈ N := fun n hn => by
    have := hjN _ (hjN n hn)
    rwa [show j * (j * n * j⁻¹) * j⁻¹ = (j * j) * n * (j * j)⁻¹ by group] at this
  set g := j * j with hg
  have hB : ∀ m : ℕ, ∀ x ∈ X, g ^ m * x * (g ^ m)⁻¹ * x⁻¹ ∈ N := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      have e : g ^ (m + 1) * x * (g ^ (m + 1))⁻¹ * x⁻¹ =
          g * (g ^ m * x * (g ^ m)⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by
        rw [pow_succ']
        group
      rw [e]
      exact mul_mem (hjjN _ (ih x hx)) (hA x hx)
  obtain ⟨k, hk⟩ := hodd
  have hj : g ^ (k + 1) = j := by
    rw [hg, ← sq, ← pow_mul, show 2 * (k + 1) = orderOf j + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  intro x hx
  have := hB (k + 1) x hx
  rwa [hj] at this

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem IG_le_normalizer_FG (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoFG h L η t Q : Set G) := by
  have : CharP K 2 := h.charP
  intro x hx
  have hJ : miyamotoPull h L η (miyamotoI1r2 h) ≤ miyamotoIG h L η :=
    miyamotoPull_mono h L η (miyamotoI1r2_le_I h)
  exact mem_normalizer_sup (hS.IG_le_normalizer_E hx)
    (mem_normalizer_inf (hS.IG_le_normalizer_F1 hx) (hS.IG_le_normalizer_centralizer hJ hx))

theorem odd_orderOf_of_mem_IG (_hS : Setting h L η t Q T) {i : G} (hi : i ∈ miyamotoIG h L η) :
    Odd (orderOf i) := by
  have : CharP K 2 := h.charP
  have h1 : Nat.card (miyamotoIG h L η) = Nat.card (miyamotoI h) :=
    card_miyamotoPull h L η (miyamotoI_le_gramSU h)
  have h2 : orderOf i ∣ Nat.card (miyamotoIG h L η) := Subgroup.orderOf_dvd_natCard _ hi
  exact Odd.of_dvd_nat (h1 ▸ odd_card_miyamotoI h) h2

theorem torusElt_inv (hS : Setting h L η t Q T) (p : Kˣ × Kˣ) (hp : miyamotoIParam h p = 1) :
    (hS.torusElt p hp)⁻¹ = hS.torusElt p⁻¹ (by rw [map_inv, hp, inv_one]) := by
  simp only [torusElt]
  rw [← L.coe_inv, ← map_inv]
  congr 3

theorem torusElt_conj_mul_inv_mem_Z2 (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpB : miyamotoWeightB h p = 1) {a : G}
    (ha : a ∈ miyamotoA1G h L η) :
    (hS.torusElt p hp)⁻¹ * a * hS.torusElt p hp * a⁻¹ ∈ miyamotoPull h L η (miyamotoZ2 h) := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  have hD := miyamotoI_le_gramSU h ((miyamotoIHom_mem_miyamotoI_iff h p).2 hp)
  have h1 := miyamotoIHom_conj_mul_inv_mem_Z2 h p hpB hg
  have h2 : ((η.symm ((⟨_, hD⟩ : gramSU h (miyamotoJ4 K))⁻¹ * g * ⟨_, hD⟩ * g⁻¹) : L) : G) ∈
      miyamotoPull h L η (miyamotoZ2 h) :=
    (symm_mem_miyamotoPull_iff h L η).2 (by simpa only [coe_mul, coe_inv] using h1)
  simpa only [map_mul, map_inv, L.coe_mul, L.coe_inv, torusElt] using h2

theorem torusElt_conj_mul_inv_mem_ZP (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpC : miyamotoWeightC h p = 1) {z : G}
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    (hS.torusElt p hp)⁻¹ * z * hS.torusElt p hp * z⁻¹ ∈ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  have hD := miyamotoI_le_gramSU h ((miyamotoIHom_mem_miyamotoI_iff h p).2 hp)
  have h1 := miyamotoIHom_conj_mul_inv_mem_Z h p hpC hg
  have h2 : ((η.symm ((⟨_, hD⟩ : gramSU h (miyamotoJ4 K))⁻¹ * g * ⟨_, hD⟩ * g⁻¹) : L) : G) ∈
      miyamotoZG h L η :=
    (symm_mem_miyamotoPull_iff h L η).2 (by simpa only [coe_mul, coe_inv] using h1)
  simpa only [map_mul, map_inv, L.coe_mul, L.coe_inv, torusElt] using h2

theorem commutator_PG_mem_Z2 (_hS : Setting h L η t Q T) {p a : G} (hp : p ∈ miyamotoPG h L η)
    (ha : a ∈ miyamotoPG h L η) :
    p * a * p⁻¹ * a⁻¹ ∈ miyamotoPull h L η (miyamotoZ2 h) := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hp
  obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  have h1 : ⁅(g : GL (Fin 4) K), (k : GL (Fin 4) K)⁆ ∈ miyamotoZ2 h := by
    rw [← commutator_miyamotoP h]
    exact commutator_mem_commutator hg hk
  have h2 : ((η.symm (g * k * g⁻¹ * k⁻¹) : L) : G) ∈ miyamotoPull h L η (miyamotoZ2 h) :=
    (symm_mem_miyamotoPull_iff h L η).2 (by
      simpa only [coe_mul, coe_inv, commutatorElement_def] using h1)
  simpa only [map_mul, map_inv, L.coe_mul, L.coe_inv] using h2

theorem crossed_conj_of_commute (_hS : Setting h L η t Q T) {g z : G} (hgt : g * t = t * g) :
    (g * z * g⁻¹)⁻¹ * t * (g * z * g⁻¹) * t = g * (z⁻¹ * t * z * t) * g⁻¹ := by
  have hgt' : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgt]
      _ = t * g⁻¹ := by group
  calc (g * z * g⁻¹)⁻¹ * t * (g * z * g⁻¹) * t = g * z⁻¹ * (g⁻¹ * t) * g * z * g⁻¹ * t := by
        group
    _ = g * z⁻¹ * (t * g⁻¹) * g * z * g⁻¹ * t := by rw [hgt']
    _ = g * z⁻¹ * t * z * (g⁻¹ * t) := by group
    _ = g * z⁻¹ * t * z * (t * g⁻¹) := by rw [hgt']
    _ = g * (z⁻¹ * t * z * t) * g⁻¹ := by group

theorem exists_mul_of_crossed_mem_Z2 (hS : Setting h L η t Q T) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) (hc : y⁻¹ * t * y * t ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    ∃ a ∈ miyamotoA1G h L η, ∃ φ ∈ miyamotoFG h L η t Q, y = a * φ := by
  obtain ⟨φ, hφ, hφc⟩ := hS.exists_F_crossed_eq hc
  have hφF := hS.F_le_F1 hφ
  have hA : y * φ⁻¹ ∈ miyamotoA1G h L η := by
    refine (hS.crossed_eq_one_iff_F1 (mul_mem hy (inv_mem hφF))).1 ?_
    rw [hS.crossed_mul_D1 (hS.F1_le_D1 hy) (inv_mem (hS.F1_le_D1 hφF)),
      hS.crossed_inv_D1 (hS.F1_le_D1 hφF), hφc, mul_inv_cancel]
  exact ⟨_, hA, φ, hφ, by group⟩

theorem mem_Z2_of_mem_F_of_mem_A1 (hS : Setting h L η t Q T) {a : G}
    (haF : a ∈ miyamotoFG h L η t Q) (haA : a ∈ miyamotoA1G h L η) :
    a ∈ miyamotoPull h L η (miyamotoZ2 h) := by
  refine hS.mem_Z2_of_commutator_mem_ZP haA fun g hg => ?_
  rw [← hS.E_inf_A1]
  refine mem_inf.2 ⟨hS.commutator_F_PG_mem_E haF hg, ?_⟩
  have := (mem_normalizer_iff.1 (hS.PG_le_normalizer_A1 hg) a⁻¹).1 (inv_mem haA)
  rw [show a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) by group]
  exact mul_mem haA this

theorem exists_mul_of_crossed_mem_ZP (hS : Setting h L η t Q T) {w : G}
    (hw : w ∈ miyamotoFG h L η t Q) (hc : w⁻¹ * t * w * t ∈ miyamotoZG h L η) :
    ∃ z ∈ miyamotoPull h L η (miyamotoZ2 h), ∃ e ∈ miyamotoEG h L η Q, w = z * e := by
  obtain ⟨e, he, hec⟩ := hS.exists_E_crossed_eq hc
  have hwF := hS.F_le_F1 hw
  have heF := hS.E_le_F1 he
  have hA : w * e⁻¹ ∈ miyamotoA1G h L η := by
    refine (hS.crossed_eq_one_iff_F1 (mul_mem hwF (inv_mem heF))).1 ?_
    rw [hS.crossed_mul_D1 (hS.F1_le_D1 hwF) (inv_mem (hS.F1_le_D1 heF)),
      hS.crossed_inv_D1 (hS.F1_le_D1 heF), hec, mul_inv_cancel]
  have hwe : w * e⁻¹ ∈ miyamotoFG h L η t Q := mul_mem hw (inv_mem (hS.E_le_F he))
  exact ⟨_, hS.mem_Z2_of_mem_F_of_mem_A1 hwe hA, e, he, by group⟩

theorem conj_mem_F_of_weightB (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpB : miyamotoWeightB h p = 1) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) :
    (hS.torusElt p hp)⁻¹ * y * hS.torusElt p hp * y⁻¹ ∈ miyamotoFG h L η t Q := by
  set i := hS.torusElt p hp with hi
  have hiI := hS.torusElt_mem_IG p hp
  have hiC : i⁻¹ * t = t * i⁻¹ :=
    mem_centralizer_singleton_iff.1 (hS.IG_le_C (inv_mem hiI))
  have hcommAF : ∀ a ∈ miyamotoA1G h L η, ∀ φ ∈ miyamotoFG h L η t Q, a * φ = φ * a :=
    fun a ha φ hφ => hS.F1_comm (hS.A1_le_F1 ha) (hS.F_le_F1 hφ)
  have hM : miyamotoA1G h L η ⊔ miyamotoFG h L η t Q ≤ miyamotoF1G h L η t :=
    sup_le hS.A1_le_F1 hS.F_le_F1
  have key := conj_mem_of_odd_orderOf (X := miyamotoF1G h L η t)
    (M := miyamotoA1G h L η ⊔ miyamotoFG h L η t Q) (N := miyamotoFG h L η t Q) (j := i⁻¹)
    (by rw [orderOf_inv]; exact hS.odd_orderOf_of_mem_IG hiI) hM (fun x hx => hS.F1_mul_self x hx)
    (fun n hn => by
      have := (mem_normalizer_iff.1 (hS.IG_le_normalizer_FG (inv_mem hiI)) n).1 hn
      exact this)
    (fun x hx => by
      have hxD := hS.F1_le_D1 hx
      have hcx := hS.crossed_mem_A1_of_mem_D1 hxD
      have hxiD : i⁻¹ * x * i⁻¹⁻¹ ∈ miyamotoD1 h L η t :=
        hS.F1_le_D1 ((mem_normalizer_iff.1 (hS.IG_le_normalizer_F1 (inv_mem hiI)) x).1 hx)
      have hc : (i⁻¹ * x * i⁻¹⁻¹ * x⁻¹)⁻¹ * t * (i⁻¹ * x * i⁻¹⁻¹ * x⁻¹) * t ∈
          miyamotoPull h L η (miyamotoZ2 h) := by
        rw [hS.crossed_mul_D1 hxiD (inv_mem hxD), hS.crossed_conj_of_commute hiC,
          hS.crossed_inv_D1 hxD, inv_inv]
        exact hS.torusElt_conj_mul_inv_mem_Z2 p hp hpB hcx
      have hw : i⁻¹ * x * i⁻¹⁻¹ * x⁻¹ ∈ miyamotoF1G h L η t :=
        mul_mem ((mem_normalizer_iff.1 (hS.IG_le_normalizer_F1 (inv_mem hiI)) x).1 hx) (inv_mem hx)
      obtain ⟨a, ha, φ, hφ, e⟩ := hS.exists_mul_of_crossed_mem_Z2 hw hc
      rw [e]
      exact mul_mem (mem_sup_left ha) (mem_sup_right hφ))
    (fun m hm => by
      obtain ⟨a, ha, φ, hφ, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommAF hm
      have h1 : i⁻¹ * a * i⁻¹⁻¹ * a⁻¹ ∈ miyamotoFG h L η t Q := by
        rw [inv_inv]
        exact hS.Z2_le_F (hS.torusElt_conj_mul_inv_mem_Z2 p hp hpB ha)
      have h2 : i⁻¹ * φ * i⁻¹⁻¹ * φ⁻¹ ∈ miyamotoFG h L η t Q :=
        mul_mem ((mem_normalizer_iff.1 (hS.IG_le_normalizer_FG (inv_mem hiI)) φ).1 hφ)
          (inv_mem hφ)
      have hcomm : a * (i⁻¹ * φ * i⁻¹⁻¹ * φ⁻¹) = (i⁻¹ * φ * i⁻¹⁻¹ * φ⁻¹) * a :=
        hS.F1_comm (hS.A1_le_F1 ha) (hS.F_le_F1 h2)
      have e : i⁻¹ * (a * φ) * i⁻¹⁻¹ * (a * φ)⁻¹ =
          (i⁻¹ * a * i⁻¹⁻¹ * a⁻¹) * (a * (i⁻¹ * φ * i⁻¹⁻¹ * φ⁻¹) * a⁻¹) := by
        group
      rw [e, hcomm, mul_inv_cancel_right]
      exact mul_mem h1 h2)
  have := key y hy
  rwa [inv_inv] at this

theorem conj_mem_E_of_weightC (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpC : miyamotoWeightC h p = 1) {w : G}
    (hw : w ∈ miyamotoFG h L η t Q) :
    (hS.torusElt p hp)⁻¹ * w * hS.torusElt p hp * w⁻¹ ∈ miyamotoEG h L η Q := by
  set i := hS.torusElt p hp with hi
  have hiI := hS.torusElt_mem_IG p hp
  have hiC : i⁻¹ * t = t * i⁻¹ :=
    mem_centralizer_singleton_iff.1 (hS.IG_le_C (inv_mem hiI))
  have hcommZE : ∀ z ∈ miyamotoPull h L η (miyamotoZ2 h), ∀ e ∈ miyamotoEG h L η Q,
      z * e = e * z := fun z hz e he =>
    hS.F1_comm (hS.A1_le_F1 (hS.Z2_le_A1 hz)) (hS.E_le_F1 he)
  have hM : miyamotoPull h L η (miyamotoZ2 h) ⊔ miyamotoEG h L η Q ≤ miyamotoFG h L η t Q :=
    sup_le hS.Z2_le_F hS.E_le_F
  have key := conj_mem_of_odd_orderOf (X := miyamotoFG h L η t Q)
    (M := miyamotoPull h L η (miyamotoZ2 h) ⊔ miyamotoEG h L η Q) (N := miyamotoEG h L η Q)
    (j := i⁻¹) (by rw [orderOf_inv]; exact hS.odd_orderOf_of_mem_IG hiI) hM
    (fun x hx => hS.F1_mul_self x (hS.F_le_F1 hx))
    (fun n hn => (mem_normalizer_iff.1 (hS.IG_le_normalizer_E (inv_mem hiI)) n).1 hn)
    (fun x hx => by
      have hxF1 := hS.F_le_F1 hx
      have hxD := hS.F1_le_D1 hxF1
      have hcx := hS.crossed_mem_Z2_of_mem_F hx
      have hxi : i⁻¹ * x * i⁻¹⁻¹ ∈ miyamotoFG h L η t Q :=
        (mem_normalizer_iff.1 (hS.IG_le_normalizer_FG (inv_mem hiI)) x).1 hx
      have hxiD := hS.F1_le_D1 (hS.F_le_F1 hxi)
      have hc : (i⁻¹ * x * i⁻¹⁻¹ * x⁻¹)⁻¹ * t * (i⁻¹ * x * i⁻¹⁻¹ * x⁻¹) * t ∈
          miyamotoZG h L η := by
        rw [hS.crossed_mul_D1 hxiD (inv_mem hxD), hS.crossed_conj_of_commute hiC,
          hS.crossed_inv_D1 hxD, inv_inv]
        exact hS.torusElt_conj_mul_inv_mem_ZP p hp hpC hcx
      obtain ⟨z, hz, e, he, hze⟩ := hS.exists_mul_of_crossed_mem_ZP (mul_mem hxi (inv_mem hx)) hc
      rw [hze]
      exact mul_mem (mem_sup_left hz) (mem_sup_right he))
    (fun m hm => by
      obtain ⟨z, hz, e, he, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommZE hm
      have h1 : i⁻¹ * z * i⁻¹⁻¹ * z⁻¹ ∈ miyamotoEG h L η Q := by
        rw [inv_inv]
        exact hS.ZP_le_E (hS.torusElt_conj_mul_inv_mem_ZP p hp hpC hz)
      have h2 : i⁻¹ * e * i⁻¹⁻¹ * e⁻¹ ∈ miyamotoEG h L η Q :=
        mul_mem ((mem_normalizer_iff.1 (hS.IG_le_normalizer_E (inv_mem hiI)) e).1 he)
          (inv_mem he)
      have hcomm : z * (i⁻¹ * e * i⁻¹⁻¹ * e⁻¹) = (i⁻¹ * e * i⁻¹⁻¹ * e⁻¹) * z :=
        hS.F1_comm (hS.A1_le_F1 (hS.Z2_le_A1 hz)) (hS.E_le_F1 h2)
      have e' : i⁻¹ * (z * e) * i⁻¹⁻¹ * (z * e)⁻¹ =
          (i⁻¹ * z * i⁻¹⁻¹ * z⁻¹) * (z * (i⁻¹ * e * i⁻¹⁻¹ * e⁻¹) * z⁻¹) := by
        group
      rw [e', hcomm, mul_inv_cancel_right]
      exact mul_mem h1 h2)
  have := key w hw
  rwa [inv_inv] at this


theorem commutator_rootElt_mem_A1_sup_F (hS : Setting h L η t Q T) (κ : K) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) :
    hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹ ∈ miyamotoA1G h L η ⊔ miyamotoFG h L η t Q := by
  set s := hS.rootElt κ with hs
  have hsP := hS.rootElt_mem_PG κ
  have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (hS.PG_le_C hsP)
  have hyD := hS.F1_le_D1 hy
  have hsy : s * y * s⁻¹ ∈ miyamotoF1G h L η t :=
    (mem_normalizer_iff.1 (hS.PG_le_normalizer_F1 hsP) y).1 hy
  have hc : (s * y * s⁻¹ * y⁻¹)⁻¹ * t * (s * y * s⁻¹ * y⁻¹) * t ∈
      miyamotoPull h L η (miyamotoZ2 h) := by
    rw [hS.crossed_mul_D1 (hS.F1_le_D1 hsy) (inv_mem hyD), hS.crossed_conj_of_commute hst,
      hS.crossed_inv_D1 hyD]
    exact hS.commutator_PG_mem_Z2 hsP (hS.A1G_le_PG (hS.crossed_mem_A1_of_mem_D1 hyD))
  obtain ⟨a, ha, φ, hφ, e⟩ := hS.exists_mul_of_crossed_mem_Z2 (mul_mem hsy (inv_mem hy)) hc
  rw [e]
  exact mul_mem (mem_sup_left ha) (mem_sup_right hφ)

theorem commutator_rootElt_mem_F (hS : Setting h L η t Q T) (κ : K) {m : G}
    (hm : m ∈ miyamotoA1G h L η ⊔ miyamotoFG h L η t Q) :
    hS.rootElt κ * m * (hS.rootElt κ)⁻¹ * m⁻¹ ∈ miyamotoFG h L η t Q := by
  set s := hS.rootElt κ with hs
  have hsP := hS.rootElt_mem_PG κ
  have hcommAF : ∀ a ∈ miyamotoA1G h L η, ∀ φ ∈ miyamotoFG h L η t Q, a * φ = φ * a :=
    fun a ha φ hφ => hS.F1_comm (hS.A1_le_F1 ha) (hS.F_le_F1 hφ)
  obtain ⟨a, ha, φ, hφ, rfl⟩ := exists_mul_of_mem_sup_of_commute hcommAF hm
  have h1 : s * a * s⁻¹ * a⁻¹ ∈ miyamotoFG h L η t Q :=
    hS.Z2_le_F (hS.commutator_PG_mem_Z2 hsP (hS.A1G_le_PG ha))
  have h2 : s * φ * s⁻¹ * φ⁻¹ ∈ miyamotoEG h L η Q := by
    have := inv_mem (hS.commutator_F_PG_mem_E hφ hsP)
    rwa [show (φ * s * φ⁻¹ * s⁻¹)⁻¹ = s * φ * s⁻¹ * φ⁻¹ by group] at this
  have hcomm : a * (s * φ * s⁻¹ * φ⁻¹) = (s * φ * s⁻¹ * φ⁻¹) * a :=
    hS.F1_comm (hS.A1_le_F1 ha) (hS.E_le_F1 h2)
  have e : s * (a * φ) * s⁻¹ * (a * φ)⁻¹ =
      (s * a * s⁻¹ * a⁻¹) * (a * (s * φ * s⁻¹ * φ⁻¹) * a⁻¹) := by
    group
  rw [e, hcomm, mul_inv_cancel_right]
  exact mul_mem h1 (hS.E_le_F h2)

theorem commutator_rootElt_add (hS : Setting h L η t Q T) (κ κ' : K) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) :
    (hS.rootElt (κ + κ') * y * (hS.rootElt (κ + κ'))⁻¹ * y⁻¹) *
        ((hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) *
          (hS.rootElt κ' * y * (hS.rootElt κ')⁻¹ * y⁻¹))⁻¹ ∈ miyamotoFG h L η t Q := by
  set w := hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹ with hw
  set w' := hS.rootElt κ' * y * (hS.rootElt κ')⁻¹ * y⁻¹ with hw'
  have hw'm := hS.commutator_rootElt_mem_A1_sup_F κ' hy
  have hwF : w ∈ miyamotoF1G h L η t :=
    (sup_le hS.A1_le_F1 hS.F_le_F1) (hS.commutator_rootElt_mem_A1_sup_F κ hy)
  have hw'F : w' ∈ miyamotoF1G h L η t := (sup_le hS.A1_le_F1 hS.F_le_F1) hw'm
  have h1 := hS.commutator_rootElt_mem_F κ hw'm
  have hcomm : w' * w = w * w' := hS.F1_comm hw'F hwF
  have e : hS.rootElt (κ + κ') * y * (hS.rootElt (κ + κ'))⁻¹ * y⁻¹ * (w * w')⁻¹ =
      (hS.rootElt κ * w' * (hS.rootElt κ)⁻¹ * w'⁻¹) * ((w' * w) * (w * w')⁻¹) := by
    rw [hS.rootElt_add, hw, hw']
    group
  rw [e, hcomm, mul_inv_cancel, mul_one]
  exact h1

theorem commutator_rootElt_weight (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpB : miyamotoWeightB h p = 1) (κ : K) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) :
    (hS.rootElt (miyamotoWeightA p * κ) * y * (hS.rootElt (miyamotoWeightA p * κ))⁻¹ * y⁻¹) *
        (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹)⁻¹ ∈ miyamotoFG h L η t Q := by
  set i := hS.torusElt p hp with hi
  have hiI := hS.torusElt_mem_IG p hp
  set s := hS.rootElt κ with hs
  set w := s * y * s⁻¹ * y⁻¹ with hw
  have hsP := hS.rootElt_mem_PG κ
  have hpB' : miyamotoWeightB h p⁻¹ = 1 := by rw [map_inv, hpB, inv_one]
  have hφ : i * y * i⁻¹ * y⁻¹ ∈ miyamotoFG h L η t Q := by
    have := hS.conj_mem_F_of_weightB p⁻¹ (by rw [map_inv, hp, inv_one]) hpB' hy
    rwa [← hS.torusElt_inv p hp, inv_inv] at this
  set φ := i * y * i⁻¹ * y⁻¹ with hφdef
  have hsφ : s * φ * s⁻¹ * φ⁻¹ ∈ miyamotoEG h L η Q := by
    have := inv_mem (hS.commutator_F_PG_mem_E hφ hsP)
    rwa [show (φ * s * φ⁻¹ * s⁻¹)⁻¹ = s * φ * s⁻¹ * φ⁻¹ by group] at this
  have hwF : w ∈ miyamotoF1G h L η t :=
    (sup_le hS.A1_le_F1 hS.F_le_F1) (hS.commutator_rootElt_mem_A1_sup_F κ hy)
  have hcomm : φ * w = w * φ := hS.F1_comm (hS.F_le_F1 hφ) hwF
  have hiw : i⁻¹ * w * i * w⁻¹ ∈ miyamotoFG h L η t Q := hS.conj_mem_F_of_weightB p hp hpB hwF
  have hiE : i⁻¹ * (s * φ * s⁻¹ * φ⁻¹) * i ∈ miyamotoEG h L η Q := by
    have := (mem_normalizer_iff.1 (hS.IG_le_normalizer_E (inv_mem hiI)) _).1 hsφ
    rwa [inv_inv] at this
  have e : hS.rootElt (miyamotoWeightA p * κ) * y * (hS.rootElt (miyamotoWeightA p * κ))⁻¹ * y⁻¹ *
      w⁻¹ = (i⁻¹ * (s * φ * s⁻¹ * φ⁻¹) * i) * (i⁻¹ * (φ * w * φ⁻¹) * i * w⁻¹) := by
    rw [← hS.torusElt_conj_rootElt p hp κ, ← hi, ← hs, hφdef, hw]
    group
  rw [e, hcomm, mul_inv_cancel_right]
  exact mul_mem (hS.E_le_F hiE) hiw

theorem commutator_rootElt_mem_F' (hS : Setting h L η t Q T) (κ : K) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) :
    hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹ ∈ miyamotoFG h L η t Q := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨γ, hγ⟩ : ∃ γ : Kˣ, γ ≠ 1 := by
    obtain ⟨u, hu⟩ := exists_add_bar_eq_one h
    by_cases hu0 : u = 0
    · exfalso
      rw [hu0, map_zero, add_zero] at hu
      exact zero_ne_one hu
    · by_cases hu1 : u = 1
      · exfalso
        rw [hu1, map_one, CharTwo.add_self_eq_zero] at hu
        exact zero_ne_one hu
      · exact ⟨Units.mk0 u hu0, fun e => hu1 (by simpa using congrArg Units.val e)⟩
  obtain ⟨p, hp, hpB, hpA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h γ
  set μ : K := (miyamotoWeightA p : K) with hμ
  have hμ1 : μ + 1 ≠ 0 := by
    intro e
    apply hγ
    have : μ = 1 := by
      calc μ = μ + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
        _ = 1 := by rw [← add_assoc, e, zero_add]
    rw [← hpA]
    exact Units.ext this
  set κ₀ := κ / (μ + 1) with hκ₀
  have hκ : κ = μ * κ₀ + κ₀ := by
    rw [hκ₀]
    field_simp
  set w₀ := hS.rootElt κ₀ * y * (hS.rootElt κ₀)⁻¹ * y⁻¹ with hw₀
  have hw₀F : w₀ ∈ miyamotoF1G h L η t :=
    (sup_le hS.A1_le_F1 hS.F_le_F1) (hS.commutator_rootElt_mem_A1_sup_F κ₀ hy)
  have h1 := hS.commutator_rootElt_add (μ * κ₀) κ₀ hy
  have h2 := hS.commutator_rootElt_weight p hp hpB κ₀ hy
  rw [← hκ] at h1
  have e : hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹ =
      ((hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) *
        ((hS.rootElt (μ * κ₀) * y * (hS.rootElt (μ * κ₀))⁻¹ * y⁻¹) * w₀)⁻¹) *
      ((hS.rootElt (μ * κ₀) * y * (hS.rootElt (μ * κ₀))⁻¹ * y⁻¹) * w₀⁻¹) * (w₀ * w₀) := by
    group
  rw [e, hS.F1_mul_self w₀ hw₀F, mul_one]
  exact mul_mem h1 h2

theorem commutator_P1_F1_mem_F (hS : Setting h L η t Q T) {x y : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hy : y ∈ miyamotoF1G h L η t) :
    x * y * x⁻¹ * y⁻¹ ∈ miyamotoFG h L η t Q := by
  set κ := hS.coordP1 x
  have hxs := hS.coordP1_spec hx
  set φ₀ := x * (hS.rootElt κ)⁻¹ with hφ₀
  have hw := hS.commutator_rootElt_mem_F' κ hy (Q := Q)
  have hwF := hS.F_le_F1 hw
  have hc1 : φ₀ * (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) =
      (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) * φ₀ := hS.F1_comm hxs hwF
  have hc2 : φ₀ * y = y * φ₀ := hS.F1_comm hxs hy
  have hc3 : y * φ₀⁻¹ * y⁻¹ = φ₀⁻¹ := by
    calc y * φ₀⁻¹ * y⁻¹ = φ₀⁻¹ * (φ₀ * y) * φ₀⁻¹ * y⁻¹ := by group
      _ = φ₀⁻¹ * (y * φ₀) * φ₀⁻¹ * y⁻¹ := by rw [hc2]
      _ = φ₀⁻¹ := by group
  have e : x * y * x⁻¹ * y⁻¹ =
      φ₀ * (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) * (y * φ₀⁻¹ * y⁻¹) := by
    rw [hφ₀]
    group
  rw [e, hc3, hc1, mul_inv_cancel_right]
  exact hw

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
