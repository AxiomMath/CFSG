module

public import CFSG.GF2Type.CenterFour.CaseBBasic

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

@[expose] def psi (z₁ q : G) : G := z₁ * (q * z₁ * q⁻¹)

private theorem comm_of_conj_eq {z₁ y : G} (hz₁ : z₁ * z₁ = 1) (h : z₁ * y * z₁ = y) :
    y * z₁ = z₁ * y := by
  calc y * z₁ = (z₁ * z₁) * y * z₁ := by rw [hz₁, one_mul]
    _ = z₁ * (z₁ * y * z₁) := by simp only [mul_assoc]
    _ = z₁ * y := by rw [h]

private theorem mem_inf_of_conj_inv {z₁ y : G} (hz₁ : z₁ * z₁ = 1) (hy : y ∈ coreAt z)
    (hinv : z₁ * y * z₁ = y⁻¹) (hy2 : y ^ 2 = 1) :
    y ∈ coreAt z ⊓ centralizer ({z₁} : Set G) := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hy2)
  rw [hyinv] at hinv
  exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hz₁ hinv)⟩

private theorem mul_self_eq_one_of_config (hC : Config z n) : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rw [hC.orderOf_eq] at h
  rw [← sq]
  exact h

private theorem conj_mul_self_eq_one (hC : Config z n) (g : G) :
    (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
  have hz2 := mul_self_eq_one_of_config hC
  calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [hz2]; group

private theorem mem_sup_decompose {F E : Subgroup G} {x : G} (hx : x ∈ F ⊔ E)
    (hE : E ≤ centralizer (F : Set G)) :
    ∃ f ∈ F, ∃ e ∈ E, x = f * e := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro v hv
    rcases hv with hvF | hvE
    · exact ⟨v, hvF, 1, E.one_mem, by simp⟩
    · exact ⟨1, F.one_mem, v, hvE, by simp⟩
  · intro v hv
    rcases hv with hvF | hvE
    · exact ⟨v⁻¹, F.inv_mem hvF, 1, E.one_mem, by simp⟩
    · exact ⟨1, F.one_mem, v⁻¹, E.inv_mem hvE, by simp⟩
  · exact ⟨1, F.one_mem, 1, E.one_mem, by simp⟩
  · intro a b _ha _hb hpa hpb
    rcases hpa with ⟨f, hf, e, he, rfl⟩
    rcases hpb with ⟨f', hf', e', he', rfl⟩
    have hcomm : e * f' = f' * e :=
      ((Subgroup.mem_centralizer_iff (g := e) (s := (F : Set G))).1 (hE he) f' hf').symm
    refine ⟨f * f', F.mul_mem hf hf', e * e', E.mul_mem he he', ?_⟩
    calc f * e * (f' * e') = f * (e * f') * e' := by simp only [mul_assoc]
      _ = f * (f' * e) * e' := by rw [hcomm]
      _ = f * f' * (e * e') := by simp only [mul_assoc]

theorem psi_mem_core (hC : Config z n) {z₁ : G} (hz₁ : z₁ * z₁ = 1)
    (hH : z₁ ∈ centralizer ({z} : Set G)) {q : G} (hq : q ∈ coreAt z) :
    psi z₁ q ∈ coreAt z := by
  have hzinv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁
  have e : psi z₁ q = (z₁ * q * z₁⁻¹) * q⁻¹ := by
    unfold psi
    rw [hzinv]
    simp only [mul_assoc]
  rw [e]
  exact Subgroup.mul_mem _ (hC.conj_mem_core hH hq) (inv_mem hq)

theorem psi_conj {z₁ q : G} (hz₁ : z₁ * z₁ = 1) : z₁ * psi z₁ q * z₁ = (psi z₁ q)⁻¹ := by
  have hzinv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁
  unfold psi
  calc z₁ * (z₁ * (q * z₁ * q⁻¹)) * z₁ = (z₁ * z₁) * (q * z₁ * q⁻¹) * z₁ := by
        simp only [mul_assoc]
    _ = (q * z₁ * q⁻¹) * z₁ := by rw [hz₁, one_mul]
    _ = (z₁ * (q * z₁ * q⁻¹))⁻¹ := by
        simp only [mul_inv_rev, inv_inv, hzinv, mul_assoc]

theorem psi_mem_iff_sq_eq_one (hC : Config z n) {z₁ : G} (hz₁ : z₁ * z₁ = 1)
    (hH : z₁ ∈ centralizer ({z} : Set G)) {q : G} (hq : q ∈ coreAt z) :
    psi z₁ q ∈ coreAt z ⊓ centralizer ({z₁} : Set G) ↔ psi z₁ q ^ 2 = 1 := by
  constructor
  · intro h
    have hc : psi z₁ q * z₁ = z₁ * psi z₁ q :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h).2
    have hfix : z₁ * psi z₁ q * z₁ = psi z₁ q := by
      rw [← hc, mul_assoc, hz₁, mul_one]
    have hinv : (psi z₁ q)⁻¹ = psi z₁ q := (psi_conj hz₁).symm.trans hfix
    rw [sq]
    exact mul_eq_one_iff_inv_eq.mpr hinv
  · intro h
    exact mem_inf_of_conj_inv hz₁ (psi_mem_core hC hz₁ hH hq) (psi_conj hz₁) h

private theorem psi_mem_sup (hC : Config z n) {z₁ : G} (hz₁ : z₁ * z₁ = 1)
    (hH : z₁ ∈ centralizer ({z} : Set G)) (hK : z₁ ∉ centralizer (centerAt z : Set G))
    {q : G} (hq : q ∈ coreAt z) :
    psi z₁ q ∈ (coreAt z ⊓ centralizer ({z₁} : Set G)) ⊔ centerAt z := by
  have hQ : psi z₁ q ∈ coreAt z := psi_mem_core hC hz₁ hH hq
  rcases hC.sq_eq _ hQ with h | h
  · exact Subgroup.mem_sup_left ((psi_mem_iff_sq_eq_one hC hz₁ hH hq).mpr h)
  · obtain ⟨k, hZk, -, hk2⟩ := hC.exists_generator
    have hkZ : k ∈ centerAt z := by
      rw [hZk]
      exact Subgroup.mem_zpowers k
    have hkQ : k ∈ coreAt z := hC.center_le_core hkZ
    have hcomm : Commute (psi z₁ q) k :=
      (Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hQ) k hkZ).symm
    have hzinv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁
    have hinvk : z₁ * k * z₁ = k⁻¹ := by
      have h' := hC.inv_of_not_mem_centralizer hH hK hkZ
      rwa [hzinv] at h'
    have hy2 : (psi z₁ q * k) ^ 2 = 1 := by
      rw [hcomm.mul_pow, h, hk2, mul_self_eq_one_of_config hC]
    have hy_inv : z₁ * (psi z₁ q * k) * z₁ = (psi z₁ q * k)⁻¹ := by
      calc z₁ * (psi z₁ q * k) * z₁ = z₁ * psi z₁ q * (z₁ * z₁) * k * z₁ := by
            rw [hz₁]
            simp only [mul_assoc, mul_one]
        _ = (z₁ * psi z₁ q * z₁) * (z₁ * k * z₁) := by simp only [mul_assoc]
        _ = (psi z₁ q)⁻¹ * k⁻¹ := by rw [psi_conj hz₁, hinvk]
        _ = (psi z₁ q * k)⁻¹ := by
            rw [mul_inv_rev]
            exact hcomm.inv_inv.eq
    have hyR : psi z₁ q * k ∈ coreAt z ⊓ centralizer ({z₁} : Set G) :=
      mem_inf_of_conj_inv hz₁ (Subgroup.mul_mem _ hQ hkQ) hy_inv hy2
    have hsplit : psi z₁ q = psi z₁ q * k * k⁻¹ := (mul_inv_cancel_right _ _).symm
    rw [hsplit]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyR) (Subgroup.mem_sup_right (inv_mem hkZ))

theorem CaseB.psi_mem (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {q : G} (hq : q ∈ coreAt z) :
    psi (g⁻¹ * z * g) q ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z :=
  psi_mem_sup hC (conj_mul_self_eq_one hC g) hH hK hq

theorem CaseB.psi_eq_psi_iff (hC : Config z n) {z₁ : G} {q q' : G}
    (hq : q ∈ coreAt z) (hq' : q' ∈ coreAt z) :
    psi z₁ q = psi z₁ q' ↔ q'⁻¹ * q ∈ coreAt z ⊓ centralizer ({z₁} : Set G) := by
  have key : psi z₁ q = psi z₁ q' ↔ q'⁻¹ * q * z₁ = z₁ * (q'⁻¹ * q) := by
    unfold psi
    constructor
    · intro h
      have h1 : q * z₁ * q⁻¹ = q' * z₁ * q'⁻¹ := mul_left_cancel h
      calc q'⁻¹ * q * z₁ = q'⁻¹ * (q * z₁ * q⁻¹) * q := by group
        _ = q'⁻¹ * (q' * z₁ * q'⁻¹) * q := by rw [h1]
        _ = z₁ * (q'⁻¹ * q) := by group
    · intro h
      have h1 : q * z₁ * q⁻¹ = q' * z₁ * q'⁻¹ := by
        calc q * z₁ * q⁻¹ = q' * (q'⁻¹ * q) * z₁ * (q'⁻¹ * q)⁻¹ * q'⁻¹ := by group
          _ = q' * ((q'⁻¹ * q) * z₁ * (q'⁻¹ * q)⁻¹) * q'⁻¹ := by group
          _ = q' * (z₁ * (q'⁻¹ * q) * (q'⁻¹ * q)⁻¹) * q'⁻¹ := by rw [h]
          _ = q' * z₁ * q'⁻¹ := by group
      rw [h1]
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact key.trans ⟨fun h => ⟨Subgroup.mul_mem _ (inv_mem hq') hq, h⟩, fun h => h.2⟩

theorem CaseB.sq_eq_of_not_mem (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {x : G}
    (hx : x ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z)
    (hxR : x ∉ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) : x ^ 2 = z := by
  have hZR : centerAt z ≤
      centralizer ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrQ : r ∈ coreAt z := (Subgroup.mem_inf.mp hr).1
    exact (Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hrQ) c hc).symm
  obtain ⟨r, hr, c, hc, rfl⟩ := mem_sup_decompose hx hZR
  have hrc : r * c = c * r := Subgroup.mem_centralizer_iff.mp (hZR hc) r hr
  have hr2 : r ^ 2 = 1 := (CaseB.isElemAbelian hC hH hK).2 r hr
  have hx2 : (r * c) ^ 2 = c ^ 2 := by
    rw [(show Commute r c from hrc).mul_pow, hr2, one_mul]
  rw [hx2]
  have hz₁ := conj_mul_self_eq_one hC g
  by_cases hc2 : c ^ 2 = 1
  · exfalso
    apply hxR
    have hconj := hC.inv_of_not_mem_centralizer hH hK hc
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hc2)
    have hz1inv : (g⁻¹ * z * g)⁻¹ = g⁻¹ * z * g := inv_eq_of_mul_eq_one_right hz₁
    rw [hcinv, hz1inv] at hconj
    have hcR : c ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) :=
      ⟨hC.center_le_core hc, Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_of_conj_eq hz₁ hconj)⟩
    exact Subgroup.mul_mem _ hr hcR
  · have hc4 : c ^ 4 = 1 := by
      have h : (⟨c, hc⟩ : centerAt z) ^ Nat.card (centerAt z) = 1 := pow_card_eq_one'
      rw [hC.card_center] at h
      simpa using congrArg Subtype.val h
    have hc2z : c ^ 2 ∈ centerAt z := Subgroup.pow_mem _ hc 2
    have hord : orderOf (c ^ 2) = 2 :=
      orderOf_eq_prime (by rw [← pow_mul]; exact hc4) hc2
    exact hC.eq_of_mem_center hc2z hord

end CFSG.GF2Type.CenterFour
