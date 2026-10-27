module

public import CFSG.GF2Type.CenterFour.CaseBPsiBasic

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private lemma cfg_mul_self (hC : Config z n) : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rw [hC.orderOf_eq, sq] at h
  exact h

private lemma cfg_conj_mul_self (hC : Config z n) (g : G) :
    g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
  calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [cfg_mul_self hC]; group

private lemma cfg_core_comm_center (hC : Config z n) {x y : G} (hx : x ∈ coreAt z)
    (hy : y ∈ centerAt z) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hx) y hy).symm

private lemma cfg_commute_sup_of_comm {H : Type*} [Group H] (R Z : Subgroup H)
    (hR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hZR : ∀ x ∈ R, ∀ y ∈ Z, x * y = y * x)
    (hZZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) {a b : H}
    (ha : a ∈ R ⊔ Z) (hb : b ∈ R ⊔ Z) : a * b = b * a := by
  have hRC : R ≤ centralizer ((R : Set H) ∪ (Z : Set H)) := by
    intro r hr
    rw [mem_centralizer_iff]
    rintro h (hh | hh)
    · exact hR h hh r hr
    · exact (hZR r hr h hh).symm
  have hZC : Z ≤ centralizer ((R : Set H) ∪ (Z : Set H)) := by
    intro y hy
    rw [mem_centralizer_iff]
    rintro h (hh | hh)
    · exact hZR h hh y hy
    · exact hZZ h hh y hy
  have hSa := mem_centralizer_iff.mp (sup_le hRC hZC ha)
  have hA : R ⊔ Z ≤ centralizer ({a} : Set H) := by
    refine sup_le (fun r hr => ?_) (fun y hy => ?_)
    · exact mem_centralizer_singleton_iff.mpr (hSa r (Set.mem_union_left _ hr))
    · exact mem_centralizer_singleton_iff.mpr (hSa y (Set.mem_union_right _ hy))
  exact (mem_centralizer_singleton_iff.mp (hA hb)).symm

theorem CaseB.psi_mul {z₁ : G} (hz₁ : z₁ * z₁ = 1) (q q' : G) :
    psi z₁ (q * q') = psi z₁ q * (q * psi z₁ q' * q⁻¹) := by
  have h1 : psi z₁ q * (q * psi z₁ q' * q⁻¹) = z₁ * q * (z₁ * z₁) * q' * z₁ * q'⁻¹ * q⁻¹ := by
    unfold psi
    group
  rw [h1, hz₁]
  unfold psi
  group

theorem CaseB.conj_psi (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) {q q' : G}
    (hq : q ∈ coreAt z) (hq' : q' ∈ coreAt z) :
    q * psi (g⁻¹ * z * g) q' * q⁻¹ = psi (g⁻¹ * z * g) q' ∨
      q * psi (g⁻¹ * z * g) q' * q⁻¹ = psi (g⁻¹ * z * g) q' * z := by
  have hx : psi (g⁻¹ * z * g) q' ∈ coreAt z :=
    psi_mem_core hC (cfg_conj_mul_self hC g) hH hq'
  rcases hC.comm_eq q hq _ hx with h | h
  · left
    rw [commutatorElement_def] at h
    exact mul_inv_eq_one.mp h
  · right
    rw [commutatorElement_def] at h
    rw [mul_inv_eq_iff_eq_mul.mp h]
    exact (mem_centralizer_singleton_iff.mp (hC.core_le_centralizer hx)).symm

private lemma cfg_commute_R1Z (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {a b : G}
    (ha : a ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z)
    (hb : b ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z) :
    Commute a b := by
  obtain ⟨hcomm, -⟩ := CaseB.isElemAbelian hC hH hK
  exact cfg_commute_sup_of_comm (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) (centerAt z)
    (fun x hx y hy => congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx y hy => cfg_core_comm_center hC (Subgroup.mem_inf.mp hx).1 hy)
    (fun x hx y hy => cfg_core_comm_center hC (hC.center_le_core hx) hy) ha hb

theorem CaseB.psi_sq_mul (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {q q' : G}
    (hq : q ∈ coreAt z) (hq' : q' ∈ coreAt z) :
    psi (g⁻¹ * z * g) (q * q') ^ 2 = psi (g⁻¹ * z * g) q ^ 2 * psi (g⁻¹ * z * g) q' ^ 2 := by
  have hz₁ := cfg_conj_mul_self hC g
  have hab : Commute (psi (g⁻¹ * z * g) q) (psi (g⁻¹ * z * g) q') :=
    cfg_commute_R1Z hC hH hK (CaseB.psi_mem hC hH hK hq) (CaseB.psi_mem hC hH hK hq')
  have haz : Commute (psi (g⁻¹ * z * g) q) z :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hC.core_le_centralizer (psi_mem_core hC hz₁ hH hq))
  have hbz : Commute (psi (g⁻¹ * z * g) q') z :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hC.core_le_centralizer (psi_mem_core hC hz₁ hH hq'))
  have hz2 : z ^ 2 = 1 := by
    rw [sq]
    exact cfg_mul_self hC
  rw [CaseB.psi_mul hz₁ q q']
  rcases CaseB.conj_psi hC hH hq hq' with h | h
  · rw [h, hab.mul_pow 2]
  · rw [h, (hab.mul_right haz).mul_pow 2, hbz.mul_pow 2, hz2, mul_one]

theorem CaseB.psi_mul_generator (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {k : G}
    (hk : centerAt z = zpowers k) (hk4 : orderOf k = 4) (hkz : k ^ 2 = z) {q : G}
    (hq : q ∈ coreAt z) : psi (g⁻¹ * z * g) (q * k) = psi (g⁻¹ * z * g) q * z := by
  have hz₁ := cfg_conj_mul_self hC g
  have hkZ : k ∈ centerAt z := by
    rw [hk]
    exact Subgroup.mem_zpowers k
  have hinv := hC.inv_of_not_mem_centralizer hH hK hkZ
  have hz1inv : (g⁻¹ * z * g)⁻¹ = g⁻¹ * z * g := inv_eq_of_mul_eq_one_right hz₁
  have hkk : k⁻¹ * k⁻¹ = z := by
    rw [← mul_inv_rev, ← sq, hkz]
    exact inv_eq_of_mul_eq_one_right (cfg_mul_self hC)
  have hpk : psi (g⁻¹ * z * g) k = z := by
    have key : g⁻¹ * z * g * (k * (g⁻¹ * z * g) * k⁻¹)
        = g⁻¹ * z * g * k * (g⁻¹ * z * g)⁻¹ * k⁻¹ := by
      rw [hz1inv]
      group
    unfold psi
    rw [key, hinv, hkk]
  have hqz : q * z * q⁻¹ = z := by
    have hc : q * z = z * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (hC.core_le_centralizer hq)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [CaseB.psi_mul hz₁ q k, hpk, hqz]

end CFSG.GF2Type.CenterFour
