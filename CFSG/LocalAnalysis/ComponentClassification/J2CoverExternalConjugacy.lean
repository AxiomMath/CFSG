module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel

public section

universe u

namespace CFSG.ComponentClassification.J2Cover.External

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def J2LiftOrders : Prop :=
  ∀ {L : Type u} [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L → ∀ {t : L}, orderOf t = 2 →
    Subgroup.center L = Subgroup.zpowers t → ∀ (π : L →* P), Function.Surjective π →
    π.ker = Subgroup.zpowers t →
    (∀ q : P, orderOf q = 2 → Models.fixCount (q : Equiv.Perm (Fin 315)) = 11 ∨
        Models.fixCount (q : Equiv.Perm (Fin 315)) = 15) ∧
    (∀ v : L, orderOf (π v) = 2 → Models.fixCount ((π v : P) : Equiv.Perm (Fin 315)) = 11 →
      orderOf v = 2) ∧
    (∀ v : L, orderOf (π v) = 2 → Models.fixCount ((π v : P) : Equiv.Perm (Fin 315)) = 15 →
      v ^ 2 = t ∧ orderOf v = 4)

theorem eq_one_or_eq_of_mem_zpowers_two {G : Type*} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one]

theorem mul_self_central_mul {G : Type*} [Group G] {c x : G} (hc : c ∈ center G)
    (hc2 : c * c = 1) (hx2 : x * x = 1) : c * x * (c * x) = 1 := by
  calc c * x * (c * x) = c * (x * c) * x := by group
    _ = c * (c * x) * x := by rw [mem_center_iff.mp hc x]
    _ = (c * c) * (x * x) := by group
    _ = 1 := by rw [hc2, hx2, one_mul]

theorem conj_apply_eq (γ : MulAut P) (g : P) :
    MulAut.conj (γ g) = γ * MulAut.conj g * γ⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, MulAut.apply_inv_self, map_inv]

section Action

variable {H : Type*} [Group H] {L : Subgroup H} [L.Normal] {t : L}
  (π : L →* P) (hπ : Function.Surjective π) (hkerZ : π.ker = center L)

theorem eq_or_eq_mul_of_fullAction_eq [Group.IsPerfect L] (ht : orderOf t = 2)
    (hCL : centralizer (L : Set H) = zpowers (t : H)) {a b : H}
    (hab : CentralCover.fullAction π hπ hkerZ a = CentralCover.fullAction π hπ hkerZ b) :
    a = b ∨ a = t * b := by
  have hmem : a * b⁻¹ ∈ (CentralCover.fullAction π hπ hkerZ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [CentralCover.ker_fullAction, hCL] at hmem
  have ht' : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe, ht]
  rcases eq_one_or_eq_of_mem_zpowers_two ht' hmem with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · right
    rw [← h]
    group

theorem fullAction_outer_involution [Group.IsPerfect L] (hCL' : centralizer (L : Set H) ≤ L)
    {p : H} (hpL : p ∉ L) (hp : orderOf p = 2) :
    orderOf (CentralCover.fullAction π hπ hkerZ p) = 2 ∧
      CentralCover.fullAction π hπ hkerZ p ∉ inner P :=
  ⟨CentralCover.orderOf_fullAction π hπ hkerZ hCL' hpL hp,
    CentralCover.fullAction_notMem_inner π hπ hkerZ hCL' hpL⟩

theorem exists_fullAction_eq_conj {p q : H}
    (hp2 : orderOf (CentralCover.fullAction π hπ hkerZ p) = 2)
    (hpo : CentralCover.fullAction π hπ hkerZ p ∉ inner P)
    (hq2 : orderOf (CentralCover.fullAction π hπ hkerZ q) = 2)
    (hqo : CentralCover.fullAction π hπ hkerZ q ∉ inner P) :
    ∃ k : L, CentralCover.fullAction π hπ hkerZ q =
      CentralCover.fullAction π hπ hkerZ ((k : H) * p * (k : H)⁻¹) := by
  obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hp2 hpo
  obtain ⟨m, hm⟩ := exists_conj_beta_of_outer hq2 hqo
  obtain ⟨k, hk⟩ := hπ (m * g⁻¹)
  refine ⟨k, ?_⟩
  rw [map_mul, map_mul, map_inv, CentralCover.fullAction_coe, hk, hm, hg]
  simp only [map_mul, map_inv]
  group

end Action

theorem lift_conj_elemC (hlift : J2LiftOrders.{u}) {H : Type u} [Group H] [Finite H]
    {L : Subgroup H} [L.Normal] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : center L = zpowers t) (π : L →* P) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers t) (hCL : centralizer (L : Set H) = zpowers (t : H)) {p : H}
    (hpL : p ∉ L) (hp : orderOf p = 2) (g : P)
    (hα : ∀ l : L, (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) (π l) =
      π (MulAut.conjNormal p l)) {v : L} (hv : π v = g * elemC * g⁻¹) :
    v ^ 2 = t ∧ (v : H) * p * (v : H)⁻¹ = t * p ∧ orderOf v = 4 := by
  have hkerZ : π.ker = center L := hker.trans hZ.symm
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have htt : (t : H) * t = 1 := by rw [← Subgroup.coe_mul, ← sq, ht2, OneMemClass.coe_one]
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL, zpowers_le]
    exact t.2
  have hg : CentralCover.fullAction π hπ hkerZ p = MulAut.conj g * betaAut * (MulAut.conj g)⁻¹ := by
    ext q
    obtain ⟨l, rfl⟩ := hπ q
    rw [CentralCover.fullAction_apply, hα]
  have hp2 : p * p = 1 := by rw [← sq, ← hp, pow_orderOf_eq_one]
  obtain ⟨hα2, hαo⟩ := fullAction_outer_involution π hπ hkerZ hCL' hpL hp
  obtain ⟨-, hc2, hc15⟩ := (conj_elemC g).2
  have hv2 : orderOf (π v) = 2 := by rw [hv, hc2]
  have hv15 : Models.fixCount ((π v : P) : Equiv.Perm (Fin 315)) = 15 := by rw [hv, hc15]
  obtain ⟨hvt, hv4⟩ := (hlift hLq ht hZ π hπ hker).2.2 v hv2 hv15
  have hαz : CentralCover.fullAction π hπ hkerZ p (g * elemC * g⁻¹) = g * elemC * g⁻¹ := by
    rw [hg]
    exact conj_beta_apply_conj g elemC elemC_mem
  have hcomm : CentralCover.fullAction π hπ hkerZ p * MulAut.conj (g * elemC * g⁻¹) =
      MulAut.conj (g * elemC * g⁻¹) * CentralCover.fullAction π hπ hkerZ p := by
    have h := conj_apply_eq (CentralCover.fullAction π hπ hkerZ p) (g * elemC * g⁻¹)
    rw [hαz] at h
    calc CentralCover.fullAction π hπ hkerZ p * MulAut.conj (g * elemC * g⁻¹)
        = CentralCover.fullAction π hπ hkerZ p * MulAut.conj (g * elemC * g⁻¹) *
            (CentralCover.fullAction π hπ hkerZ p)⁻¹ * CentralCover.fullAction π hπ hkerZ p := by
          group
      _ = MulAut.conj (g * elemC * g⁻¹) * CentralCover.fullAction π hπ hkerZ p := by rw [← h]
  have hz2 : g * elemC * g⁻¹ * (g * elemC * g⁻¹) = 1 := by
    rw [← sq, ← hc2, pow_orderOf_eq_one]
  have hθp2 :
      CentralCover.fullAction π hπ hkerZ p * CentralCover.fullAction π hπ hkerZ p = 1 := by
    rw [← map_mul, hp2, map_one]
  have hθvp : CentralCover.fullAction π hπ hkerZ ((v : H) * p) =
      MulAut.conj (g * elemC * g⁻¹) * CentralCover.fullAction π hπ hkerZ p := by
    rw [map_mul, CentralCover.fullAction_coe, hv]
  have hvpL : (v : H) * p ∉ L := fun h => hpL ((L.mul_mem_cancel_left v.2).1 h)
  have hvpo := CentralCover.fullAction_notMem_inner π hπ hkerZ hCL' hvpL
  have hvp2 : orderOf (CentralCover.fullAction π hπ hkerZ ((v : H) * p)) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hvpo (h1 ▸ one_mem _)
    rw [sq, hθvp]
    calc MulAut.conj (g * elemC * g⁻¹) * CentralCover.fullAction π hπ hkerZ p *
          (MulAut.conj (g * elemC * g⁻¹) * CentralCover.fullAction π hπ hkerZ p)
        = MulAut.conj (g * elemC * g⁻¹) * (CentralCover.fullAction π hπ hkerZ p *
            MulAut.conj (g * elemC * g⁻¹)) * CentralCover.fullAction π hπ hkerZ p := by group
      _ = MulAut.conj (g * elemC * g⁻¹ * (g * elemC * g⁻¹)) *
            (CentralCover.fullAction π hπ hkerZ p * CentralCover.fullAction π hπ hkerZ p) := by
          rw [hcomm, map_mul MulAut.conj (g * elemC * g⁻¹) (g * elemC * g⁻¹)]
          simp only [mul_assoc]
      _ = 1 := by rw [hz2, hθp2, map_one, one_mul]
  obtain ⟨k, hk⟩ := exists_fullAction_eq_conj π hπ hkerZ hα2 hαo hvp2 hvpo
  have hkp : (k : H) * p * (k : H)⁻¹ * ((k : H) * p * (k : H)⁻¹) = 1 := by
    calc (k : H) * p * (k : H)⁻¹ * ((k : H) * p * (k : H)⁻¹) = (k : H) * (p * p) * (k : H)⁻¹ := by
          group
      _ = 1 := by rw [hp2, mul_one, mul_inv_cancel]
  have hvpvp : (v : H) * p * ((v : H) * p) = 1 := by
    rcases eq_or_eq_mul_of_fullAction_eq π hπ hkerZ ht hCL hk with h | h
    · rw [h, hkp]
    · rw [h]
      exact mul_self_central_mul htH htt hkp
  refine ⟨hvt, ?_, hv4⟩
  have hvv : (v : H) * v = t := by rw [← Subgroup.coe_mul, ← sq, hvt]
  calc (v : H) * p * (v : H)⁻¹ = (v : H) * p * ((v : H) * p) * p⁻¹ * ((v : H) * v)⁻¹ := by group
    _ = p * t := by
        rw [hvpvp, hvv, one_mul, inv_eq_of_mul_eq_one_right hp2, inv_eq_of_mul_eq_one_right htt]
    _ = t * p := mem_center_iff.mp htH p

theorem external_involution_conjugacy (hlift : J2LiftOrders.{u}) {H : Type u} [Group H]
    [Finite H]
    {L : Subgroup H} [L.Normal] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* P) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers t) (hCL : centralizer (L : Set H) = zpowers (t : H)) :
    (∀ p : H, p ∉ L → orderOf p = 2 →
      ∃ v : L, v ^ 2 = t ∧ (v : H) * p * (v : H)⁻¹ = t * p ∧ orderOf v = 4) ∧
    ∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 →
      ∃ l : L, (l : H) * x * (l : H)⁻¹ = y := by
  have hkerZ : π.ker = center L := hker.trans hZ.symm
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL, zpowers_le]
    exact t.2
  have key : ∀ p : H, p ∉ L → orderOf p = 2 →
      ∃ v : L, v ^ 2 = t ∧ (v : H) * p * (v : H)⁻¹ = t * p ∧ orderOf v = 4 := by
    intro p hpL hp
    obtain ⟨hα2, hαo⟩ := fullAction_outer_involution π hπ hkerZ hCL' hpL hp
    obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα2 hαo
    obtain ⟨v, hv⟩ := hπ (g * elemC * g⁻¹)
    refine ⟨v, lift_conj_elemC hlift hLq ht hZ π hπ hker hCL hpL hp g (fun l => ?_) hv⟩
    rw [← hg, CentralCover.fullAction_apply]
  refine ⟨key, fun x y hxL hx hyL hy => ?_⟩
  obtain ⟨v, -, hvx, -⟩ := key x hxL hx
  obtain ⟨hx2, hxo⟩ := fullAction_outer_involution π hπ hkerZ hCL' hxL hx
  obtain ⟨hy2, hyo⟩ := fullAction_outer_involution π hπ hkerZ hCL' hyL hy
  obtain ⟨k, hk⟩ := exists_fullAction_eq_conj π hπ hkerZ hx2 hxo hy2 hyo
  rcases eq_or_eq_mul_of_fullAction_eq π hπ hkerZ ht hCL hk with h | h
  · exact ⟨k, h.symm⟩
  · refine ⟨k * v, ?_⟩
    rw [h, Subgroup.coe_mul]
    calc (k : H) * v * x * ((k : H) * v)⁻¹ = (k : H) * ((v : H) * x * (v : H)⁻¹) * (k : H)⁻¹ := by
          group
      _ = (k : H) * t * x * (k : H)⁻¹ := by rw [hvx]; group
      _ = t * ((k : H) * x * (k : H)⁻¹) := by rw [mem_center_iff.mp htH k]; group

end CFSG.ComponentClassification.J2Cover.External
