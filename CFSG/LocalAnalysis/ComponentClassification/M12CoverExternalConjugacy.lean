module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel

public section

namespace CFSG.ComponentClassification.M12Cover

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

private theorem eq_one_or_eq_of_mem_zpowers_two {G : Type*} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one]

private theorem mul_self_central_mul {G : Type*} [Group G] {c x : G} (hc : c ∈ center G)
    (hc2 : c * c = 1) (hx2 : x * x = 1) : c * x * (c * x) = 1 := by
  calc c * x * (c * x) = c * (x * c) * x := by group
    _ = c * (c * x) * x := by rw [mem_center_iff.mp hc x]
    _ = (c * c) * (x * x) := by group
    _ = 1 := by rw [hc2, hx2, one_mul]

section Action

variable {H : Type*} [Group H] {L : Subgroup H} [L.Normal] {t : L}
  (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π) (hkerZ : π.ker = center L)

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
      CentralCover.fullAction π hπ hkerZ p ∉ inner NativeSporadic.M12 :=
  ⟨CentralCover.orderOf_fullAction π hπ hkerZ hCL' hpL hp,
    CentralCover.fullAction_notMem_inner π hπ hkerZ hCL' hpL⟩

theorem exists_fullAction_eq_conj {p q : H}
    (hp2 : orderOf (CentralCover.fullAction π hπ hkerZ p) = 2)
    (hpo : CentralCover.fullAction π hπ hkerZ p ∉ inner NativeSporadic.M12)
    (hq2 : orderOf (CentralCover.fullAction π hπ hkerZ q) = 2)
    (hqo : CentralCover.fullAction π hπ hkerZ q ∉ inner NativeSporadic.M12) :
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

theorem ctss_m12_central_double_cover_external_involution_conjugacy_frontier
    {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : center L = zpowers t) (hQ : Nonempty (L ⧸ center L ≃* NativeSporadic.M12))
    (hCL : centralizer (L : Set H) = zpowers (t : H)) :
    (∀ p : H, p ∉ L → orderOf p = 2 →
      ∃ v : L, v ^ 2 = t ∧ (v : H) * p * (v : H)⁻¹ = t * p ∧ orderOf v = 4) ∧
    (∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 →
      ∃ l : L, (l : H) * x * (l : H)⁻¹ = y) ∧
    ∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 → ∃ h : H, h * x * h⁻¹ = y := by
  obtain ⟨e⟩ := hQ
  let π : L →* NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = zpowers t := hkerZ.trans hZ
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htH : (t : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ ht2
  have htt : (t : H) * t = 1 := by rw [← Subgroup.coe_mul, ← sq, ht2, OneMemClass.coe_one]
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL, zpowers_le]
    exact t.2
  obtain ⟨-, -, hlift⟩ := m12_double_cover_involution_lift_orders hLq ht hZ π hπ hker
  have key : ∀ p : H, p ∉ L → orderOf p = 2 →
      ∃ v : L, v ^ 2 = t ∧ (v : H) * p * (v : H)⁻¹ = t * p ∧ orderOf v = 4 := by
    intro p hpL hp
    have hp2 : p * p = 1 := by rw [← sq, ← hp, pow_orderOf_eq_one]
    obtain ⟨hα2, hαo⟩ := fullAction_outer_involution π hπ hkerZ hCL' hpL hp
    obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα2 hαo
    obtain ⟨v, hv⟩ := hπ (g * elemZ * g⁻¹)
    have hv2 : orderOf (π v) = 2 := by
      rw [hv, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_elemZ]
    have hv0 : fixedCount (π v) = 0 := by rw [hv, fixedCount_conj, fixedCount_elemZ]
    obtain ⟨hvt, hv4⟩ := hlift v hv2 hv0
    have hαz : CentralCover.fullAction π hπ hkerZ p (g * elemZ * g⁻¹) = g * elemZ * g⁻¹ := by
      rw [hg]
      exact conj_beta_apply_conj g elemZ elemZ_mem_fixSub
    have hcomm : CentralCover.fullAction π hπ hkerZ p * MulAut.conj (g * elemZ * g⁻¹) =
        MulAut.conj (g * elemZ * g⁻¹) * CentralCover.fullAction π hπ hkerZ p := by
      have h := conj_apply_eq (CentralCover.fullAction π hπ hkerZ p) (g * elemZ * g⁻¹)
      rw [hαz] at h
      calc CentralCover.fullAction π hπ hkerZ p * MulAut.conj (g * elemZ * g⁻¹)
          = CentralCover.fullAction π hπ hkerZ p * MulAut.conj (g * elemZ * g⁻¹) *
              (CentralCover.fullAction π hπ hkerZ p)⁻¹ * CentralCover.fullAction π hπ hkerZ p := by
            group
        _ = MulAut.conj (g * elemZ * g⁻¹) * CentralCover.fullAction π hπ hkerZ p := by rw [← h]
    have hz2 : g * elemZ * g⁻¹ * (g * elemZ * g⁻¹) = 1 := by
      have : elemZ * elemZ = 1 := by rw [← sq, ← orderOf_elemZ, pow_orderOf_eq_one]
      calc g * elemZ * g⁻¹ * (g * elemZ * g⁻¹) = g * (elemZ * elemZ) * g⁻¹ := by group
        _ = 1 := by rw [this, mul_one, mul_inv_cancel]
    have hθp2 :
        CentralCover.fullAction π hπ hkerZ p * CentralCover.fullAction π hπ hkerZ p = 1 := by
      rw [← map_mul, hp2, map_one]
    have hθvp : CentralCover.fullAction π hπ hkerZ ((v : H) * p) =
        MulAut.conj (g * elemZ * g⁻¹) * CentralCover.fullAction π hπ hkerZ p := by
      rw [map_mul, CentralCover.fullAction_coe, hv]
    have hvpL : (v : H) * p ∉ L := fun h => hpL ((L.mul_mem_cancel_left v.2).1 h)
    have hvpo := CentralCover.fullAction_notMem_inner π hπ hkerZ hCL' hvpL
    have hvp2 : orderOf (CentralCover.fullAction π hπ hkerZ ((v : H) * p)) = 2 := by
      refine orderOf_eq_prime ?_ fun h1 => hvpo (h1 ▸ one_mem _)
      rw [sq, hθvp]
      calc MulAut.conj (g * elemZ * g⁻¹) * CentralCover.fullAction π hπ hkerZ p *
            (MulAut.conj (g * elemZ * g⁻¹) * CentralCover.fullAction π hπ hkerZ p)
          = MulAut.conj (g * elemZ * g⁻¹) * (CentralCover.fullAction π hπ hkerZ p *
              MulAut.conj (g * elemZ * g⁻¹)) * CentralCover.fullAction π hπ hkerZ p := by group
        _ = MulAut.conj (g * elemZ * g⁻¹ * (g * elemZ * g⁻¹)) *
              (CentralCover.fullAction π hπ hkerZ p * CentralCover.fullAction π hπ hkerZ p) := by
            rw [hcomm, map_mul MulAut.conj (g * elemZ * g⁻¹) (g * elemZ * g⁻¹)]
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
    refine ⟨v, hvt, ?_, hv4⟩
    have hvv : (v : H) * v = t := by rw [← Subgroup.coe_mul, ← sq, hvt]
    calc (v : H) * p * (v : H)⁻¹ = (v : H) * p * ((v : H) * p) * p⁻¹ * ((v : H) * v)⁻¹ := by group
      _ = p * t := by
          rw [hvpvp, hvv, one_mul, inv_eq_of_mul_eq_one_right hp2, inv_eq_of_mul_eq_one_right htt]
      _ = t * p := mem_center_iff.mp htH p
  have hconj : ∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 →
      ∃ l : L, (l : H) * x * (l : H)⁻¹ = y := by
    intro x y hxL hx hyL hy
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
  refine ⟨key, hconj, fun x y hxL hx hyL hy => ?_⟩
  obtain ⟨l, hl⟩ := hconj x y hxL hx hyL hy
  exact ⟨l, hl⟩

end CFSG.ComponentClassification.M12Cover
