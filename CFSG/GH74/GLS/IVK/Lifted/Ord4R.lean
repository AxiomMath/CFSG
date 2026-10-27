module

public import CFSG.GH74.GLS.IVK.Lifted.Lem31c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

theorem cyclic_involution_eq {C : Type} [Group C] [Finite C] (hC : IsCyclic C) {x y : C}
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  let _ : Fintype C := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two]; exact hx
    · rw [pow_two]; exact hy
  have hcard : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hxy
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 h.symm, fun h => hy1 h.symm⟩
  have := Finset.card_le_card hsub
  omega

section Ord4R

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem ii4_ord4_R_of_II4 (hII : II4_4_4_center) (hlift : II4_ord4_lift) : II4_ord4_R := by
  intro G _ _ z S K F h hFc w hw w' hw' hww hw'w' hw1 hwz hw'1 hw'z
  classical
  have hRz := h.Rz_eq
  rw [hRz] at hw hw'
  have hQF : S ⊓ cSec K ≤ F := by
    rw [← h.Qz_eq, h.Q_eq]
    exact inf_le_left
  have hQc : IsCyclic ↥(S ⊓ cSec K) := Subgroup.isCyclic_of_le hQF
  have hz2 := h.z_sq
  have hzP := h.z_mem_P hII
  have hzQ := h.z_mem_Q hII
  have hzZ : z ∈ zStar K := ((h.S_inf_zStar hII).1 ▸ mem_zpowers z : z ∈ S ⊓ zStar K).2
  have hQinv : ∀ x ∈ S ⊓ cSec K, x * x = 1 → x = 1 ∨ x = z := by
    intro x hx hx2
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    exact congrArg Subtype.val (cyclic_involution_eq hQc (x := (⟨x, hx⟩ : ↥(S ⊓ cSec K)))
      (y := ⟨z, hzQ⟩) (Subtype.ext hx2) (Subtype.ext hz2) (fun h1 => hx1 (congrArg Subtype.val h1))
      (fun h1 => h.z_ne (congrArg Subtype.val h1)))
  have hdec : ∀ u ∈ (S ⊓ K) ⊔ (S ⊓ cSec K), u * u = 1 → u ≠ 1 → u ≠ z →
      ∃ p ∈ S ⊓ K, ∃ q ∈ S ⊓ cSec K, u = p * q ∧ p * p = z ∧ q * q = z := by
    intro u hu hu2 hu1 huz
    obtain ⟨p, hp, q, hq, rfl⟩ := M.mem_sup_of_commute (fun a ha b hb => h.comm_PQ ha hb) hu
    have hpq := h.comm_PQ hp hq
    have hsq : (p * p) * (q * q) = 1 := by
      calc (p * p) * (q * q) = (p * q) * (p * q) := by
            calc (p * p) * (q * q) = p * (p * q) * q := by group
              _ = p * (q * p) * q := by rw [hpq]
              _ = (p * q) * (p * q) := by group
        _ = 1 := hu2
    have hpp : p * p ∈ S ⊓ K := (S ⊓ K).mul_mem hp hp
    have hqq : (q * q)⁻¹ ∈ S ⊓ cSec K := (S ⊓ cSec K).inv_mem ((S ⊓ cSec K).mul_mem hq hq)
    have hpq2 : p * p = (q * q)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have hmem : p * p ∈ S ⊓ cSec K := hpq2 ▸ hqq
    rcases h.PQ_inf hII hpp hmem with h1 | h1
    · exfalso
      have hq2 : q * q = 1 := by
        have : (q * q)⁻¹ = 1 := by rw [← hpq2, h1]
        exact inv_eq_one.1 this
      have hp' := h.P_inv hII hp h1
      have hq' := hQinv q hq hq2
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact hu1 (by simp)
      · exact huz (by simp)
      · exact huz (by simp)
      · exact hu1 (by rw [hz2])
    · refine ⟨p, hp, q, hq, rfl, h1, ?_⟩
      have : (q * q)⁻¹ = z := by rw [← hpq2, h1]
      calc q * q = ((q * q)⁻¹)⁻¹ := (inv_inv _).symm
        _ = z⁻¹ := by rw [this]
        _ = z := by
          rw [inv_eq_of_mul_eq_one_right hz2]
  obtain ⟨p, hp, q, hq, rfl, hpz, hqz⟩ := hdec w hw hww hw1 hwz
  obtain ⟨p', hp', q', hq', rfl, hp'z, hq'z⟩ := hdec w' hw' hw'w' hw'1 hw'z
  have hQcomm : ∀ a ∈ S ⊓ cSec K, ∀ b ∈ S ⊓ cSec K, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup ↥(S ⊓ cSec K) := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(S ⊓ cSec K)) ⟨b, hb⟩)
  have hxQ : q' * q⁻¹ ∈ S ⊓ cSec K := (S ⊓ cSec K).mul_mem hq' ((S ⊓ cSec K).inv_mem hq)
  have hx2 : (q' * q⁻¹) * (q' * q⁻¹) = 1 := by
    have hc := hQcomm q' hq' q⁻¹ ((S ⊓ cSec K).inv_mem hq)
    have hqinv : q⁻¹ * q⁻¹ = z := by
      have : q⁻¹ * q⁻¹ = (q * q)⁻¹ := by group
      rw [this, hqz, inv_eq_of_mul_eq_one_right hz2]
    calc (q' * q⁻¹) * (q' * q⁻¹) = q' * (q⁻¹ * q') * q⁻¹ := by group
      _ = q' * (q' * q⁻¹) * q⁻¹ := by rw [← hc]
      _ = (q' * q') * (q⁻¹ * q⁻¹) := by group
      _ = 1 := by rw [hq'z, hqinv, hz2]
  have hxcases := hQinv _ hxQ hx2
  have hxP : q' * q⁻¹ ∈ S ⊓ K := by
    rcases hxcases with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hzP
  have hpzc : p' * z = z * p' := M.centralizer_comm (h.K_le_C hp'.2)
  set p'' : G := p' * (q' * q⁻¹) with hp''
  have hp''P : p'' ∈ S ⊓ K := (S ⊓ K).mul_mem hp' hxP
  have hp''z : p'' * p'' = z := by
    rcases hxcases with h1 | h1
    · rw [hp'', h1, mul_one]
      exact hp'z
    · rw [hp'', h1]
      calc p' * z * (p' * z) = p' * (z * p') * z := by group
        _ = p' * (p' * z) * z := by rw [← hpzc]
        _ = (p' * p') * (z * z) := by group
        _ = z := by rw [hp'z, hz2, mul_one]
  have hw'eq : p' * q' = p'' * q := by
    rw [hp'']
    group
  obtain ⟨k, hkK, hk⟩ := hlift G h.simple z h.orderOf_z K h.comp_isPCompIn h.comp_pRank hzZ p hp.2 p''
    hp''P.2 hpz hp''z
  have hkq : k * q * k⁻¹ = ⁅k, q⁆ * q := by
    simp only [commutatorElement_def]
    group
  have hoO : ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2 k hkK
  have hw₁ : k * (p * q) * k⁻¹ = p'' * (⁅k, q⁆ * q) := by
    rw [← hk, ← hkq]
    group
  have hw₁2 : (k * (p * q) * k⁻¹) * (k * (p * q) * k⁻¹) = 1 := by
    have : (k * (p * q) * k⁻¹) * (k * (p * q) * k⁻¹) = k * ((p * q) * (p * q)) * k⁻¹ := by group
    rw [this, hww]
    group
  have hw₁1 : k * (p * q) * k⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have : p * q = k⁻¹ * (k * (p * q) * k⁻¹) * k := by group
    rw [this, h1]
    group
  have hw'2 : (p' * q') * (p' * q') = 1 := hw'w'
  have hnormO : ∀ n ∈ pPrimeCoreOf 2 K, (p' * q') * n * (p' * q')⁻¹ ∈ pPrimeCoreOf 2 K := by
    intro n hn
    rw [hw'eq]
    have h1 : q * n * q⁻¹ ∈ pPrimeCoreOf 2 K := (Subgroup.mem_normalizer_iff.1 hq.2.2.1 n).1 hn
    have h2 := h.O_odd_core.normal p'' hp''P.2 _ h1
    have e : p'' * q * n * (p'' * q)⁻¹ = p'' * (q * n * q⁻¹) * p''⁻¹ := by group
    rw [e]
    exact h2
  have hxO : (k * (p * q) * k⁻¹) * (p' * q')⁻¹ ∈ pPrimeCoreOf 2 K := by
    rw [hw₁, hw'eq]
    have h2 := h.O_odd_core.normal p'' hp''P.2 _ hoO
    have e : p'' * (⁅k, q⁆ * q) * (p'' * q)⁻¹ = p'' * ⁅k, q⁆ * p''⁻¹ := by group
    rw [e]
    exact h2
  obtain ⟨g, -, hg⟩ := exists_conj_of_mul_mem_odd (O := pPrimeCoreOf 2 K)
    (TwoThin.card_pPrimeCoreOf_odd K) hw₁2 hw'2 hw₁1 hw'1 hnormO hxO
  refine isConj_iff.2 ⟨g * k, ?_⟩
  calc g * k * (p * q) * (g * k)⁻¹ = g * (k * (p * q) * k⁻¹) * g⁻¹ := by group
    _ = p' * q' := hg

end Ord4R

end CFSG.GH74.GLS.IVK.Lifted
