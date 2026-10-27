module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasicHW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma56HW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma57
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem conj_mem_P {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P := by
  refine mem_inf.mpr ⟨mul_mem (mul_mem hs (h.P_le_S hy)) (inv_mem hs), ?_⟩
  have := GSThmB.conj_mem_coreActionKernel (inv_mem (h.S_le_normalizer hs)) (mem_inf.mp hy).2
  rwa [inv_inv] at this

theorem D_inf_P_eq_bot (hZ : center (OddBar h.J) = ⊥) : h.D ⊓ h.P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨hyS, hyJ⟩, ⟨-, hyC⟩⟩ := mem_inf.mp hy |>.imp mem_inf.mp mem_inf.mp
  have h1 := inf_coreActionKernel_le_of_center_eq_bot hZ (mem_inf.mpr ⟨hyJ, hyC⟩)
  have := h.S_inf_oddCore_eq_bot ▸ mem_inf.mpr ⟨hyS, h1⟩
  exact this

theorem D_ne_bot : h.D ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJeven : Even (Nat.card h.J) := by
    have h1 := even_card_of_isQuasisimple' h.isQuasisimple_J
    obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥h.J)
    rw [hk]
    exact h1.mul_right k
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := h.J) 2 (even_iff_two_dvd.mp hJeven)
  have ht2 : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htN : (t : H) ∈ h.N0 := mem_inf.mpr ⟨h.J_le t.2, le_normalizer t.2⟩
  have h2t : IsPGroup 2 (zpowers (t : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨m, hm, hmS⟩ := exists_conjugate_le_of_sylow h.S_sylow (zpowers_le.mpr htN) h2t
  intro hD
  have hmJ : m⁻¹ * (t : H) * m ∈ h.J := by
    have := (mem_normalizer_iff.mp (inv_mem (mem_inf.mp hm).2) t).mp t.2
    rwa [inv_inv] at this
  have hmS' : m⁻¹ * (t : H) * m ∈ h.S := hmS (by
    rw [mem_conjugate_iff, show m * (m⁻¹ * (t : H) * m) * m⁻¹ = t by group]
    exact mem_zpowers _)
  have h1 : m⁻¹ * (t : H) * m = 1 := by
    have hmD : m⁻¹ * (t : H) * m ∈ h.D := mem_inf.mpr ⟨hmS', hmJ⟩
    rw [hD] at hmD
    exact mem_bot.mp hmD
  have : (t : H) = 1 := by
    calc (t : H) = m * (m⁻¹ * t * m) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [this, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

theorem exists_involution_D_center :
    ∃ z : H, z ∈ h.D ∧ (∀ s ∈ h.S, s * z = z * s) ∧ orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup h.S := h.D.subgroupOf h.S with hN
  have hNn : N.Normal := by
    constructor
    intro n hn s
    rw [hN, mem_subgroupOf] at hn ⊢
    have hsN := h.S_le_normalizer s.2
    have h1 : (s : H) * n * (s : H)⁻¹ ∈ h.S :=
      mul_mem (mul_mem s.2 (h.D_le_S hn)) (inv_mem s.2)
    have h2 : (s : H) * n * (s : H)⁻¹ ∈ h.J := (mem_normalizer_iff.mp hsN _).mp (h.D_le_J hn)
    simp only [coe_mul, coe_inv]
    exact mem_inf.mpr ⟨h1, h2⟩
  have hN1 : N ≠ ⊥ := by
    intro hb
    apply h.D_ne_bot
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, h.D_le_S hy⟩ : h.S) ∈ N := hy
    rw [hb] at this
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp this))
  have hnil : Group.IsNilpotent h.S := h.isPGroup_S.isNilpotent
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  have h2 : IsPGroup 2 ↥(N ⊓ center h.S) := h.isPGroup_S.to_subgroup _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ center h.S)) 2 (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rcases k with _ | k
    · exfalso
      apply hX
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _)
  obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
  refine ⟨((u : h.S) : H), huN, fun s hs => ?_, ?_⟩
  · exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp huZ ⟨s, hs⟩))
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]

theorem V_le_centralizer_B : h.V ≤ centralizer (h.B : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) h.B h.isPGroup_B
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  exact h1.trans (map_subtype_le _)

theorem K_le_layer_W : h.K ≤ h.V := by
  show h.K ≤ layerIn (normalizer (h.B : Set H))
  rw [← h.layer_eq_K]
  exact le_sup_left

theorem a_not_mem_B : h.a ∉ h.B := by
  intro haB
  have hax : h.a ∈ conjugate h.B h.x := by
    rw [mem_conjugate_iff, h.x_comm_a, mul_inv_cancel_right]
    exact haB
  have := h.inf_conjugate_x ▸ mem_inf.mpr ⟨haB, hax⟩
  have h1 : h.a = 1 := mem_bot.mp this
  have h2 := h.orderOf_a
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

end Hyp52W

namespace Hyp59W

variable {H : Type} [Group H] [Finite H] (h : Hyp59W H)

theorem x_mem_normalizer_T : h.x ∈ normalizer (h.T : Set H) := by
  rcases h.x_cond with hx | ⟨hPQ, -⟩
  · obtain ⟨-, hxQ⟩ := mem_inf.mp hx
    have key : ∀ c : H, c ∈ h.S → c ∈ normalizer (h.Q : Set H) →
        ∀ y ∈ h.T, c * y * c⁻¹ ∈ h.T := by
      intro c hcS hcQ y hy
      obtain ⟨hyQ, hyP⟩ := mem_inf.mp hy
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hcQ y).mp hyQ, h.toHyp52W.conj_mem_P hcS hyP⟩
    apply mem_normalizer_of_conj_mem (key _ h.x_mem hxQ)
    intro y hy
    have := key _ (inv_mem h.x_mem) (inv_mem hxQ) y hy
    rwa [inv_inv] at this
  · have hTP : h.T = h.P := le_antisymm inf_le_right (fun y hy => mem_inf.mpr ⟨hPQ hy, hy⟩)
    rw [hTP]
    apply mem_normalizer_of_conj_mem (fun y hy => h.toHyp52W.conj_mem_P h.x_mem hy)
    intro y hy
    have := h.toHyp52W.conj_mem_P (inv_mem h.x_mem) hy
    rwa [inv_inv] at this

end Hyp59W

end CFSG.ComponentClassification.GSThmB
