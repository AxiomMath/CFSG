module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenPartner

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem permOf_mul_self (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    {y : G} (hy : y ∈ centralizer ({z} : Set G)) (hy2 : y * y = 1) :
    permOf h d e hy * permOf h d e hy = 1 := by
  rw [← permOf_mul h d e hy hy (mul_mem hy hy)]
  rw [permOf_congr' hy2 (mul_mem hy hy) (one_mem _) h d e]
  unfold permOf
  exact map_one _

theorem partner_type_five (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) {g : G}
    (haC : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hk2 : 2 ≤ Multiset.card (permOf h d e haC).cycleType)
    {τ : Perm (Fin 10)} (hτ : τ ∈ (permOf h d e haC).cycleFactorsFinset)
    {y : G} (hy : y ∈ centralizer ({z} : Set G)) (hyπ : permOf h d e hy = τ)
    (hya : y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y) (hy2 : y * y = 1)
    (hle : centralizer ({y} : Set G) ≤ centralizer ({z} : Set G)) :
    Multiset.card (permOf h d e haC).cycleType = 5 := by
  classical
  have hz2 : z * z = 1 := d.mul_self
  set a : G := g⁻¹ * z * g with ha
  have hga : g * a * g⁻¹ = z := by rw [ha]; group
  have ha2 : a * a = 1 := by
    calc a * a = g⁻¹ * (z * z) * g := by rw [ha]; group
      _ = 1 := by rw [hz2]; group
  set σ := permOf h d e haC with hσ
  have hσ2 : σ * σ = 1 := permOf_mul_self h d e haC ha2
  have hk5 : Multiset.card σ.cycleType ≤ 5 := card_cycleType_le_five hσ2
  have hy' : g * y * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * z = g * (y * a) * g⁻¹ := by rw [← hga]; group
      _ = g * (a * y) * g⁻¹ := by rw [hya]
      _ = z * (g * y * g⁻¹) := by rw [← hga]; group
  have hy'2 : g * y * g⁻¹ * (g * y * g⁻¹) = 1 := by
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  set ξ := permOf h d e hy' with hξ
  have hξ2 : ξ * ξ = 1 := permOf_mul_self h d e hy' hy'2
  have hN₂ := card_inf_inf_centralizer h d T e hy haC
  rw [hyπ] at hN₂
  have heq : centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ⊓ centralizer ({a} : Set G) =
      centralizer ({y} : Set G) ⊓ centralizer ({a} : Set G) := by
    rw [inf_comm (centralizer ({z} : Set G)), inf_assoc, inf_comm (centralizer ({z} : Set G)),
      ← inf_assoc, inf_eq_left.2 (le_trans inf_le_left hle)]
  have hconj := card_inf_centralizer_conj g a y
  rw [hga, inf_comm (centralizer ({a} : Set G))] at hconj
  have hN₃ := card_inf_centralizer h d T e hy'
  have hmain := card_centralizer_inf_mul_card_cycleType hσ2 hτ
  have h1 : Nat.card (centralizer ({σ} : Set (Perm (Fin 10))) ⊓
      centralizer ({τ} : Set (Perm (Fin 10))) : Subgroup (Perm (Fin 10))) =
      Nat.card (centralizer ({ξ} : Set (Perm (Fin 10)))) := by
    have h2 : 2 * Nat.card (centralizer ({τ} : Set (Perm (Fin 10))) ⊓
        centralizer ({σ} : Set (Perm (Fin 10))) : Subgroup (Perm (Fin 10))) =
        2 * Nat.card (centralizer ({ξ} : Set (Perm (Fin 10)))) := by
      rw [← hN₂, heq, ← hconj, hN₃]
    rw [inf_comm]
    omega
  rw [h1, card_centralizer_ten hσ2, card_centralizer_ten hξ2, mul_comm] at hmain
  exact (eq_five_four_of_card_ten hk2 hk5 (card_cycleType_le_five hξ2) hmain.symm).1

theorem centralizer_le_untwisted (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {τ₀ : Perm (Fin n)} (hτ₀ : τ₀.IsSwap)
    (hle : centralizer ({(swapIota h d T e τ₀ : G)} : Set G) ≤ centralizer ({z} : Set G))
    {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    centralizer ({(swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨p, q, hpq, hτ₀e⟩ := hτ₀
  obtain ⟨r, t, hrt, hτe⟩ := hτ
  obtain ⟨π, hπ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq hrt)
  set c : G := (swapIota h d T e π : G) with hc
  have hcz : c ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e π
  have hιτ : (swapIota h d T e τ : G) = c * (swapIota h d T e τ₀ : G) * c⁻¹ := by
    rw [hτe, ← hπ, ← hτ₀e, map_mul, map_mul, map_inv]; rfl
  intro w hw
  rw [hιτ, mem_centralizer_singleton_iff] at hw
  have hw' : c⁻¹ * w * c ∈ centralizer ({(swapIota h d T e τ₀ : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * w * c * (swapIota h d T e τ₀ : G) =
        c⁻¹ * (w * (c * (swapIota h d T e τ₀ : G) * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * (swapIota h d T e τ₀ : G) * c⁻¹) * w) * c := by rw [hw]
      _ = (swapIota h d T e τ₀ : G) * (c⁻¹ * w * c) := by group
  have h1 := mem_centralizer_singleton_iff.1 (hle hw')
  have hzc := mem_centralizer_singleton_iff.1 hcz
  rw [mem_centralizer_singleton_iff]
  have hcz' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (c * z) := by rw [hzc]; group
      _ = z := by group
  calc w * z = c * (c⁻¹ * w * c * (c⁻¹ * z * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * z * c) * (c⁻¹ * w * c)) * c⁻¹ := by rw [hcz', h1]
    _ = z * w := by group

theorem centralizer_le_twisted (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {τ₀ : Perm (Fin n)} (hτ₀ : τ₀.IsSwap)
    (hle : centralizer ({z * (swapIota h d T e τ₀ : G)} : Set G) ≤ centralizer ({z} : Set G))
    {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    centralizer ({z * (swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨p, q, hpq, hτ₀e⟩ := hτ₀
  obtain ⟨r, t, hrt, hτe⟩ := hτ
  obtain ⟨π, hπ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq hrt)
  set c : G := (swapIota h d T e π : G) with hc
  have hcz : c ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e π
  have hzc := mem_centralizer_singleton_iff.1 hcz
  have hcz' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (c * z) := by rw [hzc]; group
      _ = z := by group
  have hιτ : (swapIota h d T e τ : G) = c * (swapIota h d T e τ₀ : G) * c⁻¹ := by
    rw [hτe, ← hπ, ← hτ₀e, map_mul, map_mul, map_inv]; rfl
  intro w hw
  rw [mem_centralizer_singleton_iff] at hw
  have hzι₀ : z * (swapIota h d T e τ₀ : G) = c⁻¹ * (z * (swapIota h d T e τ : G)) * c := by
    rw [hιτ]
    calc z * (swapIota h d T e τ₀ : G) = (c⁻¹ * z * c) * (swapIota h d T e τ₀ : G) := by
          rw [hcz']
      _ = c⁻¹ * (z * (c * (swapIota h d T e τ₀ : G) * c⁻¹)) * c := by group
  have hw' : c⁻¹ * w * c ∈ centralizer ({z * (swapIota h d T e τ₀ : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff, hzι₀]
    calc c⁻¹ * w * c * (c⁻¹ * (z * (swapIota h d T e τ : G)) * c) =
        c⁻¹ * (w * (z * (swapIota h d T e τ : G))) * c := by group
      _ = c⁻¹ * ((z * (swapIota h d T e τ : G)) * w) * c := by rw [hw]
      _ = c⁻¹ * (z * (swapIota h d T e τ : G)) * c * (c⁻¹ * w * c) := by group
  have h1 := mem_centralizer_singleton_iff.1 (hle hw')
  rw [mem_centralizer_singleton_iff]
  calc w * z = c * (c⁻¹ * w * c * (c⁻¹ * z * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * z * c) * (c⁻¹ * w * c)) * c⁻¹ := by rw [hcz', h1]
    _ = z * w := by group

theorem exists_double_partner_of_symOutcome (h : Setting G L 10) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10))
    (hP : ∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap →
      ¬ IsConj z y)
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf h d e hx).IsSwap)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hS : SymOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) 8) :
    ∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧
      Multiset.card (permOf h d e hb).cycleType = 2 := by
  classical
  obtain ⟨b, hb, hbz, -, hfix⟩ :=
    exists_partner_of_symOutcome h d T e (by norm_num) hx hτ hfus hzx hS
  refine ⟨b, hb, hbz, ?_⟩
  have hb2 : b * b = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hbz
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [d.mul_self]; group
  have hπ2 := permOf_mul_self h d e hb hb2
  have hsupp := card_support_eq_two_mul_card_cycleType hπ2
  have hadd := card_fixFin_add_card_support (permOf h d e hb)
  rcases hfix with h8 | h6
  · exfalso
    have hsw : (permOf h d e hb).IsSwap := by
      rw [← card_support_eq_two]
      omega
    exact hP b hb hsw hbz
  · omega

theorem false_of_double_partner (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10))
    (hcen : (∀ τ : Perm (Fin 10), τ.IsSwap →
        centralizer ({(swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G)) ∨
      (∀ τ : Perm (Fin 10), τ.IsSwap →
        centralizer ({z * (swapIota h d T e τ : G)} : Set G) ≤ centralizer ({z} : Set G)))
    {b : G} (hb : b ∈ centralizer ({z} : Set G)) (hbz : IsConj z b)
    (hb2 : Multiset.card (permOf h d e hb).cycleType = 2) : False := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.1 hbz
  have hbg : b = c⁻¹⁻¹ * z * c⁻¹ := by rw [inv_inv, ← hc]
  have haC : c⁻¹⁻¹ * z * c⁻¹ ∈ centralizer ({z} : Set G) := hbg ▸ hb
  have hσ : permOf h d e haC = permOf h d e hb := permOf_congr' hbg.symm haC hb h d e
  have hk2 : Multiset.card (permOf h d e haC).cycleType = 2 := by rw [hσ]; exact hb2
  have hσ2 : permOf h d e haC * permOf h d e haC = 1 := by
    have hb2' : c⁻¹⁻¹ * z * c⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) = 1 := by
      calc c⁻¹⁻¹ * z * c⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) = c⁻¹⁻¹ * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [d.mul_self]; group
    exact permOf_mul_self h d e haC hb2'
  obtain ⟨τ, hτ⟩ : ((permOf h d e haC).cycleFactorsFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, cycleFactorsFinset_eq_empty_iff]
    intro h1
    rw [h1, cycleType_one] at hk2
    simp at hk2
  have hτsw : τ.IsSwap :=
    card_support_eq_two.1 (card_supp_eq_two_of_mem_cycleFactorsFinset hσ2 hτ)
  have hτσ : τ * permOf h d e haC = permOf h d e haC * τ := (self_mem_cycle_factors_commute hτ).eq
  have key : ∃ (y : G) (hy : y ∈ centralizer ({z} : Set G)), permOf h d e hy = τ ∧ y * y = 1 ∧
      centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) := by
    have hιC := swapIota_mem_centralizer h d T e τ
    have hιπ : permOf h d e hιC = τ := permOf_swapIota h d T e τ
    obtain ⟨hι2, -, -⟩ := swap_elt_facts h d T e hιC (by rw [hιπ]; exact hτsw)
    rcases hcen with hU | hW
    · exact ⟨_, hιC, hιπ, hι2, hU τ hτsw⟩
    · have hzι : z * (swapIota h d T e τ : G) ∈ centralizer ({z} : Set G) :=
        mul_mem (mem_centralizer_singleton_iff.2 rfl) hιC
      refine ⟨_, hzι, ?_, ?_, hW τ hτsw⟩
      · rw [permOf_mul h d e (mem_centralizer_singleton_iff.2 rfl) hιC hzι, permOf_self, one_mul,
          hιπ]
      · have hιz : (swapIota h d T e τ : G) * z = z * (swapIota h d T e τ : G) :=
          mem_centralizer_singleton_iff.1 hιC
        calc z * (swapIota h d T e τ : G) * (z * (swapIota h d T e τ : G)) =
            z * ((swapIota h d T e τ : G) * z) * (swapIota h d T e τ : G) := by group
          _ = z * (z * (swapIota h d T e τ : G)) * (swapIota h d T e τ : G) := by rw [hιz]
          _ = (z * z) * ((swapIota h d T e τ : G) * (swapIota h d T e τ : G)) := by group
          _ = 1 := by rw [d.mul_self, hι2, one_mul]
  obtain ⟨y, hy, hyπ, hy2, hle⟩ := key
  have hya : y * (c⁻¹⁻¹ * z * c⁻¹) = (c⁻¹⁻¹ * z * c⁻¹) * y := by
    rw [comm_iff_permOf_comm h d T e hy haC, hyπ]
    exact hτσ
  have h5 := partner_type_five h d T e haC (by omega) hτ hy hyπ hya hy2 hle
  omega

end CFSG.OddStandard.AltStdSec
