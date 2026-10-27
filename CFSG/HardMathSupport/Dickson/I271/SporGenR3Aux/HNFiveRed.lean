module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCert

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.HNSchreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271.HNFive

section Conj

theorem conj_mem_centralizer_of {G : Type} [Group G] {x s s₀ g : G} (hg : g * s₀ * g⁻¹ = s)
    (hxs : s * x = x * s) : g⁻¹ * x * g ∈ Subgroup.centralizer ({s₀} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h0 : s₀ = g⁻¹ * s * g := by rw [← hg]; group
  rw [h0]
  calc g⁻¹ * x * g * (g⁻¹ * s * g) = g⁻¹ * (x * s) * g := by group
    _ = g⁻¹ * (s * x) * g := by rw [hxs]
    _ = g⁻¹ * s * g * (g⁻¹ * x * g) := by group

theorem orderOf_conj' {G : Type} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem isConj_conj_inv_mul {G : Type} [Group G] (g x : G) : IsConj x (g⁻¹ * x * g) :=
  isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩

end Conj

section Red


theorem orderOf_g3J_pow_six : orderOf (g3J ^ 6) = 5 := by
  obtain ⟨h30, h6, -⟩ := hn5_facts
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (by rw [← pow_mul]; exact h30) h6

theorem g3J_pow_six_mem : g3J ^ 6 ∈ CJ (sJ 2) := by
  have e : c3J 6 = g3J := by
    unfold c3J
    exact if_neg (by norm_num)
  have h := c3J_comm (j := 6) (by norm_num)
  rw [e] at h
  exact Subgroup.pow_mem _ (mem_CJ.2 h.symm) 6

theorem exists_conj_pow_g3J6 {x : JH} (hx : orderOf x = 5) (hnot : ∀ k : ℕ, ¬ IsConj x (fJ ^ k))
    (h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set JH))) :
    ∃ k : ℕ, IsConj x ((g3J ^ 6) ^ k) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  obtain ⟨s', hs'⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({x} : Set JH))) 3 h3
  have hso : orderOf (s' : JH) = 3 := by rw [Subgroup.orderOf_coe]; exact hs'
  have hxs := Subgroup.mem_centralizer_singleton_iff.1 s'.2
  rcases (order_three_classes (s' : JH)).1 hso with h | h
  ·
    exfalso
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    have hxm : g⁻¹ * x * g ∈ CJ (sJ 0) := conj_mem_centralizer_of hg hxs
    have hxo : orderOf (g⁻¹ * x * g) = 5 := by
      have := orderOf_conj' g⁻¹ x
      rw [inv_inv] at this
      exact this.trans hx
    obtain ⟨k, hk⟩ := isConj_fJ_of_mem_CJ_s1 hxm hxo
    exact hnot k ((isConj_conj_inv_mul g x).trans hk)
  ·
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    have hxm : g⁻¹ * x * g ∈ CJ (sJ 2) := conj_mem_centralizer_of hg hxs
    have hxo : orderOf (g⁻¹ * x * g) = 5 := by
      have := orderOf_conj' g⁻¹ x
      rw [inv_inv] at this
      exact this.trans hx
    have h25 : ¬ 5 ^ 2 ∣ Nat.card ↥(CJ (sJ 2)) := by
      rw [card_CJ_s3]
      norm_num
    obtain ⟨k, hk⟩ := isConj_pow_of_mem (CJ (sJ 2)) h25 hxm g3J_pow_six_mem hxo
      orderOf_g3J_pow_six
    exact ⟨k, (isConj_conj_inv_mul g x).trans hk⟩

theorem hnFiveMoved_holds : HNFiveMoved := by
  intro x hx hnot h3
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  obtain ⟨k, hk⟩ := exists_conj_pow_g3J6 hx hnot h3
  have hord : Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
    hnFiveOrders_holds x hx hnot
  have hy5 := orderOf_g3J_pow_six
  have hko : orderOf ((g3J ^ 6) ^ k) = 5 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hk
    rw [← hc, orderOf_conj', hx]
  have hcent : Subgroup.centralizer ({(g3J ^ 6) ^ k} : Set JH) =
      Subgroup.centralizer ({g3J ^ 6} : Set JH) :=
    centralizer_pow_eq (by rw [hko, hy5]) (by rw [hy5]; norm_num)
  have hord0 : Nat.card ↥(Subgroup.centralizer ({g3J ^ 6} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 := by
    obtain ⟨e⟩ := exists_centralizerEquiv hk
    rw [hcent] at e
    rw [← Nat.card_congr e.toEquiv]
    exact hord
  have hM0 : HNMovedIn (Subgroup.centralizer ({g3J ^ 6} : Set JH)) := hnMovedIn_g3J6 hord0
  rw [← hcent] at hM0
  exact HNMovedIn.of_isConj hk.symm hM0

end Red

end CFSG.HardMathSupport.Dickson.I271
