module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44SylGrp

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction Syl

theorem noCard2047 : NoCard2047Stmt := by
  intro V _ _ hV _ X hX
  have hX0 : Nat.card X ≠ 0 := by rw [hX]; norm_num
  have : Finite X := Nat.finite_of_card_ne_zero hX0
  have : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 89 X) := inferInstance
  have hPc : Nat.card P = 89 :=
    card_sylow_eq_prime (by rw [hX]; norm_num) (by rw [hX]; norm_num) P
  obtain ⟨x, hx, hPx⟩ := exists_gen_of_card_prime (P := (P : Subgroup X)) hPc
  have hN := card_normalizer_dvd hV X.subtype X.subtype_injective twoOrderGe11_89 hx
  have hcnt : (normalizer ((P : Subgroup X) : Set X)).index ≡ 1 [MOD 89] := by
    have h := card_sylow_modEq_one 89 X
    rw [P.card_eq_index_normalizer] at h
    exact h
  rw [hPx] at hcnt
  have hidx := Subgroup.index_mul_card (normalizer (zpowers x : Set X))
  have h89 : 89 ∣ Nat.card (normalizer (zpowers x : Set X)) := by
    have := Subgroup.card_dvd_of_le (le_normalizer (H := zpowers x))
    rwa [Nat.card_zpowers, hx] at this
  rw [hV] at hN
  rw [hX] at hidx
  exact num89 _ _ hN hidx h89 hcnt

theorem idxDvd11 : IdxDvd11Stmt := by
  intro V _ _ hV _ X hX K hKn hK23
  have hX0 : Nat.card X ≠ 0 := by rw [hX]; norm_num
  have : Finite X := Nat.finite_of_card_ne_zero hX0
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 23 hK23
  have hy : orderOf (k : X) = 23 := by rw [Subgroup.orderOf_coe]; exact hk
  have hQK : zpowers (k : X) ≤ K := zpowers_le.2 k.2
  have hQp : IsPGroup 23 (zpowers (k : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  have hPc : Nat.card P = 23 :=
    card_sylow_eq_prime (by rw [hX]; norm_num) (by rw [hX]; norm_num) P
  have hPeq : zpowers (k : X) = (P : Subgroup X) :=
    eq_of_le_of_card_ge hQP (by rw [hPc, Nat.card_zpowers, hy])
  have hPK : (P : Subgroup X) ≤ K := hPeq ▸ hQK
  have hfr : normalizer ((P : Subgroup X) : Set X) ⊔ K = ⊤ := P.normalizer_sup_eq_top' hPK
  have hN := card_normalizer_dvd hV X.subtype X.subtype_injective twoOrderGe11_23 hy
  rw [hPeq] at hN
  have hcnt : (normalizer ((P : Subgroup X) : Set X)).index ≡ 1 [MOD 23] := by
    have h := card_sylow_modEq_one 23 X
    rw [P.card_eq_index_normalizer] at h
    exact h
  have hidx := Subgroup.index_mul_card (normalizer ((P : Subgroup X) : Set X))
  have h23 : 23 ∣ Nat.card (normalizer ((P : Subgroup X) : Set X)) := by
    have := Subgroup.card_dvd_of_le (le_normalizer (H := (P : Subgroup X)))
    rwa [hPc] at this
  rw [hV] at hN
  rw [hX] at hidx
  have hc253 : Nat.card (normalizer ((P : Subgroup X) : Set X)) = 253 :=
    num23 _ _ hN hidx h23 hcnt
  have hrel : K.index = K.relIndex (normalizer ((P : Subgroup X) : Set X)) := by
    have := relIndex_sup_right (normalizer ((P : Subgroup X) : Set X)) K
    rwa [hfr, relIndex_top_right] at this
  have h3 : (P : Subgroup X).relIndex (normalizer ((P : Subgroup X) : Set X)) = 11 := by
    have h := Subgroup.card_mul_index
      ((P : Subgroup X).subgroupOf (normalizer ((P : Subgroup X) : Set X)))
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, hPc, hc253] at h
    unfold relIndex
    omega
  have hle : (P : Subgroup X) ≤ K ⊓ normalizer ((P : Subgroup X) : Set X) :=
    le_inf hPK le_normalizer
  have h2 := relIndex_dvd_of_le_left (normalizer ((P : Subgroup X) : Set X)) hle
  rw [h3, inf_relIndex_right] at h2
  rw [hrel]
  exact h2

theorem orbit23 : Orbit23Stmt := by
  intro V _ _ hV _ X hX y hy
  have hX0 : Nat.card X ≠ 0 := by rw [hX]; norm_num
  have : Finite X := Nat.finite_of_card_ne_zero hX0
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hos : Nat.card (stabilizer X y) * Nat.card (orbit X y) = 244823040 := by
    have h := Subgroup.card_mul_index (stabilizer X y)
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
    rwa [hX] at h
  by_cases h : 23 ∣ Nat.card (stabilizer X y)
  · exfalso
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer X y) 23 h
    have hs1 : orderOf (s : X) = 23 := by rw [Subgroup.orderOf_coe]; exact hs
    have hs2 : orderOf ((s : X) : MulAut V) = 23 := by rw [Subgroup.orderOf_coe]; exact hs1
    have ha : ((s : X) : MulAut V) ^ 23 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one _
    have ha1 : ((s : X) : MulAut V) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hs2
      omega
    have hsy : ((s : X) : MulAut V) y = y := by
      have := s.2
      rwa [mem_stabilizer_iff] at this
    exact hy (eq_one_of_fixed hV twoOrderGe11_23 ha ha1 hsy)
  · have h23 : 23 ∣ Nat.card (stabilizer X y) * Nat.card (orbit X y) := by
      rw [hos]; norm_num
    exact ((Nat.Prime.dvd_mul (Fact.out)).1 h23).resolve_left h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
