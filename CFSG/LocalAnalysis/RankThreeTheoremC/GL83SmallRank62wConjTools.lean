module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G]

theorem sr630e_exists_isSylowOf_le [Finite G] {p : ℕ} [Fact p.Prime] {B H : Subgroup G}
    (hBH : B ≤ H) (hB : IsPGroup p B) : ∃ W : Subgroup G, IsSylowOf p W H ∧ B ≤ W := by
  have hB' : IsPGroup p (B.subgroupOf H) := hB.comap_subtype
  obtain ⟨S, hS⟩ := hB'.exists_le_sylow
  refine ⟨(S : Subgroup H).map H.subtype, ⟨S, rfl⟩, fun b hb => ?_⟩
  exact ⟨⟨b, hBH hb⟩, hS (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb), rfl⟩

theorem sr630e_inv_conj_pow (k b : G) (n : ℕ) : (k⁻¹ * b * k) ^ n = k⁻¹ * b ^ n * k := by
  have h := conj_pow (i := n) (a := k⁻¹) (b := b)
  rwa [inv_inv] at h

theorem sr630e_inf_eq_zpowers [Finite G] {p : ℕ} (hp : p.Prime) {B C : Subgroup G} {x z : G}
    (hBc : Nat.card B = p ^ 2) (hxB : x ∈ B) (hxC : x ∈ C) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hzB : z ∈ B) (hzC : z ∉ C) : B ⊓ C = zpowers x := by
  have : Fact p.Prime := ⟨hp⟩
  have hxle : zpowers x ≤ B ⊓ C := zpowers_le.mpr ⟨hxB, hxC⟩
  have hcx : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hdvd : Nat.card (B ⊓ C : Subgroup G) ∣ p ^ 2 := by
    rw [← hBc]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hge : p ≤ Nat.card (B ⊓ C : Subgroup G) := by
    rw [← hcx]; exact Subgroup.card_le_of_le hxle
  have hk1 : k = 1 := by
    interval_cases k
    · rw [hk', pow_zero] at hge
      exact absurd hge (not_le.mpr hp.one_lt)
    · rfl
    · exfalso
      have heq : B ⊓ C = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hBc])
      exact hzC (heq.ge hzB).2
  exact (Subgroup.eq_of_le_of_card_ge hxle (by rw [hk', hk1, pow_one, hcx])).symm

theorem sr630e_mem_zpowers_of_mem [Finite G] {p : ℕ} (hp : p.Prime) {x c : G} (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) (hc : c ∈ zpowers x) (hc1 : c ≠ 1) : x ∈ zpowers c := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : zpowers c ≤ zpowers x := zpowers_le.mpr hc
  have hcx : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hdvd : Nat.card (zpowers c) ∣ p := by
    rw [← hcx]; exact Subgroup.card_dvd_of_le hle
  have hcc : Nat.card (zpowers c) ≠ 1 := by
    rw [Nat.card_zpowers]
    exact fun h => hc1 (orderOf_eq_one_iff.mp h)
  have hcp : Nat.card (zpowers c) = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hcc
  have heq : zpowers c = zpowers x := Subgroup.eq_of_le_of_card_ge hle (by rw [hcp, hcx])
  rw [heq]
  exact mem_zpowers x

theorem sr630e_orderOf_conj (g h : G) : orderOf (g * h * g⁻¹) = orderOf h := by
  have h1 := orderOf_injective (MulAut.conj g).toMonoidHom
    (fun a b hab => (MulAut.conj g).injective hab) h
  simpa [MulAut.conj_apply] using h1

theorem sr630e_isElemAbelian_map {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A)
    (φ : G →* G) : IsElemAbelian p (A.map φ) := CFSG.Open.IsElemAbelian.map hA _

end CFSG.LocalAnalysis.RankThreeTheoremC
