
module

public import CFSG.Sporadic.Schreier.J4SOdd276Base

@[expose] public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem le_card_centralizer_of_sylow {G : Type*} [Group G] [Finite G] {H Q N : Subgroup G}
    {p : ℕ} [hp : Fact p.Prime] (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {b : ℕ}
    (hb : ∀ q ∈ Q, q ≠ 1 → b ≤ Nat.card (Subgroup.centralizer {q} ⊓ N : Subgroup G))
    {h : G} (hh : h ∈ H) (ho : orderOf h = p) :
    b ≤ Nat.card (Subgroup.centralizer {h} ⊓ N : Subgroup G) := by
  have hQ' : Nat.card (Q.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  let P : Sylow p H := Sylow.ofCard (Q.subgroupOf H) hQ'
  have hP : IsPGroup p (Subgroup.zpowers (⟨h, hh⟩ : H)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ho, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P hP
  rw [Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hg
  set q := (g : G) * h * (g : G)⁻¹ with hqdef
  have hq : q ∈ Q := hg
  have hq1 : q ≠ 1 := by
    intro h1
    have : h = 1 := by
      have e : h = (g : G)⁻¹ * q * g := by rw [hqdef]; group
      rw [e, h1]; group
    rw [this, orderOf_one] at ho
    exact hp.out.one_lt.ne ho
  have e : h = (g : G)⁻¹ * q * (g : G)⁻¹⁻¹ := by rw [hqdef]; group
  rw [e, card_centralizer_inf_conj (fun n hn => hnorm _ (H.inv_mem g.2) n hn)
    (fun n hn => by rw [inv_inv]; exact hnorm _ g.2 n hn)]
  exact hb q hq hq1

theorem a276_mem_H : a276 ∈ H := K_le_H a276_mem_K

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
