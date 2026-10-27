module

public import CFSG.CGT.T75R.EAAction
public import CFSG.CGT.Timmesfeld75.Sec4OneCommon

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

theorem mem_of_mem_classD_of_centralizes {T T₁ : Subgroup G} (hP : MaxPair T T₁)
    (hTc : Nat.card T = 8) (hLc : Nat.card (normIn T T₁) ≤ 4) {U : Subgroup G}
    (hU : ∃ g : G, U = conjSubgroup g T) {d : G} (hd : d ∈ classD T)
    (hc : ∀ u ∈ U, d * u = u * d) : d ∈ U := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hd
  set d : G := g⁻¹ * t * g with hdd
  have hV : ∃ v : G, conjSubgroup g⁻¹ T = conjSubgroup v T := ⟨g⁻¹, rfl⟩
  have hdV : d ∈ conjSubgroup g⁻¹ T := by
    rw [mem_conjSubgroup]
    simpa [hdd, mul_assoc] using ht
  have hd1 : d ≠ 1 := by
    intro h
    apply ht1
    have : t = g * d * g⁻¹ := by rw [hdd]; group
    rw [this, h]
    group
  have hwcV : IsWC (conjSubgroup g⁻¹ T) := hP.wc.conj g⁻¹
  have hUN : U ≤ Subgroup.normalizer ((conjSubgroup g⁻¹ T : Subgroup G) : Set G) := fun u hu =>
    hwcV.centralizer_le_normalizer hdV hd1
      (Subgroup.mem_centralizer_iff.2 fun k hk => by
        rw [Set.mem_singleton_iff] at hk
        subst hk
        exact hc u hu)
  by_cases hVU : conjSubgroup g⁻¹ T = U
  · rw [← hVU]; exact hdV
  · exfalso
    obtain ⟨h0, hh0⟩ := hU
    have hle := hP.card_normIn_le (U := U) (V := conjSubgroup g⁻¹ T) ⟨h0, hh0⟩ hV hVU
    have hNU : normIn U (conjSubgroup g⁻¹ T) = U := by
      unfold normIn
      exact inf_eq_left.2 hUN
    rw [hNU, hh0, card_conjSubgroup] at hle
    omega

theorem false_of_commutator_subgroup [Finite G] {T T₁ : Subgroup G} (hP : MaxPair T T₁)
    (hTc : Nat.card T = 8) (hLc : Nat.card (normIn T T₁) ≤ 4) {Tx : Subgroup G}
    (hTx : ∃ g : G, Tx = conjSubgroup g T) {x : G} (hx : x ∈ Tx) (hx1 : x ≠ 1)
    {L : Subgroup G} (hLnot : ¬ L ≤ Subgroup.normalizer (Tx : Set G))
    {E : Subgroup G} (hE : IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E)
    (hEx : ∀ k ∈ E, x * k = k * x) (hEL : ∀ k ∈ E, ∀ l ∈ L, k * l = l * k)
    (hED : ∀ k ∈ E, x * k ∈ classD T) : False := by
  obtain ⟨g, hg⟩ := hTx
  have hwcx : IsWC Tx := hg ▸ hP.wc.conj g
  have hTxc : Nat.card Tx = 8 := by rw [hg, card_conjSubgroup, hTc]
  have hEN : E ≤ Subgroup.normalizer (Tx : Set G) := fun k hk =>
    hwcx.centralizer_le_normalizer hx hx1
      (Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hEx k hk)
  obtain ⟨k, hkE, hk1, hkc⟩ := exists_centralizes_of_card_ge_eight hwcx.1 hTxc hE hEN hE8
  have hxk : x * k ∈ Tx := by
    refine mem_of_mem_classD_of_centralizes hP hTc hLc ⟨g, hg⟩ (hED k hkE) fun u hu => ?_
    have h1 : x * u = u * x := elemAbelian_mul_comm hwcx.1 hx hu
    calc x * k * u = x * (k * u) := by rw [mul_assoc]
      _ = x * (u * k) := by rw [hkc u hu]
      _ = (x * u) * k := by rw [mul_assoc]
      _ = (u * x) * k := by rw [h1]
      _ = u * (x * k) := by rw [mul_assoc]
  have hkT : k ∈ Tx := by
    have : x⁻¹ * (x * k) ∈ Tx := Tx.mul_mem (Tx.inv_mem hx) hxk
    simpa using this
  apply hLnot
  intro l hl
  refine hwcx.centralizer_le_normalizer hkT hk1 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hEL k hkE l hl

end CFSG.CGT.T75R
