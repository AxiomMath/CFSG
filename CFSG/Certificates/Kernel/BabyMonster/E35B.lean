module

public import CFSG.Certificates.Kernel.BabyMonster.E35Group
public import Certificates.Certificate431004

public section

namespace CFSG.KC.BM.E35Group

open CFSG.Open CFSG.Blueprint

theorem attained_B :
    ∃ E T : Subgroup NativeSporadic.B, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ T ≠ ⊥ ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set NativeSporadic.B) := by
  obtain ⟨_, _, hx, hg, h⟩ := Certificates.certificate431004
  exact attained_of_submonoid _ hx hg h (MulEquiv.refl _)

theorem exists_elemAbelian_le {G : Type*} [Group G] {p n k : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ n) (hk : k ≤ n) :
    ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hdvd : p ^ k ∣ Nat.card E := by rw [hc]; exact pow_dvd_pow p hk
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p hdvd
  have hle : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  refine ⟨K.map E.subtype, hle, ⟨?_, fun x hx => hE.2 x (hle hx)⟩, ?_⟩
  · have := hE.1
    exact ⟨⟨fun a b => Subtype.ext (by
      have := this.is_comm.comm ⟨a.1, hle a.2⟩ ⟨b.1, hle b.2⟩
      simpa using congrArg Subtype.val this)⟩⟩
  · rw [Nat.card_congr (K.equivMapOfInjective E.subtype E.subtype_injective).toEquiv.symm]
    exact hK

theorem elemAbelian_three_four_B :
    ∃ E : Subgroup NativeSporadic.B, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  obtain ⟨E, -, hE, hc, -⟩ := attained_B
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, -, hF, hFc⟩ := exists_elemAbelian_le hE hc (by norm_num : 4 ≤ 5)
  exact ⟨F, hF, hFc⟩

end CFSG.KC.BM.E35Group

end
