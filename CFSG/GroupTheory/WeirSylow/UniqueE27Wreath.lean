module

public import CFSG.GroupTheory.WreathThreeIso
public import CFSG.GroupTheory.UniqueElemSylow
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.GroupTheory.WreathThree

theorem uniqueElemSylow_of_forall_sylow_mulEquiv_wreath {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : 1 ≤ n)
    (h : ∀ P : Sylow 3 G,
      Nonempty (↥P ≃* (Multiplicative (ZMod (3 ^ n)) ≀ᵣ Multiplicative (ZMod 3)))) :
    UniqueElemSylow 3 3 G := by
  obtain ⟨A, _, habel, hcard, huniq, _⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_unique_E27_Zwr (n := n) hn
  have hM : ∃! A : Subgroup (Multiplicative (ZMod (3 ^ n)) ≀ᵣ Multiplicative (ZMod 3)),
      CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
    refine ⟨A, ⟨habel, by rw [hcard]; norm_num⟩, ?_⟩
    intro B hB
    exact huniq B hB.1 (by rw [hB.2]; norm_num)
  exact UniqueElemSylow.of_forall_sylow_mulEquiv (p := 3) (k := 3) hM h

theorem base_sup_zpowers_le {G : Type*} [Group G] {H S : Subgroup G} {y : G} (hS : S ≤ H)
    (hy : y ∈ H) : base S y ⊔ Subgroup.zpowers y ≤ H := by
  refine sup_le (sup_le (sup_le hS ?_) ?_) (Subgroup.zpowers_le.mpr hy)
  · rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using H.mul_mem (H.mul_mem hy (hS hx)) (H.inv_mem hy)
  · rintro _ ⟨x, hx, rfl⟩
    have hy2 : y ^ 2 ∈ H := H.pow_mem hy 2
    exact H.mul_mem (H.mul_mem hy2 (hS hx)) (H.inv_mem hy2)

theorem card_base_sup_zpowers_eq {G : Type*} [Group G] [Finite G] {S : Subgroup G} {y : G}
    (h : IsWreathThree S y) (hy : y ^ 3 = 1) {n : ℕ} (hn : Nat.card S = 3 ^ n) :
    Nat.card ↥(base S y ⊔ Subgroup.zpowers y) = 3 ^ (3 * n + 1) := by
  rw [card_sup_zpowers h hy, h.card_base, hn, ← pow_mul, ← pow_succ']
  congr 1
  omega

theorem exists_forall_sylow_mulEquiv_wreath_of_isWreathThree {G : Type*} [Group G] [Finite G]
    {H S : Subgroup G} {y : G} (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hS : S ≤ H)
    (hyH : y ∈ H)
    (hord : (Nat.card H).factorization 3 = 3 * (Nat.card S).factorization 3 + 1) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card S = 3 ^ n ∧ ∀ Q : Sylow 3 H,
      Nonempty (↥Q ≃* (Multiplicative (ZMod (3 ^ n)) ≀ᵣ Multiplicative (ZMod 3))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn1, hSn, ⟨e⟩⟩ := exists_mulEquiv_regularWreathProduct h hy
  have hP : base S y ⊔ Subgroup.zpowers y ≤ H := base_sup_zpowers_le hS hyH
  have hcardP : Nat.card ↥(base S y ⊔ Subgroup.zpowers y) = 3 ^ (3 * n + 1) :=
    card_base_sup_zpowers_eq h hy hSn
  have hHn : (Nat.card H).factorization 3 = 3 * n + 1 := by
    rw [hord, hSn, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hcardPH : Nat.card ((base S y ⊔ Subgroup.zpowers y).subgroupOf H) =
      3 ^ (Nat.card H).factorization 3 := by
    rw [hHn, ← hcardP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  let P : Sylow 3 H := Sylow.ofCard ((base S y ⊔ Subgroup.zpowers y).subgroupOf H) hcardPH
  refine ⟨n, hn1, hSn, fun Q => ?_⟩
  exact ⟨(P.equiv Q).symm.trans ((Subgroup.subgroupOfEquivOfLe hP).trans e)⟩

theorem uniqueElemSylow_of_isWreathThree {G : Type*} [Group G] [Finite G] {H S : Subgroup G}
    {y : G} (h : IsWreathThree S y) (hy : y ^ 3 = 1) (hS : S ≤ H) (hyH : y ∈ H)
    (hord : (Nat.card H).factorization 3 = 3 * (Nat.card S).factorization 3 + 1) :
    UniqueElemSylow 3 3 H := by
  obtain ⟨n, hn, -, hQ⟩ := exists_forall_sylow_mulEquiv_wreath_of_isWreathThree h hy hS hyH hord
  exact uniqueElemSylow_of_forall_sylow_mulEquiv_wreath hn hQ

end CFSG.GroupTheory.WeirSylow
