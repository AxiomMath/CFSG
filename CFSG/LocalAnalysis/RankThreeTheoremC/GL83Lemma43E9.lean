module

import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l43_not_forall_card_commutator_eq_four {K X : Subgroup G} (hK : IsElemAbelian 3 K)
    (hK9 : Nat.card K = 9) (hX : IsElemAbelian 2 X) (hKX : K ≤ normalizer (X : Set G)) :
    ¬ ∀ k ∈ K, k ≠ 1 → Nat.card (⁅X, zpowers k⁆ : Subgroup G) = 4 := by
  classical
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥K →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hKX)
  let _ : MulAction ↥K ↥X := MulAction.compHom ↥X φ
  have hsmul : ∀ (k : ↥K) (x : ↥X), ((k • x : ↥X) : G) = (k : G) * (x : G) * (k : G)⁻¹ :=
    fun k x => Subgroup.normalizerMonoidHom_apply_apply_coe X (Subgroup.inclusion hKX k) x
  have hfix : ∀ k : ↥K, Nat.card (MulAction.fixedBy ↥X k) =
      Nat.card (X ⊓ Subgroup.centralizer ({(k : G)} : Set G) : Subgroup G) := by
    intro k
    have hmem1 : ∀ x : ↥X, k • x = x → (x : G) ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
      intro x hx
      have h1 := hsmul k x
      rw [hx] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * (k : G) = ((k : G) * (x : G) * (k : G)⁻¹) * (k : G) := by rw [← h1]
        _ = (k : G) * (x : G) := by group
    have hmem2 : ∀ x : ↥X, (x : G) ∈ Subgroup.centralizer ({(k : G)} : Set G) → k • x = x := by
      intro x hx
      apply Subtype.ext
      rw [hsmul]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx
      calc (k : G) * (x : G) * (k : G)⁻¹ = ((x : G) * (k : G)) * (k : G)⁻¹ := by rw [← h1]
        _ = (x : G) := by group
    exact Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨x.1.2, hmem1 x.1 x.2⟩⟩
        invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
          hmem2 ⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩ (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hXp : IsPGroup 2 ↥X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hX.2 _ x.2)⟩
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  have h3a : ¬ 3 ∣ Nat.card ↥X := by
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have : Fintype ↥K := Fintype.ofFinite _
  have : ∀ g : ↥K, Fintype (MulAction.fixedBy ↥X g) := fun g => Fintype.ofFinite _
  have : Fintype (Quotient (MulAction.orbitRel ↥K ↥X)) := Fintype.ofFinite _
  have hcg : ∀ g : ↥K, g ≠ 1 → 4 * Fintype.card (MulAction.fixedBy ↥X g) = Nat.card ↥X := by
    intro g hg
    have hg1 : (g : G) ≠ 1 := fun h => hg (Subtype.ext h)
    have hcomm := GL83.I28_3S3.card_commutator_mul_card_centralizer hX (hKX g.2) (hK.2 _ g.2)
    rw [h4 _ g.2 hg1] at hcomm
    rw [← Nat.card_eq_fintype_card, hfix g]
    exact hcomm
  have hc1 : Fintype.card (MulAction.fixedBy ↥X (1 : ↥K)) = Nat.card ↥X := by
    rw [← Nat.card_eq_fintype_card, hfix 1]
    have : (X ⊓ Subgroup.centralizer ({((1 : ↥K) : G)} : Set G) : Subgroup G) = X :=
      inf_eq_left.mpr (fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp))
    rw [this]
  have hKcard : Fintype.card ↥K = 9 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK9
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := ↥K) (X := ↥X)
  have hsplit : ∑ g : ↥K, Fintype.card (MulAction.fixedBy ↥X g) =
      Fintype.card (MulAction.fixedBy ↥X (1 : ↥K)) +
        ∑ g ∈ Finset.univ.erase (1 : ↥K), Fintype.card (MulAction.fixedBy ↥X g) :=
    (Finset.add_sum_erase Finset.univ (fun g : ↥K => Fintype.card (MulAction.fixedBy ↥X g))
      (Finset.mem_univ 1)).symm
  have hcardE : (Finset.univ.erase (1 : ↥K)).card = 8 := by
    have := Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥K))
    rw [Finset.card_univ, hKcard] at this
    omega
  have hconst : ∑ g ∈ Finset.univ.erase (1 : ↥K),
      4 * Fintype.card (MulAction.fixedBy ↥X g) =
        (Finset.univ.erase (1 : ↥K)).card * Nat.card ↥X :=
    Finset.sum_const_nat (fun g hg => hcg g (Finset.ne_of_mem_erase hg))
  have h8 : 4 * ∑ g ∈ Finset.univ.erase (1 : ↥K), Fintype.card (MulAction.fixedBy ↥X g) =
      8 * Nat.card ↥X := by
    rw [Finset.mul_sum, hconst, hcardE]
  rw [hsplit, hc1, hKcard] at hburn
  exact h3a ⟨Fintype.card (Quotient (MulAction.orbitRel ↥K ↥X)), by omega⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
