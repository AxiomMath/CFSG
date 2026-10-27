module

public import CFSG.CharacterTheory.Wreathed.SplitCyclicActorWreath
public import CFSG.CharacterTheory.Wreathed.CyclicDisjointActor

public section

namespace CFSG.Wreathed.SplitCyclicActor

open scoped Pointwise

universe u

theorem split_maximal_cyclic_actor_forces_quaternion_kernel_or_odd_complement
    {H : Type u} [Group H] [Finite H] (n : ℕ) (hn : 2 ≤ n)
    (P₀ : Sylow 2 H) (φ : (P₀ : Subgroup H) →* Wreath (2 ^ n)) (hφ : Function.Injective φ)
    (K A : Subgroup H) [K.Normal] (hAc : IsCyclic A) (hAcard : Nat.card A = 2 ^ n)
    (hKA : K ⊔ A = ⊤) (hKAbot : K ⊓ A = ⊥) :
    (∃ N : Subgroup H, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∨
    ((∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* Original.Y (2 ^ n)) ∧
        Nat.card P = 2 * 2 ^ n) ∧
      (¬ ∃ K₀ : Subgroup K, K₀.Normal ∧ K₀.index = 2) ∧
      ∀ i : K, orderOf i = 2 → CFSG.oddCore K ⊔ Subgroup.centralizer ({i} : Set K) = ⊤) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardH : Nat.card H = Nat.card K * 2 ^ n := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer K A
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      (disjoint_iff.mpr hKAbot)
    rw [hKA, Subgroup.card_top, hAcard] at h
    exact h
  have hKindex : K.index = 2 ^ n := by
    have h := K.card_mul_index
    rw [hcardH] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := n) hAcard
  obtain ⟨P, hAP⟩ := hA2.exists_le_sylow
  let ψ : (P : Subgroup H) →* Wreath (2 ^ n) := φ.comp (Sylow.equiv P P₀).toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp (Sylow.equiv P P₀).injective
  have hPKtop : (P : Subgroup H) ⊔ K = ⊤ := by
    rw [sup_comm, eq_top_iff, ← hKA]
    exact sup_le_sup_left hAP K
  have hrel : K.relIndex (P : Subgroup H) = 2 ^ n := by
    rw [← Subgroup.relIndex_sup_right (P : Subgroup H) K, hPKtop, Subgroup.relIndex_top_right,
      hKindex]
  have hcardPK : 2 ^ n * Nat.card (K ⊓ (P : Subgroup H) : Subgroup H) =
      Nat.card (P : Subgroup H) := by
    rw [← hrel]
    exact Subgroup.relIndex_mul_card K P
  let X' : Subgroup (Wreath (2 ^ n)) := (K.subgroupOf P).map ψ
  let A' : Subgroup (Wreath (2 ^ n)) := (A.subgroupOf P).map ψ
  have eX : K.subgroupOf P ≃* X' := (K.subgroupOf P).equivMapOfInjective ψ hψ
  have eA : A.subgroupOf P ≃* A' := (A.subgroupOf P).equivMapOfInjective ψ hψ
  have eKP : K.subgroupOf P ≃* (K ⊓ (P : Subgroup H) : Subgroup H) :=
    (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right K P).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have eAP : A.subgroupOf P ≃* A := Subgroup.subgroupOfEquivOfLe hAP
  have hA'c : IsCyclic A' := eA.isCyclic.mp (eAP.isCyclic.mpr hAc)
  have hA'card : Nat.card A' = 2 ^ n := by
    rw [← Nat.card_congr eA.toEquiv, Nat.card_congr eAP.toEquiv, hAcard]
  have hA'N : A' ≤ Subgroup.normalizer (X' : Set (Wreath (2 ^ n))) := by
    have hnorm : (K.subgroupOf P).Normal :=
      Subgroup.Normal.subgroupOf (inferInstance : K.Normal) (P : Subgroup H)
    have htop : Subgroup.normalizer ((K.subgroupOf P : Subgroup P) : Set P) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hnorm
    calc A' ≤ (Subgroup.normalizer ((K.subgroupOf P : Subgroup P) : Set P)).map ψ := by
          rw [htop]
          exact Subgroup.map_mono le_top
      _ ≤ Subgroup.normalizer (X' : Set (Wreath (2 ^ n))) := Subgroup.le_normalizer_map ψ
  have hX'A' : X' ⊓ A' = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ _ hψ, eq_bot_iff]
    rintro _ ⟨p, ⟨hpK, hpA⟩, rfl⟩
    have hp : (p : H) ∈ K ⊓ A := ⟨hpK, hpA⟩
    rw [hKAbot, Subgroup.mem_bot] at hp
    have hp1 : p = 1 := Subtype.ext hp
    rw [hp1, map_one]
    exact Subgroup.one_mem _
  rcases CyclicDisjointActor.maximal_cyclic_disjoint_actor_forces_cyclic_kernel_or_full_wreath
      n hn A' X' hA'c hA'card hA'N hX'A' with hXc | ⟨-, -, hX'card, hA'U, -⟩
  ·
    left
    obtain ⟨Q₀, hQ₀⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
    have eQ : (Q₀ : Subgroup K) ≃* X' :=
      (((MulEquiv.subgroupCongr hQ₀).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans
        ((MulEquiv.subgroupCongr (inf_comm _ _)).trans eKP.symm)).trans eX
    exact normal_two_complement_of_normal_cyclic_sylow K ⟨n, hKindex⟩ Q₀ (eQ.isCyclic.mpr hXc)
  ·
    have hcardX : Nat.card (K ⊓ (P : Subgroup H) : Subgroup H) = 2 * 2 ^ n := by
      rw [← Nat.card_congr eKP.toEquiv, Nat.card_congr eX.toEquiv, hX'card]
    have hcardP : Nat.card (P : Subgroup H) = Nat.card (Wreath (2 ^ n)) := by
      rw [← hcardPK, hcardX, card_wreath]
      ring
    have hbij : Function.Bijective ψ := hψ.bijective_of_nat_card_le hcardP.ge
    let e : (P : Subgroup H) ≃* Wreath (2 ^ n) := MulEquiv.ofBijective ψ hbij
    have hAB : A ≤ modelBase P e := by
      intro a ha
      let p : (P : Subgroup H) := ⟨a, hAP ha⟩
      have hpA' : ψ p ∈ A' := Subgroup.mem_map_of_mem ψ (show p ∈ A.subgroupOf P from ha)
      have hpU : ψ p ∈ baseSubgroup (2 ^ n) := by
        rw [← Original.U_eq]
        exact hA'U hpA'
      refine ⟨ψ p, hpU, ?_⟩
      change ((e.symm (e p) : (P : Subgroup H)) : H) = a
      rw [MulEquiv.symm_apply_apply]
    have hSK : Nat.card ((P : Subgroup H) ⊓ K : Subgroup H) = 2 * 2 ^ n := by
      rw [inf_comm, hcardX]
    exact split_actor_of_full_wreath n hn P e K A hAc hAcard hKA hKAbot hAB hKindex hSK

end CFSG.Wreathed.SplitCyclicActor
