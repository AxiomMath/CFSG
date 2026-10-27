module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoBLocalBound

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeABaby

theorem card_centralizer_subtype {G : Type*} [Group G] {C : Subgroup G} (u : C) :
    Nat.card (Subgroup.centralizer ({u} : Set C)) =
      Nat.card (C ⊓ Subgroup.centralizer ({(u : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun k => ⟨(k.1 : G), k.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp k.2))⟩
      invFun := fun m => ⟨⟨m.1, m.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2.2))⟩
      left_inv := fun k => rfl
      right_inv := fun m => rfl }

end CFSG.HardMathSupport.Dickson.I271.TabMThreeABaby

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

section Baby


theorem card_centralizer_inf_le_of_twoA_inv (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hB3 : TabBThreeACard) {t α k : G} (ht : IsConj a t) (hα : α ∈ twoANbr a t)
    (hk3 : orderOf k = 3) (hkt : k ∈ Subgroup.centralizer ({t} : Set G))
    (hαk : α * k * α⁻¹ = k⁻¹) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
      3 * 258247006617600 := by
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj I.sls hG ht).exists_cover
  obtain ⟨hαC, hαW⟩ := (mem_twoANbr_iff I.sls I.tableV I.leech I.tableIII hG ht hφ).1 hα
  let k' : ↥(Subgroup.centralizer ({t} : Set G)) := ⟨k, hkt⟩
  have hk'3 : orderOf k' = 3 := by rw [← Subgroup.orderOf_coe]; exact hk3
  have hs3 : orderOf (φ k') = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow, ← hk'3, pow_orderOf_eq_one, map_one]
    · have hmem : k ∈ φ.ker.map (Subgroup.centralizer ({t} : Set G)).subtype := ⟨k', h1, rfl⟩
      rw [hφ.ker_eq] at hmem
      rcases (mem_zpowers_iff_of_orderOf_eq_two hφ.orderOf_eq).1 hmem with h | h
      · rw [h, orderOf_one] at hk3
        exact absurd hk3 (by norm_num)
      · rw [h, hφ.orderOf_eq] at hk3
        exact absurd hk3 (by norm_num)
  have hinv : coverMap φ α * φ k' * (coverMap φ α)⁻¹ = (φ k')⁻¹ := by
    have h1 := coverMap_conj (φ := φ) hαC hkt
    rw [hαk, coverMap_inv hkt, coverMap_apply hkt] at h1
    exact h1.symm
  have hB : Nat.card (Subgroup.centralizer ({φ k'} : Set B)) ≤ 387370509926400 :=
    hB3 (φ k') hs3 ⟨coverMap φ α, hαW, hinv⟩
  have hker : Nat.card φ.ker = 2 := by
    have h1 : Nat.card ↥(φ.ker.map (Subgroup.centralizer ({t} : Set G)).subtype) =
        Nat.card ↥φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.centralizer ({t} : Set G)).subtype_injective
    rw [hφ.ker_eq, Nat.card_zpowers, hφ.orderOf_eq] at h1
    exact h1.symm
  haveI : Finite B := Finite.of_surjective φ hφ.surjective
  let e : ↥(Subgroup.centralizer ({t} : Set G)) ⧸ φ.ker ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ.surjective
  have hcard := @card_centralizer_le_mul ↥(Subgroup.centralizer ({t} : Set G)) B _
    Units.instGroup _ _ φ.ker _ e k'
  have he : e (QuotientGroup.mk k') = φ k' := rfl
  rw [he] at hcard
  have hKinf : Nat.card ↥(φ.ker ⊓ Subgroup.centralizer ({k'} :
      Set ↥(Subgroup.centralizer ({t} : Set G)))) ≤ 2 := by
    have h := Subgroup.card_le_of_le (inf_le_left : φ.ker ⊓ Subgroup.centralizer ({k'} :
      Set ↥(Subgroup.centralizer ({t} : Set G))) ≤ φ.ker)
    omega
  have h3 : Nat.card (Subgroup.centralizer ({k'} :
      Set ↥(Subgroup.centralizer ({t} : Set G)))) ≤ 2 * 387370509926400 :=
    hcard.trans (Nat.mul_le_mul hKinf hB)
  rw [TabMThreeABaby.card_centralizer_subtype] at h3
  calc _ ≤ 2 * 387370509926400 := h3
    _ = 3 * 258247006617600 := by norm_num

end Baby

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
