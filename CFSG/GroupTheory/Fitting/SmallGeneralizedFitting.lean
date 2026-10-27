module

public import CFSG.Foundations.Basic

import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem card_eq_one_of_card_generalizedFitting_eq_one
    (h : Nat.card (CFSG.generalizedFitting G) = 1) : Nat.card G = 1 := by
  let F := CFSG.generalizedFitting G
  have hB : Subgroup.centralizer (F : Set G) ≤ F := CFSG.centralizer_generalizedFitting_le G
  have hF : F = ⊥ := Subgroup.eq_bot_of_card_eq F h
  have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    simp
  have hB' := hB
  rw [hF] at hB'
  have htop : (⊤ : Subgroup G) ≤ ⊥ := hc ▸ hB'
  have htriv : ∀ g : G, g = 1 := by
    intro g
    have hg : g ∈ (⊥ : Subgroup G) := htop (Subgroup.mem_top g)
    simpa using hg
  haveI : Subsingleton G := ⟨fun a b => by rw [htriv a, htriv b]⟩
  exact Nat.card_unique

private theorem centralizer_generalizedFitting_eq_of_card_eq_three
    (h : Nat.card (CFSG.generalizedFitting G) = 3) :
    Subgroup.centralizer (CFSG.generalizedFitting G : Set G) =
      CFSG.generalizedFitting G := by
  let F := CFSG.generalizedFitting G
  have hB : Subgroup.centralizer (F : Set G) ≤ F := CFSG.centralizer_generalizedFitting_le G
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic F := isCyclic_of_prime_card h
  letI : IsCyclic F := hcyc
  refine le_antisymm hB ?_
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance

theorem card_dvd_six_of_card_generalizedFitting
    (h : Nat.card (CFSG.generalizedFitting G) = 1 ∨
      Nat.card (CFSG.generalizedFitting G) = 3) :
    Nat.card G ∣ 6 := by
  let F := CFSG.generalizedFitting G
  rcases h with h1 | h3
  · rw [card_eq_one_of_card_generalizedFitting_eq_one h1]
    norm_num
  · have hFn : F.Normal := by
      change (CFSG.generalizedFitting G).Normal
      rw [CFSG.generalizedFitting_eq_componentClassification]
      exact CFSG.ComponentClassification.GeneralizedFitting.normal G
    letI : F.Normal := hFn
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic F := isCyclic_of_prime_card h3
    letI : IsCyclic F := hcyc
    have hcent : Subgroup.centralizer (F : Set G) = F := by
      simpa [F] using centralizer_generalizedFitting_eq_of_card_eq_three h3
    let φ : G →* MulAut F := MulAut.conjNormal
    have hker : φ.ker = F := by
      ext g
      rw [MonoidHom.mem_ker]
      have hmem : g ∈ F ↔ g ∈ Subgroup.centralizer (F : Set G) := by rw [hcent]
      rw [hmem, Subgroup.mem_centralizer_iff]
      constructor
      · intro hg y hy
        have hconj : g * (y : G) * g⁻¹ = (y : G) := by
          have := congrArg (fun a : MulAut F => ((a ⟨y, hy⟩ : F) : G)) hg
          simpa [φ, MulAut.conjNormal_apply, MulAut.one_apply] using this
        exact ((mul_inv_eq_iff_eq_mul).mp hconj).symm
      · intro hg
        ext y
        change g * (y : G) * g⁻¹ = (y : G)
        rw [← hg y y.2, mul_inv_cancel_right]
    have hidx : F.index ∣ 2 := by
      have hkeridx : F.index = φ.ker.index := by rw [hker]
      rw [hkeridx, Subgroup.index_ker]
      refine (Subgroup.card_subgroup_dvd_card φ.range).trans ?_
      have haut : Nat.card (MulAut F) = 2 := by
        rw [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three]
      rwa [haut]
    have hG : Nat.card G = 3 * F.index := by
      have hcard := Subgroup.card_mul_index F
      rw [h3] at hcard
      omega
    rw [hG]
    exact Nat.mul_dvd_mul_left 3 hidx

theorem nonempty_mulEquiv_perm_three_of_card_generalizedFitting
    (h : Nat.card (CFSG.generalizedFitting G) = 1 ∨
      Nat.card (CFSG.generalizedFitting G) = 3)
    (heven : Even (Nat.card G)) : Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  let F := CFSG.generalizedFitting G
  rcases h with h1 | h3
  · rw [card_eq_one_of_card_generalizedFitting_eq_one h1] at heven
    norm_num at heven
  · have hdvd : Nat.card G ∣ 6 := card_dvd_six_of_card_generalizedFitting (Or.inr h3)
    have h3dvd : 3 ∣ Nat.card G := by
      have hcard := Subgroup.card_subgroup_dvd_card F
      rwa [h3] at hcard
    have h2dvd : 2 ∣ Nat.card G := even_iff_two_dvd.mp heven
    have h6 : Nat.card G = 6 := by
      have h6dvd : 6 ∣ Nat.card G :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2dvd h3dvd
      exact Nat.dvd_antisymm hdvd h6dvd
    have hcent : Subgroup.centralizer (F : Set G) = F := by
      simpa [F] using centralizer_generalizedFitting_eq_of_card_eq_three h3
    have hFne : F ≠ ⊤ := by
      intro htop
      have hcard : Nat.card F = Nat.card G := by rw [htop, Subgroup.card_top]
      have h36 : (3 : ℕ) = 6 := by rw [← h3, hcard, h6]
      norm_num at h36
    obtain ⟨x, -, hxF⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hFne)
    have hxcent : x ∉ Subgroup.centralizer (F : Set G) := by rwa [hcent]
    have hxnot : ¬ ∀ y ∈ F, y * x = x * y := by
      intro hx
      exact hxcent (Subgroup.mem_centralizer_iff.mpr hx)
    push Not at hxnot
    obtain ⟨y, -, hxy⟩ := hxnot
    exact CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 ⟨y, x, hxy⟩

end CFSG.GroupTheory
