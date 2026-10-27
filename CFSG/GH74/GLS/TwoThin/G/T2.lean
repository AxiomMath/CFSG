module

public import CFSG.GH74.GLS.TwoThin.G.Section
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.A7.Core
public import CFSG.GH74.Generic.Context
public import CFSG.CharacterTheory.Burnside
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.GH74.GLS.TwoThin.KGroupCore

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank

theorem solvable_centralizer_of_hasL2Model {K : Type} [Group K] [Finite K]
    (h : HasL2Model K (fun q => Odd q ∧ 3 < q)) (z : K) (hz : orderOf z = 2) :
    Group.IsSolvable ↥(centralizer ({z} : Set K)) := by
  obtain ⟨p, f, hp, hf, ⟨hodd, h3⟩, hL⟩ := h
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
  have hL2F : IVK.L2Field F := ⟨hF ▸ hodd, hF ▸ h3⟩
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have := Nat.odd_iff.mp hL2F.1
    omega
  have h3F : 3 < Nat.card F := hL2F.2
  have hdih : ∃ d : ℕ, IVK.IsDihedralOrder ↥(centralizer ({z} : Set K)) d := by
    rcases hmod with hm | hm
    · obtain ⟨-, hd, -⟩ := IVK.ivk_1_3a F hL2F K e 1 (Or.inl rfl)
        (by simp only [Int.ModEq]; omega) (Nat.card F - 1) (by omega) z hz
      exact ⟨_, hd⟩
    · obtain ⟨-, hd, -⟩ := IVK.ivk_1_3a F hL2F K e (-1) (Or.inr rfl)
        (by simp only [Int.ModEq]; omega) (Nat.card F + 1) (by omega) z hz
      exact ⟨_, hd⟩
  obtain ⟨d, k, -, hk, ⟨eD⟩⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  have hD := CFSG.LinearGroups.isSolvable_dihedralGroup k
  exact Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective

theorem solvable_centralizer_of_alt7 {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) (z : K) (hz : orderOf z = 2) :
    Group.IsSolvable ↥(centralizer ({z} : Set K)) := by
  classical
  let f : K →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.injective
  set u : Equiv.Perm (Fin 7) := f z with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← map_pow]
    have : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    rw [this, map_one]
  have hune : u ≠ 1 := by
    intro h1
    have : z = 1 := hfinj (by rw [← hu, h1, map_one])
    rw [this, orderOf_one] at hz
    omega
  have hsign : Equiv.Perm.sign u = 1 := by
    have := (e z).2
    exact Equiv.Perm.mem_alternatingGroup.mp this
  have hct : u.cycleType = {2, 2} := by
    rcases IVK.A7.involution_cycleType u hu2 hune with h | h | h
    · exfalso
      rw [Equiv.Perm.sign_of_cycleType, h] at hsign
      exact absurd hsign (by decide)
    · exact h
    · exfalso
      rw [Equiv.Perm.sign_of_cycleType, h] at hsign
      exact absurd hsign (by decide)
  have hcard : Nat.card ↥(centralizer ({u} : Set (Equiv.Perm (Fin 7)))) = 48 :=
    IVK.A7.card_centralizer_S7_two_two hct
  have hsolv : Group.IsSolvable ↥(centralizer ({u} : Set (Equiv.Perm (Fin 7)))) := by
    have : Fintype ↥(centralizer ({u} : Set (Equiv.Perm (Fin 7)))) := Fintype.ofFinite _
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 4) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  let g : ↥(centralizer ({z} : Set K)) →* ↥(centralizer ({u} : Set (Equiv.Perm (Fin 7)))) :=
    (f.comp (centralizer ({z} : Set K)).subtype).codRestrict _ (fun c => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
      show f c * u = u * f c
      rw [hu, ← map_mul, ← map_mul, hc])
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := Subtype.ext_iff.mp hab
    exact Subtype.ext (hfinj h1)
  exact Group.isSolvable_of_isSolvable_injective hginj

theorem twoThinT2Vertical
    : TwoThinT2Vertical := by
  intro L _ _ _ I K₀ _ _ hT hz _ _ hK₀ hφ
  obtain ⟨φ, hφs, hφo⟩ := hφ
  have hsolv : ∀ z : L, orderOf z = 2 → Group.IsSolvable ↥(centralizer ({z} : Set L)) := by
    rcases inT2_cases_of_center_bot hT hz with hL2 | hA7
    · obtain ⟨p, f, hp, hf, ⟨hodd, hnfm⟩, hL⟩ := hL2
      have hq3 : 3 < p ^ f := by
        have hp2 : 2 ≤ p ^ f := (hp.one_lt).trans_le (Nat.le_self_pow (by omega) p)
        by_contra h
        have h3 : p ^ f = 3 := by
          obtain ⟨k, hk⟩ := hodd
          omega
        exact hnfm (by
          rw [h3]
          exact Or.inr ⟨Nat.prime_three, Or.inl ⟨0, by norm_num⟩⟩)
      exact fun z hz => solvable_centralizer_of_hasL2Model ⟨p, f, hp, hf, ⟨hodd, hq3⟩, hL⟩ z hz
    · obtain ⟨e⟩ := hA7
      exact fun z hz => solvable_centralizer_of_alt7 e z hz
  exact false_of_solvable_centralizers hK₀ φ hφs hφo hsolv

theorem twoThinT2VerticalP
    (P : GroupPred) : TwoThinT2VerticalP P := by
  intro L _ _ σ I K₀ _ _ hq hT hz hσ hI hK₀ hφ
  exact twoThinT2Vertical L σ I K₀ hq hT hz hσ hI hK₀ hφ

end CFSG.GH74.GLS.TwoThin
