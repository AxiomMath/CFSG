module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshGL3Action
import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshGL3Facts
import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

private theorem pow_four_eq_one_of_commutators {G : Type*} [Group G] (A : Subgroup G) (c ℓ : G)
    (hcc : c * c = 1) (hℓc : ℓ * c * ℓ⁻¹ = c) (hAsq : ∀ a ∈ A, a * a = 1)
    (hCA : ∀ y : G, (∀ a ∈ A, y * a = a * y) → y ∈ A)
    (h : ∀ a ∈ A, ℓ * a * ℓ⁻¹ * a⁻¹ = 1 ∨ ℓ * a * ℓ⁻¹ * a⁻¹ = c) : ℓ ^ 4 = 1 := by
  have hsq : ℓ * ℓ ∈ A := by
    refine hCA _ fun a ha => ?_
    obtain ⟨x, hx, hxℓ, hxx⟩ :
        ∃ x : G, ℓ * a * ℓ⁻¹ * a⁻¹ = x ∧ ℓ * x * ℓ⁻¹ = x ∧ x * x = 1 := by
      rcases h a ha with h1 | h1
      · exact ⟨1, h1, by simp, by simp⟩
      · exact ⟨c, h1, hℓc, hcc⟩
    have e1 : ℓ * a * ℓ⁻¹ = x * a := by rw [← hx]; group
    have e2 : ℓ * ℓ * a * (ℓ * ℓ)⁻¹ = a :=
      calc ℓ * ℓ * a * (ℓ * ℓ)⁻¹ = ℓ * (ℓ * a * ℓ⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (x * a) * ℓ⁻¹ := by rw [e1]
        _ = (ℓ * x * ℓ⁻¹) * (ℓ * a * ℓ⁻¹) := by group
        _ = x * (x * a) := by rw [hxℓ, e1]
        _ = (x * x) * a := (mul_assoc x x a).symm
        _ = a := by rw [hxx, one_mul]
    exact mul_inv_eq_iff_eq_mul.1 e2
  calc ℓ ^ 4 = (ℓ * ℓ) * (ℓ * ℓ) := by simp [pow_succ, mul_assoc]
    _ = 1 := hAsq _ hsq

private theorem card_subgroupOf_eq_two_pow {G : Type*} [Group G] [Finite G] (S L : Subgroup G)
    (hSL : S ≤ L) (hS : Nat.card S = 2 ^ (Nat.card G).factorization 2) :
    Nat.card (S.subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := by
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hLG : (Nat.card L).factorization 2 = (Nat.card G).factorization 2 := by
    refine le_antisymm
      ((Nat.factorization_le_iff_dvd hL0 hG0).2 (Subgroup.card_subgroup_dvd_card L) 2) ?_
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hL0).1 ?_
    rw [← hS]
    exact Subgroup.card_dvd_of_le hSL
  rw [hLG, ← hS]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv

theorem exists_hom_gl3_ker_eq {G : Type*} [Group G] [Finite G]
    (E S A L : Subgroup G) (c v₁ v₂ v₃ : G)
    (hSsyl : Nat.card S = 2 ^ (Nat.card G).factorization 2) (hSL : S ≤ L)
    (hLc : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ = c)
    (hA : A = Subgroup.closure ({c, v₁, v₂, v₃} : Set G))
    (hAcard : Nat.card A = 16) (hAsq : ∀ a ∈ A, a * a = 1)
    (hLA : ∀ ℓ ∈ L, ∀ a ∈ A, ℓ * a * ℓ⁻¹ ∈ A)
    (hCA : ∀ y : G, (∀ a ∈ A, y * a = a * y) → y ∈ A)
    (hEA : ∀ y ∈ E, ∀ a ∈ A, ⁅y, a⁆ = 1 ∨ ⁅y, a⁆ = c)
    (hSA : ∀ y ∈ S, (∀ a ∈ A, ⁅y, a⁆ = 1 ∨ ⁅y, a⁆ = c) → y ∈ E) :
    ∃ ρ : ↥L →* GL (Fin 3) (ZMod 2), ∀ ℓ : ↥L, ρ ℓ = 1 ↔ (ℓ : G) ∈ E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcA : c ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hcc : c * c = 1 := hAsq c hcA
  obtain ⟨ρ, hρ⟩ := exists_hom_gl3 L A c v₁ v₂ v₃ hA hAcard hAsq hLA hLc
  have hpg : IsPGroup 2 ρ.ker := fun g => ⟨2, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using pow_four_eq_one_of_commutators A c (g : ↥L) hcc (hLc _ (g : ↥L).2) hAsq hCA
      ((hρ g).1 (MonoidHom.mem_ker.1 g.2))⟩
  have hle : ρ.ker ≤ (Sylow.ofCard (S.subgroupOf L)
      (card_subgroupOf_eq_two_pow S L hSL hSsyl) : Subgroup ↥L) := hpg.le_sylow_of_normal _
  refine ⟨ρ, fun ℓ => ⟨fun h1 => ?_, fun hℓ => (hρ ℓ).2 fun a ha => hEA _ hℓ a ha⟩⟩
  exact hSA _ (hle (MonoidHom.mem_ker.2 h1)) fun a ha => (hρ ℓ).1 h1 a ha

theorem le_commutator_of_fusion {G : Type*} [Group G] (E L : Subgroup G) (e u : G)
    (heL : e ∈ L) (he2 : e * e = 1)
    (hfu : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = u) (hfue : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = u * e)
    (hgen : ∀ y ∈ E, y ∈ Subgroup.closure {z : G | ∃ ℓ ∈ L, z = ℓ * e * ℓ⁻¹}) :
    E ≤ ⁅L, L⁆ := by
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  obtain ⟨ℓ₁, hℓ₁, h₁⟩ := hfu
  obtain ⟨ℓ₂, hℓ₂, h₂⟩ := hfue
  have hu : u ∈ ⁅L, L⁆ := by
    have h := Subgroup.commutator_mem_commutator hℓ₂ heL
    rwa [commutatorElement_def, h₂, mul_inv_cancel_right] at h
  have hue : u * e⁻¹ ∈ ⁅L, L⁆ := by
    have h := Subgroup.commutator_mem_commutator hℓ₁ heL
    rwa [commutatorElement_def, h₁] at h
  have he : e ∈ ⁅L, L⁆ := by
    have h := ⁅L, L⁆.mul_mem (⁅L, L⁆.inv_mem hu) hue
    rwa [inv_mul_cancel_left, heinv] at h
  have hconj : ∀ ℓ ∈ L, ℓ * e * ℓ⁻¹ ∈ ⁅L, L⁆ := fun ℓ hℓ => by
    have h := ⁅L, L⁆.mul_mem (Subgroup.commutator_mem_commutator hℓ heL) he
    rwa [commutatorElement_def, inv_mul_cancel_right] at h
  intro y hy
  refine (Subgroup.closure_le ⁅L, L⁆).2 ?_ (hgen y hy)
  rintro z ⟨ℓ, hℓ, rfl⟩
  exact hconj ℓ hℓ

set_option linter.unusedVariables false in
theorem normalizer_quotient_gl3 {G : Type*} [Group G] [Finite G]
    (E S A L : Subgroup G) (c e u v₁ v₂ v₃ : G)
    (hL : L = Subgroup.normalizer (E : Set G))
    (hSsyl : Nat.card S = 2 ^ (Nat.card G).factorization 2)
    (hES : E ≤ S) (hSL : S ≤ L)
    (hcE : c ∈ E) (hEcomm : ∀ y ∈ E, ∀ z ∈ E, ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = c)
    (hLc : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ = c)
    (hA : A = Subgroup.closure ({c, v₁, v₂, v₃} : Set G)) (hAE : A ≤ E)
    (hAcard : Nat.card A = 16) (hAsq : ∀ a ∈ A, a * a = 1)
    (hLA : ∀ ℓ ∈ L, ∀ a ∈ A, ℓ * a * ℓ⁻¹ ∈ A)
    (hCA : ∀ y : G, (∀ a ∈ A, y * a = a * y) → y ∈ A)
    (hEA : ∀ y ∈ E, ∀ a ∈ A, ⁅y, a⁆ = 1 ∨ ⁅y, a⁆ = c)
    (hSA : ∀ y ∈ S, (∀ a ∈ A, ⁅y, a⁆ = 1 ∨ ⁅y, a⁆ = c) → y ∈ E)
    (hcard : Nat.card L = 168 * Nat.card E)
    (heE : e ∈ E) (huE : u ∈ E) (he2 : e * e = 1) (hu2 : u * u = 1) (heu : e * u = u * e)
    (hfu : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = u)
    (hfue : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = u * e)
    (hgen : ∀ y ∈ E, y ∈ Subgroup.closure {z : G | ∃ ℓ ∈ L, z = ℓ * e * ℓ⁻¹}) :
    haveI : (E.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hL.le
    Nonempty (↥L ⧸ E.subgroupOf L ≃* GL (Fin 3) (ZMod 2)) ∧ ⁅L, L⁆ = L ∧
      ∀ z ∈ L, (∀ ℓ ∈ L, ⁅z, ℓ⁆ ∈ E) → z ∈ E := by
  haveI : (E.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hL.le
  obtain ⟨ρ, hρ⟩ := exists_hom_gl3_ker_eq E S A L c v₁ v₂ v₃ hSsyl hSL hLc hA hAcard hAsq hLA hCA
    hEA hSA
  have hEL : E ≤ L := hES.trans hSL
  have hquot := quotient_equiv_gl3 L E hEL ρ hρ hcard
  obtain ⟨φ⟩ := hquot
  have hEc : E ≤ ⁅L, L⁆ :=
    le_commutator_of_fusion E L e u (hSL (hES heE)) he2 hfu hfue hgen
  have hEc' : E.subgroupOf L ≤ commutator ↥L := fun x hx => by
    have h1 : L.subtype x ∈ (commutator ↥L).map L.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hEc hx
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 h1
  haveI : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := Group.isPerfect_def.2 commutator_gl32
  haveI : Group.IsPerfect (↥L ⧸ E.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2
    (commutator_eq_top_of_quotient_perfect (E.subgroupOf L) hEc' Group.IsPerfect.commutator_eq_top)
  exact ⟨⟨φ⟩, Subgroup.commutator_eq_self, center_quotient_trivial L E hEL ρ hρ hcard⟩

end CFSG.EvenSporadicStandard.M12Std.Yosh
