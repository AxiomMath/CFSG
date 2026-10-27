module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.A1cTransferVariants
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.C3.Layer2

open Subgroup CFSG CFSG.ABGLocalTools

theorem exists_conj_mem_of_simple {G : Type*} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {Q : Subgroup G} (hQP : Q ≤ P)
    (hindex : Q.relIndex (P : Subgroup G) = 2) {u : G} (hu : orderOf u = 2) :
    ∃ g : G, g⁻¹ * u * g ∈ Q := by
  by_contra hno
  push Not at hno
  obtain ⟨N, hN, hsq, huN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal P hQP hindex hu hno
  rcases hN.eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hx : ∀ x : G, x * x = 1 := fun x => by
      have := hsq x
      rw [h, Subgroup.mem_bot, sq] at this
      exact this
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hx (a * b))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (hx a), inv_eq_of_mul_eq_one_right (hx b)]
  · exact huN (by rw [h]; exact Subgroup.mem_top u)

theorem exists_mem_conj_le_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K X : Subgroup G} (hP : IsSylowOf p P K) (hXK : X ≤ K) (hX : IsPGroup p X) :
    ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ P := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

private theorem centralizer_map_equiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G}
    {P' : Subgroup G'} (e : ↥P ≃* ↥P') {g : G} (hg : g ∈ P) {w : G} (hw : w ∈ P)
    (hwc : w ∈ centralizer ({g} : Set G)) :
    ((e ⟨w, hw⟩ : ↥P') : G') ∈ centralizer ({((e ⟨g, hg⟩ : ↥P') : G')} : Set G') := by
  have h1 : (⟨w, hw⟩ : ↥P) * ⟨g, hg⟩ = ⟨g, hg⟩ * ⟨w, hw⟩ :=
    Subtype.ext (mem_centralizer_singleton_iff.1 hwc)
  have h2 := congrArg (fun y => ((e y : ↥P') : G')) h1
  simp only [map_mul, Subgroup.coe_mul] at h2
  exact mem_centralizer_singleton_iff.2 h2

theorem card_centralizer_inf_equiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G}
    {P' : Subgroup G'} (e : ↥P ≃* ↥P') {g : G} (hg : g ∈ P) :
    Nat.card ↥(centralizer ({g} : Set G) ⊓ P) =
      Nat.card ↥(centralizer ({((e ⟨g, hg⟩ : ↥P') : G')} : Set G') ⊓ P') := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun w => ⟨((e ⟨(w : G), w.2.2⟩ : ↥P') : G'),
        centralizer_map_equiv e hg w.2.2 w.2.1, (e _).2⟩
      invFun := fun w => ⟨((e.symm ⟨(w : G'), w.2.2⟩ : ↥P) : G), by
        have h := centralizer_map_equiv e.symm (g := ((e ⟨g, hg⟩ : ↥P') : G'))
          (e ⟨g, hg⟩).2 (w := (w : G')) w.2.2 w.2.1
        have h3 : e.symm ⟨((e ⟨g, hg⟩ : ↥P') : G'), (e ⟨g, hg⟩).2⟩ = ⟨g, hg⟩ := by simp
        rw [h3] at h
        exact h, (e.symm _).2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem card_alt_factorization (n : ℕ) (hn : n = 6 ∨ n = 7) :
    (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 = 7 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  rcases hn with rfl | rfl <;>
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide +kernel

end CFSG.GH74.GLS.C3.Layer2
