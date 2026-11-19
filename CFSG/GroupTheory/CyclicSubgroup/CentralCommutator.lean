module


public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory.CyclicSubgroup

theorem isCyclic_of_faithful_central_commutator {G : Type*} [Group G]
    (D X : Subgroup G) [IsCyclic X] (y : G)
    (hcent : D ≤ Subgroup.centralizer (X : Set G))
    (hcomm : ∀ d ∈ D, d * y * d⁻¹ * y⁻¹ ∈ X)
    (hfaith : ∀ d ∈ D, d * y = y * d → d = 1) :
    IsCyclic D := by
  let f : D →* X :=
    { toFun := fun d => ⟨d.1 * y * d.1⁻¹ * y⁻¹, hcomm d.1 d.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        have hb : (b.1 * y * b.1⁻¹ * y⁻¹) * a.1 = a.1 * (b.1 * y * b.1⁻¹ * y⁻¹) := by
          have := hcent a.2 (b.1 * y * b.1⁻¹ * y⁻¹) (hcomm b.1 b.2)
          simpa [mul_assoc] using this
        have hc : (a.1 * y * a.1⁻¹ * y⁻¹) * (b.1 * y * b.1⁻¹ * y⁻¹)
            = (b.1 * y * b.1⁻¹ * y⁻¹) * (a.1 * y * a.1⁻¹ * y⁻¹) := by
          let := IsCyclic.commGroup (α := X)
          have := mul_comm (⟨a.1 * y * a.1⁻¹ * y⁻¹, hcomm a.1 a.2⟩ : X)
            ⟨b.1 * y * b.1⁻¹ * y⁻¹, hcomm b.1 b.2⟩
          exact congrArg Subtype.val this
        ext
        simp only [Subgroup.coe_mul]
        rw [hc]
        calc (a.1 * b.1) * y * (a.1 * b.1)⁻¹ * y⁻¹
            = (a.1 * (b.1 * y * b.1⁻¹ * y⁻¹) * a.1⁻¹) *
                (a.1 * y * a.1⁻¹ * y⁻¹) := by group
          _ = _ := by rw [← hb]; group }
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro d hd
    have h1 : d.1 * y * d.1⁻¹ * y⁻¹ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hd)
      simpa [f] using this
    apply Subtype.ext
    apply hfaith d.1 d.2
    calc d.1 * y = (d.1 * y * d.1⁻¹ * y⁻¹) * (y * d.1) := by group
      _ = y * d.1 := by rw [h1, one_mul]
  have hcyc : IsCyclic f.range := by
    classical
    obtain ⟨g, hg⟩ := exists_zpow_surjective X
    by_cases hK : ∃ x : X, x ∈ f.range ∧ x ≠ (1 : X)
    · obtain ⟨x, hx₁, hx₂⟩ := hK
      obtain ⟨k, hk⟩ := hg x
      have hk : g ^ k = x := hk
      have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ f.range :=
        ⟨k.natAbs,
          Nat.pos_of_ne_zero fun h => hx₂ <| by
            rw [← hk, Int.natAbs_eq_zero.mp h, zpow_zero], by
              rcases k with k | k
              · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
                  ← Int.ofNat_eq_natCast, hk]
                exact hx₁
              · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff]; simp_all⟩
      refine ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ => ?_⟩⟩
      obtain ⟨k, hk⟩ := hg x
      have hk : g ^ k = x := hk
      have hk₂ : g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) ∈ f.range := by
        rw [zpow_mul]
        apply Subgroup.zpow_mem
        exact mod_cast (Nat.find_spec hex).2
      have hk₃ : g ^ (k % Nat.find hex : ℤ) ∈ f.range :=
        (Subgroup.mul_mem_cancel_right f.range hk₂).1 <| by
          rw [← zpow_add, Int.emod_add_mul_ediv, hk]; exact hx
      have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
        rw [Int.natAbs_of_nonneg
            (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
      have hk₅ : g ^ (k % Nat.find hex).natAbs ∈ f.range := by rwa [← zpow_natCast, ← hk₄]
      have hk₆ : (k % (Nat.find hex : ℤ)).natAbs = 0 :=
        by_contradiction fun h =>
          Nat.find_min hex
            (Int.ofNat_lt.1 <| by
              rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
            ⟨Nat.pos_of_ne_zero h, hk₅⟩
      exact ⟨k / (Nat.find hex : ℤ),
        Subtype.ext_iff.2
          (by
            suffices g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) = x by simpa [zpow_mul]
            rw [Int.mul_ediv_cancel'
                (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆)), hk])⟩
    · have hbot : f.range = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        by_contra hne
        exact hK ⟨x, hx, hne⟩
      rw [hbot]
      have : Subsingleton (⊥ : Subgroup X) :=
        ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
      exact isCyclic_of_subsingleton
  exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm
    (MonoidHom.ofInjective hinj).symm.surjective

end CFSG.GroupTheory.CyclicSubgroup
