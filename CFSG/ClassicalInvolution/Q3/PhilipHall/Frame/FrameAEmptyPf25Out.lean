module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D CFSG.ClassicalInvolution.Asc77.T3CII Equiv

section Finite

abbrev P3 : Type := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

@[expose] def signEq : Subgroup P3 where
  carrier := {x | Perm.sign x.1 = Perm.sign x.2}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at *
    rw [ha]

theorem sign_of_invol : ∀ p : Perm (Fin 3), p ≠ 1 → p * p = 1 → Perm.sign p = -1 := by decide

theorem cube_of_sign : ∀ p : Perm (Fin 3), Perm.sign p = 1 → p ^ 3 = 1 := by decide

@[expose] def evenPart : Subgroup P3 :=
  (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))

theorem card_evenPart : Nat.card evenPart = 9 := by
  have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  unfold evenPart
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, h3]

theorem card_units_int : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_two_iff]
  exact ⟨1, -1, by decide, by
    ext u
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    rcases Int.units_eq_one_or u with h | h <;> simp [h]⟩

theorem card_of_signEq {H : Subgroup P3} (hH : H ≤ signEq) (hodd : ∃ x ∈ H, Perm.sign x.1 = -1) :
    Nat.card H = 2 ∨ Nat.card H = 6 ∨ Nat.card H = 18 := by
  let φ : H →* ℤˣ := Perm.sign.comp (MonoidHom.fst _ _ |>.comp H.subtype)
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨x, hx, hxs⟩ := hodd
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨⟨x, hx⟩, hxs⟩
  have hcardr : Nat.card φ.range = 2 := by
    rw [hrange, Subgroup.card_top, card_units_int]
  have hmul : Nat.card H = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker)
  have hker : φ.ker.map H.subtype ≤ evenPart := by
    rintro _ ⟨⟨x, hx⟩, hxk, rfl⟩
    have h1 : Perm.sign x.1 = 1 := hxk
    have h2 : Perm.sign x.2 = 1 := by rw [← hH hx]; exact h1
    refine ⟨?_, ?_⟩
    · exact (Equiv.Perm.mem_alternatingGroup).mpr h1
    · exact (Equiv.Perm.mem_alternatingGroup).mpr h2
  have hdvd : Nat.card φ.ker ∣ 9 := by
    have h1 : Nat.card (φ.ker.map H.subtype) ∣ Nat.card evenPart := Subgroup.card_dvd_of_le hker
    rw [card_evenPart] at h1
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h1
  rw [hmul, hcardr]
  have : Nat.card φ.ker ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [h9] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h <;> rw [h] <;> simp

end Finite

section Alt

theorem eq_of_card_two {H : Subgroup P3} (h2 : Nat.card H = 2) {a b : P3} (ha : a ∈ H)
    (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
  have h1 : (⟨a, ha⟩ : H) = y := hy _ (fun h => ha1 (congrArg Subtype.val h))
  have h2' : (⟨b, hb⟩ : H) = y := hy _ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2'.symm)

theorem perm3_eq_one_of_even_invol : ∀ p : Perm (Fin 3), p * p = 1 → Perm.sign p = 1 → p = 1 := by
  decide

@[expose] def Frame203Psi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      ∃ ψ : ↥(sec20X (CoreAssembly.conjClass K) z K K') →* P3,
        ψ.ker = (oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')).subgroupOf
            (sec20X (CoreAssembly.conjClass K) z K K') ∧
          (∀ x, Perm.sign (ψ x).1 = Perm.sign (ψ x).2) ∧
          V ≤ sec20X (CoreAssembly.conjClass K) z K K' ∧
          ∃ (v : G) (hv : v ∈ sec20X (CoreAssembly.conjClass K) z K K'),
            v ∈ V ∧ v * v ∈ K ⊔ K' ∧ ψ ⟨v, hv⟩ ≠ 1

end Alt

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
