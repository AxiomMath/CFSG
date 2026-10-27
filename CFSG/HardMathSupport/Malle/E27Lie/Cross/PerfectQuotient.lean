module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Subgroup

theorem not_sylow_le_center_of_perfect {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hperf : commutator G = ⊤) (hp : p ∣ Nat.card G) (P : Sylow p G) :
    ¬ (P : Subgroup G) ≤ center G := by
  intro hPc
  have hnorm : normalizer (P : Subgroup G) ≤ centralizer (P : Set G) := by
    intro g _ x hx
    exact (mem_center_iff.mp (hPc hx) g).symm
  have : (P : Subgroup G).FiniteIndex := inferInstance
  have hcomm : ∀ a b : (P : Subgroup G), a * b = b * a := fun a b =>
    Subtype.ext (hnorm (le_normalizer b.2) a a.2)
  have htriv : ∀ g : G, MonoidHom.transferSylow P hnorm g = 1 := by
    intro g
    have hg : g ∈ commutator G := by rw [hperf]; exact mem_top g
    have hmap := Subgroup.mem_map_of_mem (MonoidHom.transferSylow P hnorm) hg
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at hmap
    have hbot : ⁅(MonoidHom.transferSylow P hnorm).range,
        (MonoidHom.transferSylow P hnorm).range⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha b hb
      exact (hcomm a b).symm
    rw [hbot] at hmap
    exact hmap
  have hP1 : ∀ g : (P : Subgroup G), g = 1 := by
    intro g
    have h1 := MonoidHom.transferSylow_eq_pow P hnorm (g : G) g.2
    rw [htriv] at h1
    have h2 : g ^ (P : Subgroup G).index = 1 := by
      have := congrArg Subtype.val h1.symm
      exact Subtype.ext (by simpa using this)
    have hinj := (P.2.powEquiv' P.not_dvd_index).injective
    exact hinj (by simpa using h2)
  have hcard : Nat.card (P : Subgroup G) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hP1 a).trans (hP1 b).symm⟩, ⟨1⟩⟩
  rw [Sylow.card_eq_multiplicity] at hcard
  have hfac : 1 ≤ (Nat.card G).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization Fact.out (Nat.card_pos).ne').mp hp
  have : p ^ 1 ≤ p ^ (Nat.card G).factorization p := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hfac
  rw [hcard, pow_one] at this
  have := (Fact.out : p.Prime).two_le
  omega

theorem dvd_card_quotient_of_perfect {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hperf : commutator G = ⊤) (hp : p ∣ Nat.card G) {N : Subgroup G} [N.Normal]
    (hN : N ≤ center G) : p ∣ Nat.card (G ⧸ N) := by
  by_contra hnd
  have hidx : ¬ p ∣ N.index := hnd
  have hcardN : Nat.card N * N.index = Nat.card G := N.card_mul_index
  obtain ⟨P'⟩ : Nonempty (Sylow p N) := inferInstance
  have hfac : (Nat.card G).factorization p = (Nat.card N).factorization p := by
    have h := congrArg (fun m => m.factorization p) hcardN.symm
    rw [Nat.factorization_mul (Nat.card_pos).ne' (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero] at h
    exact h
  have hcard : Nat.card (P'.toSubgroup.map N.subtype) = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  let P : Sylow p G := Sylow.ofCard (P'.toSubgroup.map N.subtype) hcard
  refine not_sylow_le_center_of_perfect hperf hp P ?_
  exact (Subgroup.map_subtype_le _).trans hN

end CFSG.HardMathSupport.Malle.E27Lie
