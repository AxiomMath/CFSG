module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.HSStd.HOv

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.EvenSporadicStandard.HSStd.HL34

variable {D : Type*} [Group D]

theorem isElemAbelian_subgroupOf_inf {A : Subgroup D} (S : Subgroup D)
    (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2 ((A ⊓ S).subgroupOf S) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have h := hA.1.is_comm.comm (⟨x.1.1, x.2.1⟩ : A) ⟨y.1.1, y.2.1⟩
    have h' : (x.1.1 : D) * y.1.1 = y.1.1 * x.1.1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · exact Subtype.ext (by simpa using hA.2 x.1 hx.1)

theorem exists_card_eq_mul_outer [Finite D] (S : Subgroup D) [S.Normal]
    (hC : centralizer (S : Set D) = ⊥) {A : Subgroup D} (hA : ∀ a ∈ A, a * a = 1) :
    ∃ r : ℕ, Nat.card A = Nat.card ↥(A ⊓ S) * r ∧ r ∣ Nat.card (Outer ↥S) ∧
      ∃ k : ℕ, r = 2 ^ k := by
  let ρ : D →* MulAut ↥S := actionHom S (MulEquiv.refl ↥S)
  let f : ↥A →* Outer ↥S := (QuotientGroup.mk' (inner ↥S)).comp (ρ.comp A.subtype)
  have hρS : ∀ s : ↥S, ρ (s : D) = MulAut.conj s := fun s => by
    refine MulEquiv.ext fun x => ?_
    show MulAut.conjNormal (s : D) x = _
    rw [MulAut.conjNormal_val]
  have hker : ∀ a : ↥A, a ∈ f.ker ↔ (a : D) ∈ S := by
    intro a
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (ρ (a : D)) : Outer ↥S) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨s, hs⟩
      have h1 : ρ ((a : D) * (s : D)⁻¹) = 1 := by
        rw [map_mul, map_inv, hρS, hs, mul_inv_cancel]
      have h2 := (actionHom_eq_one_iff S (MulEquiv.refl ↥S) _).1 h1
      rw [hC, mem_bot, mul_inv_eq_one] at h2
      rw [h2]
      exact s.2
    · intro h
      exact ⟨⟨a, h⟩, (hρS ⟨a, h⟩).symm⟩
  have hkc : Nat.card f.ker = Nat.card ↥(A ⊓ S) :=
    Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, (hker a.1).1 a.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, (hker ⟨b.1, b.2.1⟩).2 b.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card A = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hAp : IsPGroup 2 ↥A := fun g => ⟨1, by
    refine Subtype.ext ?_
    simpa [pow_two] using hA g g.2⟩
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hdvd : Nat.card f.range ∣ 2 ^ n := by
    rw [← hn, hcard]
    exact Dvd.intro_left _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨Nat.card f.range, by rw [hcard, hkc], Subgroup.card_subgroup_dvd_card _, k, hk⟩

end CFSG.EvenSporadicStandard.HSStd.HOv
