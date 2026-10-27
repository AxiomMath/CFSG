module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
@[expose] def omega1 (D : Subgroup G) (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) : Subgroup G where
  carrier := {x | x ∈ D ∧ x ^ 2 = 1}
  mul_mem' := fun {a b} ha hb => ⟨D.mul_mem ha.1 hb.1, by
    rw [(show Commute a b from hD a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨D.one_mem, one_pow 2⟩
  inv_mem' := fun {a} ha => ⟨D.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

omit [Finite G] in
theorem mem_omega1_iff {hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x} {x : G} :
    x ∈ omega1 D hD ↔ x ∈ D ∧ x ^ 2 = 1 := Iff.rfl

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.card_omega1 (hsq : ∀ d ∈ D, d ^ 2 ∈ A) : Nat.card (omega1 D hD.comm) = 2 ^ 8 := by
  have hmap : omega1 D hD.comm = (sqD hD hsq).ker.map D.subtype := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 (Subtype.ext hx2), rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.2, congrArg (fun a : ↥A => (a : G)) (MonoidHom.mem_ker.1 hd)⟩
  rw [hmap, Subgroup.card_map_of_injective D.subtype_injective]
  exact H.card_ker_sqD W W2 hD hsq

theorem ThCyc.A_le_omega1 : A ≤ omega1 D hD.comm := fun a ha =>
  ⟨hD.Aa_le (W2.A_le ha), W.A_sq a ha⟩

theorem ThCyc.omega1_inf_Aa : omega1 D hD.comm ⊓ Aa = A := by
  refine le_antisymm (fun x ⟨hx, hxA⟩ => W2.mem_A_of_sq_eq_one W hxA hx.2)
    (le_inf (H.A_le_omega1 W W2 hD) (W2.A_le))

theorem ThCyc.omega1_inf_centralizer_t :
    omega1 D hD.comm ⊓ centralizer ({t} : Set G) = A := by
  refine le_antisymm ?_ (le_inf (H.A_le_omega1 W W2 hD) ?_)
  · rintro x ⟨hx, hxc⟩
    have hxAa : x ∈ Aa := by
      refine (H.D_theta_eq_one_iff W W2 hD hx.1).1 ?_
      have h1 : x * t = t * x := mem_centralizer_singleton_iff.1 hxc
      calc theta t x = (x * t) * x⁻¹ * t⁻¹ := rfl
        _ = 1 := by rw [h1]; group
    exact W2.mem_A_of_sq_eq_one W hxAa hx.2
  · intro a ha
    exact mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (le_trans
      (fun y hy => ((W.mem_A_iff y).1 hy).1) W.S_le ha)).symm

theorem ThCyc.normalizer_le_normalizer_omega1 :
    normalizer ((W5 A t : Subgroup G) : Set G) ≤ normalizer (omega1 D hD.comm : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ⟨hD.norm n hn x hx.1, ?_⟩, fun hx => ?_⟩
  · calc (n * x * n⁻¹) ^ 2 = n * x ^ 2 * n⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hx.2]; group
  · have hn' := (normalizer _).inv_mem hn
    have h1 := hD.norm n⁻¹ hn' (n * x * n⁻¹) hx.1
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rw [e] at h1
    refine ⟨h1, ?_⟩
    have h2 : (n * x * n⁻¹) ^ 2 = 1 := hx.2
    calc x ^ 2 = n⁻¹ * (n * x * n⁻¹) ^ 2 * n := by rw [sq, sq]; group
      _ = 1 := by rw [h2]; group

end

end CFSG.EvenSporadicStandard.ThStd
