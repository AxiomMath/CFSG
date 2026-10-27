module

public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section ZJ

variable {X : Type} [Group X]

theorem zjSubgroup_eq_closure (p : ℕ) (R : Subgroup X) :
    zjSubgroup p R = Subgroup.closure {x : X | x ∈ thompsonCenter R ∧ x ^ p = 1} := by
  unfold zjSubgroup omega₁ CFSG.omega
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, pow_one]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
  · rintro ⟨hy, hyp⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyp), rfl⟩

theorem zjSubgroup_le (p : ℕ) (R : Subgroup X) : zjSubgroup p R ≤ R :=
  (Subgroup.map_subtype_le _).trans (thompsonCenter_le R)

theorem thompsonCenter_map_of_injective' [Finite X] {Y : Type} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Injective f) (R : Subgroup X) :
    (thompsonCenter R).map f = thompsonCenter (R.map f) := by
  let e : R ≃* R.map f := R.equivMapOfInjective f hf
  have hcomp : f.comp R.subtype = (R.map f).subtype.comp e.toMonoidHom := by
    ext x
    simp [e]
  rw [← thompsonCenter_top_map_subtype R, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    thompsonCenter_top_map_mulEquiv e, thompsonCenter_top_map_subtype]

theorem zjSubgroup_conjugate [Finite X] (p : ℕ) (R : Subgroup X) (g : X) :
    zjSubgroup p (conjugate R g) = conjugate (zjSubgroup p R) g := by
  have hc : ∀ A : Subgroup X, conjugate A g = A.map (MulAut.conj g⁻¹).toMonoidHom := fun A => rfl
  set f : X →* X := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  rw [hc, hc, zjSubgroup_eq_closure, zjSubgroup_eq_closure, MonoidHom.map_closure,
    ← thompsonCenter_map_of_injective' f hfinj]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hyp⟩
    refine ⟨x, ⟨hx, hfinj ?_⟩, rfl⟩
    rw [map_pow, hyp, map_one]
  · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, hxp, map_one]⟩

theorem normalizer_thompsonCenter_le_normalizer_zjSubgroup [Finite X] (p : ℕ) (R : Subgroup X) :
    normalizer (thompsonCenter R : Set X) ≤ normalizer (zjSubgroup p R : Set X) := by
  have hchar : (omega₁ (G := thompsonCenter (G := X) R) (p := p)).Characteristic :=
    omega₁_characteristic (G := thompsonCenter (G := X) R) (p := p)
  exact section8_normalizer_map_subtype_le_of_characteristic
    (H := thompsonCenter (G := X) R) (K := omega₁ (G := thompsonCenter (G := X) R) (p := p))

theorem normalizer_le_normalizer_zjSubgroup [Finite X] (p : ℕ) (_hp : p.Prime) (R : Subgroup X) :
    normalizer (R : Set X) ≤ normalizer (zjSubgroup p R : Set X) :=
  (normalizer_le_normalizer_thompsonCenter R).trans
    (normalizer_thompsonCenter_le_normalizer_zjSubgroup p R)

theorem zjSubgroup_ne_bot [Finite X] (p : ℕ) (hp : p.Prime) {R : Subgroup X} (hR : IsPGroup p R)
    (hne : R ≠ ⊥) : zjSubgroup p R ≠ ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hJne : thompsonCenter R ≠ ⊥ := section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hR hne
  have hJp : IsPGroup p (thompsonCenter R) := hR.to_le (thompsonCenter_le R)
  have hpdiv : p ∣ Nat.card (thompsonCenter R) := by
    rcases IsPGroup.card_eq_or_dvd hJp with hcard | hdiv
    · exact absurd ((Subgroup.card_eq_one (H := thompsonCenter R)).mp hcard) hJne
    · exact hdiv
  exact omega₁_map_subtype_ne_bot (thompsonCenter R) p hpdiv

end ZJ

section Glauberman

variable {X : Type} [Group X] [Finite X]

theorem le_normalizer_zjSubgroup_of_odd {p : ℕ} (hp : p.Prime) {H R : Subgroup X}
    (hR : ABGLocalTools.IsSylowOf p R H) (hHodd : Odd (Nat.card H))
    (hOp : pPrimeCore p ↥H = ⊥) : H ≤ normalizer (zjSubgroup p R : Set X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsSolvable ↥H := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥H hHodd
  obtain ⟨S, rfl⟩ := hR
  have h62 := theorem_6_2 (G := ↥H) hHodd S
  rw [hOp, sup_bot_eq] at h62
  have hN : (thompsonCenter (S : Subgroup ↥H)).Normal := h62
  have hle := ABGLocalTools.le_normalizer_map_subtype H (thompsonCenter (S : Subgroup ↥H))
  rw [thompsonCenter_map_of_injective' H.subtype H.subtype_injective] at hle
  exact hle.trans (normalizer_thompsonCenter_le_normalizer_zjSubgroup p _)

end Glauberman

end CFSG.GH74.Uniqueness
