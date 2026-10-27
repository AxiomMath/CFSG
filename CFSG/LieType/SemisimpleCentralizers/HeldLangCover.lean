module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.1 hz b).symm
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_mul_central {G : Type*} [Group G] {a b z z' : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_central hz, ← commutatorElement_inv, commutatorElement_mul_central hz',
    commutatorElement_inv]

variable {S L X : Type} [Group S] [Group L] [Group X]

@[expose] def fibreProduct (πL : L →* X) (πS : S →* X) : Subgroup (L × S) :=
  MonoidHom.eqLocus (πL.comp (MonoidHom.fst L S)) (πS.comp (MonoidHom.snd L S))

theorem nonempty_mulEquiv_of_central_covers [Finite S] [Finite L]
    (πS : S →* X) (πL : L →* X) (hS : Function.Surjective πS) (hL : Function.Surjective πL)
    (hcL : πL.ker ≤ Subgroup.center L) (hperf : Group.IsPerfect L)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : S →* E, ∀ g, π (s g) = g)
    (hker : Nat.card πS.ker ≤ Nat.card πL.ker) : Nonempty (S ≃* L) := by
  classical
  let E : Subgroup (L × S) := fibreProduct πL πS
  let π : E →* S := (MonoidHom.snd L S).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := hL (πS g)
    exact ⟨⟨(l, g), hl⟩, rfl⟩
  have hπc : π.ker ≤ Subgroup.center E := by
    intro x hx
    obtain ⟨⟨l, s⟩, hxm⟩ := x
    have hs : s = 1 := hx
    subst hs
    have hl : l ∈ Subgroup.center L :=
      hcL (by rw [MonoidHom.mem_ker]; exact (show πL l = πS 1 from hxm).trans (map_one πS))
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨l', s'⟩, hy⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Subgroup.mem_center_iff.1 hl l'
    · exact (mul_one s').trans (one_mul s').symm
  obtain ⟨s, hs⟩ := hsec E π hπ hπc
  let φ : S →* L := (MonoidHom.fst L S).comp (E.subtype.comp s)
  have hφ : ∀ g, πL (φ g) = πS g := by
    intro g
    calc πL (φ g) = πS (π (s g)) := (s g).2
      _ = πS g := by rw [hs g]
  have hdec : ∀ x : L, ∃ g : S, ∃ z ∈ Subgroup.center L, x = φ g * z := by
    intro x
    obtain ⟨g, hg⟩ := hS (πL x)
    refine ⟨g, (φ g)⁻¹ * x, ?_, by group⟩
    apply hcL
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hg, inv_mul_cancel]
  have hcomm : ∀ x y : L, ⁅x, y⁆ ∈ φ.range := by
    intro x y
    obtain ⟨g, z, hz, rfl⟩ := hdec x
    obtain ⟨g', z', hz', rfl⟩ := hdec y
    rw [commutatorElement_mul_central_mul_central hz hz']
    exact ⟨⁅g, g'⁆, by simp [commutatorElement_def]⟩
  have hsurj : Function.Surjective φ := by
    have h1 : commutator L ≤ φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      exact fun x _ y _ => hcomm x y
    rw [hperf.commutator_eq_top] at h1
    intro x
    exact h1 (Subgroup.mem_top x)
  have hcardS : Nat.card S = Nat.card X * Nat.card πS.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πS.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πS hS).toEquiv]
  have hcardL : Nat.card L = Nat.card X * Nat.card πL.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πL.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πL hL).toEquiv]
  have hle : Nat.card S ≤ Nat.card L := by
    rw [hcardS, hcardL]
    exact Nat.mul_le_mul_left _ hker
  exact ⟨MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hle)⟩

end CFSG.LieType.SemisimpleCentralizers.HeldLang
