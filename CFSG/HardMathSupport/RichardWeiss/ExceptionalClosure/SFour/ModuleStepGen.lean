module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.ModuleStep
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Support

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pi_commutator_eq_one_of_rel_mul_free {X M : Subgroup G} {d : ℕ}
    (π : ↥X →* Multiplicative (altHeart d)) (θ : ↥M →* Perm (Fin d))
    (hequiv : SectionEquiv X M π θ) {g δ u w : G} (hgM : g ∈ M) (hδM : δ ∈ M)
    (hXn : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X) (hu : u ∈ X) (hw : w ∈ X) {x' : G} (hx' : x' ∈ X) (hx1 : π ⟨x', hx'⟩ = 1)
    (hrel : (g * w * g⁻¹) * u = x' * ((δ * u * δ⁻¹) * w))
    (T Γ : Finset (Fin d)) (hfree : ∃ i, i ∉ T ∧ i ∉ Γ)
    (hdis : Disjoint T Γ) (hc : ∀ x ∉ T, θ ⟨g, hgM⟩ x = x)
    (hf : ∀ x ∉ Γ, θ ⟨δ, hδM⟩ x = x) :
    ∃ h : ⁅δ, u⁆ ∈ X, π ⟨⁅δ, u⁆, h⟩ = 1 := by
  classical
  have hgw : g * w * g⁻¹ ∈ X := hXn g hgM w hw
  have hδu : δ * u * δ⁻¹ ∈ X := hXn δ hδM u hu
  have hcomm : ⁅δ, u⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem hδu (X.inv_mem hu)
  refine ⟨hcomm, ?_⟩
  obtain ⟨xu, hxu⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π ⟨u, hu⟩))
  obtain ⟨xw, hxw⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π ⟨w, hw⟩))
  have h1 : Multiplicative.toAdd (π ⟨g * w * g⁻¹, hgw⟩) =
      (QuotientAddGroup.mk (evenWeightPerm (θ ⟨g, hgM⟩) xw) : altHeart d) :=
    hequiv ⟨g, hgM⟩ ⟨w, hw⟩ ⟨g * w * g⁻¹, hgw⟩ rfl xw hxw.symm
  have h2 : Multiplicative.toAdd (π ⟨δ * u * δ⁻¹, hδu⟩) =
      (QuotientAddGroup.mk (evenWeightPerm (θ ⟨δ, hδM⟩) xu) : altHeart d) :=
    hequiv ⟨δ, hδM⟩ ⟨u, hu⟩ ⟨δ * u * δ⁻¹, hδu⟩ rfl xu hxu.symm
  have hmul : (⟨g * w * g⁻¹, hgw⟩ * ⟨u, hu⟩ : ↥X) = ⟨x', hx'⟩ * (⟨δ * u * δ⁻¹, hδu⟩ * ⟨w, hw⟩) :=
    Subtype.ext hrel
  have hπ := congrArg (fun x => Multiplicative.toAdd (π x)) hmul
  simp only [map_mul, toAdd_mul, hx1, toAdd_one, zero_add] at hπ
  rw [h1, h2, ← hxu, ← hxw] at hπ
  set f := θ ⟨δ, hδM⟩ with hfdef
  set c := θ ⟨g, hgM⟩ with hcdef
  have hz : (QuotientAddGroup.mk ((evenWeightPerm f xu - xu) - (evenWeightPerm c xw - xw)) :
      altHeart d) = 0 := by
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub]
    exact altHeart_sub_aux _ _ _ _ hπ
  have hz' := (QuotientAddGroup.eq_zero_iff _).1 hz
  have h0 : evenWeightPerm f xu - xu = 0 :=
    ewp_sub_eq_zero_of_free_point f c T Γ hfree hdis hc hf xw xu hz'
  have hcm : (⟨⁅δ, u⁆, hcomm⟩ : ↥X) = ⟨δ * u * δ⁻¹, hδu⟩ * ⟨u, hu⟩⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [hcm, map_mul, map_inv]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, h2, ← hxu, toAdd_one]
  rw [← sub_eq_add_neg, ← QuotientAddGroup.mk_sub, h0]
  simp

theorem pi_commutator_eq_one_of_rel_mul {X M : Subgroup G} {d : ℕ}
    (π : ↥X →* Multiplicative (altHeart d)) (θ : ↥M →* Perm (Fin d))
    (hequiv : SectionEquiv X M π θ) {g δ u w : G} (hgM : g ∈ M) (hδM : δ ∈ M)
    (hXn : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X) (hu : u ∈ X) (hw : w ∈ X) {x' : G}
    (hx' : x' ∈ X) (hx1 : π ⟨x', hx'⟩ = 1)
    (hrel : (g * w * g⁻¹) * u = x' * ((δ * u * δ⁻¹) * w))
    (hd : 7 < d) (T Γ : Finset (Fin d)) (hT : T.card ≤ 3) (hΓ : Γ.card ≤ 4)
    (hdis : Disjoint T Γ) (hc : ∀ x ∉ T, θ ⟨g, hgM⟩ x = x)
    (hf : ∀ x ∉ Γ, θ ⟨δ, hδM⟩ x = x) :
    ∃ h : ⁅δ, u⁆ ∈ X, π ⟨⁅δ, u⁆, h⟩ = 1 := by
  classical
  have hlt : (T ∪ Γ).card < (Finset.univ : Finset (Fin d)).card := by
    have := Finset.card_union_le T Γ
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_union, not_or] at hi0
  exact pi_commutator_eq_one_of_rel_mul_free π θ hequiv hgM hδM hXn hu hw hx' hx1 hrel T Γ
    ⟨i0, hi0⟩ hdis hc hf

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
