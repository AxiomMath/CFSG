module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderAlt
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderMax

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type} [Group G]

@[expose] def SectionEquiv (U M : Subgroup G) {d : ℕ} (π : ↥U →* Multiplicative (altHeart d))
    (θ : ↥M →* Perm (Fin d)) : Prop :=
  ∀ (m : ↥M) (u u' : ↥U), (u' : G) = (m : G) * u * (m : G)⁻¹ →
    ∀ x : evenWeight d, Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart d) →
      Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm (θ m) x) : altHeart d)

theorem altFix_index_le [Finite G] {U M A : Subgroup G} {d : ℕ}
    {π : ↥U →* Multiplicative (altHeart d)} (hπ : Function.Surjective π)
    {θ : ↥M →* Perm (Fin d)} (hequiv : SectionEquiv U M π θ) :
    (altFix d ((A.subgroupOf M).map θ)).index ≤
      (Subgroup.centralizer (A : Set G)).relIndex U := by
  set E := (A.subgroupOf M).map θ with hE
  let K : Subgroup (Multiplicative (altHeart d)) := AddSubgroup.toSubgroup (altFix d E)
  let C : Subgroup ↥U := K.comap π
  have hidx : C.index = (altFix d E).index := by
    rw [Subgroup.index_comap_of_surjective K hπ, AddSubgroup.index_toSubgroup]
  have hle : (Subgroup.centralizer (A : Set G)).subgroupOf U ≤ C := by
    intro u hu
    have hu' : u ∈ (Subgroup.centralizer (A : Set G)).subgroupOf U := hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hu'
    show π u ∈ K
    show Multiplicative.toAdd (π u) ∈ altFix d E
    rw [mem_altFix_iff]
    rintro g ⟨a, ha, rfl⟩ x hx
    have haA : ((a : ↥M) : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have hax : ((a : ↥M) : G) * (u : G) * ((a : ↥M) : G)⁻¹ = (u : G) :=
      mul_inv_eq_iff_eq_mul.2 (hu' (a : G) haA)
    exact (hequiv a u u hax.symm x hx.symm).symm
  have := Subgroup.index_dvd_of_le hle
  rw [← hidx]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) this

theorem relIndex_le_card_image [Finite G] {M A : Subgroup G} {d : ℕ} (V : Subgroup G)
    (hAM : A ≤ M) (θ : ↥M →* Perm (Fin d))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G)) :
    (Subgroup.centralizer (V : Set G)).relIndex A ≤ Nat.card ↥((A.subgroupOf M).map θ) := by
  set A' := A.subgroupOf M with hA'
  let f := θ.domRestrict A'
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = A'.map θ := MonoidHom.domRestrict_range A' θ
  have hAA' : Nat.card ↥A' = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  have hkerle : Nat.card ↥f.ker ≤ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ A) := by
    let g : f.ker → ↥(Subgroup.centralizer (V : Set G) ⊓ A) := fun a =>
      ⟨((a.1 : ↥A') : ↥M), hker _ (by
        have := a.2
        rw [MonoidHom.mem_ker] at this
        exact this), a.1.2⟩
    refine Nat.card_le_card_of_injective g ?_
    intro a b hab
    have : (((a.1 : ↥A') : ↥M) : G) = (((b.1 : ↥A') : ↥M) : G) :=
      congrArg (fun z : ↥(Subgroup.centralizer (V : Set G) ⊓ A) => (z : G)) hab
    apply Subtype.ext
    apply Subtype.ext
    exact Subtype.ext this
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (V : Set G)) A
  have hpos : 0 < Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ A) := Nat.card_pos
  rw [hrange, hAA'] at h1
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ A) = Nat.card ↥A := h2
    _ = Nat.card ↥f.ker * Nat.card ↥(A'.map θ) := h1.symm
    _ ≤ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ A) * Nat.card ↥(A'.map θ) :=
        Nat.mul_le_mul_right _ hkerle
    _ = Nat.card ↥(A'.map θ) * Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ A) := by ring

theorem offender_of_section [Finite G] {S M A V U : Subgroup G} {d : ℕ}
    {π : ↥U →* Multiplicative (altHeart d)} (hπ : Function.Surjective π)
    {θ : ↥M →* Perm (Fin d)} (hequiv : SectionEquiv U M π θ)
    (hV : IsElemAb2 V) (hVS : V ≤ S) (hUV : U ≤ V) (hA : IsElemAb2 A) (hAS : A ≤ S) (hAM : A ≤ M)
    (hmax : ∀ B : Subgroup G, B ≤ S → IsElemAb2 B → Nat.card B ≤ Nat.card A)
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G)) :
    (altFix d ((A.subgroupOf M).map θ)).index ≤ Nat.card ↥((A.subgroupOf M).map θ) := by
  have h1 := altFix_index_le hπ hequiv (A := A)
  have h2 := relIndex_le_of_max hV hVS hUV hA hAS hmax
  have h3 : (S ⊓ Subgroup.centralizer (V : Set G)).relIndex A =
      (Subgroup.centralizer (V : Set G)).relIndex A := by
    have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (V : Set G)) S A
    rw [Subgroup.relIndex_eq_one.2 hAS, mul_one, inf_eq_right.2 hAS] at this
    rw [inf_comm, ← this]
  have h4 := relIndex_le_card_image V hAM θ hker
  exact le_trans h1 (le_trans h2 (h3 ▸ h4))

theorem offender_shape_of_section [Finite G] {S M A V U : Subgroup G} {d : ℕ} (hd : d = 7 ∨ 9 ≤ d)
    {π : ↥U →* Multiplicative (altHeart d)} (hπ : Function.Surjective π)
    {θ : ↥M →* Perm (Fin d)} (hequiv : SectionEquiv U M π θ)
    (hV : IsElemAb2 V) (hVS : V ≤ S) (hUV : U ≤ V) (hA : IsElemAb2 A) (hAS : A ≤ S) (hAM : A ≤ M)
    (hmax : ∀ B : Subgroup G, B ≤ S → IsElemAb2 B → Nat.card B ≤ Nat.card A)
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G)) :
    OffenderShapeConcl ((A.subgroupOf M).map θ) := by
  refine offender_shape_altHeart hd _ ?_ (offender_of_section hπ hequiv hV hVS hUV hA hAS hAM hmax hker)
  rintro g ⟨a, ha, rfl⟩
  have : (a * a : ↥M) = 1 := by
    apply Subtype.ext
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.1 ha
    exact (hA a haA).1
  rw [← map_mul, this, map_one]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
