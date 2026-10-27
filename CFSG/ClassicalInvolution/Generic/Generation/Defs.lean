module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

@[expose] def centMembers (Ω : Set (Subgroup G)) (a : G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ L ≤ Subgroup.centralizer ({a} : Set G)}

@[expose] def centLayer (Ω : Set (Subgroup G)) (a : G) : Subgroup G :=
  ⨆ L ∈ centMembers Ω a, L

@[expose] def centSpan (Ω : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, ⨆ (_ : a ≠ 1), centLayer Ω a

variable {Ω : Set (Subgroup G)}

theorem mem_centMembers {a : G} {L : Subgroup G} :
    L ∈ centMembers Ω a ↔ L ∈ Ω ∧ L ≤ Subgroup.centralizer ({a} : Set G) :=
  Iff.rfl

theorem mem_centMembers_iff_commute {a : G} {L : Subgroup G} :
    L ∈ centMembers Ω a ↔ L ∈ Ω ∧ ∀ k ∈ L, k * a = a * k := by
  refine and_congr_right fun _ => ⟨fun h k hk => ?_, fun h k hk => ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp (h hk)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (h k hk)

theorem le_centLayer {a : G} {L : Subgroup G} (hL : L ∈ centMembers Ω a) : L ≤ centLayer Ω a :=
  le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ centMembers Ω a) => L) L hL

theorem centLayer_le {a : G} {H : Subgroup G} (h : ∀ L ∈ centMembers Ω a, L ≤ H) :
    centLayer Ω a ≤ H :=
  iSup₂_le h

theorem le_centSpan {A : Subgroup G} {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    centLayer Ω a ≤ centSpan Ω A :=
  le_iSup₂_of_le a ha (le_iSup (fun _ : a ≠ 1 => centLayer Ω a) ha1)

theorem centSpan_le {A H : Subgroup G} (h : ∀ a ∈ A, a ≠ 1 → centLayer Ω a ≤ H) :
    centSpan Ω A ≤ H :=
  iSup₂_le fun a ha => iSup_le fun ha1 => h a ha ha1

theorem centSpan_mono {A B : Subgroup G} (h : A ≤ B) : centSpan Ω A ≤ centSpan Ω B :=
  centSpan_le fun _ ha ha1 => le_centSpan (h ha) ha1

theorem le_centSpan_of_commute {A L : Subgroup G} (hL : L ∈ Ω) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hc : ∀ k ∈ L, k * a = a * k) : L ≤ centSpan Ω A :=
  (le_centLayer (mem_centMembers_iff_commute.mpr ⟨hL, hc⟩)).trans (le_centSpan ha ha1)

variable (hΩ : ConjInvariant Ω)
include hΩ

theorem conjSub_mem_centMembers {n a : G} {L : Subgroup G} (hL : L ∈ centMembers Ω a) :
    conjSub n L ∈ centMembers Ω (n * a * n⁻¹) := by
  refine mem_centMembers_iff_commute.mpr ⟨hΩ n L hL.1, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h := (mem_centMembers_iff_commute.mp hL).2 _ hx
  calc x * (n * a * n⁻¹) = n * ((n⁻¹ * x * n) * a) * n⁻¹ := by group
    _ = n * (a * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
    _ = n * a * n⁻¹ * x := by group

theorem conjSub_centLayer_le (n a : G) :
    conjSub n (centLayer Ω a) ≤ centLayer Ω (n * a * n⁻¹) := by
  have key : centLayer Ω a ≤ conjSub n⁻¹ (centLayer Ω (n * a * n⁻¹)) := by
    refine centLayer_le fun L hL => ?_
    have h1 := le_centLayer (conjSub_mem_centMembers hΩ (n := n) hL)
    have h2 := conjSub_mono (n := n⁻¹) h1
    rwa [conjSub_inv_conjSub] at h2
  have h := conjSub_mono (n := n) key
  rwa [conjSub_conjSub_inv] at h

theorem conjSub_centLayer (n a : G) :
    conjSub n (centLayer Ω a) = centLayer Ω (n * a * n⁻¹) := by
  refine le_antisymm (conjSub_centLayer_le hΩ n a) ?_
  have h := conjSub_mono (n := n) (conjSub_centLayer_le hΩ n⁻¹ (n * a * n⁻¹))
  rw [conjSub_conjSub_inv] at h
  have e : n⁻¹ * (n * a * n⁻¹) * n⁻¹⁻¹ = a := by group
  rw [e] at h
  exact h

theorem conjSub_centSpan_le (n : G) (A : Subgroup G) :
    conjSub n (centSpan Ω A) ≤ centSpan Ω (conjSub n A) := by
  have key : centSpan Ω A ≤ conjSub n⁻¹ (centSpan Ω (conjSub n A)) := by
    refine centSpan_le fun a ha ha1 => ?_
    have hna : n * a * n⁻¹ ∈ conjSub n A := conj_mem_conjSub ha
    have hne : n * a * n⁻¹ ≠ 1 := by
      intro h
      apply ha1
      have := congrArg (fun t => n⁻¹ * t * n) h
      simpa [mul_assoc] using this
    have h1 := le_centSpan (Ω := Ω) hna hne
    rw [← conjSub_centLayer hΩ n a] at h1
    have h2 := conjSub_mono (n := n⁻¹) h1
    rwa [conjSub_inv_conjSub] at h2
  have h := conjSub_mono (n := n) key
  rwa [conjSub_conjSub_inv] at h

theorem conjSub_centSpan (n : G) (A : Subgroup G) :
    conjSub n (centSpan Ω A) = centSpan Ω (conjSub n A) := by
  refine le_antisymm (conjSub_centSpan_le hΩ n A) ?_
  have h := conjSub_mono (n := n) (conjSub_centSpan_le hΩ n⁻¹ (conjSub n A))
  rw [conjSub_conjSub_inv, conjSub_inv_conjSub] at h
  exact h

omit hΩ in
theorem mem_normalizer_of_conjSub_eq {n : G} {X : Subgroup G} (h : conjSub n X = X) :
    n ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : n * x * n⁻¹ ∈ conjSub n X ↔ x ∈ X := by
    rw [mem_conjSub_iff]
    simp [mul_assoc]
  rw [h] at hx
  exact hx.symm

theorem normalizer_le_normalizer_centSpan (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (centSpan Ω A : Set G) := by
  intro n hn
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_centSpan hΩ, conjSub_eq_of_mem_normalizer hn]

end CFSG.ClassicalInvolution.Generic
