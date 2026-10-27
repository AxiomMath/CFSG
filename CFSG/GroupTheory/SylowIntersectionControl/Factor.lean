module

public import CFSG.GroupTheory.SylowIntersectionControl.Defs
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_isSylowOf_inf_map_conj_le [Finite G] [Fact p.Prime] {E G₁ G₂ S : Subgroup G}
    (hS : IsSylowOf p S E) (h₁ : S ≤ G₁) (h₂ : S ≤ G₂) (hE : (G₁ : Set G) * G₂ = E) {g : G}
    (hg : g ∈ E) :
    ∃ U : Subgroup G, IsSylowOf p U E ∧ S ⊓ S.map (MulAut.conj g).toMonoidHom ≤ U ∧
      U ≤ G₁ ⊓ G₂.map (MulAut.conj g).toMonoidHom := by
  have hg' : g ∈ (G₁ : Set G) * G₂ := by
    rw [hE]
    exact hg
  obtain ⟨g₁, hg₁, g₂, hg₂, hgg⟩ := Set.mem_mul.mp hg'
  subst hgg
  have hG₁E : G₁ ≤ E := by
    intro x hx
    show x ∈ (E : Set G)
    rw [← hE]
    exact ⟨x, hx, 1, G₂.one_mem, mul_one x⟩
  have hg₁E : g₁ ∈ E := hG₁E hg₁
  have hG₁fix : G₁.map (MulAut.conj g₁).toMonoidHom = G₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg₁)
  have hEfix : E.map (MulAut.conj g₁).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg₁E)
  let T : Subgroup G := S.map (MulAut.conj g₁).toMonoidHom
  have hTE : IsSylowOf p T E := by
    rw [← hEfix]
    exact isSylowOf_map_conj hS g₁
  have hTW₁ : T ≤ G₁ := by
    rw [← hG₁fix]
    exact Subgroup.map_mono h₁
  have hTW₂ : T ≤ G₂.map (MulAut.conj (g₁ * g₂)).toMonoidHom := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨g₂⁻¹ * s * g₂, ?_, ?_⟩
    · exact G₂.mul_mem (G₂.mul_mem (G₂.inv_mem hg₂) (h₂ hs)) hg₂
    · change (MulAut.conj (g₁ * g₂)) (g₂⁻¹ * s * g₂) = (MulAut.conj g₁) s
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
  let W : Subgroup G := G₁ ⊓ G₂.map (MulAut.conj (g₁ * g₂)).toMonoidHom
  have hWE : W ≤ E := inf_le_left.trans hG₁E
  have hTW : T ≤ W := le_inf hTW₁ hTW₂
  have hTWsylow : IsSylowOf p T W := hTE.of_le hTW hWE
  let R : Subgroup G := S ⊓ S.map (MulAut.conj (g₁ * g₂)).toMonoidHom
  have hRp : IsPGroup p R := hS.isPGroup.to_inf_left
  have hRW : R ≤ W :=
    le_inf (inf_le_left.trans h₁) (inf_le_right.trans (Subgroup.map_mono h₂))
  obtain ⟨U, hRU, hUWsylow⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hRp hRW
  have hUE : U ≤ E := hUWsylow.le.trans hWE
  have hcardU : Nat.card U = Nat.card S := by
    rw [hUWsylow.card_eq, ← hTWsylow.card_eq,
      Subgroup.card_map_of_injective (MulAut.conj g₁).injective]
  refine ⟨U, isSylowOf_of_card hUE ?_, hRU, hUWsylow.le⟩
  rw [hcardU]
  exact hS.card_eq

private theorem sylowConjLink_lift_step [Finite G] [Fact p.Prime]
    {𝓔 𝓕 𝓓 : Set (Subgroup G)} {K D A B : Subgroup G}
    (h𝓔 : ∀ E ∈ 𝓔, E ≤ K) (h𝓕 : IsNormalSetIn 𝓕 K)
    (hind : ∀ X ∈ 𝓔 ∪ 𝓕, ¬ p ∣ X.relIndex K)
    (hfac : ∀ S : Subgroup G, IsSylowOf p S K → ∀ E ∈ sylowMembers p 𝓔 S,
      ∃ F₁ ∈ sylowMembers p 𝓕 S, ∃ F₂ ∈ sylowMembers p 𝓕 S,
        ((F₁ ⊓ E : Subgroup G) : Set G) * ((F₂ ⊓ E : Subgroup G) : Set G) = E)
    (h : SylowConjLink p (𝓔 ∪ 𝓓) K D A B) :
    Relation.ReflTransGen (SylowConjLink p (𝓕 ∪ 𝓓) K D) A B := by
  obtain ⟨hA, hB, X, hXA, hXB, hD, x, hxX, rfl⟩ := h
  obtain ⟨hXmem, hXsA⟩ := hXA
  obtain ⟨-, hXsB⟩ := hXB
  rcases hXmem with hX𝓔 | hX𝓓
  · obtain ⟨F₁, hF₁, F₂, hF₂, hfacX⟩ := hfac A hA X ⟨hX𝓔, hXsA⟩
    have hXK : X ≤ K := h𝓔 X hX𝓔
    have hindX : ¬ p ∣ X.relIndex K := hind X (Or.inl hX𝓔)
    have hAX : A ≤ X := le_of_isSylowOf_inf hA hXK hindX hXsA
    have hF₁K : F₁ ≤ K := h𝓕.1 F₁ hF₁.1
    have hF₂K : F₂ ≤ K := h𝓕.1 F₂ hF₂.1
    have hAF₁ : A ≤ F₁ :=
      le_of_isSylowOf_inf hA hF₁K (hind F₁ (Or.inr hF₁.1)) hF₁.2
    have hAF₂ : A ≤ F₂ :=
      le_of_isSylowOf_inf hA hF₂K (hind F₂ (Or.inr hF₂.1)) hF₂.2
    have hAsylowX : IsSylowOf p A X := by
      simpa only [inf_eq_left.mpr hAX] using hXsA
    obtain ⟨U, hUX, hAU, hUW⟩ :=
      exists_isSylowOf_inf_map_conj_le (E := X) (G₁ := F₁ ⊓ X) (G₂ := F₂ ⊓ X)
        (S := A) hAsylowX (le_inf hAF₁ hAX) (le_inf hAF₂ hAX) hfacX hxX
    have hUK : IsSylowOf p U K := by
      have hUXle : U ≤ X := hUX.le
      rw [isSylowOf_iff] at hUX ⊢
      obtain ⟨-, hUp, hUidx⟩ := hUX
      refine ⟨hUXle.trans hXK, hUp, ?_⟩
      intro hdvd
      rw [← Subgroup.relIndex_mul_relIndex U X K hUXle hXK] at hdvd
      exact (Nat.Prime.dvd_mul Fact.out).mp hdvd |>.elim hUidx hindX
    have hUF₁ : U ≤ F₁ := hUW.trans (inf_le_left.trans inf_le_left)
    have hUF₂ : U ≤ F₂.map (MulAut.conj x).toMonoidHom :=
      hUW.trans (inf_le_right.trans (Subgroup.map_mono inf_le_left))
    have hDAB : D ≤ A ⊓ A.map (MulAut.conj x).toMonoidHom := hD.trans inf_le_left
    have hDU : D ≤ U := hDAB.trans hAU
    have hDB : D ≤ A.map (MulAut.conj x).toMonoidHom := hDAB.trans inf_le_right
    have hlink₁ : SylowConjLink p (𝓕 ∪ 𝓓) K D A U :=
      (sylowConjLink_of_le hA hUK hF₁.1 hF₁K hAF₁ hUF₁
        (le_inf (hDAB.trans inf_le_left) hDU)).mono_family Set.subset_union_left
    have hF₂conj : F₂.map (MulAut.conj x).toMonoidHom ∈ 𝓕 :=
      h𝓕.2 F₂ hF₂.1 x (hXK hxX)
    have hlink₂ :
        SylowConjLink p (𝓕 ∪ 𝓓) K D U (A.map (MulAut.conj x).toMonoidHom) :=
      (sylowConjLink_of_le hUK hB hF₂conj (h𝓕.1 _ hF₂conj) hUF₂
        (Subgroup.map_mono hAF₂) (le_inf hDU hDB)).mono_family Set.subset_union_left
    exact (Relation.ReflTransGen.single hlink₁).trans (Relation.ReflTransGen.single hlink₂)
  · exact Relation.ReflTransGen.single ⟨hA, hB, X, ⟨Or.inr hX𝓓, hXsA⟩,
      ⟨Or.inr hX𝓓, hXsB⟩, hD, x, hxX, rfl⟩

private theorem reflTransGen_sylowConjLink_lift [Finite G] [Fact p.Prime]
    {𝓔 𝓕 𝓓 : Set (Subgroup G)} {K D S T : Subgroup G}
    (h𝓔 : ∀ E ∈ 𝓔, E ≤ K) (h𝓕 : IsNormalSetIn 𝓕 K)
    (hind : ∀ X ∈ 𝓔 ∪ 𝓕, ¬ p ∣ X.relIndex K)
    (hfac : ∀ S : Subgroup G, IsSylowOf p S K → ∀ E ∈ sylowMembers p 𝓔 S,
      ∃ F₁ ∈ sylowMembers p 𝓕 S, ∃ F₂ ∈ sylowMembers p 𝓕 S,
        ((F₁ ⊓ E : Subgroup G) : Set G) * ((F₂ ⊓ E : Subgroup G) : Set G) = E)
    (h : Relation.ReflTransGen (SylowConjLink p (𝓔 ∪ 𝓓) K D) S T) :
    Relation.ReflTransGen (SylowConjLink p (𝓕 ∪ 𝓓) K D) S T := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hBC ih => exact ih.trans (sylowConjLink_lift_step h𝓔 h𝓕 hind hfac hBC)

theorem ControlsSylowIntersections.of_factor [Finite G] [Fact p.Prime]
    {𝓔 𝓕 𝓓 : Set (Subgroup G)} {K : Subgroup G} (h𝓔 : ∀ E ∈ 𝓔, E ≤ K)
    (h𝓕 : IsNormalSetIn 𝓕 K) (hind : ∀ X ∈ 𝓔 ∪ 𝓕, ¬ p ∣ X.relIndex K)
    (hfac : ∀ S : Subgroup G, IsSylowOf p S K → ∀ E ∈ sylowMembers p 𝓔 S,
      ∃ F₁ ∈ sylowMembers p 𝓕 S, ∃ F₂ ∈ sylowMembers p 𝓕 S,
        ((F₁ ⊓ E : Subgroup G) : Set G) * ((F₂ ⊓ E : Subgroup G) : Set G) = E)
    (h : ControlsSylowIntersections p (𝓔 ∪ 𝓓) K) : ControlsSylowIntersections p (𝓕 ∪ 𝓓) K := by
  intro S T hS hT hne hinter
  exact reflTransGen_sylowConjLink_lift h𝓔 h𝓕 hind hfac (h S T hS hT hne hinter)

end CFSG.GroupTheory
