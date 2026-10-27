module

public import CFSG.GroupTheory.SylowIntersectionControl.Selection
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.SylowIntersectionControl.Factor
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.GroupTheory.PSubgroupSelection

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ} {f : PSubgroupSelection p G}

private theorem sylowConjLink_family_lift [Finite G] [Fact p.Prime]
    {K X D W W' : Subgroup G} (hXK : X ≤ K) (hindX : ¬ p ∣ X.relIndex K)
    (h : SylowConjLink p (f.family X) X D W W') :
    SylowConjLink p (f.family K) K D W W' := by
  obtain ⟨hW, hW', Y, hYW, hYW', hD, y, hyY, hWy⟩ := h
  have htransport : ∀ {P : Subgroup G}, IsSylowOf p P X → IsSylowOf p P K := by
    intro P hP
    rw [isSylowOf_iff] at hP ⊢
    obtain ⟨hPX, hPp, hPidx⟩ := hP
    refine ⟨hPX.trans hXK, hPp, ?_⟩
    intro hdvd
    rw [← Subgroup.relIndex_mul_relIndex P X K hPX hXK] at hdvd
    exact (Nat.Prime.dvd_mul Fact.out).mp hdvd |>.elim hPidx hindX
  have hWK : IsSylowOf p W K := htransport hW
  have hW'K : IsSylowOf p W' K := htransport hW'
  rw [sylowMembers_family (f := f) hW] at hYW
  obtain ⟨F, hFW, hYF⟩ := hYW
  subst hYF
  have hyY' : y ∈ X ⊓ normalizer (F : Set G) := hyY
  have hFfix : F.map (MulAut.conj y).toMonoidHom = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyY'.2
  have hFW' : F ∈ f.sets W' := by
    rw [hWy, f.sets_map_conj W hW.isPGroup y]
    exact ⟨F, hFW, hFfix⟩
  have hZW : K ⊓ normalizer (F : Set G) ∈ sylowMembers p (f.family K) W := by
    rw [sylowMembers_family (f := f) hWK]
    exact ⟨F, hFW, rfl⟩
  have hZW' : K ⊓ normalizer (F : Set G) ∈ sylowMembers p (f.family K) W' := by
    rw [sylowMembers_family (f := f) hW'K]
    exact ⟨F, hFW', rfl⟩
  have hYZ : X ⊓ normalizer (F : Set G) ≤ K ⊓ normalizer (F : Set G) :=
    le_inf (inf_le_left.trans hXK) inf_le_right
  have hD' : D ≤ W ⊓ W' ⊓ (K ⊓ normalizer (F : Set G)) :=
    le_inf (hD.trans inf_le_left) ((hD.trans inf_le_right).trans hYZ)
  have hyZ : y ∈ K ⊓ normalizer (F : Set G) := ⟨hXK hyY'.1, hyY'.2⟩
  exact ⟨hWK, hW'K, K ⊓ normalizer (F : Set G), hZW, hZW', hD', y, hyZ, hWy⟩

theorem isRegular_of_mem_family [Finite G] [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ f.family M) : f.IsRegular M := by
  intro A B hA hB _ _
  exact Relation.ReflTransGen.single
    (sylowConjLink_of_le hA hB hM le_rfl hA.le hB.le le_rfl)

theorem isRegular_of_le_normalizer [Finite G] [Fact p.Prime] {M S F : Subgroup G}
    (hS : IsSylowOf p S M) (hF : F ∈ f.sets S) (hM : M ≤ normalizer (F : Set G)) :
    f.IsRegular M :=
  isRegular_of_mem_family ⟨S, hS, F, hF, (inf_eq_left.mpr hM).symm⟩

theorem IsRegular.of_controlsSylowIntersections [Finite G] [Fact p.Prime] {K : Subgroup G}
    {𝓓 : Set (Subgroup G)} (h𝓓 : ∀ X ∈ 𝓓, X ≤ K) (hind : ∀ X ∈ 𝓓, ¬ p ∣ X.relIndex K)
    (hreg : ∀ X ∈ 𝓓, f.IsRegular X) (h : ControlsSylowIntersections p 𝓓 K) :
    f.IsRegular K := by
  intro S T hS hT hne hinter
  have hD : S ⊓ T ≠ ⊥ := hinter
  have hstep : SylowConjLink p 𝓓 K (S ⊓ T) ≤
      Relation.ReflTransGen (SylowConjLink p (f.family K) K (S ⊓ T)) := by
    intro A B hAB
    obtain ⟨hA, hB, X, hXA, hXB, hDX, -, -, -⟩ := hAB
    have hX𝓓 : X ∈ 𝓓 := hXA.1
    have hXK : X ≤ K := h𝓓 X hX𝓓
    have hAX : A ≤ X := le_of_isSylowOf_inf hA hXK (hind X hX𝓓) hXA.2
    have hBX : B ≤ X := le_of_isSylowOf_inf hB hXK (hind X hX𝓓) hXB.2
    have hDAB : S ⊓ T ≤ A ⊓ B := hDX.trans inf_le_left
    by_cases hABeq : A = B
    · subst hABeq
      exact Relation.ReflTransGen.refl
    · have hinterAB : A ⊓ B ≠ ⊥ := by
        intro hbot
        exact hD (le_bot_iff.mp (hDAB.trans (le_of_eq hbot)))
      have hvia : ConjVia p (f.family X) X A B :=
        hreg X hX𝓓 A B (hA.of_le hAX hXK) (hB.of_le hBX hXK) hABeq hinterAB
      have hinner : SylowConjLink p (f.family X) X (S ⊓ T) ≤
          Relation.ReflTransGen (SylowConjLink p (f.family K) K (S ⊓ T)) := by
        intro U V hUV
        exact Relation.ReflTransGen.single
          (sylowConjLink_family_lift hXK (hind X hX𝓓) hUV)
      exact Relation.reflTransGen_closed (r := SylowConjLink p (f.family X) X (S ⊓ T))
        (p := SylowConjLink p (f.family K) K (S ⊓ T)) hinner A B
        (hvia.reflTransGen_of_le hDAB)
  exact Relation.reflTransGen_closed (r := SylowConjLink p 𝓓 K (S ⊓ T))
    (p := SylowConjLink p (f.family K) K (S ⊓ T)) hstep S T
    (h S T hS hT hne hinter)

private def mulFamily (K G₁ G₂ : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ k ∈ K, X = G₁.map (MulAut.conj k).toMonoidHom ∨
    X = G₂.map (MulAut.conj k).toMonoidHom}

private theorem isNormalSetIn_mulFamily {K G₁ G₂ : Subgroup G} (h₁ : G₁ ≤ K) (h₂ : G₂ ≤ K)
    (hKfix : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K) :
    IsNormalSetIn (mulFamily K G₁ G₂) K := by
  constructor
  · rintro X ⟨k, hk, rfl | rfl⟩
    · exact (Subgroup.map_mono h₁).trans (le_of_eq (hKfix k hk))
    · exact (Subgroup.map_mono h₂).trans (le_of_eq (hKfix k hk))
  · rintro X ⟨k, hk, rfl | rfl⟩ g hg
    · exact ⟨g * k, K.mul_mem hg hk, Or.inl (CFSG.GroupTheory.map_conj_map_conj g k G₁)⟩
    · exact ⟨g * k, K.mul_mem hg hk, Or.inr (CFSG.GroupTheory.map_conj_map_conj g k G₂)⟩

private theorem not_dvd_relIndex_mulFamily {K G₁ G₂ : Subgroup G}
    (h₁ : ¬ p ∣ G₁.relIndex K) (h₂ : ¬ p ∣ G₂.relIndex K)
    (hKfix : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K) :
    ∀ X ∈ mulFamily K G₁ G₂, ¬ p ∣ X.relIndex K := by
  rintro X ⟨k, hk, rfl | rfl⟩ hdvd
  · apply h₁
    rw [← hKfix k hk] at hdvd
    rwa [Subgroup.relIndex_map_map_of_injective G₁ K (MulAut.conj k).injective] at hdvd
  · apply h₂
    rw [← hKfix k hk] at hdvd
    rwa [Subgroup.relIndex_map_map_of_injective G₂ K (MulAut.conj k).injective] at hdvd

private theorem isRegular_mulFamily [Finite G] [Fact p.Prime] {K G₁ G₂ : Subgroup G}
    (h₁ : f.IsRegular G₁) (h₂ : f.IsRegular G₂) :
    ∀ X ∈ mulFamily K G₁ G₂, f.IsRegular X := by
  rintro X ⟨k, -, rfl | rfl⟩
  · exact h₁.map_conj k
  · exact h₂.map_conj k

private theorem mulFamily_map_mul {K G₁ G₂ : Subgroup G} (hK : (G₁ : Set G) * G₂ = K)
    (hKfix : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K) {k : G} (hk : k ∈ K) :
    ((G₁.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) *
      ((G₂.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) = K := by
  have hKimage : (MulAut.conj k).toMonoidHom '' (K : Set G) = K := by
    rw [← Subgroup.coe_map, hKfix k hk]
  calc ((G₁.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) *
        ((G₂.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G)
      = ((MulAut.conj k).toMonoidHom '' (G₁ : Set G)) *
          ((MulAut.conj k).toMonoidHom '' (G₂ : Set G)) := by
        rw [Subgroup.coe_map, Subgroup.coe_map]
    _ = (MulAut.conj k).toMonoidHom '' ((G₁ : Set G) * G₂) :=
        (Set.image_mul (MulAut.conj k).toMonoidHom).symm
    _ = (MulAut.conj k).toMonoidHom '' (K : Set G) := by rw [hK]
    _ = K := hKimage

private theorem exists_factor_mulFamily [Finite G] [Fact p.Prime]
    {K G₁ G₂ S : Subgroup G} (hS : IsSylowOf p S K) (h₁ : S ≤ G₁) (h₂ : S ≤ G₂)
    (hG₁K : G₁ ≤ K) (hG₂K : G₂ ≤ K) (hK : (G₁ : Set G) * G₂ = K)
    (hKfix : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K) :
    ∀ T : Subgroup G, IsSylowOf p T K → ∀ E ∈ sylowMembers p {K} T,
      ∃ F₁ ∈ sylowMembers p (mulFamily K G₁ G₂) T,
      ∃ F₂ ∈ sylowMembers p (mulFamily K G₁ G₂) T,
        ((F₁ ⊓ E : Subgroup G) : Set G) * ((F₂ ⊓ E : Subgroup G) : Set G) = E := by
  intro T hT E hE
  have hEK : E = K := Set.mem_singleton_iff.mp hE.1
  rw [hEK] at hE ⊢
  obtain ⟨k, hk, hconj⟩ := IsSylowOf.exists_mem_conj hS hT
  have hTmap : T = S.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hconj x, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  let F₁ : Subgroup G := G₁.map (MulAut.conj k).toMonoidHom
  let F₂ : Subgroup G := G₂.map (MulAut.conj k).toMonoidHom
  have hTle₁ : T ≤ F₁ := (le_of_eq hTmap).trans (Subgroup.map_mono h₁)
  have hTle₂ : T ≤ F₂ := (le_of_eq hTmap).trans (Subgroup.map_mono h₂)
  have hmem₁ : F₁ ∈ sylowMembers p (mulFamily K G₁ G₂) T := by
    refine ⟨⟨k, hk, Or.inl rfl⟩, ?_⟩
    rw [inf_eq_left.mpr hTle₁]
    rw [hTmap]
    exact isSylowOf_map_conj (hS.of_le h₁ hG₁K) k
  have hmem₂ : F₂ ∈ sylowMembers p (mulFamily K G₁ G₂) T := by
    refine ⟨⟨k, hk, Or.inr rfl⟩, ?_⟩
    rw [inf_eq_left.mpr hTle₂]
    rw [hTmap]
    exact isSylowOf_map_conj (hS.of_le h₂ hG₂K) k
  have hF₁K : F₁ ≤ K := (Subgroup.map_mono hG₁K).trans (le_of_eq (hKfix k hk))
  have hF₂K : F₂ ≤ K := (Subgroup.map_mono hG₂K).trans (le_of_eq (hKfix k hk))
  refine ⟨F₁, hmem₁, F₂, hmem₂, ?_⟩
  rw [inf_eq_left.mpr hF₁K, inf_eq_left.mpr hF₂K]
  exact mulFamily_map_mul hK hKfix hk

private theorem controlsSylowIntersections_mulFamily [Finite G] [Fact p.Prime]
    {K G₁ G₂ S : Subgroup G} (hS : IsSylowOf p S K) (h₁ : S ≤ G₁) (h₂ : S ≤ G₂)
    (hG₁K : G₁ ≤ K) (hG₂K : G₂ ≤ K) (hK : (G₁ : Set G) * G₂ = K)
    (hind₁ : ¬ p ∣ G₁.relIndex K) (hind₂ : ¬ p ∣ G₂.relIndex K)
    (hKfix : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K) :
    ControlsSylowIntersections p (mulFamily K G₁ G₂) K := by
  have hcontrol : ControlsSylowIntersections p ({K} ∪ ∅) K := by
    intro A B hA hB _ _
    exact Relation.ReflTransGen.single
      (sylowConjLink_of_le hA hB (by simp) le_rfl hA.le hB.le le_rfl)
  have hfactor := ControlsSylowIntersections.of_factor (𝓔 := {K})
    (𝓕 := mulFamily K G₁ G₂) (𝓓 := ∅)
    (by
      intro E hE
      rw [Set.mem_singleton_iff] at hE
      subst hE
      exact le_rfl)
    (isNormalSetIn_mulFamily hG₁K hG₂K hKfix)
    (by
      intro X hX
      rcases hX with hX | hX
      · rw [Set.mem_singleton_iff] at hX
        subst hX
        rw [Subgroup.relIndex_self]
        exact Nat.Prime.not_dvd_one Fact.out
      · exact not_dvd_relIndex_mulFamily hind₁ hind₂ hKfix X hX)
    (exists_factor_mulFamily hS h₁ h₂ hG₁K hG₂K hK hKfix) hcontrol
  simpa using hfactor

theorem IsRegular.of_mul_eq [Finite G] [Fact p.Prime] {K G₁ G₂ S : Subgroup G}
    (hS : IsSylowOf p S K) (h₁ : S ≤ G₁) (h₂ : S ≤ G₂) (hK : (G₁ : Set G) * G₂ = K)
    (hr₁ : f.IsRegular G₁) (hr₂ : f.IsRegular G₂) : f.IsRegular K := by
  have hG₁K : G₁ ≤ K := by
    intro x hx
    have hmem : x ∈ (G₁ : Set G) * G₂ := ⟨x, hx, 1, G₂.one_mem, mul_one x⟩
    rwa [hK] at hmem
  have hG₂K : G₂ ≤ K := by
    intro x hx
    have hmem : x ∈ (G₁ : Set G) * G₂ := ⟨1, G₁.one_mem, x, hx, one_mul x⟩
    rwa [hK] at hmem
  have hSrel : ¬ p ∣ S.relIndex K := (isSylowOf_iff.mp hS).2.2
  have hind₁ : ¬ p ∣ G₁.relIndex K := by
    intro hdvd
    apply hSrel
    rw [← Subgroup.relIndex_mul_relIndex S G₁ K h₁ hG₁K]
    exact dvd_mul_of_dvd_right hdvd _
  have hind₂ : ¬ p ∣ G₂.relIndex K := by
    intro hdvd
    apply hSrel
    rw [← Subgroup.relIndex_mul_relIndex S G₂ K h₂ hG₂K]
    exact dvd_mul_of_dvd_right hdvd _
  have hKfix : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K := by
    intro k hk
    simpa using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk))
  exact IsRegular.of_controlsSylowIntersections (f := f) (K := K)
    (𝓓 := mulFamily K G₁ G₂)
    (isNormalSetIn_mulFamily hG₁K hG₂K hKfix).1
    (not_dvd_relIndex_mulFamily hind₁ hind₂ hKfix)
    (isRegular_mulFamily hr₁ hr₂)
    (controlsSylowIntersections_mulFamily hS h₁ h₂ hG₁K hG₂K hK hind₁ hind₂ hKfix)

end CFSG.GroupTheory.PSubgroupSelection
