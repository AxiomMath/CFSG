module

public import CFSG.GroupTheory.SylowIntersectionControl.Defs
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

structure PSubgroupSelection (p : ℕ) (G : Type*) [Group G] where
  sets : Subgroup G → Set (Subgroup G)
  le_of_mem : ∀ P : Subgroup G, IsPGroup p P → ∀ F ∈ sets P, F ≤ P
  normalizer_le : ∀ P : Subgroup G, IsPGroup p P → ∀ F ∈ sets P,
    normalizer (P : Set G) ≤ normalizer (F : Set G)
  sets_map_conj : ∀ P : Subgroup G, IsPGroup p P → ∀ g : G,
    sets (P.map (MulAut.conj g).toMonoidHom) =
      (fun F : Subgroup G => F.map (MulAut.conj g).toMonoidHom) '' sets P

namespace PSubgroupSelection

variable {G : Type*} [Group G] {p : ℕ} (f : PSubgroupSelection p G)

@[expose] def family (M : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ P : Subgroup G, IsSylowOf p P M ∧ ∃ F ∈ f.sets P, X = M ⊓ normalizer (F : Set G)}

@[expose] def IsRegular (M : Subgroup G) : Prop :=
  ControlsSylowIntersections p (f.family M) M

@[expose] def singularMaxLocals : Set (Subgroup G) :=
  {M | Maximal (IsPLocal p) M ∧ ¬ f.IsRegular M}

private theorem map_conj_map_conj_inv (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

private theorem map_conj_inv_map_conj (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  simpa using map_conj_map_conj_inv H g⁻¹

private theorem isSylowOf_map_conj_iff [Finite G] [Fact p.Prime] {P K : Subgroup G} (g : G) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) ↔
      IsSylowOf p P K := by
  constructor
  · intro h
    have h' := isSylowOf_map_conj h g⁻¹
    rwa [map_conj_map_conj_inv P g, map_conj_map_conj_inv K g] at h'
  · exact fun h => isSylowOf_map_conj h g

private theorem sylowMembers_map_conj [Finite G] [Fact p.Prime] (𝓕 : Set (Subgroup G))
    (S : Subgroup G) (g : G) :
    sylowMembers p (Subgroup.map (MulAut.conj g).toMonoidHom '' 𝓕)
        (S.map (MulAut.conj g).toMonoidHom) =
      Subgroup.map (MulAut.conj g).toMonoidHom '' sylowMembers p 𝓕 S := by
  ext X
  constructor
  · rintro ⟨hX, hSX⟩
    obtain ⟨Y, hY, rfl⟩ := hX
    refine ⟨Y, ⟨hY, ?_⟩, rfl⟩
    rw [← Subgroup.map_inf_eq S Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at hSX
    exact (isSylowOf_map_conj_iff g).mp hSX
  · rintro ⟨Y, ⟨hY, hSY⟩, rfl⟩
    refine ⟨⟨Y, hY, rfl⟩, ?_⟩
    rw [← Subgroup.map_inf_eq S Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    exact isSylowOf_map_conj hSY g

private theorem sylowConjLink_map_conj [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {K D S S' : Subgroup G} (h : SylowConjLink p 𝓕 K D S S') (g : G) :
    SylowConjLink p (Subgroup.map (MulAut.conj g).toMonoidHom '' 𝓕)
      (K.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (S.map (MulAut.conj g).toMonoidHom) (S'.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hS, hS', X, hXS, hXS', hD, x, hx, rfl⟩ := h
  refine ⟨isSylowOf_map_conj hS g, isSylowOf_map_conj hS' g,
    X.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, MulAut.conj g x, ?_, ?_⟩
  · rw [sylowMembers_map_conj]
    exact Set.mem_image_of_mem _ hXS
  · rw [sylowMembers_map_conj]
    exact Set.mem_image_of_mem _ hXS'
  · have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hD
    rwa [Subgroup.map_inf_eq (S ⊓ S.map (MulAut.conj x).toMonoidHom) X
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      Subgroup.map_inf_eq S (S.map (MulAut.conj x).toMonoidHom)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at h
  · exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (MulAut.conj g x)).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem conjVia_map_conj [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {K S T : Subgroup G} (h : ConjVia p 𝓕 K S T) (g : G) :
    ConjVia p (Subgroup.map (MulAut.conj g).toMonoidHom '' 𝓕)
      (K.map (MulAut.conj g).toMonoidHom)
      (S.map (MulAut.conj g).toMonoidHom) (T.map (MulAut.conj g).toMonoidHom) := by
  unfold ConjVia at h ⊢
  refine Relation.ReflTransGen.lift (Subgroup.map (MulAut.conj g).toMonoidHom) ?_ S T h
  intro a b hab
  have h := sylowConjLink_map_conj hab g
  rwa [Subgroup.map_inf_eq S T (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at h

private theorem controlsSylowIntersections_map_conj [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K : Subgroup G}
    (h : ControlsSylowIntersections p 𝓕 K) (g : G) :
    ControlsSylowIntersections p
      (Subgroup.map (MulAut.conj g).toMonoidHom '' 𝓕)
      (K.map (MulAut.conj g).toMonoidHom) := by
  intro S T hS hT hne hinf
  have hS' : IsSylowOf p (S.map (MulAut.conj g⁻¹).toMonoidHom) K := by
    have h0 := isSylowOf_map_conj hS g⁻¹
    rwa [map_conj_map_conj_inv K g] at h0
  have hT' : IsSylowOf p (T.map (MulAut.conj g⁻¹).toMonoidHom) K := by
    have h0 := isSylowOf_map_conj hT g⁻¹
    rwa [map_conj_map_conj_inv K g] at h0
  have hne' : S.map (MulAut.conj g⁻¹).toMonoidHom ≠
      T.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro hEq
    apply hne
    have h1 : (S.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (T.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [hEq]
    rwa [map_conj_inv_map_conj S g, map_conj_inv_map_conj T g] at h1
  have hinf' : S.map (MulAut.conj g⁻¹).toMonoidHom ⊓
      T.map (MulAut.conj g⁻¹).toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hinf
    have h1 : (S.map (MulAut.conj g⁻¹).toMonoidHom ⊓
        T.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (⊥ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [hbot]
    rw [Subgroup.map_inf_eq (S.map (MulAut.conj g⁻¹).toMonoidHom)
        (T.map (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective,
      map_conj_inv_map_conj S g, map_conj_inv_map_conj T g, Subgroup.map_bot] at h1
    exact h1
  have hconj := h _ _ hS' hT' hne' hinf'
  have hmap := conjVia_map_conj hconj g
  have hSback : (S.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = S := map_conj_inv_map_conj S g
  have hTback : (T.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = T := map_conj_inv_map_conj T g
  rw [hSback, hTback] at hmap
  exact hmap

private theorem family_map_conj [Finite G] [Fact p.Prime] (M : Subgroup G) (g : G) :
    f.family (M.map (MulAut.conj g).toMonoidHom) =
      Subgroup.map (MulAut.conj g).toMonoidHom '' f.family M := by
  ext X
  constructor
  · rintro ⟨P, hP, F, hF, rfl⟩
    have hP0 : IsSylowOf p (P.map (MulAut.conj g⁻¹).toMonoidHom) M := by
      have h0 := isSylowOf_map_conj hP g⁻¹
      rwa [map_conj_map_conj_inv M g] at h0
    have hF0 : F.map (MulAut.conj g⁻¹).toMonoidHom ∈
        f.sets (P.map (MulAut.conj g⁻¹).toMonoidHom) := by
      rw [f.sets_map_conj P hP.isPGroup g⁻¹]
      exact Set.mem_image_of_mem _ hF
    refine ⟨M ⊓ normalizer ((F.map (MulAut.conj g⁻¹).toMonoidHom) : Set G),
      ⟨P.map (MulAut.conj g⁻¹).toMonoidHom, hP0,
        F.map (MulAut.conj g⁻¹).toMonoidHom, hF0, rfl⟩, ?_⟩
    rw [Subgroup.map_inf_eq M (normalizer (F.map (MulAut.conj g⁻¹).toMonoidHom))
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      Subgroup.map_equiv_normalizer_eq, map_conj_inv_map_conj F g]
  · rintro ⟨Y, ⟨P, hP, F, hF, rfl⟩, rfl⟩
    refine ⟨P.map (MulAut.conj g).toMonoidHom, isSylowOf_map_conj hP g,
      F.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
    · rw [f.sets_map_conj P hP.isPGroup g]
      exact Set.mem_image_of_mem _ hF
    · rw [Subgroup.map_inf_eq M (normalizer (F : Set G)) (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective,
        Subgroup.map_equiv_normalizer_eq]

theorem family_top :
    f.family ⊤ = {X | ∃ P : Subgroup G, IsSylowOf p P ⊤ ∧ ∃ F ∈ f.sets P,
      X = normalizer (F : Set G)} := by
  ext X
  simp only [family, Set.mem_setOf_eq, top_inf_eq]

theorem isNormalSetIn_family [Finite G] [Fact p.Prime] (M : Subgroup G) :
    IsNormalSetIn (f.family M) M := by
  constructor
  · rintro X ⟨P, hP, F, hF, rfl⟩
    exact inf_le_left
  · rintro X ⟨P, hP, F, hF, rfl⟩ g hg
    have hMmap : M.map (MulAut.conj g).toMonoidHom = M := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg))
    have hP' : IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) M := by
      rw [← hMmap]
      exact isSylowOf_map_conj hP g
    have hF' : F.map (MulAut.conj g).toMonoidHom ∈
        f.sets (P.map (MulAut.conj g).toMonoidHom) := by
      rw [f.sets_map_conj P hP.isPGroup g]
      exact Set.mem_image_of_mem _ hF
    refine ⟨P.map (MulAut.conj g).toMonoidHom, hP',
      F.map (MulAut.conj g).toMonoidHom, hF', ?_⟩
    rw [Subgroup.map_inf_eq M (normalizer (F : Set G)) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective, Subgroup.map_equiv_normalizer_eq, hMmap]

theorem sylowMembers_family [Finite G] [Fact p.Prime] {M P : Subgroup G}
    (hP : IsSylowOf p P M) :
    sylowMembers p (f.family M) P = (fun F : Subgroup G => M ⊓ normalizer (F : Set G)) '' f.sets P
    := by
  ext X
  constructor
  · rintro ⟨hXfam, hX⟩
    obtain ⟨Q, hQ, F₀, hF₀, rfl⟩ := hXfam
    have hQnorm : Q ≤ normalizer (F₀ : Set G) :=
      (Subgroup.le_normalizer : Q ≤ normalizer (Q : Set G)).trans
        (f.normalizer_le Q hQ.isPGroup F₀ hF₀)
    have hQX : Q ≤ M ⊓ normalizer (F₀ : Set G) := le_inf hQ.le hQnorm
    have hQ_X : IsSylowOf p Q (M ⊓ normalizer (F₀ : Set G)) := hQ.of_le hQX inf_le_left
    have hcard : Nat.card (P ⊓ (M ⊓ normalizer (F₀ : Set G)) : Subgroup G) = Nat.card P := by
      rw [hX.card_eq, ← hQ_X.card_eq, hQ.card_eq, ← hP.card_eq]
    have hPX : P ≤ M ⊓ normalizer (F₀ : Set G) := by
      have heq : (P ⊓ (M ⊓ normalizer (F₀ : Set G)) : Subgroup G) = P :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
      exact (le_of_eq heq.symm).trans inf_le_right
    have hP_X : IsSylowOf p P (M ⊓ normalizer (F₀ : Set G)) := hP.of_le hPX inf_le_left
    obtain ⟨x, hxX, hx⟩ := hQ_X.exists_mem_conj hP_X
    have hPmap : P = Q.map (MulAut.conj x).toMonoidHom := by
      ext y
      rw [hx y, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hfix : F₀.map (MulAut.conj x).toMonoidHom = F₀ := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hxX.2)
    refine ⟨F₀.map (MulAut.conj x).toMonoidHom, ?_, ?_⟩
    · rw [hPmap, f.sets_map_conj Q hQ.isPGroup x]
      exact Set.mem_image_of_mem _ hF₀
    · rw [hfix]
  · rintro ⟨F, hF, rfl⟩
    have hFnorm : P ≤ normalizer (F : Set G) :=
      (Subgroup.le_normalizer : P ≤ normalizer (P : Set G)).trans
        (f.normalizer_le P hP.isPGroup F hF)
    have hPX : P ≤ M ⊓ normalizer (F : Set G) := le_inf hP.le hFnorm
    refine ⟨⟨P, hP, F, hF, rfl⟩, ?_⟩
    rw [inf_eq_left.mpr hPX]
    exact hP.of_le hPX inf_le_left

variable {f} in
theorem IsRegular.map_conj [Finite G] [Fact p.Prime] {M : Subgroup G} (h : f.IsRegular M)
    (g : G) : f.IsRegular (M.map (MulAut.conj g).toMonoidHom) := by
  rw [IsRegular, family_map_conj f M g]
  exact controlsSylowIntersections_map_conj h g

end PSubgroupSelection

end CFSG.GroupTheory
