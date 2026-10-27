module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.SylowIntersectionControl.Fusion
import CFSG.GroupTheory.SylowIntersectionControl.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ}

private lemma reflTransGen_sylowConjLink_of_eqvGen {𝓕 : Set (Subgroup G)} {K S T : Subgroup G}
    (h : ControlsSylowIntersections p 𝓕 K)
    (hST : Relation.EqvGen (fun A B : Subgroup G =>
      IsSylowOf p A K ∧ IsSylowOf p B K ∧ (⊥ : Subgroup G) < A ⊓ B) S T) :
    Relation.ReflTransGen (SylowConjLink p 𝓕 K (⊥ : Subgroup G)) S T := by
  have hstep : ∀ A B : Subgroup G,
      (IsSylowOf p A K ∧ IsSylowOf p B K ∧ (⊥ : Subgroup G) < A ⊓ B) →
      Relation.ReflTransGen (SylowConjLink p 𝓕 K (⊥ : Subgroup G)) A B := by
    rintro A B ⟨hA, hB, hbot⟩
    by_cases hAB : A = B
    · subst hAB
      exact Relation.ReflTransGen.refl
    · exact ConjVia.reflTransGen_of_le
        (h A B hA hB hAB (bot_lt_iff_ne_bot.mp hbot)) bot_le
  have hEqv : Relation.EqvGen (SylowConjLink p 𝓕 K (⊥ : Subgroup G)) S T := by
    rw [← Relation.EqvGen.eqvGen_reflTransGen]
    exact Relation.EqvGen.mono hstep S T hST
  have : Std.Symm (SylowConjLink p 𝓕 K (⊥ : Subgroup G)) := ⟨fun _ _ h => h.symm⟩
  rwa [Relation.EqvGen.eqvGen_eq_reflTransGen] at hEqv

private lemma mem_iSup_sylowMembers_of_reflTransGen_fusionChain {𝓕 : Set (Subgroup G)}
    {S : Subgroup G} {g : G}
    (h : Relation.ReflTransGen (FusionChainStep p 𝓕 S ((⊥ : Subgroup G) : Set G)) 1 g) :
    g ∈ ⨆ X ∈ sylowMembers p 𝓕 S, X := by
  refine Relation.ReflTransGen.rec (motive := fun x _ =>
    x ∈ ⨆ X ∈ sylowMembers p 𝓕 S, X) ?_ ?_ h
  · exact Subgroup.one_mem _
  · intro b c _ hbc ih
    obtain ⟨Y, hY, z, hz, rfl, -⟩ := hbc
    exact Subgroup.mul_mem _
      (Subgroup.mem_iSup_of_mem Y (Subgroup.mem_iSup_of_mem hY hz)) ih

theorem ControlsSylowIntersections.mul_normalizer_eq [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K S : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K)
    (h : ControlsSylowIntersections p 𝓕 K) (hK : ¬ IsPIsolatedOver p K ⊥)
    (hS : IsSylowOf p S K) :
    ((⨆ X ∈ sylowMembers p 𝓕 S, X : Subgroup G) : Set G) *
      ((K ⊓ normalizer (S : Set G) : Subgroup G) : Set G) = K := by
  classical
  unfold IsPIsolatedOver at hK
  set P : Subgroup G := ⨆ X ∈ sylowMembers p 𝓕 S, X with hP
  have hPK : P ≤ K := by
    rw [hP]
    exact iSup₂_le fun X hX => h𝓕.1 X hX.1
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    exact K.mul_mem (hPK ha) hb.1
  · intro k hk
    set T : Subgroup G := S.map (MulAut.conj k).toMonoidHom with hTdef
    have hKmap : K.map (MulAut.conj k).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk)
    have hT : IsSylowOf p T K := by
      have hT' := isSylowOf_map_conj hS k
      rw [hKmap] at hT'
      rwa [hTdef]
    have hEqv : Relation.EqvGen (fun A B : Subgroup G =>
        IsSylowOf p A K ∧ IsSylowOf p B K ∧ (⊥ : Subgroup G) < A ⊓ B) S T := by
      by_contra hne
      exact hK ⟨S, T, hS, hT, hne⟩
    have hchain := reflTransGen_sylowConjLink_of_eqvGen h hEqv
    obtain ⟨g, hgK, hgchain, hST⟩ := exists_fusionChain_of_reflTransGen h𝓕 hchain
    have hgP : g ∈ P := by
      rw [hP]
      exact mem_iSup_sylowMembers_of_reflTransGen_fusionChain hgchain
    have hSgk : S.map (MulAut.conj (g * k)).toMonoidHom = S := by
      calc S.map (MulAut.conj (g * k)).toMonoidHom
          = S.map ((MulAut.conj g).toMonoidHom.comp
              (MulAut.conj k).toMonoidHom) := by
            congr 1
            ext x
            simp [MulAut.conj_apply, mul_assoc]
        _ = (S.map (MulAut.conj k).toMonoidHom).map
              (MulAut.conj g).toMonoidHom := by rw [Subgroup.map_map]
        _ = T.map (MulAut.conj g).toMonoidHom := by rw [← hTdef]
        _ = S := hST.symm
    have hgk : g * k ∈ K ⊓ normalizer (S : Set G) :=
      ⟨K.mul_mem hgK hk,
        (Subgroup.mem_normalizer_iff_map_conj_eq (H := S)).mpr hSgk⟩
    exact Set.mem_mul.mpr ⟨g⁻¹, P.inv_mem hgP, g * k, hgk, by group⟩

end CFSG.GroupTheory
