module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepNontriv
public import CFSG.RankThree.FFModules.ChiefFactors
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped Classical
open CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b Representation
open CFSG.RankThree.FFModules

section Restrict

variable {K L : Type} [Group K] [Group L] (α : L →* K)

@[expose] def restrictMap {V₁ V₂ : Type} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] {ρ₁ : Representation (ZMod 2) K V₁}
    {ρ₂ : Representation (ZMod 2) K V₂} (f : ρ₁.IntertwiningMap ρ₂) :
    Representation.IntertwiningMap (ρ₁.comp α) (ρ₂.comp α) where
  toLinearMap := f.toLinearMap
  isIntertwining' l := f.isIntertwining' (α l)

theorem nontrivCount_comp_eq_add_of_exact {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [AddCommGroup V₃] [Module (ZMod 2) V₃] [Finite V₁]
    [Finite V₂] [Finite V₃] {ρ₁ : Representation (ZMod 2) K V₁}
    {ρ₂ : Representation (ZMod 2) K V₂} {ρ₃ : Representation (ZMod 2) K V₃}
    (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) :
    nontrivCount (ρ₂.comp α) = nontrivCount (ρ₁.comp α) + nontrivCount (ρ₃.comp α) :=
  nontrivCount_eq_add_of_exact (restrictMap α f) (restrictMap α g) hf hg H

end Restrict

section Chain

variable {K L : Type} [Group K] [Group L] (α : L →* K)
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def subInclusion {ρ : Representation (ZMod 2) K V} {S S' : Subrepresentation ρ}
    (h : S ≤ S') : S.toRepresentation.IntertwiningMap S'.toRepresentation where
  toLinearMap := Submodule.inclusion (show S.toSubmodule ≤ S'.toSubmodule from h)
  isIntertwining' g := by ext x; rfl

@[expose] def factorProj {ρ : Representation (ZMod 2) K V} (S S' : Subrepresentation ρ) :
    S'.toRepresentation.IntertwiningMap (factorRep S S') where
  toLinearMap := (factorSub S S').mkQ
  isIntertwining' g := by ext x; rfl

theorem exact_subInclusion_factorProj {ρ : Representation (ZMod 2) K V}
    {S S' : Subrepresentation ρ} (h : S ≤ S') :
    Function.Exact (subInclusion h) (factorProj S S') := by
  intro y
  constructor
  · intro hy
    have h0 : (factorSub S S').mkQ y = 0 := hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact ⟨⟨y.1, h0⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    show (factorSub S S').mkQ (Submodule.inclusion (show S.toSubmodule ≤ S'.toSubmodule from h) x)
      = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2

theorem nontrivCount_comp_factor_add {ρ : Representation (ZMod 2) K V}
    {S S' : Subrepresentation ρ} (h : S ≤ S') :
    nontrivCount (S'.toRepresentation.comp α) =
      nontrivCount (S.toRepresentation.comp α) + nontrivCount ((factorRep S S').comp α) := by
  haveI := factor_finite S S'
  exact nontrivCount_comp_eq_add_of_exact α (subInclusion h) (factorProj S S')
    (Submodule.inclusion_injective (show S.toSubmodule ≤ S'.toSubmodule from h))
    (Submodule.mkQ_surjective _) (exact_subInclusion_factorProj h)

theorem nontrivCount_comp_sub_quot (ρ : Representation (ZMod 2) K V) (W : Subrepresentation ρ) :
    nontrivCount (ρ.comp α) =
      nontrivCount (W.toRepresentation.comp α) + nontrivCount (W.quotient.comp α) := by
  haveI : Finite (V ⧸ W.toSubmodule) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact nontrivCount_comp_eq_add_of_exact α (subIncl ρ W) (quotProj ρ W)
    W.toSubmodule.injective_subtype W.toSubmodule.mkQ_surjective (LinearMap.exact_subtype_mkQ _)

theorem nontrivCount_comp_bot (ρ : Representation (ZMod 2) K V) :
    nontrivCount ((⊥ : Subrepresentation ρ).toRepresentation.comp α) = 0 := by
  haveI : Subsingleton ↥(⊥ : Subrepresentation ρ).toSubmodule :=
    inferInstanceAs (Subsingleton ↥(⊥ : Submodule (ZMod 2) V))
  exact nontrivCount_of_subsingleton _

theorem nontrivCount_comp_top (ρ : Representation (ZMod 2) K V) :
    nontrivCount ((⊤ : Subrepresentation ρ).toRepresentation.comp α) =
      nontrivCount (ρ.comp α) := by
  have h := nontrivCount_comp_sub_quot α ρ ⊤
  haveI : Subsingleton (V ⧸ (⊤ : Subrepresentation ρ).toSubmodule) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  rw [nontrivCount_of_subsingleton ((⊤ : Subrepresentation ρ).quotient.comp α)] at h
  omega

theorem nontrivCount_comp_eq_sum {ρ : Representation (ZMod 2) K V} {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ} (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ)
    (h0 : Vs 0 = ⊥) (hlast : Vs (Fin.last r) = ⊤) :
    nontrivCount (ρ.comp α) =
      ∑ i : Fin r, nontrivCount ((factorRep (Vs i.castSucc) (Vs i.succ)).comp α) := by
  have h := fin_telescope (fun j => nontrivCount ((Vs j).toRepresentation.comp α))
    (fun i => nontrivCount ((factorRep (Vs i.castSucc) (Vs i.succ)).comp α)) fun i =>
      nontrivCount_comp_factor_add α (hmono i)
  rw [hlast, h0, nontrivCount_comp_top, nontrivCount_comp_bot] at h
  simpa using h

theorem three_le_nontrivCount (hperf : commutator L = ⊤) {ρ : Representation (ZMod 2) K V}
    {S₀ S₁ S₂ S₃ : Subrepresentation ρ} (h01 : S₀ ≤ S₁) (h12 : S₁ ≤ S₂) (h23 : S₂ ≤ S₃)
    (n1 : ∃ l : L, factorRep S₀ S₁ (α l) ≠ 1) (n2 : ∃ l : L, factorRep S₁ S₂ (α l) ≠ 1)
    (n3 : ∃ l : L, factorRep S₂ S₃ (α l) ≠ 1) : 3 ≤ nontrivCount (ρ.comp α) := by
  have pos : ∀ {S S' : Subrepresentation ρ}, (∃ l : L, factorRep S S' (α l) ≠ 1) →
      1 ≤ nontrivCount ((factorRep S S').comp α) := by
    intro S S' ⟨l, hl⟩
    haveI := factor_finite S S'
    by_contra hc
    have h0 : nontrivCount ((factorRep S S').comp α) = 0 := by omega
    exact hl (trivial_of_nontrivCount_eq_zero hperf ((factorRep S S').comp α) h0 l)
  have e1 := nontrivCount_comp_factor_add α h01
  have e2 := nontrivCount_comp_factor_add α h12
  have e3 := nontrivCount_comp_factor_add α h23
  have e4 := nontrivCount_comp_sub_quot α ρ S₃
  have p1 := pos n1
  have p2 := pos n2
  have p3 := pos n3
  omega

theorem isIrreducible_factor_comp {ρ : Representation (ZMod 2) K V}
    {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (hsurj : ∀ k : K, ∃ l : L, factorRep U U' k = factorRep U U' (α l)) :
    Representation.IsIrreducible ((factorRep U U').comp α) := by
  haveI : Nontrivial (U'.toSubmodule ⧸ factorSub U U') := factor_nontrivial h
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro hbt
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule hbt)
  · intro S
    have hS := factor_invariant_eq_bot_or_top h S.toSubmodule fun k x hx => by
      obtain ⟨l, hl⟩ := hsurj k
      rw [hl]
      exact S.apply_mem_toSubmodule l hx
    rcases hS with h0 | h0
    · left
      exact Subrepresentation.toSubmodule_injective h0
    · right
      exact Subrepresentation.toSubmodule_injective h0

theorem nontrivCount_factor_comp_le {ρ : Representation (ZMod 2) K V}
    {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (hsurj : ∀ k : K, ∃ l : L, factorRep U U' k = factorRep U U' (α l)) :
    nontrivCount ((factorRep U U').comp α) ≤ if ∃ k, factorRep U U' k ≠ 1 then 1 else 0 := by
  haveI := factor_finite U U'
  split_ifs with hnt
  · exact nontrivCount_le_one_of_isIrreducible _ (isIrreducible_factor_comp α h hsurj)
  · have h0 : nontrivCount ((factorRep U U').comp α) = 0 :=
      nontrivCount_eq_zero_of_trivial _ fun l => by
        by_contra hl
        exact hnt ⟨α l, hl⟩
    omega

theorem nontrivCount_comp_le_card {ρ : Representation (ZMod 2) K V} {r : ℕ}
    {Vs : Fin (r + 1) → Subrepresentation ρ} (hVs : IsCompositionSeries r Vs)
    (hsurj : ∀ (i : Fin r) (k : K), ∃ l : L,
      factorRep (Vs i.castSucc) (Vs i.succ) k = factorRep (Vs i.castSucc) (Vs i.succ) (α l)) :
    nontrivCount (ρ.comp α) ≤ (nontrivialFactors Vs).card := by
  rw [nontrivCount_comp_eq_sum α (fun i => (hVs.covBy i).le) hVs.zero hVs.last]
  calc ∑ i : Fin r, nontrivCount ((factorRep (Vs i.castSucc) (Vs i.succ)).comp α)
      ≤ ∑ i : Fin r, if i ∈ nontrivialFactors Vs then 1 else 0 := Finset.sum_le_sum fun i _ => by
        have := nontrivCount_factor_comp_le α (hVs.covBy i) (hsurj i)
        simpa only [mem_nontrivialFactors] using this
    _ = (nontrivialFactors Vs).card := by simp [Finset.sum_boole]

end Chain

end CFSG.LocalAnalysis.RankThreeUC.S15
