module

public import CFSG.RankThree.FFModules.ChiefFactors

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules Module

universe u

section Step

variable {K : Type*} [Group K] {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) K V}

theorem finrank_inf_fixSub_le (A : Subgroup K) {U U' : Subrepresentation ρ} (h : U ≤ U') :
    finrank (ZMod 2) ↥(U'.toSubmodule ⊓ fixSub ρ A) ≤
      finrank (ZMod 2) ↥(U.toSubmodule ⊓ fixSub ρ A) +
        finrank (ZMod 2) ↥(fixSub (factorRep U U') A) := by
  classical
  let φ : ↥(U'.toSubmodule ⊓ fixSub ρ A) →ₗ[ZMod 2] (U'.toSubmodule ⧸ factorSub U U') :=
    (factorSub U U').mkQ ∘ₗ Submodule.inclusion (inf_le_left)
  have hrange : LinearMap.range φ ≤ fixSub (factorRep U U') A := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    rw [mem_fixSub]
    intro a ha
    have hxF : ρ a x = x := hx.2 a ha
    have hfix : U'.toRepresentation a ⟨x, hx.1⟩ = ⟨x, hx.1⟩ := by
      rw [Subrepresentation.toRepresentation_apply_mk]
      exact hxF
    change factorRep U U' a (Submodule.Quotient.mk ⟨x, hx.1⟩) = Submodule.Quotient.mk ⟨x, hx.1⟩
    rw [factorRep_mk, hfix]
  have hker : (LinearMap.ker φ).map (U'.toSubmodule ⊓ fixSub ρ A).subtype ≤
      U.toSubmodule ⊓ fixSub ρ A := by
    rintro _ ⟨⟨x, hx⟩, hxk, rfl⟩
    refine ⟨?_, hx.2⟩
    have h0 : (factorSub U U').mkQ (Submodule.inclusion inf_le_left ⟨x, hx⟩) = 0 := hxk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank (ZMod 2) (LinearMap.range φ) ≤
      finrank (ZMod 2) (fixSub (factorRep U U') A) := Submodule.finrank_mono hrange
  have h3 : finrank (ZMod 2) (LinearMap.ker φ) ≤
      finrank (ZMod 2) ↥(U.toSubmodule ⊓ fixSub ρ A) := by
    have e : finrank (ZMod 2) ↥((LinearMap.ker φ).map (U'.toSubmodule ⊓ fixSub ρ A).subtype) =
        finrank (ZMod 2) (LinearMap.ker φ) :=
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm.finrank_eq
    rw [← e]
    exact Submodule.finrank_mono hker
  omega

theorem finrank_factor_add {U U' : Subrepresentation ρ} (hUU' : U ≤ U') :
    finrank (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') + finrank (ZMod 2) U.toSubmodule =
      finrank (ZMod 2) U'.toSubmodule := by
  have h1 := Submodule.finrank_quotient_add_finrank (factorSub U U')
  have h2 : finrank (ZMod 2) ↥(factorSub U U') = finrank (ZMod 2) U.toSubmodule :=
    (Submodule.comapSubtypeEquivOfLe (show U.toSubmodule ≤ U'.toSubmodule from hUU')).finrank_eq
  omega

end Step

section Sum

variable {K : Type*} [Group K] {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) K V}

theorem telescope_le {r : ℕ} (f : Fin (r + 1) → ℕ) (a : Fin r → ℕ)
    (h : ∀ i : Fin r, f i.castSucc + a i ≤ f i.succ) : f 0 + ∑ i, a i ≤ f (Fin.last r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h' := ih (fun i => f i.succ) (fun i => a i.succ) fun i => h i.succ
    rw [Fin.sum_univ_succ]
    have h0 := h 0
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0
    have hl : f (Fin.last (r + 1)) = f (Fin.last r).succ := rfl
    rw [hl]
    have h1 : f (0 : Fin (r + 1)).succ = f 1 := rfl
    simp only [h1] at h'
    omega

theorem sum_factorCodim_le {r : ℕ} (Vs : Fin (r + 1) → Subrepresentation ρ)
    (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ) (h0 : Vs 0 = ⊥)
    (hlast : Vs (Fin.last r) = ⊤) (A : Subgroup K) :
    ∑ i : Fin r, factorCodim Vs A i ≤ finrank (ZMod 2) V - finrank (ZMod 2) (fixSub ρ A) := by
  let c : Fin (r + 1) → ℕ := fun j =>
    finrank (ZMod 2) (Vs j).toSubmodule - finrank (ZMod 2) ↥((Vs j).toSubmodule ⊓ fixSub ρ A)
  have hstep : ∀ i : Fin r, c i.castSucc + factorCodim Vs A i ≤ c i.succ := by
    intro i
    have hle := hmono i
    have e1 := finrank_factor_add hle
    have e2 := finrank_inf_fixSub_le A hle
    have e3 : finrank (ZMod 2) ↥((Vs i.castSucc).toSubmodule ⊓ fixSub ρ A) ≤
        finrank (ZMod 2) (Vs i.castSucc).toSubmodule := Submodule.finrank_mono inf_le_left
    have e4 : finrank (ZMod 2) ↥((Vs i.succ).toSubmodule ⊓ fixSub ρ A) ≤
        finrank (ZMod 2) (Vs i.succ).toSubmodule := Submodule.finrank_mono inf_le_left
    have e5 : finrank (ZMod 2) ↥(fixSub (factorRep (Vs i.castSucc) (Vs i.succ)) A) ≤
        finrank (ZMod 2) ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) :=
      Submodule.finrank_le _
    unfold factorCodim
    simp only [c]
    omega
  have h := telescope_le c (fun i => factorCodim Vs A i) hstep
  have hc0 : c 0 = 0 := by
    have hb : (Vs 0).toSubmodule = ⊥ := by rw [h0]; rfl
    have key : ∀ S : Submodule (ZMod 2) V, S = ⊥ →
        finrank (ZMod 2) ↥S - finrank (ZMod 2) ↥(S ⊓ fixSub ρ A) = 0 := by
      rintro S rfl
      simp
    exact key _ hb
  have hcl : c (Fin.last r) = finrank (ZMod 2) V - finrank (ZMod 2) (fixSub ρ A) := by
    have ht : (Vs (Fin.last r)).toSubmodule = ⊤ := by rw [hlast]; rfl
    have key : ∀ S : Submodule (ZMod 2) V, S = ⊤ →
        finrank (ZMod 2) ↥S - finrank (ZMod 2) ↥(S ⊓ fixSub ρ A) =
          finrank (ZMod 2) V - finrank (ZMod 2) (fixSub ρ A) := by
      rintro S rfl
      rw [top_inf_eq, finrank_top]
    exact key _ ht
  omega

end Sum

end CFSG.LocalAnalysis.RankThreeUC.S15
