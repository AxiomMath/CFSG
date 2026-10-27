module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36A

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem perm_eq_of_conj_eq {r : ℕ} (hr : 4 ≤ r) {σ τ : Perm (Fin r)}
    (h : ∀ a : alternatingGroup (Fin r), σ * (a : Perm (Fin r)) * σ⁻¹ = τ * a * τ⁻¹) :
    σ = τ := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup r hr
  exact MulEquiv.ext fun a => Subtype.ext (h a)

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.eq_of_conj (hρ : IsPermAction θ ρ) (hr : 4 ≤ r)
    {g : ↥(normalizer (M : Set X))} {τ : Perm (Fin r)}
    (h : ∀ x : ↥M, ((θ ((M.normalizerMonoidHom g x : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) :
        alternatingGroup (Fin r)) : Perm (Fin r)) =
      τ * (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin r)) * τ⁻¹) : ρ g = τ := by
  refine perm_eq_of_conj_eq hr fun a => ?_
  obtain ⟨q, rfl⟩ := θ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← hρ g x, h x]

theorem IsPermAction.card_support_eq {θ' : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ' : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θ ρ)
    (hρ' : IsPermAction θ' ρ') (hr5 : 5 ≤ r) (hr6 : r ≠ 6) (g : ↥(normalizer (M : Set X))) :
    (ρ' g).support.card = (ρ g).support.card := by
  classical
  obtain ⟨π, hπ⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj r hr5 hr6).2
      (θ.symm.trans θ')
  have hθ' : ∀ q, (θ' q : Perm (Fin r)) = π * (θ q : Perm (Fin r)) * π⁻¹ := by
    intro q
    have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin r)) =>
      ((φ (θ q) : alternatingGroup (Fin r)) : Perm (Fin r))) hπ
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [← h1]
    rfl
  have h1 : ρ' g = π * ρ g * π⁻¹ := by
    refine hρ'.eq_of_conj (by omega) fun x => ?_
    rw [hθ', hθ', hρ g x]
    group
  rw [h1, Perm.card_support_conj]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem exists_isPermAction_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htM : t ∈ normalizer (M : Set X)) (hJM : J ≤ M)
    {m : ℕ} (hnm : n < m) (θ₀ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)) :
    ∃ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)),
      IsPermAction θ ρ ∧ (ρ ⟨t, htM⟩).support.card + n = m := by
  have hn9 := S.nine_le
  have hZ := fusionZStar_eq_of_alt (by omega) θ₀
  let eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans θ₀
  obtain ⟨θ, τ, -, hτ, -, hcard⟩ :=
    S.exists_perm_of_pumped hT13 hML hSch hMY hMpc htM hJM hnm eM
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  refine ⟨θ, ρ, hρ, ?_⟩
  rw [hρ.eq_of_conj (by omega) hτ]
  exact hcard

theorem centralizer_le_of_four_of_add_four (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} {m : ℕ}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHM : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hm : m = n + 4)
    (hker : normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M ≤
      (pPrimeCore 2 ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).map
        (normalizer (Sol78.signalizerCompletion E E : Set X)).subtype)
    {θ' : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ' : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ' : IsPermAction θ' ρ') {x : X}
    (hxH : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hx2 : x * x = 1)
    (hx4 : (ρ' ⟨x, hHM hxH⟩).support.card = 4) :
    centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hn9 := S.nine_le
  have hCt := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    hCt (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨θ, ρ, hρ, hcard⟩ := S.exists_isPermAction_of_pumped hT13 hML hSch hMH hMpc
    (hHM htH) hJM (by omega) θ'
  have hx4' : (ρ ⟨x, hHM hxH⟩).support.card = 4 :=
    (hρ.card_support_eq hρ' (by omega) (by omega) _).symm.trans hx4
  exact S.centralizer_le_of_conj_t h33 h35 hT13 hML hSch (by omega) hMH hHM hker hρ (hHM htH)
    (by omega) hxH hx2 hx4'

end Sig36

end CFSG.ComponentClassification.SolMax
