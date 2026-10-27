module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Triple59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKComp

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeKMU

theorem eq_of_sup_oddCore
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) {X : Type} [Group X] [Finite X]
    (hsimp : IsSimpleGroup X) (hnab : ∃ x y : X, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog X) {w : X} (hw : orderOf w = 2)
    {M N E : Subgroup X} (hMq : IsQuasisimple ↥M) (hM2 : 2 ∣ Nat.card M)
    (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X)))) (hMN : M ≤ N)
    (hMO : M ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) (hEw : E ≤ centralizer ({w} : Set X))
    (hEM : ∀ e ∈ E, ∀ m ∈ M, e * m = m * e) (hEe : IsElemTwo E) (hE8 : 8 ≤ Nat.card E)
    (hWE : wGroup E = ⊥) : N = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMperf : ⁅M, M⁆ = M := isPerfect_iff.mp hMq.1
  have hEN : E ≤ normalizer (N : Set X) := by
    intro e he
    have hew : (MulAut.conj e) w = w := by
      rw [MulAut.conj_apply, mem_centralizer_singleton_iff.mp (hEw he), mul_inv_cancel_right]
    obtain ⟨hNe, hNep⟩ := GSLit.isPComponent_map_centralizer (MulAut.conj e) hNw hNp
    rw [hew] at hNe hNep
    have hMNe : M ≤ N.map (MulAut.conj e).toMonoidHom := fun m hm => ⟨m, hMN hm, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hEM e he m hm, mul_inv_cancel_right]⟩
    have heq := GrS5.eq_of_isPComponent_of_le hNw hNe hNp hNep hMN hMNe hMperf hM2
    rw [mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have h : e * n * e⁻¹ ∈ N.map (MulAut.conj e).toMonoidHom := ⟨n, hn, rfl⟩
      rwa [← heq] at h
    · intro hn
      rw [heq] at hn
      obtain ⟨n', hn', h⟩ := hn
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      rwa [← mul_left_cancel (mul_right_cancel h)]
  have hEcen : ∀ e ∈ E, ∀ l ∈ N, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥N).map N.subtype := by
    intro e he l hl
    have hl' : l ∈ ((M ⊔ (pPrimeCore 2 ↥N).map N.subtype : Subgroup X) : Set X) := by
      rw [hMO]
      exact hl
    rw [UnbalancedGS.coe_sup_primeCore_eq_mul hMN] at hl'
    obtain ⟨m, hm, o, ho, rfl⟩ := hl'
    have hem := hEM e he m hm
    have hy : e * o * e⁻¹ * o⁻¹ ∈ (pPrimeCore 2 ↥N).map N.subtype :=
      mul_mem (HeUV.conj_mem_of_normalizer (hEN he) ho) (inv_mem ho)
    have h := HeUV.conj_mem_of_normalizer (le_normalizer (hMN hm)) hy
    have heq : e * (m * o) * e⁻¹ * (m * o)⁻¹ = m * (e * o * e⁻¹ * o⁻¹) * m⁻¹ := by
      calc e * (m * o) * e⁻¹ * (m * o)⁻¹ = (e * m) * o * e⁻¹ * o⁻¹ * m⁻¹ := by group
        _ = (m * e) * o * e⁻¹ * o⁻¹ * m⁻¹ := by rw [hem]
        _ = m * (e * o * e⁻¹ * o⁻¹) * m⁻¹ := by group
    rw [heq]
    exact h
  have hO := oddCore_le_center_of_wGroup_eq_bot hNw hNp hEw hEe.1 hEe.2 (by omega) hEN hEcen hWE
    (fun e he he1 => GrS5.commutator_oddCore_pLayer_le hS hU hheld hK hw hNw hNp
      (mem_centralizer_singleton_iff.mp (hEw he)).symm (HeKC.centralizer_ne_top hsimp hnab he1))
    (Or.inr hE8)
  have hNperf : commutator ↥N = ⊤ := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hNp
    exact (Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hNw).toMonoidHom)
      (subgroupOfEquivOfLe hNw).surjective).commutator_eq_top
  have htop : M.subgroupOf N ⊔ center ↥N = ⊤ := by
    have h1 : ((pPrimeCore 2 ↥N).map N.subtype).subgroupOf N = pPrimeCore 2 ↥N :=
      comap_map_eq_self_of_injective N.subtype_injective _
    have h2 : M.subgroupOf N ⊔ pPrimeCore 2 ↥N = ⊤ := by
      rw [← h1, ← subgroupOf_sup hMN (map_subtype_le _), hMO, subgroupOf_self]
    rw [eq_top_iff, ← h2]
    refine sup_le_sup_left (fun x hx => mem_center_iff.mpr fun g => ?_) _
    exact Subtype.ext (hO _ (mem_map_of_mem _ hx) g g.2).symm
  have hMtop := eq_top_of_sup_center_eq_top hNperf htop
  refine le_antisymm (fun n hn => ?_) hMN
  have h : (⟨n, hn⟩ : ↥N) ∈ M.subgroupOf N := hMtop ▸ mem_top _
  exact h

end HeKMU

end CFSG.ComponentClassification.GrSLit
