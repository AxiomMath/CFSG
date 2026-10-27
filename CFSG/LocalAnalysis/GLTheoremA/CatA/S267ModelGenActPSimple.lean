module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActCentral
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

private theorem chevQuotHom_ker_le_center (hcore : GLAPPrimeCore p ↥S = ⊥) :
    (chevQuotHom p S).ker ≤ Subgroup.center ↥S := by
  intro x hx
  refine Subgroup.mem_center_iff.2 fun s => ?_
  have hx' : pQuotHom p S x ∈ Subgroup.center (PQuot p S) := by
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff _).1 hx
  have hinj : Function.Injective (pQuotHom p S) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_pQuotHom, hcore]
  apply hinj
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 hx' (pQuotHom p S s)

theorem exists_actHom_pSimple (hS : S.Normal) (hperf : ⁅S, S⁆ = S) {X : Type} [Group X]
    (e : PSimple p S ≃* X) :
    ∃ Γ : Ω →* MulAut X, (∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom p S g)) =
        e (chevQuotHom p S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩)) ∧
      Γ.ker = centModSubgroup p S := by
  have hN : ∀ b : Ω, b ∈ Subgroup.normalizer (S : Set Ω) := fun b =>
    (Subgroup.normalizer_eq_top_iff.2 hS).symm ▸ Subgroup.mem_top b
  set Γ : Ω →* MulAut X := (MulAut.congr e).toMonoidHom.comp
    ((chevAut p S).comp ((MonoidHom.id Ω).codRestrict _ hN)) with hΓ
  have hΓb : ∀ b : Ω, Γ b = MulAut.congr e (chevAut p S ⟨b, hN b⟩) := fun b => rfl
  haveI : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.2 hperf
  haveI : Group.IsPerfect (PQuot p S) := Group.IsPerfect.ofSurjective (pQuotHom_surjective p S)
  refine ⟨Γ, fun b g => ?_, ?_⟩
  · rw [hΓb, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, chevAut_chevQuotHom]
    rfl
  · ext b
    rw [MonoidHom.mem_ker, hΓb, map_eq_one_iff _ (MulAut.congr e).injective, ← centMod_iff,
      ← chev_barAut_eq_one_iff_centMod (hN b)]
    show CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (PQuot p S)
      (barAut p S ⟨b, hN b⟩) = 1 ↔ _
    rw [← map_one (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
      (PQuot p S))]
    exact (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
      (PQuot p S)).eq_iff

theorem concA_of_actData_pSimple (hp : p.Prime) (hp2 : p ≠ 2) (hS : S.Normal)
    (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {X : Type} [Group X] [Finite X]
    (e : PSimple p S ≃* X) (α : ↥B → MulAut X)
    (hα : ∀ (x : ↥B) (g : ↥S),
      e (chevQuotHom p S ⟨(x : Ω) * g * (x : Ω)⁻¹, hS.conj_mem _ g.2 _⟩) =
        α x (e (chevQuotHom p S g)))
    (hW : ActData p B α) : S267ConcA p S B := by
  refine concA_of_actData_central hp hp2 hS hperf hcore hB hBC
    (e.toMonoidHom.comp (chevQuotHom p S)) (e.surjective.comp (chevQuotHom_surjective p S))
    ?_ α hα hW
  intro x hx
  refine chevQuotHom_ker_le_center hcore ?_
  rw [MonoidHom.mem_ker] at hx ⊢
  exact (map_eq_one_iff e e.injective).1 hx

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
