module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem exists_fixed_embedding_of_fieldAut {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Group K] {θ : K ≃* projectiveSL n F} {α : MulAut K}
    {β : MulAut (projectiveSL n F)} (hβdef : β = MulAut.congr θ α) (σ : F ≃+* F)
    (H : GL (Fin n) F) (hβh : β = conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹) :
    ∃ ι : StatedProj (StatedSL n (semilinearFixedSubfield σ)) →* K,
      Function.Injective ι ∧ ∀ y, α (ι y) = ι y := by
  classical
  let k := semilinearFixedSubfield σ
  have hInj : Function.Injective (linearSubfieldInclusion n k) :=
    linearSubfieldInclusion_injective (K := F) (n := n) (by omega) k
  have hfix : ∀ x : projectiveSL n k,
      fieldAut n F σ (linearSubfieldInclusion n k x) = linearSubfieldInclusion n k x :=
    fun x => fieldAut_linearSubfieldInclusion
      (fun c hc => (RingHom.mem_eqLocusField).mp hc) x
  let ι : StatedProj (StatedSL n k) →* K :=
    { toFun := fun y =>
        θ.symm (conjAut n F H (linearSubfieldInclusion n k (statedProjSLEquiv n k y)))
      map_one' := by simp
      map_mul' := by intro x y; simp [map_mul] }
  have hιinj : Function.Injective ι := by
    intro x y hxy
    change θ.symm (conjAut n F H (linearSubfieldInclusion n k
        (statedProjSLEquiv n k x))) =
      θ.symm (conjAut n F H (linearSubfieldInclusion n k
        (statedProjSLEquiv n k y))) at hxy
    exact (statedProjSLEquiv n k).injective (hInj ((conjAut n F H).injective
      (θ.symm.injective hxy)))
  refine ⟨ι, hιinj, fun y => ?_⟩
  have hfz : fieldAut n F σ (linearSubfieldInclusion n k (statedProjSLEquiv n k y)) =
      linearSubfieldInclusion n k (statedProjSLEquiv n k y) := hfix _
  have hβz : β (conjAut n F H (linearSubfieldInclusion n k (statedProjSLEquiv n k y))) =
      conjAut n F H (linearSubfieldInclusion n k (statedProjSLEquiv n k y)) := by
    rw [hβh]
    simp [MulAut.mul_apply, hfz]
  have hθι : θ (ι y) =
      conjAut n F H (linearSubfieldInclusion n k (statedProjSLEquiv n k y)) := by
    change θ (θ.symm (conjAut n F H (linearSubfieldInclusion n k
      (statedProjSLEquiv n k y)))) = _
    rw [MulEquiv.apply_symm_apply]
  have hθα : β (θ (ι y)) = θ (α (ι y)) := by
    rw [hβdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  apply θ.injective
  rw [← hθα, hθι]
  exact hβz

theorem psl_prime_outer_fixed_subfield_embedding {K : Type} [Group K] {n ℓ f : ℕ} (hn : 3 ≤ n)
    (hcl : StatedClassicalModel K .PSL n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1)) (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ℓ), Nat.card k = ℓ ^ (f / p) ∧
      ∃ ι : StatedProj (StatedSL n k) →* K, Function.Injective ι ∧ ∀ y, α (ι y) = ι y := by
  classical
  obtain ⟨⟨hℓ, hf, -, -, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  have : CharP F ℓ := charP_of_card_eq_prime_pow hFcard'
  have hdiv' : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := by rw [hFcard]; exact hdiv
  let θ : K ≃* projectiveSL n F := e.trans (statedProjSLEquiv n F)
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n F) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ semilinearAutGroup n F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow
      hn (hp.odd_of_ne_two hp2) hβp
  by_cases hD : β ∈ linearAutGroup n F
  · refine absurd (CFSG.RankThree.PartOne.OutStructure.linear_D2 hp hn hdiv' β hD 1 ?_) hβout
    rw [pow_one, hβp]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem
  obtain ⟨hpf, σ, -, ⟨h, hh, hβh⟩, hcardk⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ hf hn hFcard hp β hβE hD hβord
  obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
  obtain ⟨ι, hιinj, hfixι⟩ := exists_fixed_embedding_of_fieldAut hn hβdef σ H hβh
  exact ⟨hpf, semilinearFixedSubfield σ, inferInstance, Subtype.finite, inferInstance, hcardk,
    ι, hιinj, hfixι⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
