module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.RankThree.PartOne.KE.CTRational

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

section Descent

variable {ℓ f : ℕ} {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem langDescent_twE6 (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (D : LangDatum Tag.E6 L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) :
    LangDescent D p
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) := by
  classical
  obtain ⟨hfin, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  have hfix : D.fix = twistedFixedGroup TwistTag.E6 L Fr := by
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  set R' := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  set ι : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype with hι
  have hrange : ι.range = C' := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨hfix ▸ hfin, hfix ▸ hrange ▸ hle, fun P hPX hP => ?_, hfix ▸ hrange ▸ hder⟩
  rw [hfix] at hPX
  change P ≤ ι.range
  rw [hrange]
  have hPfin : Finite P :=
    @Finite.of_injective P ↥R' hfin _ (Subgroup.inclusion_injective hPX)
  exact @le_of_isPGroup_of_index_eq_pow _ _ C' R' P hPX hnormal p 3 k hp Nat.prime_three
    (by omega) hk hPfin hP

end Descent

end CFSG.HardMathSupport.Timmesfeld.LangTorus
