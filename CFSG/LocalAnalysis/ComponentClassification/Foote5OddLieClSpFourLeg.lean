module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem eq_one_of_commute_leg_of_odd [Finite K] (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    {A : gsp r K} {d : K} (hd : d ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    {S : StatedSp r K} {e : K} (he : e ≠ 0)
    (hSS : ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e • 1)
    (hcomm : ∀ D : gsp r K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ∃ m : ℕ, conjAut r K (D ^ 2 ^ m) = 1)
    {x : MulAut (StatedProj (StatedSp r K))} (hodd : Odd (orderOf x))
    (hxt : x * conjAut r K A = conjAut r K A * x)
    (hxS : x * conjProjH (StatedSp r K) S = conjProjH (StatedSp r K) S * x) : x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hp3 : (Nat.card K).Prime := by rw [h3]; norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three h3
  have hK : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.spec K 2
    exact_mod_cast (this.2 (by rw [h])))
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr x
  have hτ : τ = 1 := ringEquiv_eq_one_of_prime_card hp3 τ
  subst hτ
  rw [map_one, mul_one] at hodd hxt hxS ⊢
  have hS' : conjAut r K ⟨S, statedSp_le_gsp S.2⟩ = conjProjH (StatedSp r K) S :=
    Burgoyne.Sp.conjAut_statedSp S
  rw [← hS'] at hxS
  have h1 := pow_orderOf_succ_commute (by omega) hd hAA hxt hodd
  set SG : gsp r K := ⟨S, statedSp_le_gsp S.2⟩ with hSG
  have hSS' : ((SG : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((SG : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e • 1 := hSS
  have h2' := pow_orderOf_succ_commute (by omega) he hSS' hxS hodd
  obtain ⟨m, hm⟩ := hcomm _ h1 h2'
  rw [map_pow, conjAut_pow_orderOf_succ] at hm
  exact UnbalancedCatalog.SpChain.eq_one_of_odd_orderOf hodd hm

theorem conjProjH_eq_one_of_smul [Finite K] (hr : 1 ≤ r) {g : StatedSp r K} {c : K} (hc : c ≠ 0)
    (hg : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = c • 1) :
    conjProjH (StatedSp r K) g = 1 := by
  rw [← Burgoyne.Sp.conjAut_statedSp, conjAut_eq_one_iff hr]
  refine ⟨Units.mk0 c hc, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact hg.trans (smul_one_eq_diagonal c)

theorem conj_mem_of_mem_closure {i : MulAut (StatedProj (StatedSp r K))}
    {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    {t : StatedProj (StatedSp r K)} (ht : t ∈ closure {s | i s = s ∧ Odd (orderOf s)})
    {y : MulAut (StatedProj (StatedSp r K))} (hy : y ∈ R) :
    MulAut.conj t * y * (MulAut.conj t)⁻¹ ∈ R :=
  (mem_normalizer_iff.mp (conj_mem_normalizer hRc ht) y).mp hy

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
