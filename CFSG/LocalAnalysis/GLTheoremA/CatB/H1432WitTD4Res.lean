module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432WitTD4
import CFSG.LocalAnalysis.UniqueFourCatalog.TrialityD4Odd
import CFSG.LieType.Chevalley.RootCommutatorReduction
import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnSL2
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Norm
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.Sporadic.ThSchreier.Perfect
public import CFSG.Sporadic.ThSchreier.Rigidity
public import Certificates.Certificate10091Base
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open scoped MatrixGroups

local notation "θ₄" =>
  (Pi.single (nd 0) 1 + Pi.single (nd 1) 1 + Pi.single (nd 2) 2 + Pi.single (nd 3) 1 :
    Fin d4.rank → ℤ)

private theorem commute_xTheta_slShort
    {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (d : K) (A : SL(2, K)) :
    Commute (xPar (rootOperatorFamily d4) θ₄ d) (slShort σ hσ A : adjointGroup d4 K) := by
  have hθ : IsRoot d4 θ₄ := RootOps.isRootB_iff.1 (by decide +kernel)
  have hkey : ∀ a : Fin d4.rank, a ≠ nd 2 → ∀ s ∈ [(1 : ℤ), -1],
      θ₄ ≠ s • Pi.single a 1 ∧ θ₄ ≠ -(s • Pi.single a 1) ∧
        RootOps.isRootB d4 (θ₄ + s • Pi.single a 1) = false := by
    decide +kernel
  have hO : ∀ {s : ℤ}, s = 1 ∨ s = -1 → ∀ c₀ c₁ c₃ : K,
      Commute (xPar (rootOperatorFamily d4) θ₄ d) (xOuter s c₀ c₁ c₃) := by
    intro s hs c₀ c₁ c₃
    have hs' : s ∈ [(1 : ℤ), -1] := by rcases hs with rfl | rfl <;> simp
    have h : ∀ a : Fin d4.rank, a ≠ nd 2 → ∀ c : K,
        Commute (xPar (rootOperatorFamily d4) θ₄ d)
          (xPar (rootOperatorFamily d4) (s • Pi.single a 1) c) := fun a ha c => by
      obtain ⟨h1, h2, h3⟩ := hkey a ha s hs'
      exact commute_xPar hθ (isRoot_smul_single hs a) h1 h2
        (fun h => Bool.false_ne_true (h3.symm.trans (RootOps.isRootB_iff.2 h))) d c
    exact ((h (nd 0) (by decide) c₀).mul_right (h (nd 1) (by decide) c₁)).mul_right
      (h (nd 3) (by decide) c₃)
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      (Subgroup.centralizer {xPar (rootOperatorFamily d4) θ₄ d}).comap
        ((twistedGroup σ).subtype.comp (slShort σ hσ)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;>
      refine Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    · show (slShort σ hσ (sl2Upper c) : adjointGroup d4 K) * _ =
        _ * (slShort σ hσ (sl2Upper c) : adjointGroup d4 K)
      rw [slShort_upper]
      exact (hO (Or.inl rfl) _ _ _).eq.symm
    · show (slShort σ hσ (sl2Lower c) : adjointGroup d4 K) * _ =
        _ * (slShort σ hσ (sl2Lower c) : adjointGroup d4 K)
      rw [slShort_lower]
      exact (hO (Or.inr rfl) _ _ _).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1
    (Subgroup.mem_comap.1 (hle (Sp.mem_closure_sl2 A)))).symm

private theorem twistedGroup_witness
    {K : Type} [Field K] [CharP K 3] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : Nat.card K = 27) :
    ∃ V E : Subgroup (twistedGroup σ), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      E ≤ Subgroup.normalizer (V : Set (twistedGroup σ)) ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι := WitG2.iota3 K
  have hι : ∀ n, σ (ι n) = ι n := fun n => RingHom.congr_fun (Subsingleton.elim (σ.comp ι) ι) n
  have hθr : IsRoot d4 θ₄ := RootOps.isRootB_iff.1 (by decide +kernel)
  have hθ : ∀ n, xPar (rootOperatorFamily d4) θ₄ (ι n) ∈ twistedGroup σ := fun n =>
    twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hθr)
      ((mem_twistedRootSubgroupD4_iff_of_fixed hσ hθr rfl (funext (by decide +kernel)) _).2
        ⟨ι n, hι n, rfl⟩)
  let xT : ZMod 3 → twistedGroup σ := fun n => ⟨_, hθ n⟩
  have hxT : ∀ n m, xT (n + m) = xT n * xT m := fun n m => Subtype.ext (by
    show xPar (rootOperatorFamily d4) θ₄ (ι (n + m)) =
      xPar (rootOperatorFamily d4) θ₄ (ι n) * xPar (rootOperatorFamily d4) θ₄ (ι m)
    rw [map_add, xPar_add])
  have hcT : ∀ n A, Commute (xT n) (slShort σ hσ A) := fun n A =>
    Subtype.ext (commute_xTheta_slShort hσ (ι n) A).eq
  let φ : Multiplicative (K × ZMod 3) →* twistedGroup σ :=
    MonoidHom.mk' (fun p => slShort σ hσ (sl2Upper p.toAdd.1) * xT p.toAdd.2) fun p q => by
      show slShort σ hσ (sl2Upper (p.toAdd.1 + q.toAdd.1)) * xT (p.toAdd.2 + q.toAdd.2) = _
      rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.un_sl2Upper_add, map_mul, hxT]
      exact WitG2.mul_mul_aux _ _ _ _ (hcT _ _).eq.symm
  have hneg : (-1 : SL(2, K)) ≠ 1 := fun h => WitD4.two_ne_zero_of_charThree (K := K) (by
    have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    linear_combination -h00)
  set z := slShort σ hσ (-1) with hz
  have hz1 : z ≠ 1 := fun h => hneg (slShort_injective hσ (h.trans (map_one _).symm))
  have hz2 : z ^ 2 = 1 := by rw [hz, ← map_pow, neg_one_sq, map_one]
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hcz : ∀ p, Commute (φ p) z := fun p =>
    ((Commute.neg_one_right (sl2Upper p.toAdd.1)).map (slShort σ hσ)).mul_left (hcT _ _)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hp' : slShort σ hσ (sl2Upper p.toAdd.1) * xT p.toAdd.2 = 1 := hp
    have hu : Commute (slShort σ hσ (sl2Upper p.toAdd.1)) (slShort σ hσ (sl2Lower 1)) := by
      rw [eq_inv_of_mul_eq_one_left hp']
      exact (hcT _ _).inv_left
    have hc : p.toAdd.1 = 0 := by
      have h := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0)
        (slShort_injective hσ ((map_mul _ _ _).trans (hu.eq.trans (map_mul _ _ _).symm)))
      simpa [coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] using h
    have hu0 : sl2Upper (0 : K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_sl2Upper]
    rw [hc, hu0, map_one, one_mul] at hp'
    have h3 : xPar (rootOperatorFamily d4) θ₄ (ι p.toAdd.2) =
        xPar (rootOperatorFamily d4) θ₄ 0 :=
      (congrArg Subtype.val hp').trans (xPar_zero _).symm
    have hn : p.toAdd.2 = 0 :=
      WitG2.iota3_injective K ((xPar_injective hθr h3).trans (map_zero ι).symm)
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext hc hn
  refine ⟨Subgroup.zpowers z, φ.range, fun h => hz1 (Subgroup.zpowers_eq_bot.1 h),
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num), ?_, ?_, ?_⟩
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨p, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hcz p).zpow_right k).eq.symm
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨p, hp⟩ := a.2
      obtain ⟨q, hq⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨p, rfl⟩ := hx
      rw [← map_pow, WitG2.pow_three_eq_one_K3 K p, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    show Nat.card (K × ZMod 3) = 3 ^ 4
    rw [Nat.card_prod, hK, Nat.card_eq_fintype_card, ZMod.card]
    norm_num

theorem td4Res_holds :
    TD4Res := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have hσq : ∀ c : GaloisField 3 3, frobenius (GaloisField 3 3) 3 c = c ^ 3 := fun c => by
    rw [frobenius_def]
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniqueFourCatalog.nonempty_derivedCentralQuotient_equiv_twistedGroup
      (by norm_num) hK hσq
  haveI : Finite (Module.End (GaloisField 3 3) (RootModule d4 (GaloisField 3 3))) :=
    Module.finite_of_finite (GaloisField 3 3)
  haveI : Finite TD4Model := Finite.of_equiv _ e.symm.toEquiv
  exact hasTwoLocalWitness_of_mulEquiv_exists e
    (twistedGroup_witness (sigma_three_of_card hK hσq) (hK.trans (by norm_num)))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
