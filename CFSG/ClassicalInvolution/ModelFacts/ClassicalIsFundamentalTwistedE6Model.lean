module

public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable (p f : ℕ) [Fact p.Prime]

@[expose] noncomputable def twistedE6Phi (k : Type) [Field k] [Algebra (GaloisField p (2 * f)) k] :
    twistedE6Group p f →* ModGL TwistTag.E6.tag k :=
  (baseChangeGL (algebraMap (GaloisField p (2 * f)) k)).comp (e6IsogenyFixed (frobQ p f))

theorem ker_twistedE6Phi_le_center (k : Type) [Field k] [Algebra (GaloisField p (2 * f)) k] :
    (twistedE6Phi p f k).ker ≤ Subgroup.center (twistedE6Group p f) := by
  intro x hx
  have hx1 : e6IsogenyFixed (frobQ p f) x = 1 := by
    apply baseChangeGL_injective (algebraMap (GaloisField p (2 * f)) k)
    rw [map_one]
    exact hx
  have hker : (x : ↥(e6Data_valid.minGroup (GaloisField p (2 * f)))) ∈
      (e6IsogenyT (GaloisField p (2 * f))).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hx1
  have hc := ker_e6IsogenyT_le_center (GaloisField p (2 * f)) hker
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc y)

theorem card_galoisField_two_mul' (hf : 1 ≤ f) :
    Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ TwistTag.E6.order := by
  rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  rfl

theorem range_twistedE6Phi (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f)))).range =
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))),
        fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f)))))⁆ := by
  classical
  set K0 := GaloisField p (2 * f) with hK0
  set k := AlgebraicClosure K0 with hk
  have hodd : Odd (p ^ f) := (Nat.Prime.eq_two_or_odd' Fact.out |>.resolve_left hp2).pow
  have hK : Nat.card K0 = (p ^ f) ^ TwistTag.E6.order := card_galoisField_two_mul' p f hf
  have hfin : Finite K0 := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos
    (Fact.out : p.Prime).pos f) _).ne')
  have hCharK : CharP K0 p := inferInstance
  have hChark : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  have hFr : ∀ c : k, iterateFrobenius k p f c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hσ : ∀ c : K0, frobQ p f c = c ^ (p ^ f) := fun c => frobQ_apply p f c
  have hK2 : ringChar K0 ≠ 2 := by
    rw [ringChar.eq K0 p]
    exact hp2
  let σK : K0 ≃+* K0 := RingEquiv.ofBijective (frobQ p f)
    ⟨(frobQ p f).injective, Finite.surjective_of_injective (frobQ p f).injective⟩
  have hσK : σK.toRingHom = frobQ p f := RingHom.ext fun _ => rfl
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.E6 (Fact.out : p.Prime) hf hodd K0 hK (frobQ p f) hσ k (iterateFrobenius k p f) hFr
  have h1 := (odd_diagram_fixed_root_group_perfect TwistTag.E6 K0 hK2 σK).2.2
  rw [hσK] at h1
  have h2 := range_e6IsogenyFixed_frobQ p f hf
  rw [twistedE6Phi, MonoidHom.range_comp, h2, h1]
  exact hder.symm

section Involutions

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem orderOf_hm_neg_one (h2 : (2 : k) ≠ 0) (l : Fin τ.rank) :
    orderOf (hV.hm k l (-1)) = 2 := by
  have hsq : hV.hm k l (-1) ^ 2 = 1 := by
    rw [pow_two, ← hV.hm_mul, neg_mul_neg, one_mul, hV.hm_one]
  refine orderOf_eq_prime hsq ?_
  intro h1
  obtain ⟨a, ha⟩ := hV.exists_wt_eq_one l
  have h3 := congrArg (fun g => hV.endo k g) h1
  simp only [MinData.Valid.endo_hm, MinData.Valid.endo_one] at h3
  have h4 := congrArg (fun f : Module.End k (Fin D.d →₀ k) => f (Finsupp.single a 1) a) h3
  simp only [D.hDiag_single, ha, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    Module.End.one_apply] at h4
  apply h2
  have : ((-1 : kˣ) ^ (1 : ℤ) : kˣ) = -1 := by simp
  rw [this, Units.val_neg, Units.val_one] at h4
  linear_combination -h4

theorem hm_neg_one_ne (h2 : (2 : k) ≠ 0) {i j : Fin τ.rank} (hij : i ≠ j) :
    hV.hm k i (-1) ≠ hV.hm k j (-1) := by
  intro h
  have hdisj := (hV.torus_iSupIndep k).pairwiseDisjoint hij
  have h1 : hV.hm k i (-1) = 1 := Subgroup.disjoint_def.1 hdisj (hV.hm_mem_torus k i (-1))
    (h ▸ hV.hm_mem_torus k j (-1))
  have := orderOf_hm_neg_one hV k h2 i
  rw [h1, orderOf_one] at this
  omega

end Involutions

theorem exists_two_involutions_fixedGroup {k : Type} [Field k] (θ : k →+* k) (h2 : (2 : k) ≠ 0) :
    ∃ y₁ y₂ : fixedGroup k θ, orderOf y₁ = 2 ∧ orderOf y₂ = 2 ∧ y₁ ≠ y₂ := by
  have hfix : ∀ l : Fin (Tag.rank .E6), rhoPerm l = l →
      e6Data_valid.hm k l (-1) ∈ fixedGroup k θ := by
    intro l hl
    rw [mem_fixedGroup, sigma_hm]
    have : Units.map (θ : k →* k) (-1 : kˣ) = -1 := Units.ext (by simp)
    rw [this]
    rw [hl]
  have h1 : rhoPerm (nd 1) = nd 1 := by decide
  have h3 : rhoPerm (nd 3) = nd 3 := by decide
  refine ⟨⟨_, hfix (nd 1) h1⟩, ⟨_, hfix (nd 3) h3⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_hm_neg_one e6Data_valid k h2 (nd 1)
  · rw [Subgroup.orderOf_mk]
    exact orderOf_hm_neg_one e6Data_valid k h2 (nd 3)
  · intro h
    exact hm_neg_one_ne e6Data_valid k h2 (i := nd 1) (j := nd 3) (by decide)
      (congrArg Subtype.val h)

end CFSG.ClassicalInvolution.ModelFacts
