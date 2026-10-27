module

public import CFSG.ClassicalInvolution.AschTight.S19FChartD4
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.Stage2.Bender.Thm1

section Fixed

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

def FixedSub : Subgroup (twistedGroup σ.toRingHom) :=
  MonoidHom.eqLocus ((Units.map (entrywiseHom σ.toRingHom)).comp (twistedIncl σ.toRingHom))
    (twistedIncl σ.toRingHom)

theorem mem_FixedSub {z : twistedGroup σ.toRingHom} :
    z ∈ FixedSub σ ↔
      Units.map (entrywiseHom σ.toRingHom) (twistedIncl σ.toRingHom z) = twistedIncl σ.toRingHom z :=
  Iff.rfl

section Equiv

variable (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
  (hσq : ∀ c, σ c = c ^ q)

include hK2 hq hK hσq

theorem twistedIncl_mem_root (z : twistedGroup σ.toRingHom) :
    twistedIncl σ.toRingHom z ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup (σ := σ.toRingHom) hK2 hq hK hσq
  rw [← h]
  exact ⟨(z : adjointGroup d4 K), z.2, rfl⟩

theorem mem_J_iff (hσ3 : ∀ c, σ (σ (σ c)) = c) (z : twistedGroup σ.toRingHom) :
    twistedIncl σ.toRingHom z ∈ trialityFieldImage σ σ ↔ z ∈ FixedSub σ := by
  have hC := twistedIncl_mem_root σ hK2 hq hK hσq z
  have h := d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨twistedIncl σ.toRingHom z, hC⟩
  rw [mem_FixedSub]
  refine h.trans ?_
  constructor
  · intro hz
    have := congrArg Subtype.val hz
    rwa [coe_fieldActor] at this
  · intro hz
    refine Subtype.ext ?_
    rw [coe_fieldActor]
    exact hz

def fixedSubEquivJ (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    ↥(FixedSub σ) ≃* ↥(trialityFieldImage σ σ) :=
  MulEquiv.ofBijective
    (((twistedIncl σ.toRingHom).comp (FixedSub σ).subtype).codRestrict (trialityFieldImage σ σ)
      (fun z => (mem_J_iff σ hK2 hq hK hσq hσ3 z.1).2 z.2))
    ⟨fun a b h => by
      have h1 : twistedIncl σ.toRingHom a.1 = twistedIncl σ.toRingHom b.1 :=
        congrArg (Subtype.val : ↥(trialityFieldImage σ σ) → ModGL TwistTag.D4.tag K) h
      exact Subtype.ext (CFSG.ClassicalInvolution.G2D4Models.twistedIncl_injective σ.toRingHom h1), by
      rintro ⟨g, hg⟩
      have hgC : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
        d4_trialityFieldImage_self_le σ hg
      have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup (σ := σ.toRingHom) hK2 hq hK hσq
      rw [← h] at hgC
      obtain ⟨a, ha, rfl⟩ := hgC
      refine ⟨⟨⟨a, ha⟩, (mem_J_iff σ hK2 hq hK hσq hσ3 ⟨a, ha⟩).1 hg⟩, rfl⟩⟩

end Equiv

section FixedElements

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F CFSG.LocalAnalysis.ComponentInitial
  Matrix.SpecialLinearGroup

variable (hσ3 : ∀ c, σ (σ (σ c)) = c)

include hσ3

theorem slLong_mem_FixedSub (A : SL(2, fixedField σ.toRingHom)) :
    slLong σ.toRingHom hσ3 A ∈ FixedSub σ := by
  rw [mem_FixedSub]
  have h := slLong_entrywise (σ := σ.toRingHom) hσ3 σ (fun c => rfl) A
  have hA : Matrix.SpecialLinearGroup.map (fixRestrict σ (fun c => rfl)).toRingHom A = A := by
    refine Subtype.ext ?_
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (coe_fixRestrict (σ := σ.toRingHom) σ (fun c => rfl) (A.1 i j)).trans (A.1 i j).2
  rw [hA] at h
  exact h

theorem slShort_mem_FixedSub (A : SL(2, K)) (hA : Matrix.SpecialLinearGroup.map σ.toRingHom A = A) :
    slShort σ.toRingHom hσ3 A ∈ FixedSub σ := by
  rw [mem_FixedSub]
  have h := slShort_entrywise (σ := σ.toRingHom) hσ3 σ (fun c => rfl) A
  rw [hA] at h
  exact h

theorem nHat_zero_mem_FixedSub : nHat σ.toRingHom (ng 0) ∈ FixedSub σ := by
  obtain ⟨A, hA⟩ := CFSG.ClassicalInvolution.ModelFacts.rankOne_long_le_range_slLong σ.toRingHom hσ3 (nHat_mem_rankOne σ.toRingHom (ng 0))
  rw [← hA]
  exact slLong_mem_FixedSub σ hσ3 A

theorem nHat_one_mem_FixedSub : nHat σ.toRingHom (ng 1) ∈ FixedSub σ := by
  have hσ3' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have h1 : σ.toRingHom (1 : K) = 1 := map_one _
  have h2 : σ.toRingHom (-1 : K) = -1 := by rw [map_neg, map_one]
  have e : nHat σ.toRingHom (ng 1) = slShort σ.toRingHom hσ3'
      (sl2Upper (1 : K) * sl2Lower (-1 : K) * sl2Upper (1 : K)) := by
    refine Subtype.ext ?_
    rw [map_mul, map_mul]
    rw [nHat_val, nHatE_one_eq, Subgroup.coe_mul, Subgroup.coe_mul, slShort_upper,
      slShort_lower]
    simp only [h1, h2]
  rw [e]
  refine slShort_mem_FixedSub σ hσ3 _ ?_
  refine Subtype.ext ?_
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, LieType.Steinberg.sl2Upper,
      LieType.Steinberg.sl2Lower]

end FixedElements

end Fixed

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
