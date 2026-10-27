module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameLift
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.PGroup
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.QuatWeyl
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWInvolution

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1

section Kernel

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ℓ f : ℕ}

theorem frameWeyl_ker_mem (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {x : frameNorm F} (hx : x ∈ (frameWeyl F).ker) :
    frameConj F x ∈ twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) := by
  have h1 : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨frameConj F x, x.2⟩ = 1 := hx
  have hT : frameConj F x ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) := by
    refine mem_torusGroup_of_mapsRootLines_one x.2 ?_
    have := mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := AlgebraicClosure K)
      ⟨frameConj F x, x.2⟩
    rwa [h1] at this
  refine mem_twistedTorusOf.2 ⟨hT, ?_⟩
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      F.Fr.comp (algebraMap K (AlgebraicClosure K)) :=
    RingHom.ext fun c => by simp [hσ, F.hFr, map_pow]
  have hfix := triEmb_fixed (K := K) (σ := σ) (L := AlgebraicClosure K) F.Fr hcomm (x : _)
  rw [frameConj_apply]
  simp only [map_mul, map_inv, hfix, F.hg0]
  group

theorem frameWeyl_ker_card_odd [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1)) :
    Odd (Nat.card (frameWeyl F).ker) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (by omega : 1 ≤ f * 3) (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  let j : (frameWeyl F).ker →*
      twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) :=
    ((frameConj F).comp ((frameNorm F).subtype.comp (frameWeyl F).ker.subtype)).codRestrict _
      fun x => frameWeyl_ker_mem hσ F x.2
  have hj : Function.Injective j := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (frameConj_injective F h'))
  have hdvd := Subgroup.card_dvd_of_injective j hj
  have hT := twistedTorus_D4_eq_map_of_weylImage F.Fr F.hn F.w F.hnw (d4T36M (-1)) F.hw
  have hcard : Nat.card (twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr)) =
      d4T36d (-1) (ℓ ^ f) * d4T36d (-1) (ℓ ^ f) := by
    rw [hT, Subgroup.card_map_of_injective rootDiagUnit_injective]
    exact d4T36_card (Or.inr rfl) hq1 hℓq F.hFr
  rw [hcard] at hdvd
  exact Odd.of_dvd_nat (Odd.mul (d4T36d_odd (Or.inr rfl) hq1) (d4T36d_odd (Or.inr rfl) hq1)) hdvd

end Kernel

section Torus

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ℓ f : ℕ}

theorem frameTorus_le_frameNorm (F : D4PhiFrame K σ (ℓ ^ f) (-1)) :
    frameTorus F ≤ frameNorm F := fun y hy =>
  torusGroup_le_monomialSubgroup (mem_twistedTorusOf.1 hy).1

theorem frameTorus_mem_ker (F : D4PhiFrame K σ (ℓ ^ f) (-1)) {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hy : y ∈ frameTorus F) :
    ∃ hy' : y ∈ frameNorm F, (⟨y, hy'⟩ : frameNorm F) ∈ (frameWeyl F).ker := by
  refine ⟨frameTorus_le_frameNorm F hy, ?_⟩
  have hT : frameConj F y ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 hy).1
  change weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)
    ⟨frameConj F y, torusGroup_le_monomialSubgroup hT⟩ = 1
  exact weylQuotientHom_eq (by simpa using mapsRootLines_of_mem_torusGroup hT)

theorem frameTorus_comm (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {x y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : x ∈ frameTorus F)
    (hy : y ∈ frameTorus F) : x * y = y * x := by
  apply frameConj_injective F
  rw [map_mul, map_mul]
  exact torusGroup_comm (mem_twistedTorusOf.1 hx).1 (mem_twistedTorusOf.1 hy).1

theorem conj_mem_frameTorus (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hg : g ∈ frameNorm F)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hy : y ∈ frameTorus F) :
    g * y * g⁻¹ ∈ frameTorus F := by
  obtain ⟨hy', hker⟩ := frameTorus_mem_ker F hy
  have hn : (⟨g, hg⟩ : frameNorm F) * ⟨y, hy'⟩ * (⟨g, hg⟩ : frameNorm F)⁻¹ ∈ (frameWeyl F).ker :=
    (frameWeyl F).normal_ker.conj_mem _ hker _
  have := frameWeyl_ker_mem hσ F hn
  exact this

end Torus

section Opposition

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ℓ f : ℕ}

theorem involution_inv_frameTorus (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {s : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hs : s ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hw : triEmb K σ (AlgebraicClosure K) w =
      F.g0 * (s * trialityOpposition (AlgebraicClosure K)) * F.g0⁻¹)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hy : y ∈ frameTorus F) :
    w * y * w⁻¹ = y⁻¹ := by
  have hφw : frameConj F w = s * trialityOpposition (AlgebraicClosure K) := by
    rw [frameConj_apply, hw]
    group
  have hyT : frameConj F y ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 hy).1
  have hcomm : s * (frameConj F y)⁻¹ * s⁻¹ = (frameConj F y)⁻¹ := by
    have := torusGroup_comm hs (inv_mem hyT)
    calc s * (frameConj F y)⁻¹ * s⁻¹ = ((frameConj F y)⁻¹ * s) * s⁻¹ := by rw [this]
      _ = (frameConj F y)⁻¹ := mul_inv_cancel_right _ _
  have hzu := trialityOpposition_conj_torus hyT
  apply frameConj_injective F
  rw [map_mul, map_mul, map_inv, map_inv, hφw]
  calc s * trialityOpposition (AlgebraicClosure K) * frameConj F y *
        (s * trialityOpposition (AlgebraicClosure K))⁻¹
      = s * (trialityOpposition (AlgebraicClosure K) * frameConj F y *
          (trialityOpposition (AlgebraicClosure K))⁻¹) * s⁻¹ := by group
    _ = (frameConj F y)⁻¹ := by rw [hzu, hcomm]

end Opposition

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
