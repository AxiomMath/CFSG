module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJInv
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJTorus
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJTorsion
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWInvolution
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJFrameOf
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJLangG2
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJNumerics
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJRoots
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryGraph

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)


section FieldActor

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

theorem fieldActor_eq_iff (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L))
    (y : 𝒞[K, σ]) :
    fieldActor (t := TwistTag.D4) σ σ y = y ↔
      diagramMap TwistTag.D4 L * triEmb K σ L y = triEmb K σ L y * diagramMap TwistTag.D4 L := by
  have h := triEmb_fieldActor Fr hcomm y
  constructor
  · intro hy
    rw [hy] at h
    calc diagramMap TwistTag.D4 L * triEmb K σ L y
        = diagramMap TwistTag.D4 L * ((diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L y *
            diagramMap TwistTag.D4 L) := by rw [← h]
      _ = triEmb K σ L y * diagramMap TwistTag.D4 L := by group
  · intro hy
    apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [h]
    calc (diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L y * diagramMap TwistTag.D4 L
        = (diagramMap TwistTag.D4 L)⁻¹ * (triEmb K σ L y * diagramMap TwistTag.D4 L) :=
          mul_assoc _ _ _
      _ = (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * triEmb K σ L y) := by
          rw [hy]
      _ = triEmb K σ L y := by group

end FieldActor

section Involution

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {r : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem invTuple_invariant (xy : Fin Tag.G2.rank → Lˣ) (i : Fin TwistTag.D4.tag.rank) :
    invTuple xy (TwistTag.D4.perm i) = invTuple xy i := by
  fin_cases i <;> rfl

theorem commute_diagramMap_rootDiagUnit {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha : ∀ i, a (TwistTag.D4.perm i) = a i) :
    diagramMap TwistTag.D4 L * rootDiagUnit TwistTag.D4.tag a =
      rootDiagUnit TwistTag.D4.tag a * diagramMap TwistTag.D4 L := by
  have h1 := diagramMap_pow_conj_rootDiagUnit (L := L) a 1
  have hfun : (fun i => a (((TwistTag.D4.perm.symm) ^ 1) i)) = a := by
    funext i
    have := ha (TwistTag.D4.perm.symm i)
    simpa using this.symm
  rw [hfun, pow_one] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem weylTwist_jW2 : weylTwist TwistTag.D4 jW2 = jW2 := by
  refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x, y = permLattice TwistTag.D4.perm x :=
    ⟨permLattice TwistTag.D4.perm.symm y, by ext j; simp [permLattice]⟩
  rw [weylTwist_smul_permLattice]
  exact (jWeyl_zero_spec.2.1 x).symm

theorem exists_J_involution (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (F : D4PhiFrame ℓ f K σ (-1) r L) {g₂ : ModGL TwistTag.D4.tag L}
    (hg₂C : g₂ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₂P : diagramMap TwistTag.D4 L * g₂ = g₂ * diagramMap TwistTag.D4 L)
    (hg₂F : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g₂ = g₂ * jRep L jW2)
    (hg0 : F.g0 = jG0 L jU g₂) :
    ∃ s ∈ torusGroup TwistTag.D4.tag L, ∃ w : 𝒞[K, σ],
      triEmb K σ L w = F.g0 * (s * trialityOpposition L) * F.g0⁻¹ ∧ w * w = 1 ∧
      fieldActor (t := TwistTag.D4) σ σ w = w ∧
      ∀ y : 𝒞[K, σ], F.g0⁻¹ * triEmb K σ L y * F.g0 ∈
          twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) →
        F.g0⁻¹ * triEmb K σ L (w * y * w⁻¹) * F.g0 =
          (F.g0⁻¹ * triEmb K σ L y * F.g0)⁻¹ := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  set Fh := twistHom TwistTag.D4 L Fr with hFh
  set z := trialityOpposition L with hz
  set P := diagramMap TwistTag.D4 L with hP
  set nU := jRep L jU with hnU
  set n₂ := jRep L jW2 with hn₂
  have hn₂P : P * n₂ = n₂ * P :=
    diagramMap_comm_canonicalRep ((mem_relWeylTwist TwistTag.D4).2 weylTwist_jW2)
  have hM : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n₂, jRep_mem_monomial jW2⟩ • x =
      jMw *ᵥ permLattice TwistTag.D4.perm.symm x := fun x => by
    rw [weylQuotientHom_jRep]
    exact jW2_smul_eq x
  obtain ⟨xy, hxy⟩ := exists_invariant_lang_opposition Fr hFr (jRep_mem_monomial jW2) hn₂P jMw hM
    jMbar jMw_proj (jMbar_det_ne_zero (ℓ ^ f))
  set a := invTuple xy with ha
  set da := rootDiagUnit TwistTag.D4.tag a with hda
  have hdaT : da ∈ torusGroup TwistTag.D4.tag L := rootDiagUnit_mem_torusGroup a
  have hdaP : P * da = da * P := commute_diagramMap_rootDiagUnit (invTuple_invariant xy)
  have hzP : P * z = z * P := diagramMap_comm_trialityOpposition
  have hzz : z * z = 1 := by
    have := trialityOpposition_sq (K := L)
    rwa [pow_two] at this
  have hnUM : nU ∈ monomialSubgroup TwistTag.D4.tag L := jRep_mem_monomial jU
  have hsT : nU * da * nU⁻¹ * (nU * z * nU⁻¹ * z⁻¹) ∈ torusGroup TwistTag.D4.tag L := by
    refine mul_mem ?_ (n_conj_opposition_mem_torus hnUM)
    rw [hda, monomial_conj_rootDiagUnit hnUM]
    exact rootDiagUnit_mem_torusGroup _
  set s := nU * da * nU⁻¹ * (nU * z * nU⁻¹ * z⁻¹) with hs
  have hsz : s * z = nU * (da * z) * nU⁻¹ := by
    rw [hs]
    group
  have hŵ : F.g0 * (s * z) * F.g0⁻¹ = g₂ * (da * z) * g₂⁻¹ := by
    have hg0' : F.g0 = g₂ * nU⁻¹ := hg0
    rw [hg0', hsz]
    group
  have hdaA : da ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' hdaT
  have hzA : z ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' trialityOpposition_mem_monomialSubgroup
  have hŵA : g₂ * (da * z) * g₂⁻¹ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem hg₂C (mul_mem hdaA hzA)) (inv_mem hg₂C)
  have hzF : Fh z = z := twistHom_trialityOpposition Fr
  have hŵF : Fh (g₂ * (da * z) * g₂⁻¹) = g₂ * (da * z) * g₂⁻¹ := by
    have hl : n₂ * Fh (da * z) * n₂⁻¹ = da * z := hxy
    rw [map_mul, map_mul, map_inv, hg₂F]
    calc g₂ * n₂ * Fh (da * z) * (g₂ * n₂)⁻¹
        = g₂ * (n₂ * Fh (da * z) * n₂⁻¹) * g₂⁻¹ := by group
      _ = g₂ * (da * z) * g₂⁻¹ := by rw [hl]
  have hrange : Subgroup.zpowers (g₂ * (da * z) * g₂⁻¹) ≤ (triEmb K σ L).range := by
    refine F.hperf _ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hŵA
    · rintro x ⟨k, rfl⟩
      rw [map_zpow, hŵF]
  obtain ⟨w, hw⟩ := hrange (Subgroup.mem_zpowers (g₂ * (da * z) * g₂⁻¹))
  have hwι : triEmb K σ L w = F.g0 * (s * z) * F.g0⁻¹ := by rw [hw, hŵ]
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzd : z * da * z⁻¹ = da⁻¹ := trialityOpposition_conj_torus hdaT
  have hdd : (da * z) * (da * z) = 1 := by
    calc (da * z) * (da * z) = da * (z * da * z⁻¹) * (z * z) := by group
      _ = 1 := by rw [hzd, hzz]; group
  refine ⟨s, hsT, w, hwι, ?_, ?_, ?_⟩
  · apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [map_mul, hw, map_one]
    calc g₂ * (da * z) * g₂⁻¹ * (g₂ * (da * z) * g₂⁻¹)
        = g₂ * ((da * z) * (da * z)) * g₂⁻¹ := by group
      _ = 1 := by rw [hdd]; group
  · rw [fieldActor_eq_iff Fr hcomm, hw]
    have hC : Commute P g₂ := hg₂P
    have hC2 : Commute P (da * z) :=
      Commute.mul_right (show Commute P da from hdaP) (show Commute P z from hzP)
    exact ((hC.mul_right hC2).mul_right hC.inv_right)
  · intro y hy
    have hyT : F.g0⁻¹ * triEmb K σ L y * F.g0 ∈ torusGroup TwistTag.D4.tag L := hy.1
    rw [map_mul, map_mul, map_inv, hwι]
    set u := F.g0⁻¹ * triEmb K σ L y * F.g0 with hu
    have hcomm' : s * u⁻¹ * s⁻¹ = u⁻¹ := by
      have := torusGroup_comm hsT (inv_mem hyT)
      calc s * u⁻¹ * s⁻¹ = (u⁻¹ * s) * s⁻¹ := by rw [this]
        _ = u⁻¹ := mul_inv_cancel_right _ _
    have hzu : z * u * z⁻¹ = u⁻¹ := trialityOpposition_conj_torus hyT
    have hy' : triEmb K σ L y = F.g0 * u * F.g0⁻¹ := by rw [hu]; group
    rw [hy']
    calc F.g0⁻¹ * (F.g0 * (s * z) * F.g0⁻¹ * (F.g0 * u * F.g0⁻¹) * (F.g0 * (s * z) * F.g0⁻¹)⁻¹) *
          F.g0 = (s * z) * u * (s * z)⁻¹ := by group
      _ = s * (z * u * z⁻¹) * s⁻¹ := by group
      _ = u⁻¹ := by rw [hzu, hcomm']

end Involution

section Plane

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {r : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_elt_of_mem_twistedTorus {ε : ℤ} {p : ℕ} (F : D4PhiFrame ℓ f K σ ε p L)
    {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ y : 𝒞[K, σ], F.g0⁻¹ * triEmb K σ L y * F.g0 = t := by
  obtain ⟨htT, htF⟩ := mem_twistedTorusOf.1 ht
  have htA : t ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' htT
  have hA : F.g0 * t * F.g0⁻¹ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem F.hg0C htA) (inv_mem F.hg0C)
  have hF : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) (F.g0 * t * F.g0⁻¹) =
      F.g0 * t * F.g0⁻¹ := by
    rw [map_mul, map_mul, map_inv, F.hg0]
    calc F.g0 * F.n * twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) t * (F.g0 * F.n)⁻¹
        = F.g0 * (F.n * twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) t * F.n⁻¹) * F.g0⁻¹ := by
          group
      _ = F.g0 * t * F.g0⁻¹ := by rw [htF]
  have hrange : Subgroup.zpowers (F.g0 * t * F.g0⁻¹) ≤ (triEmb K σ L).range := by
    refine F.hperf _ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hA
    · rintro x ⟨k, rfl⟩
      rw [map_zpow, hF]
  obtain ⟨y, hy⟩ := hrange (Subgroup.mem_zpowers (F.g0 * t * F.g0⁻¹))
  exact ⟨y, by rw [hy]; group⟩

@[expose] def planeSet (F : D4PhiFrame ℓ f K σ (-1) r L) : Set 𝒞[K, σ] :=
  {y | y ^ r = 1 ∧ F.g0⁻¹ * triEmb K σ L y * F.g0 ∈
    twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))}

theorem finite_torsionTuples (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) [NeZero r] :
    Finite (torsionTuples Fr r) := by
  let g : torsionTuples Fr r → rootsOfUnity r L × rootsOfUnity r L := fun b =>
    (⟨(b : Fin TwistTag.D4.tag.rank → Lˣ) 0, (mem_rootsOfUnity r _).2 (b.2.2 0)⟩,
      ⟨(b : Fin TwistTag.D4.tag.rank → Lˣ) 2, (mem_rootsOfUnity r _).2 (b.2.2 2)⟩)
  have hg : Function.Injective g := by
    intro b b' h
    have h0 : (b : Fin TwistTag.D4.tag.rank → Lˣ) 0 = (b' : Fin TwistTag.D4.tag.rank → Lˣ) 0 :=
      congrArg (fun x => ((x.1 : rootsOfUnity r L) : Lˣ)) h
    have h2 : (b : Fin TwistTag.D4.tag.rank → Lˣ) 2 = (b' : Fin TwistTag.D4.tag.rank → Lˣ) 2 :=
      congrArg (fun x => ((x.2 : rootsOfUnity r L) : Lˣ)) h
    exact Subtype.ext (fixed_tuple_ext hFr b.2.1 b'.2.1 h0 h2)
  exact Finite.of_injective g hg

theorem ncard_planeSet_le (F : D4PhiFrame ℓ f K σ (-1) r L) [NeZero r] :
    (planeSet F).ncard ≤ r * r := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr F.hn F.w F.hnw (d4T36M (-1)) F.hw
  have hex : ∀ y : planeSet F, ∃ b : torsionTuples Fr r,
      rootDiagUnit TwistTag.D4.tag (b : Fin TwistTag.D4.tag.rank → Lˣ) =
        F.g0⁻¹ * triEmb K σ L (y : 𝒞[K, σ]) * F.g0 := by
    intro y
    have h1 := y.2.2
    rw [hT] at h1
    obtain ⟨b, hb, hbd⟩ := h1
    refine ⟨⟨b, hb, fun i => ?_⟩, hbd⟩
    have hbd' : rootDiagUnit TwistTag.D4.tag b =
        F.g0⁻¹ * triEmb K σ L (y : 𝒞[K, σ]) * F.g0⁻¹⁻¹ := by rw [inv_inv]; exact hbd
    have hr : (rootDiagUnit TwistTag.D4.tag b) ^ r = 1 := by
      rw [hbd', conj_pow, ← map_pow, y.2.1, map_one]
      group
    have hr' : rootDiagUnit TwistTag.D4.tag (b ^ r) = rootDiagUnit TwistTag.D4.tag 1 := by
      have e1 : rootDiagUnit TwistTag.D4.tag (b ^ r) = (rootDiagUnit TwistTag.D4.tag b) ^ r :=
        (rootDiagUnitHom TwistTag.D4.tag L).map_pow b r
      have e2 : rootDiagUnit TwistTag.D4.tag (1 : Fin TwistTag.D4.tag.rank → Lˣ) = 1 :=
        (rootDiagUnitHom TwistTag.D4.tag L).map_one
      rw [e1, e2, hr]
    have := congrFun (rootDiagUnit_injective hr') i
    simpa using this
  choose bf hbf using hex
  have hinj : Function.Injective bf := by
    intro y y' h
    have e1 := hbf y
    have e2 := hbf y'
    rw [h] at e1
    have e3 : F.g0⁻¹ * triEmb K σ L (y : 𝒞[K, σ]) * F.g0 =
        F.g0⁻¹ * triEmb K σ L (y' : 𝒞[K, σ]) * F.g0 := e1.symm.trans e2
    have e4 : triEmb K σ L (y : 𝒞[K, σ]) = triEmb K σ L (y' : 𝒞[K, σ]) :=
      mul_left_cancel (mul_right_cancel e3)
    exact Subtype.ext (triEmb_injective e4)
  have := finite_torsionTuples (f := f) Fr hFr (r := r)
  calc (planeSet F).ncard = Nat.card (planeSet F) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (torsionTuples Fr r) := Nat.card_le_card_of_injective bf hinj
    _ ≤ r * r := natCard_torsionTuples_le hFr r

theorem exists_unit_pow_eq_one_ne_one' (L : Type) [Field L] [IsAlgClosed L] {r : ℕ} (hr1 : 1 < r)
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hr : ¬ ℓ ∣ r) :
    ∃ ζ : Lˣ, ζ ^ r = 1 ∧ ζ ≠ 1 := by
  have : NeZero (r : L) := ⟨by
    intro h
    exact hr ((CharP.cast_eq_zero_iff L ℓ r).1 h)⟩
  have : NeZero r := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L r
  refine ⟨hζ.isUnit (by omega) |>.unit, ?_, ?_⟩
  · apply Units.ext
    simpa using hζ.pow_eq_one
  · intro h
    have := hζ.ne_one hr1
    apply this
    simpa using congrArg Units.val h

theorem frame_torus_eq (F : D4PhiFrame ℓ f K σ (-1) r L) :
    twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) =
      (fixedCharTuples (d4T36M (-1)) (iterateFrobenius L ℓ f)).map
        (rootDiagUnitHom TwistTag.D4.tag L) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  exact twistedTorus_D4_eq_map_of_weylImage _ F.hn F.w F.hnw (d4T36M (-1)) F.hw

theorem frame_not_dvd (F : D4PhiFrame ℓ f K σ (-1) r L) : ¬ ℓ ∣ r := by
  intro hdvd
  have hℓ : ℓ.Prime := Fact.out
  have hrl : ℓ = r := ((Nat.dvd_prime F.hp).1 hdvd).resolve_left hℓ.one_lt.ne'
  have h1 : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) := by
    rw [← hrl]
    exact_mod_cast dvd_pow_self ℓ (by have := F.hf; omega)
  have h2 : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) * (((ℓ ^ f : ℕ) : ℤ) - 1) := dvd_mul_of_dvd_left h1 _
  have h3 := F.hpd
  have h4 : ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 =
      ((ℓ ^ f : ℕ) : ℤ) * (((ℓ ^ f : ℕ) : ℤ) - 1) + 1 := by ring
  rw [h4] at h3
  have h5 : (r : ℤ) ∣ 1 := (dvd_add_right h2).1 h3
  have := Int.eq_one_of_dvd_one (by positivity) h5
  have := F.hp.one_lt
  omega

theorem exists_c_in_plane (F : D4PhiFrame ℓ f K σ (-1) r L) {g₂ : ModGL TwistTag.D4.tag L}
    (hg₂P : diagramMap TwistTag.D4 L * g₂ = g₂ * diagramMap TwistTag.D4 L)
    (hg0 : F.g0 = jG0 L jU g₂) :
    ∃ c ∈ planeSet F, c ≠ 1 ∧ fieldActor (t := TwistTag.D4) σ σ c = c := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [F.hσ, hFr, map_pow]
  have hrℓ : ¬ ℓ ∣ r := frame_not_dvd F
  obtain ⟨ζ, hζ, hζ1⟩ := exists_unit_pow_eq_one_ne_one' L F.hp.one_lt hrℓ
  set bc := cTuple ζ (ℓ ^ f) with hbc
  have hbcF : bc ∈ fixedCharTuples (d4T36M (-1)) Fr := cTuple_mem_fixed hFr hζ F.hpd
  have ht : rootDiagUnit TwistTag.D4.tag bc ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L Fr) := by
    rw [frame_torus_eq F]
    exact ⟨bc, hbcF, rfl⟩
  obtain ⟨c, hc⟩ := exists_elt_of_mem_twistedTorus F ht
  have hιc : triEmb K σ L c = F.g0 * rootDiagUnit TwistTag.D4.tag bc * F.g0⁻¹ := by
    rw [← hc]; group
  have hdr : (rootDiagUnit TwistTag.D4.tag bc) ^ r = 1 := by
    have e1 : rootDiagUnit TwistTag.D4.tag (bc ^ r) = (rootDiagUnit TwistTag.D4.tag bc) ^ r :=
      (rootDiagUnitHom TwistTag.D4.tag L).map_pow bc r
    have e2 : rootDiagUnit TwistTag.D4.tag (1 : Fin TwistTag.D4.tag.rank → Lˣ) = 1 :=
      (rootDiagUnitHom TwistTag.D4.tag L).map_one
    rw [← e1, ← e2]
    congr 1
    funext i
    exact cTuple_pow hζ (ℓ ^ f) i
  refine ⟨c, ⟨?_, ?_⟩, ?_, ?_⟩
  · apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [map_pow, hιc, conj_pow, hdr, map_one]
    group
  · rw [hc]; exact ht
  · intro h1
    rw [h1, map_one] at hιc
    have h2 : rootDiagUnit TwistTag.D4.tag bc = 1 := by
      have : F.g0 * rootDiagUnit TwistTag.D4.tag bc * F.g0⁻¹ = 1 := hιc.symm
      have h3 := congrArg (fun x => F.g0⁻¹ * x * F.g0) this
      simpa [mul_assoc] using h3
    have h4 : rootDiagUnit TwistTag.D4.tag bc = rootDiagUnit TwistTag.D4.tag 1 := by
      rw [h2]
      exact ((rootDiagUnitHom TwistTag.D4.tag L).map_one).symm
    exact cTuple_ne_one hζ1 (ℓ ^ f) (rootDiagUnit_injective h4)
  · rw [fieldActor_eq_iff Fr hcomm, hιc]
    have hg0' : F.g0 = g₂ * (jRep L jU)⁻¹ := hg0
    have hcm : diagramMap TwistTag.D4 L *
        ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag bc * jRep L jU) =
        ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag bc * jRep L jU) *
          diagramMap TwistTag.D4 L :=
      jRep_inv_conj_comm_of_tuple bc (cTuple_one ζ _) (cTuple_three ζ _)
    have hC : Commute (diagramMap TwistTag.D4 L) g₂ := hg₂P
    have hC2 : Commute (diagramMap TwistTag.D4 L)
        ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag bc * jRep L jU) := hcm
    have hE : F.g0 * rootDiagUnit TwistTag.D4.tag bc * F.g0⁻¹ =
        g₂ * ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag bc * jRep L jU) * g₂⁻¹ := by
      rw [hg0']
      group
    rw [hE]
    exact ((hC.mul_right hC2).mul_right hC.inv_right)

theorem fieldActor_eq_of_mem_Px (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (F : D4PhiFrame ℓ f K σ (-1) r L) {g₂ : ModGL TwistTag.D4.tag L}
    (hg₂P : diagramMap TwistTag.D4 L * g₂ = g₂ * diagramMap TwistTag.D4 L)
    (hg0 : F.g0 = jG0 L jU g₂) {x : 𝒞[K, σ]} (sp : D4PhiSpecial F x 0) (hsp : sp.c = 1)
    {y : 𝒞[K, σ]} (hy : y ∈ d4phiPx sp) : fieldActor (t := TwistTag.D4) σ σ y = y := by
  classical
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  obtain ⟨z, hz, rfl⟩ := hy
  change fieldActor (t := TwistTag.D4) σ σ (z : 𝒞[K, σ]) = (z : 𝒞[K, σ])
  have hz' : d4phiPsi sp z ∈ d4phiQ F 0 := hz
  have hpsi : d4phiPsi sp z = F.g0⁻¹ * triEmb K σ L (z : 𝒞[K, σ]) * F.g0 := by
    rw [d4phiPsi, d4QPsi_apply, hsp, one_mul, inv_one, mul_one]
  have hroot : F.g0⁻¹ * triEmb K σ L (z : 𝒞[K, σ]) * F.g0 ∈
      rootSpan TwistTag.D4.tag L (d4Sigma 0) := by
    rw [← hpsi]
    exact (Subgroup.mem_inf.1 hz').1
  rw [fieldActor_eq_iff Fr hcomm]
  have hg0' : F.g0 = g₂ * (jRep L jU)⁻¹ := hg0
  have hE : triEmb K σ L (z : 𝒞[K, σ]) = g₂ * (jRep L jU)⁻¹ *
      (F.g0⁻¹ * triEmb K σ L (z : 𝒞[K, σ]) * F.g0) * jRep L jU * g₂⁻¹ := by
    rw [hg0']
    group
  rw [hE]
  exact diagramMap_comm_conj_rootSpan_sigma jWeyl_zero_spec.2.2.2 hg₂P hroot

end Plane


end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
