module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieConj
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieAux
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieSL2
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjExp
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjLift
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLift
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInputs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
import CFSG.RankThree.Classical2.TwistedE6RationalOrder
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori
import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairData
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoInverter
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootTransport
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieHeis
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwVacuity
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjClass
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjCore
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjFin
import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLiftConv
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic
import CFSG.RankThree.PartOne.SLB4A.ClassExcRest

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.SeitzGeneration.ExcWideThree
open scoped Matrix commutatorElement

section LeviCube


private theorem lc_iform_neg_right (x y : Fin TwistTag.E6.tag.rank → ℤ) :
    iform x (-y) = -iform x y := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

private theorem lc_iform_self {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  have hs : TwistTag.E6.tag.symmetrizer j j = 1 := by
    change (1 : Matrix (Fin 6) (Fin 6) ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [hj, hs, mul_one]

private theorem lc_rootChar_coroot {L : Type} [Field L] (β : Fin TwistTag.E6.tag.rank → ℤ)
    (c : Lˣ) (u : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (fun i => c ^ iform β (Pi.single i 1)) u = c ^ iform β u := by
  rw [rootChar, CFSG.SeitzReduction.F4Pilot.iform_eq_sum_mul_iform_single β u,
    ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

private theorem lc_coroot_mem_rootSpan {L : Type} [Field L] {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (c : Lˣ) :
    rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform β (Pi.single i 1)) ∈
      rootSpan TwistTag.E6.tag L {β, -β} := by
  have he : (fun i => c ^ iform β (Pi.single i 1)) =
      fun i => c ^ (2 * iform β (Pi.single i 1) / iform β β) := by
    funext i
    rw [lc_iform_self hβ]
    congr 1
    omega
  rw [he, ← rootTorusSL2_eq_rootDiagUnit_corootPair hβ c]
  have hmem : rootTorusSL2 TwistTag.E6.tag L β c ∈ rootRankOneGroup TwistTag.E6.tag L β :=
    ⟨_, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag L hβ).1] at hmem
  have hle : ∀ γ ∈ ({β, -β} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      rootSubgroup TwistTag.E6.tag L γ ≤ rootSpan TwistTag.E6.tag L {β, -β} := fun γ hγ =>
    le_iSup₂ (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin TwistTag.E6.tag.rank → ℤ))) =>
      rootSubgroup TwistTag.E6.tag L γ) γ hγ
  exact sup_le (hle β (Set.mem_insert _ _)) (hle (-β) (Set.mem_insert_of_mem _ rfl)) hmem

private theorem lc_fixed_coroot {L : Type} [Field L] {q : ℕ} {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (β : Fin TwistTag.E6.tag.rank → ℤ) {d : Lˣ} (hd : d ^ (q + 1) = 1) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        twistHom TwistTag.E6 L Fr
          (rootDiagUnit TwistTag.E6.tag (fun i => d ^ iform β (Pi.single i 1))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => d ^ iform β (Pi.single i 1)) := by
  have hvM : ∀ x, v • permLattice TwistTag.E6.perm x =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) *ᵥ x := fun x => by
    rw [hv, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hdq : d ^ q = d⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hd]
  have hFd : Units.map Fr.toMonoidHom d = d⁻¹ := by
    rw [← hdq]
    exact Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  rw [← twFrob_apply, twFrob_rootDiagUnit]
  refine congrArg (rootDiagUnit TwistTag.E6.tag) ?_
  refine (twisted_weylTuple_eq_iff_fixedCharTuples TwistTag.E6 Fr v _ hvM
    (fun i => d ^ iform β (Pi.single i 1))).2 fun u => ?_
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [lc_rootChar_coroot, lc_rootChar_coroot, map_zpow, hFd, inv_zpow', lc_iform_neg_right]

private theorem lc_class_dvd {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hq : (p ^ f) % 3 = 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) (v : WeylGroup Tag.E6) (g0 : ModGL Tag.E6 (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v)
    (hv : ∀ γ : Fin Tag.E6.rank → ℤ, v • permLattice CFSG.RankThree.E6.e6Rho γ = -γ)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ 9) (m : Fin Tag.E6.rank → ℤ)
    {y : ModGL Tag.E6 K} (hy : y ∈ twistedE6RootGroup K σ)
    (hyu : baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
      g0 * rootDiagUnit Tag.E6 (e6RootParams (fun l => ζ ^ m l)) * g0⁻¹)
    (l : Fin Tag.E6.rank) : (9 : ℤ) ∣ (((p ^ f : ℕ) : ℤ) + 1) * m l := by
  obtain ⟨ωv, hωv, hvw⟩ := (coxeterSystem Tag.E6).exists_isReduced v
  have hF' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        ((coxeterSystem Tag.E6).wordProd ωv) := by
    rw [← hvw]
    exact hg0
  have key := tw_class_trivial_of_mem hp hf hK σ hσ hq Fr hFr g0 hg0C hωv hF'
    (fun l => ζ ^ m l) hy hyu
  have hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ (p ^ f) :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  have hρ : CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6RhoFour =
      CFSG.RankThree.E6.e6Rho :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6RhoFour_eq_twistPerm
  have hinner : (fun l => Units.map Fr.toMonoidHom ((fun l => ζ ^ m l)
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6RhoFour l))) =
      fun l => ζ ^ ((((p ^ f : ℕ) : ℤ) • permLattice CFSG.RankThree.E6.e6Rho m) l) := by
    funext l
    show Units.map Fr.toMonoidHom
      (ζ ^ m (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6RhoFour l)) = _
    rw [map_zpow, hFrζ, ← zpow_natCast, ← zpow_mul]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, permLattice, Function.comp_apply,
      CFSG.RankThree.E6.e6Rho_symm, hρ]
  have key2 : ωv.foldr e6StarS
      (fun l => ζ ^ ((((p ^ f : ℕ) : ℤ) • permLattice CFSG.RankThree.E6.e6Rho m) l)) =
      fun l => ζ ^ m l :=
    (congrArg (ωv.foldr e6StarS) hinner.symm).trans key
  have key3 : (fun l => ζ ^ (((coxeterSystem Tag.E6).wordProd ωv •
      (((p ^ f : ℕ) : ℤ) • permLattice CFSG.RankThree.E6.e6Rho m)) l)) =
      fun l => ζ ^ m l := by
    rw [wordProd_smul_eq_foldr]
    exact (foldr_e6StarS_zpow ζ ωv _).symm.trans key2
  rw [← hvw, smul_comm v (((p ^ f : ℕ) : ℤ)), hv] at key3
  have h1 : ζ ^ (-(((p ^ f : ℕ) : ℤ) * m l)) = ζ ^ m l := by
    have := congrFun key3 l
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply, mul_neg] using this
  have h2 : ζ ^ ((((p ^ f : ℕ) : ℤ) + 1) * m l) = 1 := by
    rw [add_mul, one_mul, zpow_add, ← h1, ← zpow_add, add_neg_cancel, zpow_zero]
  exact_mod_cast (hζ.zpow_eq_one_iff_dvd _).1 h2

private theorem lc_coroot_mem_levi {q : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (hder : ⁅twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
      (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {k : ℕ} (hk : (((twistedE6RootGroup K σ).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)).index = 3 ^ k)
    {θ : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    {X Xm : Subgroup (twistedE6RootGroup K σ)}
    (hS : ∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ, -θ}).map
          (MulAut.conj g0).toMonoidHom)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hθβ : iform θ β = 0)
    {m : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hmA : m ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hmF : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v *
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr m *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)⁻¹ = m)
    (hmi : ∀ d : (AlgebraicClosure K)ˣ,
      m * rootDiagUnit TwistTag.E6.tag (fun i => d ^ iform β (Pi.single i 1)) * m⁻¹ =
        rootDiagUnit TwistTag.E6.tag (fun i => d⁻¹ ^ iform β (Pi.single i 1)))
    (hmc : ∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ, -θ}, m * y = y * m)
    {d : (AlgebraicClosure K)ˣ} (hd : d ^ (q + 1) = 1) :
    g0 * rootDiagUnit TwistTag.E6.tag (fun i => (d ^ 4) ^ iform β (Pi.single i 1)) * g0⁻¹ ∈
      (twE6LongRootLevi X Xm).map
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (twistedE6RootGroup K σ).subtype) := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) L v with hn
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C' := (twistedE6RootGroup K σ).map (baseChangeGL ι) with hC'
  set ιG := (baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype with hιG
  have hιGinj : Function.Injective ιG :=
    (baseChangeGL_injective ι).comp (Subgroup.subtype_injective _)
  let H : Lˣ →* ModGL TwistTag.E6.tag L :=
    { toFun := fun c => rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform β (Pi.single i 1))
      map_one' := by
        have e : (fun i => (1 : Lˣ) ^ iform β (Pi.single i 1)) = 1 := funext fun i => one_zpow _
        simp only [e, rootDiagUnit_one]
      map_mul' := fun c c' => by
        rw [← rootDiagUnit_mul]
        congr 1
        funext i
        simp only [Pi.mul_apply, mul_zpow] }
  have hH : ∀ c, H c = rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform β (Pi.single i 1)) :=
    fun _ => rfl
  let A : Lˣ →* ModGL TwistTag.E6.tag L := (MulAut.conj g0).toMonoidHom.comp H
  have hA : ∀ c, A c = g0 * H c * g0⁻¹ := fun _ => rfl
  obtain ⟨M, hM⟩ : ∃ M, M = g0 * m * g0⁻¹ := ⟨_, rfl⟩
  have hconjR : ∀ z ∈ adjointGroup TwistTag.E6.tag L,
      n * twistHom TwistTag.E6 L Fr z * n⁻¹ = z → g0 * z * g0⁻¹ ∈ R := by
    intro z hzA hzF
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨mul_mem (mul_mem hg0C hzA) (inv_mem hg0C), ?_⟩
    rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * n * twistHom TwistTag.E6 L Fr z * (g0 * n)⁻¹ =
        g0 * (n * twistHom TwistTag.E6 L Fr z * n⁻¹) * g0⁻¹ := by group
      _ = g0 * z * g0⁻¹ := by rw [hzF]
  have hAR : ∀ c : Lˣ, c ^ (q + 1) = 1 → A c ∈ R := fun c hc =>
    hconjR _ (CFSG.SeitzReduction.E6Pilot.rootDiagUnit_corootTuple_mem_adjointGroup β c)
      (lc_fixed_coroot hFr hv β hc)
  have hMR : M ∈ R := hM ▸ hconjR m hmA hmF
  have hMA : ∀ c, M * A c * M⁻¹ = A c⁻¹ := fun c => by
    rw [hA, hA, hM]
    calc g0 * m * g0⁻¹ * (g0 * H c * g0⁻¹) * (g0 * m * g0⁻¹)⁻¹ =
        g0 * (m * H c * m⁻¹) * g0⁻¹ := by group
      _ = g0 * H c⁻¹ * g0⁻¹ := by rw [hH, hH, hmi c]
  have hcomm : ∀ (N : ModGL TwistTag.E6.tag L) (c : Lˣ), N * A c * N⁻¹ = A c⁻¹ →
      ⁅A c, N⁆ = A (c ^ 2) := by
    intro N c hN
    rw [commutatorElement_def]
    calc A c * N * (A c)⁻¹ * N⁻¹ = A c * (N * A c⁻¹ * N⁻¹) := by rw [map_inv]; group
      _ = A c * A c := by
        congr 1
        calc N * A c⁻¹ * N⁻¹ = (N * A c * N⁻¹)⁻¹ := by rw [map_inv]; group
          _ = A c := by rw [hN, map_inv, inv_inv]
      _ = A (c ^ 2) := by rw [← map_mul, sq]
  have hA2 : A (d ^ 2) ∈ C' := by
    rw [← hcomm M d (hMA d), ← hder]
    exact Subgroup.commutator_mem_commutator (hAR d hd) hMR
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  have hMk : M ^ (3 ^ k) ∈ C' := by
    have h := Subgroup.pow_index_mem (C'.subgroupOf R) (⟨M, hMR⟩ : R)
    rw [hk, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hodd : ∀ j : ℕ, ∀ c, M ^ (2 * j + 1) * A c * (M ^ (2 * j + 1))⁻¹ = A c⁻¹ := by
    intro j
    induction j with
    | zero => intro c; simpa using hMA c
    | succ j ih =>
      intro c
      calc M ^ (2 * (j + 1) + 1) * A c * (M ^ (2 * (j + 1) + 1))⁻¹ =
          M * (M * (M ^ (2 * j + 1) * A c * (M ^ (2 * j + 1))⁻¹) * M⁻¹) * M⁻¹ := by
            rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, pow_succ', pow_succ']
            group
        _ = A c⁻¹ := by rw [ih, hMA, hMA, inv_inv]
  obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hMki : M ^ (3 ^ k) * A (d ^ 2) * (M ^ (3 ^ k))⁻¹ = A (d ^ 2)⁻¹ := by
    rw [hj]
    exact hodd j _
  have hcent : ∀ (z : twistedE6RootGroup K σ) (w : ModGL TwistTag.E6.tag L),
      ιG z = g0 * w * g0⁻¹ → (∀ y ∈ rootSpan TwistTag.E6.tag L {θ, -θ}, w * y = y * w) →
      z ∈ Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) := by
    intro z w hz hw
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 ((hS u).1 hu)
    have hyu' : ιG u = g0 * y * g0⁻¹ := by
      simpa [MulAut.conj_apply, hιG] using hyu.symm
    apply hιGinj
    rw [map_mul, map_mul, hz, hyu']
    calc g0 * y * g0⁻¹ * (g0 * w * g0⁻¹) = g0 * (y * w) * g0⁻¹ := by group
      _ = g0 * (w * y) * g0⁻¹ := by rw [hw y hy]
      _ = g0 * w * g0⁻¹ * (g0 * y * g0⁻¹) := by group
  have hβθ : iform β θ = 0 := by rw [iform_comm]; exact hθβ
  have hHc : ∀ c : Lˣ, ∀ y ∈ rootSpan TwistTag.E6.tag L {θ, -θ}, H c * y = y * H c := by
    intro c y hy
    have hle := CFSG.LieType.SeitzGeneration.ExcWideThree.rootSpan_le_centralizer_rootDiagUnit
      (L := L) (fun i => c ^ iform β (Pi.single i 1)) (S := {θ, -θ}) (by
        intro α hα
        rcases hα with rfl | rfl
        · exact ⟨hθ, by rw [lc_rootChar_coroot, hβθ, zpow_zero]⟩
        · exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hθ, by
            rw [lc_rootChar_coroot, lc_iform_neg_right, hβθ, neg_zero, zpow_zero]⟩)
    exact (Subgroup.mem_centralizer_iff.1 (hle hy)) _ rfl
  obtain ⟨a2, ha2G, ha2⟩ := Subgroup.mem_map.1 hA2
  obtain ⟨mk, hmkG, hmk⟩ := Subgroup.mem_map.1 hMk
  have hca2 : (⟨a2, ha2G⟩ : twistedE6RootGroup K σ) ∈
      Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) :=
    hcent _ (H (d ^ 2)) ha2 (hHc (d ^ 2))
  have hcmk : (⟨mk, hmkG⟩ : twistedE6RootGroup K σ) ∈
      Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) :=
    hcent _ (m ^ (3 ^ k)) (by change baseChangeGL ι mk = _; rw [hmk, hM, conj_pow]) fun y hy =>
      (Commute.pow_left (hmc y hy) (3 ^ k)).eq
  refine ⟨⁅(⟨a2, ha2G⟩ : twistedE6RootGroup K σ), ⟨mk, hmkG⟩⁆,
    Subgroup.commutator_mem_commutator hca2 hcmk, ?_⟩
  change ιG ⁅(⟨a2, ha2G⟩ : twistedE6RootGroup K σ), ⟨mk, hmkG⟩⁆ = A (d ^ 4)
  rw [map_commutatorElement]
  change ⁅baseChangeGL ι a2, baseChangeGL ι mk⁆ = A (d ^ 4)
  rw [ha2, hmk, hcomm _ _ hMki, ← pow_mul]

private theorem lc_psi_mem {q : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq : q % 3 = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (hder : ⁅twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
      (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {k : ℕ} (hk : (((twistedE6RootGroup K σ).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf
        (twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)).index = 3 ^ k)
    {θ : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    {X Xm : Subgroup (twistedE6RootGroup K σ)}
    (hS : ∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ, -θ}).map
          (MulAut.conj g0).toMonoidHom)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ 9)
    (x : twistedE6RootGroup K σ) (hx3 : x ^ 3 = 1)
    (hxT : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : rootDiagUnit TwistTag.E6.tag a =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0) :
    g0 * rootDiagUnit TwistTag.E6.tag (a * fun i => rootChar a θ ^ iform θ (Pi.single i 1)) *
        g0⁻¹ ∈
      (twE6LongRootLevi X Xm).map
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (twistedE6RootGroup K σ).subtype) := by
  classical
  set L := AlgebraicClosure K with hL
  have hq2 : 2 ≤ q := by omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hFrc : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [hFr, hqf]
  have hq' : (ringChar K ^ f) % 3 = 2 := by rw [← hqf]; exact hq
  have hω' : IsPrimitiveRoot (ζ ^ 3) 3 := hζ.pow (by norm_num) (by norm_num)
  have hω : IsPrimitiveRoot ((ζ ^ 3 : Lˣ) : L) 3 := IsPrimitiveRoot.coe_units_iff.2 hω'
  obtain ⟨k₀, hk₀, -⟩ := tw_diag_exponent hω Fr _ g0 x hx3 hxT
  have hak : a = fun i => (ζ ^ 3) ^ k₀ i :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (ha.trans hk₀.symm)
  obtain ⟨m, hm⟩ : ∃ m : Fin TwistTag.E6.tag.rank → ℤ,
      m = fun l => ∑ i, e6CartanAdj i l * (k₀ i : ℤ) := ⟨_, rfl⟩
  have hmc : ∀ j : Fin Tag.E6.rank, ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * m l =
      3 * (k₀ j : ℤ) := by
    intro j
    have e : ∀ i, ∑ l, Tag.E6.cartan l j * (e6CartanAdj i l * (k₀ i : ℤ)) =
        (k₀ i : ℤ) * (if i = j then 3 else 0) := by
      intro i
      rw [← e6CartanAdj_mul i j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hm]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hpar : e6RootParams (fun l => ζ ^ m l) = a := by
    refine (tw_e6RootParams_zpow ζ m).trans ?_
    rw [hak]
    funext j
    show ζ ^ _ = (ζ ^ 3) ^ k₀ j
    rw [hmc j, ← pow_mul, ← zpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have hyu : baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) =
      g0 * rootDiagUnit TwistTag.E6.tag (e6RootParams (fun l => ζ ^ m l)) * g0⁻¹ := by
    rw [hpar]
    calc baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) =
        g0 * (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * g0) *
          g0⁻¹ := by group
      _ = g0 * rootDiagUnit TwistTag.E6.tag a * g0⁻¹ := by rw [ha]
  have h9 : ∀ l : Fin TwistTag.E6.tag.rank, (9 : ℤ) ∣ ((q : ℤ) + 1) * m l := by
    intro l
    have h := lc_class_dvd hpr hf1 hK' σ hσ' hq' Fr hFrc v g0 hg0C hg0 (fun γ => hv γ) hζ m
      x.2 hyu l
    rwa [← hqf] at h
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, κ = 3 * ∑ i, (k₀ i : ℤ) * θ i := ⟨_, rfl⟩
  have hχ : rootChar a θ = ζ ^ κ := by
    rw [hak]
    exact (tw_rootChar_pow_exp (ζ ^ 3) k₀ θ).trans (by rw [hκ, zpow_mul, zpow_ofNat]; rfl)
  obtain ⟨w, hw⟩ :=
    CFSG.SeitzReduction.EPilot.exists_smul_highRoot_eq (τ := TwistTag.E6.tag) (Or.inl rfl) hθ
  obtain ⟨m', hm'⟩ : ∃ m' : Fin TwistTag.E6.tag.rank → ℤ, m' = m + κ • θ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : Fin TwistTag.E6.tag.rank → ℤ, n = w⁻¹ • m' := ⟨_, rfl⟩
  have hwn : w • n = m' := by rw [hn, smul_inv_smul]
  have hexp : ∀ z y : Fin TwistTag.E6.tag.rank → ℤ,
      ∑ j, z j * iform (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) y =
        iform (w • z) y := by
    intro z y
    have h1 : ∀ j, iform (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) y =
        iform (w⁻¹ • y) (Pi.single j 1) := fun j => by
      rw [iform_comm, ← CFSG.ClassicalInvolution.ModelFacts.LeviE6.iform_smul_smul w⁻¹ y,
        inv_smul_smul]
    have h2 : iform (w • z) y = iform (w⁻¹ • y) z := by
      rw [iform_comm, ← CFSG.ClassicalInvolution.ModelFacts.LeviE6.iform_smul_smul w⁻¹ y,
        inv_smul_smul]
    simp_rw [h1, h2, CFSG.SeitzReduction.F4Pilot.iform_eq_sum_mul_iform_single (w⁻¹ • y) z]
  have hmi : ∀ i, iform m (Pi.single i 1) = 3 * (k₀ i : ℤ) := fun i =>
    (CFSG.SeitzReduction.E6Pilot.iform_single_right_E6 m i).trans (by
      rw [← hmc i]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _)
  have hn0 : (9 : ℤ) ∣ n (CFSG.SeitzReduction.highNode TwistTag.E6.tag) := by
    have e1 : n (CFSG.SeitzReduction.highNode TwistTag.E6.tag) = iform θ m' := by
      rw [← CFSG.SeitzReduction.EPilot.iform_highRoot (τ := TwistTag.E6.tag) (Or.inl rfl) n,
        ← CFSG.ClassicalInvolution.ModelFacts.LeviE6.iform_smul_smul w, hw, hwn]
    have e3 : iform θ m = κ := by
      rw [iform_comm, CFSG.SeitzReduction.F4Pilot.iform_eq_sum_mul_iform_single m θ]
      simp_rw [hmi]
      rw [hκ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hm', iform_add_right, iform_smul_right, e3, lc_iform_self hθ, hκ]
    exact ⟨∑ i, (k₀ i : ℤ) * θ i, by ring⟩
  have h3 : (3 : ℤ) ∣ (q : ℤ) + 1 := by omega
  have h9m' : ∀ l, (9 : ℤ) ∣ ((q : ℤ) + 1) * m' l := by
    intro l
    obtain ⟨c, hc⟩ := h3
    have e : ((q : ℤ) + 1) * m' l =
        ((q : ℤ) + 1) * m l + 9 * (c * (∑ i, (k₀ i : ℤ) * θ i) * θ l) := by
      rw [hm', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hκ, hc]
      ring
    rw [e]
    exact dvd_add (h9 l) (dvd_mul_right _ _)
  choose y hy using h9m'
  have h9n : ∀ j, (9 : ℤ) ∣ ((q : ℤ) + 1) * n j := by
    intro j
    have e : ((q : ℤ) + 1) • m' = (9 : ℤ) • y := funext fun l => by
      simp only [Pi.smul_apply, smul_eq_mul, hy l]
    have e2 : ((q : ℤ) + 1) • n = (9 : ℤ) • (w⁻¹ • y) := by
      rw [hn, smul_comm, e, smul_comm]
    exact ⟨(w⁻¹ • y) j, by simpa only [Pi.smul_apply, smul_eq_mul] using congrFun e2 j⟩
  have hprod : (a * fun i => rootChar a θ ^ iform θ (Pi.single i 1)) =
      ∏ j, fun i => (ζ ^ n j) ^
        iform (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) (Pi.single i 1) := by
    funext i
    have e1 : ∏ j, (ζ ^ n j) ^
        iform (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) (Pi.single i 1) =
        ζ ^ (3 * (k₀ i : ℤ) + κ * iform θ (Pi.single i 1)) := by
      simp only [← zpow_mul]
      rw [Finset.prod_zpow_eq_zpow_sum, hexp n, hwn, hm', iform_add_left, iform_smul_left,
        hmi]
    rw [Finset.prod_apply, e1, Pi.mul_apply, hχ, hak, zpow_add, zpow_mul ζ κ, zpow_mul ζ 3,
      zpow_natCast, zpow_ofNat]
  let Φ : (Fin TwistTag.E6.tag.rank → Lˣ) →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0).toMonoidHom.comp (rootDiagUnitHom TwistTag.E6.tag L)
  change Φ (a * fun i => rootChar a θ ^ iform θ (Pi.single i 1)) ∈ _
  change (a * fun i => rootChar a θ ^ iform θ (Pi.single i 1)) ∈
    ((twE6LongRootLevi X Xm).map ((baseChangeGL (algebraMap K L)).comp
      (twistedE6RootGroup K σ).subtype)).comap Φ
  rw [hprod]
  refine Subgroup.prod_mem _ fun j _ => ?_
  rw [Subgroup.mem_comap]
  change g0 * rootDiagUnit TwistTag.E6.tag (fun i => (ζ ^ n j) ^
    iform (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) (Pi.single i 1)) * g0⁻¹ ∈ _
  by_cases hj : j = CFSG.SeitzReduction.highNode TwistTag.E6.tag
  ·
    have h9j : (9 : ℤ) ∣ n j := hj ▸ hn0
    have h1 : ζ ^ n j = 1 := (hζ.zpow_eq_one_iff_dvd _).2 (by exact_mod_cast h9j)
    have e : (fun i => (ζ ^ n j) ^
        iform (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) (Pi.single i 1)) = 1 :=
      funext fun i => by rw [h1, one_zpow]; rfl
    rw [e, rootDiagUnit_one, mul_one, mul_inv_cancel]
    exact one_mem _
  ·
    have hβ : IsRoot TwistTag.E6.tag (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) :=
      CFSG.LieType.Chevalley.IsRoot.smul (isRoot_single _ j) w
    have hθβ : iform θ (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 := by
      rw [← hw, CFSG.ClassicalInvolution.ModelFacts.LeviE6.iform_smul_smul,
        CFSG.SeitzReduction.EPilot.iform_highRoot_single (τ := TwistTag.E6.tag) (Or.inl rfl),
        if_neg hj]
    obtain ⟨mβ, hmA, hmF, hmi', hmc'⟩ := exists_fixed_coroot_inverter Fr hFr hv hθ hβ hθβ
    obtain ⟨c, hc⟩ := h9n j
    have hd : (ζ ^ (7 * n j)) ^ (q + 1) = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      refine (hζ.zpow_eq_one_iff_dvd _).2 ⟨7 * c, ?_⟩
      push_cast
      linear_combination 7 * hc
    have h9' : ζ ^ (9 : ℤ) = 1 := by rw [zpow_ofNat]; exact hζ.pow_eq_one
    have h4 : (ζ ^ (7 * n j)) ^ 4 = ζ ^ n j := by
      rw [← zpow_natCast, ← zpow_mul,
        show 7 * n j * ((4 : ℕ) : ℤ) = n j + 9 * (3 * n j) by push_cast; ring,
        zpow_add, zpow_mul, h9', one_zpow, mul_one]
    have h := lc_coroot_mem_levi hFr hg0C hg0 hv hder hk hθ hS hθβ hmA hmF hmi' hmc' hd
    rwa [h4] at h

private theorem lc_conj_coroot_inv {L : Type} [Field L] (g0 : ModGL TwistTag.E6.tag L)
    (θ : Fin TwistTag.E6.tag.rank → ℤ) (c : Lˣ) :
    (g0 * rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform θ (Pi.single i 1)) * g0⁻¹)⁻¹ =
      g0 * rootDiagUnit TwistTag.E6.tag (fun i => c⁻¹ ^ iform θ (Pi.single i 1)) * g0⁻¹ := by
  have e : (fun i => c ^ iform θ (Pi.single i 1))⁻¹ = fun i => c⁻¹ ^ iform θ (Pi.single i 1) :=
    funext fun i => by rw [Pi.inv_apply, inv_zpow]
  rw [mul_inv_rev, mul_inv_rev, inv_inv, rootDiagUnit_inv, e, mul_assoc]

theorem exists_levi_cube_of_negDatum (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq : q % 3 = 2)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : CFSG.Open.IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    {θ : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    (hES : ∀ x ∈ E₀, ∀ c : (AlgebraicClosure K)ˣ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
        g0 * rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform θ (Pi.single i 1)) * g0⁻¹ →
      x = 1)
    {X Xm : Subgroup (twistedE6RootGroup K σ)} (hpair : IsTwE6LongRootPair K σ X Xm)
    (hS : ∀ u : twistedE6RootGroup K σ, u ∈ twE6LongRootSL2 X Xm ↔
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {θ, -θ}).map
          (MulAut.conj g0).toMonoidHom) :
    ∃ φ : E₀ →* twistedE6RootGroup K σ, Function.Injective φ ∧
      (∀ x, φ x ∈ twE6LongRootLevi X Xm) ∧
      ∀ x : E₀, ∀ j ∈ twE6LongRootLevi X Xm,
        (x : twistedE6RootGroup K σ) * j * (x : twistedE6RootGroup K σ)⁻¹ = φ x * j * (φ x)⁻¹ := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  have hq2 : 2 ≤ q := by omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hFrc : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [hFr, hqf]
  obtain ⟨-, -, hder, ⟨k, hk⟩, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order hpr hf1 K hK'
      σ.toRingHom hσ' L Fr hFrc
  have hr3 : ringChar K ≠ 3 := by
    intro h
    have h3 : 3 ∣ q := by
      rw [hqf, h]
      exact dvd_pow_self 3 (by omega)
    omega
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap ι.injective _
  obtain ⟨ζ, hζ⟩ := ExcWideThree.exists_primitiveRoot_nine (L := L) (ringChar K) hr3
  set ιG := (baseChangeGL ι).comp (twistedE6RootGroup K σ).subtype with hιG
  have hιGinj : Function.Injective ιG :=
    (baseChangeGL_injective ι).comp (Subgroup.subtype_injective _)
  let δ : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ιG
  have hδ : ∀ x, δ x = g0⁻¹ * ιG x * g0 := fun x => by
    show g0⁻¹ * ιG x * g0⁻¹⁻¹ = _
    rw [inv_inv]
  have hδT : ∀ x ∈ E₀, δ x ∈ torusGroup TwistTag.E6.tag L := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hT x hx)
    have hyx' : g0 * y * g0⁻¹ = ιG x := by
      have h : g0 * y * g0⁻¹ = baseChangeGL ι (x : ModGL TwistTag.E6.tag K) := by
        simpa [MulAut.conj_apply] using hyx
      exact h
    have hxy : δ x = y := by
      rw [hδ, ← hyx']
      group
    rw [hxy]
    exact ((mem_twistedTorusOf).1 hy).1
  have hinj : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) :=
    fun _ _ h => CFSG.LieType.Chevalley.rootDiagUnit_injective h
  let e := MonoidHom.ofInjective hinj
  have hrange : ∀ x ∈ E₀, δ x ∈ (rootDiagUnitHom TwistTag.E6.tag L).range := by
    intro x hx
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hδT x hx)
    exact ⟨l, hl.symm⟩
  let δE : E₀ →* (rootDiagUnitHom TwistTag.E6.tag L).range :=
    (δ.comp E₀.subtype).codRestrict _ fun x => hrange x x.2
  let par : E₀ →* (Fin TwistTag.E6.tag.rank → Lˣ) := e.symm.toMonoidHom.comp δE
  have hpar : ∀ x : E₀, rootDiagUnit TwistTag.E6.tag (par x) = δ x := by
    intro x
    have h1 := congrArg Subtype.val (e.apply_symm_apply (δE x))
    rw [MonoidHom.ofInjective_apply] at h1
    exact h1
  let χ : E₀ →* Lˣ :=
    { toFun := fun x => rootChar (par x) θ
      map_one' := by simp [rootChar]
      map_mul' := fun x y => by
        simp only [map_mul, rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib] }
  let H : Lˣ →* (Fin TwistTag.E6.tag.rank → Lˣ) :=
    { toFun := fun c i => c ^ iform θ (Pi.single i 1)
      map_one' := funext fun i => one_zpow _
      map_mul' := fun c c' => funext fun i => mul_zpow c c' _ }
  let Ψ : E₀ →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0).toMonoidHom.comp ((rootDiagUnitHom TwistTag.E6.tag L).comp (par * H.comp χ))
  have hΨ : ∀ x, Ψ x = g0 * rootDiagUnit TwistTag.E6.tag
      (par x * fun i => rootChar (par x) θ ^ iform θ (Pi.single i 1)) * g0⁻¹ := fun _ => rfl
  have hΨx : ∀ x : E₀, Ψ x = ιG x *
      (g0 * rootDiagUnit TwistTag.E6.tag (fun i => rootChar (par x) θ ^ iform θ (Pi.single i 1)) *
        g0⁻¹) := by
    intro x
    rw [hΨ, rootDiagUnit_mul, hpar x, hδ x]
    group
  have hΨJ : ∀ x : E₀, Ψ x ∈ (twE6LongRootLevi X Xm).map ιG := by
    intro x
    exact lc_psi_mem hK hσ hq hFr hg0C hg0 hv hder hk hθ hS hζ x (hE₀.2 _ x.2) (hT x x.2)
      ((hpar x).trans (hδ x))
  let eJ := Subgroup.equivMapOfInjective (twE6LongRootLevi X Xm) ιG hιGinj
  let φ : E₀ →* twistedE6RootGroup K σ :=
    (twE6LongRootLevi X Xm).subtype.comp (eJ.symm.toMonoidHom.comp (Ψ.codRestrict _ hΨJ))
  have hφι : ∀ x, ιG (φ x) = Ψ x := by
    intro x
    have h1 := Subgroup.coe_equivMapOfInjective_apply (twE6LongRootLevi X Xm) ιG hιGinj
      (eJ.symm (Ψ.codRestrict _ hΨJ x))
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨φ, ?_, fun x => (eJ.symm (Ψ.codRestrict _ hΨJ x)).2, ?_⟩
  ·
    refine (injective_iff_map_eq_one φ).2 fun x hx => ?_
    have h1 : Ψ x = 1 := by rw [← hφι, hx, map_one]
    rw [hΨx] at h1
    have h2 : ιG x = g0 * rootDiagUnit TwistTag.E6.tag
        (fun i => (rootChar (par x) θ)⁻¹ ^ iform θ (Pi.single i 1)) * g0⁻¹ := by
      rw [← lc_conj_coroot_inv]
      exact eq_inv_of_mul_eq_one_left h1
    exact Subtype.ext (hES _ x.2 _ h2)
  ·
    intro x j hj
    obtain ⟨s, hs⟩ : ∃ s, s = (φ x)⁻¹ * (x : twistedE6RootGroup K σ) := ⟨_, rfl⟩
    have hsι : ιG s = g0 * rootDiagUnit TwistTag.E6.tag
        (fun i => (rootChar (par x) θ)⁻¹ ^ iform θ (Pi.single i 1)) * g0⁻¹ := by
      rw [hs, map_mul, map_inv, hφι, hΨx, ← lc_conj_coroot_inv]
      group
    have hsS : s ∈ twE6LongRootSL2 X Xm := by
      refine (hS s).2 (Subgroup.mem_map.2
        ⟨_, lc_coroot_mem_rootSpan hθ (rootChar (par x) θ)⁻¹, ?_⟩)
      exact hsι.symm
    have hJC : twE6LongRootLevi X Xm ≤
        Subgroup.centralizer (twE6LongRootSL2 X Xm : Set (twistedE6RootGroup K σ)) := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hsj : s * j = j * s := Subgroup.mem_centralizer_iff.1 (hJC hj) s hsS
    have hx : (x : twistedE6RootGroup K σ) = φ x * s := by rw [hs, mul_inv_cancel_left]
    rw [hx]
    calc φ x * s * j * (φ x * s)⁻¹ = φ x * (s * j) * s⁻¹ * (φ x)⁻¹ := by group
      _ = φ x * (j * s) * s⁻¹ * (φ x)⁻¹ := by rw [hsj]
      _ = φ x * j * (φ x)⁻¹ := by group

end LeviCube

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
