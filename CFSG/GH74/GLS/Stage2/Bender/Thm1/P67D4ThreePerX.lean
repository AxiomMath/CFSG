module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeEmb
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
public import CFSG.RankThree.PartOne.KGD.D4QPerX
public import CFSG.RankThree.PartOne.KGD.D4T36Family

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
open CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4T36_perx_three {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ]
    [IsAlgClosed L] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) [Algebra K L]
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : 2 < ℓ ^ f) (hℓ3 : ℓ ≠ 3)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (w : WeylGroup TwistTag.D4.tag) (hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = 3)
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    (hne : (rootCharKernel b).Nonempty) :
    ∀ V : Subgroup (Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      V.Normal → Group.IsSolvable V → ∀ v ∈ V,
        d4QPsi (triEmb K σ L) g0 c x v ∈
          twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ,
          d4QPsi (triEmb K σ L) g0 c x v = rootDiagUnit TwistTag.D4.tag a ∧
            ∀ α ∈ rootCharKernel b, rootChar a α = 1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2' : ε = 1 ∨ 2 < ℓ ^ f := Or.inr hq2
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hn w hnw (d4T36M ε) hw
  have hιC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L)
  have hιΦ := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm
  have hperf' : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
        ⁅P, P⁆ = P → P ≤ (triEmb K σ L).range := fun P _ hPC hPF _ => hperf P hPC hPF
  have hordb : orderOf (rootDiagUnit TwistTag.D4.tag b) = 3 := by
    rw [hb]
    have e1 : orderOf (g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0) =
        orderOf (triEmb K σ L (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (triEmb K σ L (c * x * c⁻¹))
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (triEmb K σ L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective _ triEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      rw [show ((MulAut.conj c).toMonoidHom x) = c * x * c⁻¹ from rfl] at this
      exact this
    rw [e1, e2, e3, hx]
  have hb1 := ne_one_of_orderOf_rootDiagUnit Nat.prime_three hordb
  have hbfix : b ∈ fixedCharTuples (d4T36M ε) Fr := by
    have hh' := hh
    rw [hT] at hh'
    obtain ⟨b', hb', hbb'⟩ := Subgroup.mem_map.1 hh'
    have : b' = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) hbb'
    exact this ▸ hb'
  obtain ⟨i, hSig⟩ : ∃ i, rootCharKernel b = d4Sigma i := by
    rcases d4T36_rootCharKernel_cases hε hbfix hb1 with h | ⟨i, hi⟩
    · rw [h] at hne
      exact absurd hne Set.not_nonempty_empty
    · exact ⟨i, hi⟩
  have conj1 : ∀ z : ModGL TwistTag.D4.tag L,
      z ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) (d4Sigma i) →
      z ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, z = rootDiagUnit TwistTag.D4.tag a ∧
          ∀ α ∈ rootCharKernel b, rootChar a α = 1 := by
    intro z hz
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨hzH, -⟩ := mem_twistedTorusOf.1 hzT
    obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzH
    refine ⟨hzT, a', ha', fun α hα => ?_⟩
    rw [hSig] at hα
    exact (rootDiagUnit_mem_centralizer_rootSpan_iff a'
      (fun α hα => isRoot_of_mem_d4Sigma hα)).1 (ha' ▸ hzC) α hα
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4,
      (fun α : Fin Tag.D4.rank → ℤ => v • α) '' d4A2Sigma = trialitySigma i := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  have hvS : rootCharKernel b =
      (fun α : Fin Tag.D4.rank → ℤ => v • α) '' d4A2Sigma := by
    rw [hSig]
    exact hv.symm
  have hpK : ringChar L ≠ 3 := by
    rw [ringChar.eq L ℓ]
    exact hℓ3
  obtain ⟨-, hMset, -, -, -, -, -, -, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer L 3 Nat.prime_three (by norm_num) hpK b hordb v hvS
  have hcentH : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag a = g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0 →
      ∀ y : ModGL TwistTag.D4.tag L, y ∈ adjointGroup TwistTag.D4.tag L →
        y * rootDiagUnit TwistTag.D4.tag a = rootDiagUnit TwistTag.D4.tag a * y →
        y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    intro a ha y hyG hyc
    have hab : a = b := rootDiagUnit_injective (ha.trans hb.symm)
    subst hab
    have hy : y ∈ toralCentralizer Tag.D4 L a :=
      Subgroup.mem_inf.2 ⟨hyG, Subgroup.mem_centralizer_singleton_iff.2 hyc⟩
    have hy' : y ∈ (torusGroup Tag.D4 L : Set (ModGL Tag.D4 L)) *
        (d4A2Qv L v : Set (ModGL Tag.D4 L)) := by
      rw [← hMset]
      exact hy
    obtain ⟨h, hh', q, hq, rfl⟩ := hy'
    rw [d4A2Qv_eq_rootSpan] at hq
    have hq' : q ∈ rootSpan TwistTag.D4.tag L (d4Sigma i) := by
      rw [← hSig, hvS]
      exact hq
    exact Subgroup.mul_mem_sup hh' hq'
  have hdψ : ∀ (ψ : Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →* ModGL TwistTag.D4.tag L),
      (∀ y, ψ y = g0⁻¹ * triEmb K σ L
        (c * (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * c⁻¹) * g0) →
      d4QPsi (triEmb K σ L) g0 c x = ψ := fun ψ hψ =>
    MonoidHom.ext fun y => (d4QPsi_apply (triEmb K σ L) g0 c x y).trans (hψ y).symm
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, -⟩ := d4T36_family hf hk hε hq2' Fr
    hFr n hn (fun x => by rw [hnw]; exact hw x) i
  have hcb : rootDiagUnit TwistTag.D4.tag b ∈
      subtorusSigma n (twistHom TwistTag.D4 L Fr) (d4Sigma i) :=
    Subgroup.mem_inf.2 ⟨hh, (rootDiagUnit_mem_centralizer_rootSpan_iff b
      (fun α hα => isRoot_of_mem_d4Sigma hα)).2 fun α hα => by
        rw [← hSig] at hα
        exact hα.2⟩
  have hcS : c * x * c⁻¹ ∈ subtorusImage (triEmb K σ L) g0
      (subtorusSigma n (twistHom TwistTag.D4 L Fr) (d4Sigma i)) :=
    (mem_subtorusImage_iff (triEmb K σ L) g0 _ (c * x * c⁻¹)).2 (by rw [← hb]; exact hcb)
  obtain ⟨ψ, -, hψ, -, -, -, -, hψV⟩ := sigma_embedding_data_gen (triEmb K σ L)
    triEmb_injective hιC (twistHom TwistTag.D4 L Fr) hιΦ n g0 hg0C hg0 hperf' Nat.prime_three
    (fun _ : Unit => P) (fun _ => hPfin) (fun _ => hPq) (fun _ => hPQ) (fun _ => hPR)
    (fun _ => hPadj) (fun _ y hy hyR u hu => hPnorm y hy hyR u hu)
    (fun y hy hyR hcomm' => hPcent y hy hyR (fun u hu => hcomm' () u hu)) hx c hcS hcentH
  intro V hVn hVs v hv
  rw [hdψ ψ hψ]
  exact conj1 _ (hψV V hVn hVs v hv)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
