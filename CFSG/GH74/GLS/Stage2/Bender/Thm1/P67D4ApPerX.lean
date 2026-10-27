module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnStab
public import CFSG.RankThree.PartOne.KGD.D4QPerX
public import CFSG.RankThree.PartOne.KGD.D4QPlane
public import CFSG.RankThree.PartOne.KE.StabGeneral

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem ap_perx {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ] [IsAlgClosed L]
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} [Algebra K L] (hq : (ℓ ^ f) % 3 = 2)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * trialityOpposition L)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    (hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L))
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α)
    (hSn : ∀ α ∈ S, -α ∈ S)
    (hfam : ∃ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan TwistTag.D4.tag L S ∧
      P ≤ twistedFixedPoints (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) ∧
      P ≤ adjointGroup TwistTag.D4.tag L ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S,
        y ∈ twistedFixedPoints (trialityOpposition L)
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S,
        y ∈ twistedFixedPoints (trialityOpposition L)
          (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) →
        (∀ u ∈ P, y * u = u * y) →
          y ∈ subtorusSigma (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) S))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = 3)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * triEmb K σ L x * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    (hcen : rootDiagUnit TwistTag.D4.tag b ∈
      Subgroup.centralizer (rootSpan TwistTag.D4.tag L S : Set (ModGL TwistTag.D4.tag L)))
    (hker : rootCharKernel b ⊆ S) :
    ∀ V : Subgroup (Subgroup.centralizer
      ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
      V.Normal → Group.IsSolvable V → ∀ v ∈ V,
        d4QPsi (triEmb K σ L) g0 1 x v ∈
          subtorusSigma (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) S := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpq : 3 ∣ ℓ ^ f + 1 := by omega
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hιC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L)
  have hιΦ := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm
  have hperf' : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
        ⁅P, P⁆ = P → P ≤ (triEmb K σ L).range := fun P _ hPC hPF _ => hperf P hPC hPF
  have hstab : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, (∀ i, a i ^ 3 = 1) → a ≠ 1 →
      rootDiagUnit TwistTag.D4.tag a ∈ twistedTorusOf (trialityOpposition L)
        (twistHom TwistTag.D4 L Fr) → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)) := by
    intro a ha3 ha1 haT
    have hafix : a ∈ fixedCharTuples d4QM Fr := by
      have h := haT
      rw [d4Q_twistedTorus] at h
      obtain ⟨a', ha', haa'⟩ := h
      have : a' = a := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) haa'
      exact this ▸ ha'
    obtain ⟨h1, h3⟩ := d4Q_eq_of_pow_eq_one hFr hpq hafix ha3
    refine d4_stab_three ha3 ha1 (fun i => ?_)
    fin_cases i
    · exact h1
    · exact (congrArg a (show TwistTag.D4.perm (1 : Fin 4) = 3 from by decide)).trans
        (h3.trans h1.symm)
    · rfl
    · exact (congrArg a (show TwistTag.D4.perm (3 : Fin 4) = 0 from by decide)).trans h3.symm
  intro V hVn hVs v hv
  have := sigma_embedding_data_of_stab (ι' := PUnit) (triEmb K σ L) triEmb_injective hιC
    (twistHom TwistTag.D4 L Fr) hιΦ (trialityOpposition L) g0 hg0C hg0 hperf' Nat.prime_three hstab
    hS hSn (fun _ => P) (fun _ => hPfin) (fun _ => hPq) (fun _ => hPQ) (fun _ => hPR)
    (fun _ => hPadj) (fun _ => hPnorm) (fun y hy hyR hc => hPcent y hy hyR (hc ())) hx 1
    ((mem_subtorusImage_iff (triEmb K σ L) g0 _ (1 * x * 1⁻¹)).2 (by
      rw [one_mul, inv_one, mul_one, ← hb]
      exact Subgroup.mem_inf.2 ⟨hh, hcen⟩))
    (by
      intro a ha
      have hab : a = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
        (by rw [ha, one_mul, inv_one, mul_one, hb])
      exact hab ▸ hker)
  obtain ⟨ψ, -, hψ, -, -, -, -, hψV⟩ := this
  have h := hψV V hVn hVs v hv
  have e : d4QPsi (triEmb K σ L) g0 1 x v = ψ v := by
    rw [hψ v]
    exact d4QPsi_apply (triEmb K σ L) g0 1 x v
  rw [e]
  exact h


end CFSG.GH74.GLS.Stage2.Bender.Thm1
