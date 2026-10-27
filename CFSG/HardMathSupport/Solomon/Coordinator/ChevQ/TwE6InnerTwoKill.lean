module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree


theorem normalizesRGroup_of_twKills (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hkill : TwKills K σ E₀ g0 α) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  let A : Subgroup (ModGL TwistTag.E6.tag K) := E₀.map (twistedE6RootGroup K σ).subtype
  let D : CFSG.LieType.SeitzGeneration.ExcWideThree.TwLangData K σ q A :=
    { v := v, Fr := Fr, hFr := hFr, g0 := g0, hg0C := hg0C, hg0 := hg0, c := 1,
      hcI := one_mem _, hc := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        simp only [one_mul, inv_one, mul_one]
        exact hT y hy }
  have hkill' : ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨a, ha, hχ⟩ := hkill y hy
    exact ⟨a, by simpa [D] using ha, hχ⟩
  obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K σ q hr hσ hK A D α hα hkill'
  let g : ↥(twistedE6RootGroup K σ) := ⟨u, hu⟩
  have hg1 : g ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hgn : g ^ (ringChar K ^ n) = 1 := Subtype.ext (by simpa using hn)
  refine ⟨Subgroup.zpowers g, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hg1
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h.2
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hgn, one_zpow]
  · intro y hy
    have hA : (twistedE6RootGroup K σ).subtype y ∈ A := Subgroup.mem_map_of_mem _ hy
    have hyc : Commute g y := Subtype.ext (hcomm _ hA)
    rw [MonoidHom.map_zpowers]
    congr 1
    change y * g * y⁻¹ = g
    rw [← hyc.eq, mul_inv_cancel_right]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
