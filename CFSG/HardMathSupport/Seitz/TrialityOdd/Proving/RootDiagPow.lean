module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.D4RegularStabilizer

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rootDiagUnit_pow_imp_forall
    {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) (n : ℕ)
    (h : rootDiagUnit τ b ^ n = 1) : ∀ i, b i ^ n = 1 := by
  have hpow : ∀ m : ℕ, rootDiagUnit τ b ^ m = rootDiagUnit τ (b ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ m ih => rw [pow_succ, ih, ← rootDiagUnit_mul, pow_succ]
  have h1 : rootDiagUnit τ (b ^ n) = rootDiagUnit τ 1 := by
    rw [rootDiagUnit_one, ← hpow n, h]
  have h2 : rootDiagAutHom τ K (b ^ n) = rootDiagAutHom τ K 1 := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change rootDiagUnit τ (b ^ n) * (g : ModGL τ K) * (rootDiagUnit τ (b ^ n))⁻¹ =
      rootDiagUnit τ 1 * (g : ModGL τ K) * (rootDiagUnit τ 1)⁻¹
    rw [h1]
  have hb : b ^ n = 1 := rootDiagAutHom_injective h2
  intro i
  have hi := congrFun hb i
  simpa using hi

theorem stab_one_of_rootDiagUnit_pow
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {b : Fin Tag.D4.rank → Lˣ} (hbp : rootDiagUnit Tag.D4 b ^ p = 1)
    (hker : rootCharKernel (τ := Tag.D4) b = ∅) :
    ∀ w ∈ rootCharStabilizer (τ := Tag.D4) b, w = 1 := by
  intro w hw
  have hsub := d4_rootCharStabilizer_subset_one hp hp5
    (rootDiagUnit_pow_imp_forall b p hbp) hker hw
  exact Set.mem_singleton_iff.1 hsub

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

end
