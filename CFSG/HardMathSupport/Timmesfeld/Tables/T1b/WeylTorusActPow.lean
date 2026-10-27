module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rootChar_zpow {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (m : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar (a ^ m) v = rootChar a v ^ m := by
  simp only [rootChar, Pi.pow_apply]
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, ← zpow_mul, mul_comm]

theorem weylAct_zpow {τ : Tag} {K : Type} [Field K] (w : WeylGroup τ) (a : Fin τ.rank → Kˣ)
    (m : ℤ) : weylAct w (a ^ m) = weylAct w a ^ m := by
  funext i
  simp only [weylAct, Pi.pow_apply, rootChar_zpow]

private theorem rootChar_iterate {τ : Tag} {K : Type} [Field K]
    {u : WeylGroup τ} {c : Fin τ.rank → Kˣ} {m : ℤ}
    (hc : weylAct u (c ^ m) = c) (k : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar c v = rootChar c (((u⁻¹) ^ k) • v) ^ (m ^ k) := by
  have hstep : ∀ v : Fin τ.rank → ℤ, rootChar c v = rootChar c (u⁻¹ • v) ^ m := fun v => by
    calc rootChar c v = rootChar (weylAct u (c ^ m)) v := by rw [hc]
      _ = rootChar (c ^ m) (u⁻¹ • v) := rootChar_weylAct u (c ^ m) v
      _ = rootChar c (u⁻¹ • v) ^ m := rootChar_zpow c m (u⁻¹ • v)
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      calc rootChar c v = rootChar c (u⁻¹ • v) ^ m := hstep v
        _ = (rootChar c (((u⁻¹) ^ k) • (u⁻¹ • v)) ^ (m ^ k)) ^ m := by
              rw [ih (u⁻¹ • v)]
        _ = rootChar c (((u⁻¹) ^ (k + 1)) • v) ^ (m ^ (k + 1)) := by
              rw [← zpow_mul, ← mul_smul, ← pow_succ, ← pow_succ]

theorem rootChar_pow_sub_one_eq_one_of_weylAct_zpow_eq {τ : Tag} {K : Type} [Field K]
    {u : WeylGroup τ} {c : Fin τ.rank → Kˣ} {m : ℤ} (hc : weylAct u (c ^ m) = c)
    {v : Fin τ.rank → ℤ} {ℓ : ℕ} (hv : (u ^ ℓ) • v = v) : rootChar c v ^ (m ^ ℓ - 1) = 1 := by
  have hiter := rootChar_iterate hc ℓ v
  have hinv : ((u⁻¹) ^ ℓ) • v = v := by
    rw [inv_pow]
    simpa using (congrArg (fun x => (u ^ ℓ)⁻¹ • x) hv).symm
  rw [hinv] at hiter
  calc rootChar c v ^ (m ^ ℓ - 1)
      = rootChar c v ^ (m ^ ℓ) * (rootChar c v)⁻¹ := by rw [zpow_sub, zpow_one]
    _ = rootChar c v * (rootChar c v)⁻¹ := by rw [hiter.symm]
    _ = 1 := mul_inv_cancel _

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
