module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4
import CFSG.ClassicalGroups.Alternating.OrderEleven
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad
import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)

theorem ten_dvd_finrank_of_geomSum_eq_zero {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) (N : Submodule F V) (T : Module.End F V)
    (hTN : ∀ v ∈ N, T v ∈ N) (hS : ∀ v ∈ N, (∑ i ∈ Finset.range 11, T ^ i) v = 0) :
    10 ∣ Module.finrank F N := by
  have hchar : CharP F 2 :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.card_two_charP hF
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have h2 : ∀ w : N, (2 : ℕ) • w = 0 := fun w => by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  letI : Module (ZMod 2) N := AddCommGroup.zmodModule h2
  haveI : Finite V := Module.finite_of_finite F
  haveI : FiniteDimensional (ZMod 2) N := Module.Finite.of_finite
  let T' : Module.End (ZMod 2) N := ((T.restrict hTN : N →ₗ[F] N) : N →+ N).toZModLinearMap 2
  have hpow : ∀ (i : ℕ) (n : N), ((T' ^ i) n : V) = (T ^ i) (n : V) := by
    intro i
    induction i with
    | zero => intro n; rfl
    | succ i ih =>
      intro n
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      exact ih (T' n)
  have hT' : ∑ i ∈ Finset.range 11, T' ^ i = 0 := by
    refine LinearMap.ext fun n => Subtype.ext ?_
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    simp only [hpow]
    rw [← LinearMap.sum_apply]
    exact hS n n.2
  have h10 := CFSG.ClassicalGroups.Alternating.ten_dvd_finrank_of_sum_eq_zero hT'
  have hc1 : Nat.card N = 2 ^ Module.finrank F N := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF]
  have hc2 : Nat.card N = 2 ^ Module.finrank (ZMod 2) N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rwa [Nat.pow_right_injective le_rfl (hc1.symm.trans hc2)]

theorem fixedByEnd_eq_bot_of_commute_eleven {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] (hF : Nat.card F = 2) (hV : Module.finrank F V = 10) {d y : V ≃ₗ[F] V}
    (hd : d ≠ 1) (hy : y ^ 11 = 1) (hy1 : y ≠ 1) (hdy : d * y = y * d) :
    fixedByEnd d = ⊥ := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by omega)
  set T : Module.End F V := (y : V →ₗ[F] V) with hTdef
  have hT11 : T ^ 11 = 1 := by
    ext v
    have h := LinearEquiv.congr_fun hy v
    rw [LinearEquiv.coe_one, id, LinearEquiv.pow_apply] at h
    rw [hTdef, Module.End.pow_apply, Module.End.one_apply]
    exact h
  have hT1 : T - 1 ≠ 0 := fun h => hy1 (LinearEquiv.ext fun v => by
    have := LinearMap.congr_fun h v
    simpa [hTdef, sub_eq_zero] using this)
  set W : Submodule F V := LinearMap.range (T - 1)
  have hWT : ∀ v ∈ W, T v ∈ W := by
    rintro _ ⟨u, rfl⟩
    exact ⟨T u, by simp [LinearMap.sub_apply]⟩
  have hWS : ∀ v ∈ W, (∑ i ∈ Finset.range 11, T ^ i) v = 0 := by
    rintro _ ⟨u, rfl⟩
    have h := congrArg (fun f : Module.End F V => f u) (geom_sum_mul T 11)
    simpa [hT11] using h
  have hWne : W ≠ ⊥ := fun h => hT1 (LinearMap.range_eq_bot.1 h)
  have hW10 := ten_dvd_finrank_of_geomSum_eq_zero hF W T hWT hWS
  have hWle : Module.finrank F W ≤ 10 := hV ▸ Submodule.finrank_le W
  have hWpos : 1 ≤ Module.finrank F W := Submodule.one_le_finrank_iff.2 hWne
  have hWtop : W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    obtain ⟨k, hk⟩ := hW10
    omega
  have hS0 : ∀ v, (∑ i ∈ Finset.range 11, T ^ i) v = 0 := fun v =>
    hWS v (hWtop ▸ Submodule.mem_top)
  have hNT : ∀ v ∈ fixedByEnd d, T v ∈ fixedByEnd d := fun v hv => by
    rw [mem_fixedByEnd] at hv ⊢
    have h := LinearEquiv.congr_fun hdy v
    simp only [LinearEquiv.mul_apply] at h
    rw [hv] at h
    exact h
  have hN10 := ten_dvd_finrank_of_geomSum_eq_zero hF (fixedByEnd d) T hNT fun v _ => hS0 v
  by_contra hne
  have hNle : Module.finrank F (fixedByEnd d) ≤ 10 := hV ▸ Submodule.finrank_le _
  have hNpos : 1 ≤ Module.finrank F (fixedByEnd d) := Submodule.one_le_finrank_iff.2 hne
  have hNtop : fixedByEnd d = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    obtain ⟨k, hk⟩ := hN10
    omega
  exact hd (LinearEquiv.ext fun v => mem_fixedByEnd.1 (hNtop ▸ Submodule.mem_top))

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
