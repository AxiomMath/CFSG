module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Vtw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ClassicalInvolution.Balance.StrongBalance (GUid conjSUid coe_conjSUid)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
  {c : Kˣ} (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1)
  (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))

theorem vtwPhi_coords_of_forall_conj_leviSU {y : Fin 6 → Multiplicative (ZMod 3)}
    (h : ∀ z : Su K ℓ f 6,
      (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
          (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) *
          (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K)⁻¹ =
        (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K)) :
    y 0 = 1 ∧ ∀ j : Fin 4, y j.succ.succ = 1 := by
  set k := (Multiplicative.toAdd (y 0)).val with hk
  set x : Fin 5 → Multiplicative (ZMod 3) :=
    snocOneHom (Multiplicative (ZMod 3)) 4 fun j : Fin 4 => y j.succ.succ with hx
  set a : Fin 6 → Kˣ := vtwD0 c ^ k * diagTuple c hc x with ha
  have hfix : ∀ z, leviSU hK hf hζ hσζ P hP
      (conjSUid (unitaryInvolution K ℓ f) 6 (vtwA hc h3 y) z) = leviSU hK hf hζ hσζ P hP z :=
    fun z => Subtype.ext ((vtwPhi_conj_leviSU hK hf hζ hσζ P hP hc h3 hct y z).symm.trans (h z))
  have hall := eq_of_forall_leviSU_conjSUid_eq hK hf hζ hσζ P hP (coe_vtwA hc h3 y) hfix
  have hU : ∀ i j, a i = a j := fun i j => Units.ext (hall i j)
  have hP3 : Function.Injective (powHom c hc) := powHom_injective hc
  have hj : ∀ j : Fin 4, a j.castSucc.castSucc = powHom c hc (y j.succ.succ) := by
    intro j
    have hd : vtwD0 c j.castSucc.castSucc = 1 := by fin_cases j <;> rfl
    rw [ha, Pi.mul_apply, Pi.pow_apply, hd, one_pow, one_mul, diagTuple_castSucc, hx,
      snocOneHom_apply_castSucc]
  have h4 : a 4 = powHom c hc (y 0)⁻¹ := by
    have hd : vtwD0 c 4 = c⁻¹ := rfl
    have hx4 : diagTuple c hc x 4 = 1 := by
      rw [show (4 : Fin 6) = (Fin.last 4).castSucc from rfl, diagTuple_castSucc, hx,
        snocOneHom_apply_last, map_one]
    rw [ha, Pi.mul_apply, Pi.pow_apply, hd, hx4, mul_one, map_inv, powHom_apply, inv_pow]
  have h5 : a 5 = powHom c hc (y 2 * y 3 * y 4 * y 5)⁻¹ := by
    have hd : vtwD0 c 5 = 1 := rfl
    have hprod : ∏ j : Fin 5, x j = y 2 * y 3 * y 4 * y 5 := by
      rw [Fin.prod_univ_castSucc, hx, snocOneHom_apply_last, mul_one]
      simp only [snocOneHom_apply_castSucc]
      rw [Fin.prod_univ_four]
      rfl
    rw [ha, Pi.mul_apply, Pi.pow_apply, hd, one_pow, one_mul]
    change diagTuple c hc x (Fin.last 5) = _
    rw [diagTuple_last, ← map_prod, hprod, map_inv]
  have e23 : y 2 = y 3 := hP3 ((hj 0).symm.trans ((hU _ _).trans (hj 1)))
  have e34 : y 3 = y 4 := hP3 ((hj 1).symm.trans ((hU _ _).trans (hj 2)))
  have e45 : y 4 = y 5 := hP3 ((hj 2).symm.trans ((hU _ _).trans (hj 3)))
  have e02 : (y 0)⁻¹ = y 2 := hP3 (h4.symm.trans ((hU _ _).trans (hj 0)))
  have e52 : (y 2 * y 3 * y 4 * y 5)⁻¹ = y 2 := hP3 (h5.symm.trans ((hU _ _).trans (hj 0)))
  have h3' : y 3 = y 2 := e23.symm
  have h4' : y 4 = y 2 := (e23.trans e34).symm
  have h5' : y 5 = y 2 := (e23.trans (e34.trans e45)).symm
  rw [h3', h4', h5'] at e52
  have key : ∀ t : Multiplicative (ZMod 3), (t * t * t * t)⁻¹ = t → t = 1 := by decide
  have h2 : y 2 = 1 := key _ e52
  have h0 : y 0 = 1 := by rw [← _root_.inv_inj, inv_one, e02, h2]
  refine ⟨h0, fun j => ?_⟩
  fin_cases j
  · exact h2
  · exact e23.symm.trans h2
  · exact (e23.trans e34).symm.trans h2
  · exact (e23.trans (e34.trans e45)).symm.trans h2

theorem vtwPhi_conj_injective :
    Function.Injective ((twistedE6InndiagConj K (unitaryInvolution K ℓ f)).comp
      (vtwPhi hK hf hζ hσζ P hP hc h3 hct)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hfix : ∀ z : Su K ℓ f 6,
      (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
          (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) *
          (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K)⁻¹ =
        (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) := fun z => by
    have h := congrArg (fun φ : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) =>
      ((φ (leviSU hK hf hζ hσζ P hP z) : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
        ModGL TwistTag.E6.tag K)) hy
    simpa only [MonoidHom.comp_apply, twistedE6InndiagConj_apply, MulAut.one_apply] using h
  obtain ⟨h0, h25⟩ := vtwPhi_coords_of_forall_conj_leviSU hK hf hζ hσζ P hP hc h3 hct hfix
  have hy1 : vtwPhi hK hf hζ hσζ P hP hc h3 hct y = 1 :=
    twistedE6InndiagConj_injective Fact.out hf hK _ (unitaryInvolution_apply K ℓ f)
      (hy.trans (map_one _).symm)
  rw [vtwPhi_eq_of_eq_one hK hf hζ hσζ P hP hc h3 hct h0 h25] at hy1
  have hr : twE6R0 c hct ^ (Multiplicative.toAdd (y 1)).val = 1 :=
    Subgroup.inclusion_injective _ (hy1.trans (map_one _).symm)
  have h1 : y 1 = 1 := powHom_injective (orderOf_twE6R0 Nat.prime_three (by norm_num) hc hct)
    (by rw [powHom_apply, hr, map_one])
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h25 0
  · exact h25 1
  · exact h25 2
  · exact h25 3

theorem isElemAbelian_vtwV :
    IsElemAbelian 3 (vtwV hK hf hζ hσζ P hP hc h3 hct) ∧
      Nat.card (vtwV hK hf hζ hσζ P hP hc h3 hct) = 3 ^ 6 :=
  isElemAbelian_range_of_injective (vtwPhi_conj_injective hK hf hζ hσζ P hP hc h3 hct)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
