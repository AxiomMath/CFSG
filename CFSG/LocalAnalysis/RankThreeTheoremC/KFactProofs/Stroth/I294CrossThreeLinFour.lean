module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinBase
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODEigen
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.Open.StatedAPI CFSG.RankThree.PartOne.KFU
open CFSG.LocalAnalysis.RankFourTheoremC.I294OD

namespace LinThree

section Torus

variable {K : Type} [Field K]

def torusThreeFour : (Fin 3 → Kˣ) →* (Fin 4 → Kˣ) where
  toFun a := ![a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹]
  map_one' := by
    funext j
    fin_cases j <;> simp
  map_mul' a b := by
    funext j
    fin_cases j <;> simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

theorem torusThreeFour_injective : Function.Injective (torusThreeFour (K := K)) := by
  intro a b h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp only [torusThreeFour, MonoidHom.coe_mk, OneHom.coe_mk] at e0 e1 e2
  funext i
  fin_cases i
  · simpa using e0
  · simpa using e1
  · simpa using e2

theorem prod_torusThreeFour (a : Fin 3 → Kˣ) : ∏ i, torusThreeFour a i = 1 := by
  simp [torusThreeFour, Fin.prod_univ_four]

end Torus

theorem scalar_pow_four_eq_one {K : Type} [Field K] (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 K) : c ^ 4 = 1 := by
  have h := det_of_mem_statedSL hc
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] at h
  apply Units.ext
  simpa using h

end LinThree

open LinThree

theorem i294CrossModelPSL4_holds : I294CrossModelPSL4 := by
  intro K _ _ h3 x hx
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hZ : ∀ z ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K), z ^ 4 = 1 :=
    pow_eq_one_of_mem_statedScalars_subgroupOf fun c hc => scalar_pow_four_eq_one c hc
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three (N := 4) (by norm_num) hZ hx3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  have hωprim : IsPrimitiveRoot ω 3 := hω ▸ IsPrimitiveRoot.orderOf ω
  have hprim : IsPrimitiveRoot (ω : K) 3 :=
    hωprim.map_of_injective (f := Units.coeHom K) Units.val_injective
  haveI : NeZero ((3 : ℕ) : K) := hprim.neZero'
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  let μ : Subgroup Kˣ := Subgroup.zpowers ω
  have hμp : ∀ y : μ, y ^ 3 = 1 := by
    rintro ⟨y, k, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω3, one_zpow]
  have hμcard : Nat.card μ = 3 := by rw [Nat.card_zpowers, hω]
  have hAcard : Nat.card (Fin 3 → μ) = 3 ^ 3 := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hμcard]
  have hgA : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    have := congrArg (fun z : StatedSL 4 K => ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hg3
    simpa using this
  obtain ⟨P, Q, u, hPQ, hQP, hAP⟩ := exists_eigenbasis_matrix
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    (top_le_span_eigenvectors _ hprim (by norm_num) (NeZero.ne _) hgA)
  let P' : GL (Fin 4) K := ⟨P, Q, hPQ, hQP⟩
  let t : (Fin 3 → μ) →* (Fin 4 → Kˣ) :=
    torusThreeFour.comp (MonoidHom.compLeft μ.subtype (Fin 3))
  let φ : (Fin 3 → μ) →* GL (Fin 4) K :=
    (MulAut.conj P').toMonoidHom.comp ((diagUHom (n := 4) (K := K)).comp t)
  have hφval : ∀ a, ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      P * Matrix.diagonal (fun j => ((t a j : Kˣ) : K)) * Q := fun a => rfl
  have hφinj : Function.Injective φ := by
    refine (MulAut.conj P').injective.comp (diagU_injective.comp ?_)
    refine torusThreeFour_injective.comp ?_
    intro a b hab
    funext i
    exact Subtype.ext (congrFun hab i)
  have hH : ∀ a, φ a ∈ StatedSL 4 K := by
    intro a
    refine mem_statedSL_of_det ?_
    rw [hφval, Matrix.det_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.det_diagonal,
      ← Units.coe_prod]
    show ((∏ i, torusThreeFour (fun j => (a j : Kˣ)) i : Kˣ) : K) = 1
    rw [prod_torusThreeFour, Units.val_one]
  have hcomm : ∀ a, ((g : GL (Fin 4) K)) * φ a = φ a * (g : GL (Fin 4) K) := by
    intro a
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hφval]
    exact (commute_conj_diagonal P Q hPQ hQP _ u hAP _).symm
  exact le_pRank_centralizer_statedProj_of_coprime (H := StatedSL 4 K) (A := Fin 3 → μ) (k := 3)
    (N := 4) (by norm_num) hZ (fun a b => mul_comm a b) (fun a => funext fun i => hμp (a i))
    hAcard φ hφinj hH g hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
