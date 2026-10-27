module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed
import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8NegC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Weyl


theorem e8nc_conj_inv_rootDiagUnit {L : Type} [Field L] (v : WeylGroup Tag.E8)
    (a : Fin Tag.E8.rank → Lˣ) :
    (canonicalRep (coxeterSystem Tag.E8) L v)⁻¹ * rootDiagUnit Tag.E8 a *
        canonicalRep (coxeterSystem Tag.E8) L v = rootDiagUnit Tag.E8 (weylTuple v⁻¹ a) := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff a (weylTuple v⁻¹ a) v).2
    (fun μ => by rw [rootChar_weylTuple, inv_inv])
  rw [h]
  group

end Weyl

section Diag


theorem e8nc_datum_char {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 3 = 1)
    (D : LangPlaneData Tag.E8 K E₀) {x : adjointGroup Tag.E8 K} (hx : x ∈ E₀)
    {a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit Tag.E8 a = diagMap D x) :
    (∀ i, a i ^ 3 = 1) ∧ ∀ v, rootChar a (D.w • v) = (rootChar a v)⁻¹ := by
  have hinj : Function.Injective (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hA3 : a ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    show rootDiagUnit Tag.E8 a ^ 3 = 1
    rw [ha, ← map_pow, hE₀p x hx, map_one]
  have hcube : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun hA3 i
  obtain ⟨t, ht, hte⟩ := D.hc x hx
  have hat : rootDiagUnit Tag.E8 a = t := by
    rw [ha, diagMap_apply, ← hte]
    simp [MulAut.conj_apply, mul_assoc]
  have hT := (mem_twistedTorusOf.1 ht).2
  rw [← hat, CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit D.Fr D.hFr] at hT
  have htw := (rootDiagUnit_eq_conj_canonicalRep_iff a _ D.w).1 hT.symm
  have hFa : a ^ Nat.card K = a⁻¹ := by
    rw [pow_eq_pow_mod (Nat.card K) hA3, hK]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hA3]
  refine ⟨hcube, fun v => ?_⟩
  rw [htw v, hFa, rootChar_inv_apply]

theorem e8nc_diagMap_fixed {K : Type} [Field K] [Finite K] {A : Subgroup (adjointGroup Tag.E8 K)}
    (D : LangPlaneData Tag.E8 K A) (x : adjointGroup Tag.E8 K) :
    canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) D.w *
        Units.map (entrywiseHom D.Fr) (diagMap D x) *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) D.w)⁻¹ = diagMap D x := by
  have hι : Units.map (entrywiseHom D.Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((D.c * x * D.c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * x * D.c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) :=
    adjEmb_frobenius D.Fr D.hFr (D.c * x * D.c⁻¹)
  rw [diagMap_apply, map_mul, map_mul, map_inv, hι, D.hg0]
  group

theorem e8nc_diagMap_mem_adj {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup Tag.E8 K)} (D : LangPlaneData Tag.E8 K A)
    (x : adjointGroup Tag.E8 K) : diagMap D x ∈ adjointGroup Tag.E8 (AlgebraicClosure K) := by
  have h := adjEmb_mem (τ := Tag.E8) (K := K) (L := AlgebraicClosure K) (D.c * x * D.c⁻¹)
  rw [adjEmb_apply] at h
  rw [diagMap_apply]
  exact mul_mem (mul_mem (inv_mem D.hg0C) h) D.hg0C

end Diag

section Rational


theorem e8nc_diagMap_rational {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup Tag.E8 K)} (D : LangPlaneData Tag.E8 K A)
    (P : Subgroup (ModGL Tag.E8 (AlgebraicClosure K))) (hPfin : Finite P)
    (hPC : P ≤ adjointGroup Tag.E8 (AlgebraicClosure K))
    (hPF : ∀ x ∈ P, canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) D.w *
        Units.map (entrywiseHom D.Fr) x *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) D.w)⁻¹ = x)
    (hPP : ⁅P, P⁆ = P) : ∀ x ∈ P, ∃ g, diagMap D g = x := by
  set n := canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) D.w
  set Φ : ModGL Tag.E8 (AlgebraicClosure K) →* ModGL Tag.E8 (AlgebraicClosure K) :=
    Units.map (entrywiseHom D.Fr)
  set P' : Subgroup (ModGL Tag.E8 (AlgebraicClosure K)) := P.map (MulAut.conj D.g0).toMonoidHom
    with hP'
  haveI : Finite P' :=
    Finite.of_surjective _ ((MulAut.conj D.g0).toMonoidHom.subgroupMap_surjective P)
  have hP'C : P' ≤ adjointGroup Tag.E8 (AlgebraicClosure K) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mul_mem (mul_mem D.hg0C (hPC hv)) (inv_mem D.hg0C)
  have hP'F : ∀ w ∈ P', Φ w = w := by
    rintro _ ⟨v, hv, rfl⟩
    have hvR := hPF v hv
    change Φ (D.g0 * v * D.g0⁻¹) = D.g0 * v * D.g0⁻¹
    rw [map_mul, map_mul, map_inv, D.hg0]
    calc D.g0 * n * Φ v * (D.g0 * n)⁻¹ = D.g0 * (n * Φ v * n⁻¹) * D.g0⁻¹ := by group
      _ = D.g0 * v * D.g0⁻¹ := by rw [hvR]
  have hP'P : ⁅P', P'⁆ = P' := by rw [hP', ← Subgroup.map_commutator, hPP]
  obtain ⟨-, -, hrat⟩ := finite_fixed_subgroup_rational_perfect (K := K) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) D.Fr D.hFr P' hP'C hP'F
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hrat P' le_rfl hP'P ⟨x, hx, rfl⟩
  refine ⟨D.c⁻¹ * ⟨z, hz⟩ * D.c, ?_⟩
  rw [diagMap_apply]
  have e1 : (D.c * (D.c⁻¹ * ⟨z, hz⟩ * D.c) * D.c⁻¹ : adjointGroup Tag.E8 K) = ⟨z, hz⟩ := by group
  rw [e1]
  change D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) z * D.g0 = x
  rw [hzx]
  change D.g0⁻¹ * (D.g0 * x * D.g0⁻¹) * D.g0 = x
  group

end Rational

end KSE8NegC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
