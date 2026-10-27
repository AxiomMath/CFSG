module

public import CFSG.LieType.Chevalley.LatticeCharacterInterpolation
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KGD.D4T36Torus

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Lattice

theorem exists_tuple_of_char_eq {L : Type} [Field L] [IsAlgClosed L] {τ : Tag}
    (B C : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (hB : B.det ≠ 0) (b : Fin τ.rank → Lˣ) :
    ∃ a : Fin τ.rank → Lˣ, ∀ m, rootChar a (B *ᵥ m) = rootChar b (C *ᵥ m) := by
  let _ : DivisibleBy (Additive Lˣ) ℤ := divisibleByOfSMulRightSurj _ _ fun {n} hn y => by
    obtain ⟨x, hx⟩ := exists_zpow_eq_of_isAlgClosed hn (Additive.toMul y)
    refine ⟨Additive.ofMul x, ?_⟩
    change n • Additive.ofMul x = y
    rw [← ofMul_zpow, hx, ofMul_toMul]
  have hBaer : Module.Baer ℤ (Additive Lˣ) := Module.Baer.of_divisible _
  have hf : Function.Injective (Matrix.mulVecLin B) := by
    intro x y hxy
    have h1 : B.adjugate *ᵥ (B *ᵥ x) = B.adjugate *ᵥ (B *ᵥ y) := by
      simpa only [Matrix.mulVecLin_apply] using congrArg (fun z => B.adjugate *ᵥ z) hxy
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h1
    exact smul_right_injective (Fin τ.rank → ℤ) hB h1
  let ψ0 : (Fin τ.rank → ℤ) →ₗ[ℤ] Additive Lˣ :=
    { toFun := fun m => Additive.ofMul (rootChar b (C *ᵥ m))
      map_add' := fun x y => by
        rw [Matrix.mulVec_add, rootChar_add, ofMul_mul]
      map_smul' := fun c x => by
        rw [Matrix.mulVec_smul, rootChar_zsmul, ofMul_zpow]
        rfl }
  obtain ⟨ψ, hψ⟩ := hBaer.extension_property (Matrix.mulVecLin B) hf ψ0
  refine ⟨fun i => Additive.toMul (ψ (Pi.single i 1)), fun m => ?_⟩
  have h1 : rootChar (fun i => Additive.toMul (ψ (Pi.single i 1))) (B *ᵥ m) =
      Additive.toMul (ψ (B *ᵥ m)) := CTTorus.prod_zpow_eq_toMul ψ (B *ᵥ m)
  have h2 : ψ (B *ᵥ m) = ψ0 m := by
    have := congrArg (fun φ : (Fin τ.rank → ℤ) →ₗ[ℤ] Additive Lˣ => φ m) hψ
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply] using this
  rw [h1, h2]
  rfl

end Lattice

section Determinant

theorem det_d4T36_sub_fin_four {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (q : ℤ) :
    Matrix.det !![q, 0, 0, ε; 0, q + ε, -ε, ε; -ε, ε, q, ε; -ε, 0, 0, q + ε] =
      (q ^ 2 + ε * q + 1) ^ 2 := by
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  rcases hε with rfl | rfl <;> ring

theorem d4T36M_sub_det_ne_zero {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ} (hq : 1 ≤ q) :
    ((q : ℤ) • (1 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) -
      d4T36M ε).det ≠ 0 := by
  have hM : ((q : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) -
      ε • !![0, 0, 0, -1; 0, -1, 1, -1; 1, -1, 0, -1; 1, 0, 0, -1]) =
      !![(q : ℤ), 0, 0, ε; 0, q + ε, -ε, ε; -ε, ε, q, ε; -ε, 0, 0, q + ε] := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp
  have hdet : ((q : ℤ) • (1 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) -
      d4T36M ε).det = ((q : ℤ) ^ 2 + ε * q + 1) ^ 2 := by
    rw [← det_d4T36_sub_fin_four hε (q : ℤ), ← hM]
    rfl
  have hpos : (0 : ℤ) < (q : ℤ) ^ 2 + ε * q + 1 := by
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
    rcases hε with rfl | rfl <;> nlinarith
  rw [hdet]
  exact pow_ne_zero 2 hpos.ne'

end Determinant

section Torus

theorem d4_torus_adjust {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hM : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x =
      M *ᵥ permLattice TwistTag.D4.perm.symm x)
    (hdet : ((q : ℤ) • (1 : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) -
      M).det ≠ 0)
    {t : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L) :
    ∃ s ∈ torusGroup TwistTag.D4.tag L, n * twistHom TwistTag.D4 L Fr s * n⁻¹ = s * t := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set ρ := TwistTag.D4.perm
  set v := weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩
  obtain ⟨a, ha⟩ := exists_tuple_of_char_eq ((q : ℤ) • 1 - M) M hdet b
  have hkey : ∀ m, rootChar a m ^ q = rootChar a (M *ᵥ m) * rootChar b (M *ᵥ m) := fun m => by
    have h := ha m
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, rootChar_sub, rootChar_zsmul,
      zpow_natCast, mul_inv_eq_iff_eq_mul] at h
    rw [h, mul_comm]
  set c := canonicalRep (coxeterSystem TwistTag.D4.tag) L v with hc
  have hh : c * n⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    canonicalRep_mul_inv_mem_torusGroup hn v rfl
  have hh' : n * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    simpa using inv_mem hh
  set a' : Fin TwistTag.D4.tag.rank → Lˣ := fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))
    with ha'
  have e1 : twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag a' := twistHom_rootDiagUnit_eq a
  have e2 : n * rootDiagUnit TwistTag.D4.tag a' * n⁻¹ =
      rootDiagUnit TwistTag.D4.tag (weylTuple v a') := by
    have hcy : c * rootDiagUnit TwistTag.D4.tag a' * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
      rw [hc, canonicalRep_conj_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    have hcomm := torusGroup_comm hh' hcy
    calc n * rootDiagUnit TwistTag.D4.tag a' * n⁻¹ =
          (n * c⁻¹) * (c * rootDiagUnit TwistTag.D4.tag a' * c⁻¹) * (n * c⁻¹)⁻¹ := by group
      _ = c * rootDiagUnit TwistTag.D4.tag a' * c⁻¹ := by rw [hcomm, mul_inv_cancel_right]
      _ = _ := canonicalRep_conj_rootDiagUnit v a'
  refine ⟨rootDiagUnit TwistTag.D4.tag a, rootDiagUnit_mem_torusGroup a, ?_⟩
  rw [e1, e2, ← rootDiagUnit_mul]
  congr 1
  have hchar : ∀ u, rootChar (weylTuple v a') u = rootChar (a * b) u := fun u => by
    obtain ⟨x, rfl⟩ : ∃ x, u = v • x := ⟨v⁻¹ • u, (smul_inv_smul v u).symm⟩
    rw [rootChar_weylTuple, inv_smul_smul, CTTorus.rootChar_mul, ha',
      rootChar_map_tuple Fr (fun i => a (ρ.symm i)) x, ← rootChar_permLattice a ρ.symm x,
      CTTorus.map_units_eq_pow hFr, hM x]
    exact hkey _
  funext i
  have := hchar (Pi.single i 1)
  rwa [CTTorus.rootChar_single, CTTorus.rootChar_single] at this

end Torus

end CFSG.GH74.GLS.Stage2.Bender.Thm1
