module

public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Roots

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_zpow_eq_of_isAlgClosed {d : ℤ} (hd : d ≠ 0) (c : Lˣ) : ∃ x : Lˣ, x ^ d = c := by
  have hroot : ∀ (n : ℕ), n ≠ 0 → ∀ c : Lˣ, ∃ x : Lˣ, x ^ n = c := fun n hn c => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (c : L) (Nat.pos_of_ne_zero hn)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hy
      exact c.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · obtain ⟨x, hx⟩ := hroot n (by rintro rfl; exact hd rfl) c
    exact ⟨x, by rw [zpow_natCast, hx]⟩
  · obtain ⟨x, hx⟩ := hroot n (by rintro rfl; exact hd rfl) c⁻¹
    exact ⟨x, by rw [zpow_neg, zpow_natCast, hx, inv_inv]⟩

theorem exists_rootChar_rows_eq {τ : Tag} {N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hN : N.det ≠ 0) (γ : Fin τ.rank → Lˣ) :
    ∃ a : Fin τ.rank → Lˣ, ∀ i, FourGroupChevalley.rootChar a (N i) = γ i := by
  classical
  choose e he using fun i => exists_zpow_eq_of_isAlgClosed (L := L) hN (γ i)
  refine ⟨fun j => FourGroupChevalley.rootChar e (N.adjugate j), fun i => ?_⟩
  have hrow : (N * N.adjugate) i = ∑ j, N i j • N.adjugate j := by
    funext k
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  have h1 : FourGroupChevalley.rootChar (fun j => FourGroupChevalley.rootChar e (N.adjugate j))
      (N i) = FourGroupChevalley.rootChar e ((N * N.adjugate) i) := by
    rw [hrow, rootChar_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [rootChar_zsmul]
  rw [h1, Matrix.mul_adjugate, show ((N.det • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) i) =
    N.det • (Pi.single i 1 : Fin τ.rank → ℤ) by
      funext k
      simp [Matrix.one_apply, Pi.single_apply, eq_comm], rootChar_zsmul, CTTorus.rootChar_single,
    he i]

end Roots

section TorusLang

variable {τ : Tag} {L : Type} [Field L]

theorem det_ne_zero_of_mapMatrix_eq_one {r q : ℕ} (hq : 2 ≤ q) {N : Matrix (Fin r) (Fin r) ℤ}
    (hN : (Int.castRingHom (ZMod q)).mapMatrix N = 1) : N.det ≠ 0 := by
  have : Fact (1 < q) := ⟨by omega⟩
  intro h0
  have h1 := (Int.castRingHom (ZMod q)).map_det N
  rw [hN, Matrix.det_one, h0, map_zero] at h1
  exact zero_ne_one h1

theorem rootChar_units_map_pow {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (a : Fin τ.rank → Lˣ) (u : Fin τ.rank → ℤ) :
    FourGroupChevalley.rootChar (fun j => Units.map Fr.toMonoidHom (a j)) u =
      FourGroupChevalley.rootChar a ((q : ℤ) • u) := by
  simp only [FourGroupChevalley.rootChar, Pi.smul_apply, smul_eq_mul]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : Units.map Fr.toMonoidHom (a j) = a j ^ q :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  rw [h, ← zpow_natCast, ← zpow_mul]

theorem exists_torus_lang [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup τ) {k : ModGL τ L} (hk : k ∈ torusGroup τ L) :
    ∃ h ∈ torusGroup τ L, h * (canonicalRep (coxeterSystem τ) L w *
      Units.map (entrywiseHom Fr) h * (canonicalRep (coxeterSystem τ) L w)⁻¹)⁻¹ = k := by
  classical
  obtain ⟨γ, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hk
  set M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    LinearMap.toMatrix' (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w⁻¹) with hM
  have hMw : ∀ u : Fin τ.rank → ℤ, w⁻¹ • u = M *ᵥ u := fun u => by
    rw [smul_def, hM, LinearMap.toMatrix'_mulVec]
  set N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    Matrix.of fun i => (Pi.single i 1 : Fin τ.rank → ℤ) - (q : ℤ) • (M *ᵥ Pi.single i 1) with hN
  have hNdet : N.det ≠ 0 := by
    refine det_ne_zero_of_mapMatrix_eq_one hq ?_
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hN, Matrix.of_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      sub_zero, Matrix.one_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  obtain ⟨a, ha⟩ := exists_rootChar_rows_eq hNdet γ
  refine ⟨rootDiagUnit τ a, rootDiagUnit_mem_torusGroup a, ?_⟩
  rw [units_map_entrywiseHom_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  change rootDiagUnitHom τ L a * (rootDiagUnitHom τ L _)⁻¹ = rootDiagUnitHom τ L γ
  rw [← map_inv, ← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, Pi.inv_apply, ← ha i]
  simp only [weylTuple]
  rw [hMw, rootChar_units_map_pow hFr, ← CTTorus.rootChar_single a i]
  change _ = FourGroupChevalley.rootChar a (Pi.single i 1 - (q : ℤ) • (M *ᵥ Pi.single i 1))
  rw [rootChar_sub]

end TorusLang

section Conj

variable {τ : Tag} {L : Type} [Field L]

theorem canonicalRep_inv_conj_mem_torusGroup [IsAlgClosed L] (v : WeylGroup τ) {k : ModGL τ L}
    (hk : k ∈ torusGroup τ L) :
    (canonicalRep (coxeterSystem τ) L v)⁻¹ * k * canonicalRep (coxeterSystem τ) L v ∈
      torusGroup τ L := by
  obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hk
  have h1 := canonicalRep_conj_rootDiagUnit (K := L) v (weylTuple v⁻¹ c)
  have h2 : weylTuple v (weylTuple v⁻¹ c) = c := by
    funext i
    simp only [weylTuple]
    rw [rootChar_weylTuple, inv_inv, smul_inv_smul, CTTorus.rootChar_single]
  rw [h2] at h1
  change (canonicalRep (coxeterSystem τ) L v)⁻¹ * rootDiagUnit τ c *
    canonicalRep (coxeterSystem τ) L v ∈ torusGroup τ L
  rw [← h1]
  rw [show (canonicalRep (coxeterSystem τ) L v)⁻¹ * (canonicalRep (coxeterSystem τ) L v *
      rootDiagUnit τ (weylTuple v⁻¹ c) * (canonicalRep (coxeterSystem τ) L v)⁻¹) *
      canonicalRep (coxeterSystem τ) L v = rootDiagUnit τ (weylTuple v⁻¹ c) by group]
  exact rootDiagUnit_mem_torusGroup _

theorem canonicalRep_inv_mul_conj_mem [IsAlgClosed L] (v w : WeylGroup τ) :
    ∃ k₀ ∈ torusGroup τ L, (canonicalRep (coxeterSystem τ) L v)⁻¹ *
      canonicalRep (coxeterSystem τ) L (v * w * v⁻¹) * canonicalRep (coxeterSystem τ) L v =
        k₀ * canonicalRep (coxeterSystem τ) L w := by
  obtain ⟨k₁, hk₁, h₁⟩ := canonicalRep_mul_mem (τ := τ) (R := L) v w
  obtain ⟨k₂, hk₂, h₂⟩ := canonicalRep_mul_mem (τ := τ) (R := L) (v * w * v⁻¹) v
  rw [show v * w * v⁻¹ * v = v * w by group] at h₂
  refine ⟨(canonicalRep (coxeterSystem τ) L v)⁻¹ * (k₂ * k₁⁻¹) * canonicalRep (coxeterSystem τ) L v,
    canonicalRep_inv_conj_mem_torusGroup v (mul_mem hk₂ (inv_mem hk₁)), ?_⟩
  have h₃ : canonicalRep (coxeterSystem τ) L (v * w) =
      k₁⁻¹ * (canonicalRep (coxeterSystem τ) L v * canonicalRep (coxeterSystem τ) L w) := by
    rw [h₁]
    group
  rw [mul_assoc, h₂, h₃]
  group

end Conj

end CFSG.HardMathSupport.Timmesfeld.CrossChar
