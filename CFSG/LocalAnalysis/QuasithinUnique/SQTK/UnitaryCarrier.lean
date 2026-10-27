module

public import CFSG.Adapters.TypeALinearCandidate
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryFixed
public import CFSG.StronglyEmbedded.Catalog.Basic

public section

namespace CFSG.QuasithinUnique.SQTK

open Matrix TauCeti CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank
open CFSG.BenderSuzuki.Catalog (galoisEmbedding exists_map_galoisEmbedding_eq)

noncomputable section

section Conjugation

variable {F : Type} [Field F] (σ : F ≃+* F) {n : ℕ}

theorem conjTr_isometry_conj_iff (Bm Bi S gm : Matrix (Fin n) (Fin n) F)
    (hBBi : Bm * Bi = 1) (hS : conjTr σ Bm * S * Bm = 1) :
    conjTr σ (Bi * gm * Bm) * (Bi * gm * Bm) = 1 ↔ conjTr σ gm * S * gm = S := by
  have h1 : conjTr σ Bi * conjTr σ Bm = 1 := by rw [← conjTr_mul, hBBi, conjTr_one]
  have hSeq : S = conjTr σ Bi * Bi :=
    calc S = (conjTr σ Bi * conjTr σ Bm) * S * (Bm * Bi) := by rw [h1, hBBi]; simp
      _ = conjTr σ Bi * (conjTr σ Bm * S * Bm) * Bi := by simp only [Matrix.mul_assoc]
      _ = conjTr σ Bi * Bi := by rw [hS, Matrix.mul_one]
  have hkey : conjTr σ (Bi * gm * Bm) * (Bi * gm * Bm) =
      conjTr σ Bm * (conjTr σ gm * S * gm) * Bm := by
    rw [conjTr_mul, conjTr_mul, hSeq]
    simp only [Matrix.mul_assoc]
  rw [hkey]
  constructor
  · intro h
    calc conjTr σ gm * S * gm
        = (conjTr σ Bi * conjTr σ Bm) * (conjTr σ gm * S * gm) * (Bm * Bi) := by
          rw [h1, hBBi]; simp
      _ = conjTr σ Bi * (conjTr σ Bm * (conjTr σ gm * S * gm) * Bm) * Bi := by
          simp only [Matrix.mul_assoc]
      _ = S := by rw [h, Matrix.mul_one, ← hSeq]
  · intro h
    rw [h, hS]

theorem conj_mem_SUid_iff_isometry (Q : Matrix (Fin n) (Fin n) F) (B g : GL (Fin n) F) (c : F)
    (hc : c ≠ 0)
    (hB : conjTr σ (B : Matrix (Fin n) (Fin n) F) * (c • Q) * (B : Matrix (Fin n) (Fin n) F) = 1) :
    B⁻¹ * g * B ∈ SUid σ n ↔
      (g : Matrix (Fin n) (Fin n) F).det = 1 ∧
        conjTr σ (g : Matrix (Fin n) (Fin n) F) * Q * (g : Matrix (Fin n) (Fin n) F) = Q := by
  have hBBi : (B : Matrix (Fin n) (Fin n) F) * ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdetconj : ((B⁻¹ * g * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      (g : Matrix (Fin n) (Fin n) F).det := by
    have h1 : ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det *
        (B : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← det_mul, hBiB, det_one]
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul]
    calc _ = (g : Matrix (Fin n) (Fin n) F).det *
          (((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det *
            (B : Matrix (Fin n) (Fin n) F).det) := by ring
      _ = _ := by rw [h1, mul_one]
  have hiso := conjTr_isometry_conj_iff σ (B : Matrix (Fin n) (Fin n) F)
    ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (c • Q)
    (g : Matrix (Fin n) (Fin n) F) hBBi hB
  rw [mem_SUid]
  constructor
  · rintro ⟨hdet, hiso'⟩
    refine ⟨hdetconj ▸ hdet, ?_⟩
    have h1 := hiso.1 (by rw [Units.val_mul, Units.val_mul] at hiso'; exact hiso')
    rw [Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ hc h1
  · rintro ⟨hdet, hiso'⟩
    refine ⟨hdetconj.trans hdet, ?_⟩
    rw [Units.val_mul, Units.val_mul]
    apply hiso.2
    rw [Matrix.mul_smul, Matrix.smul_mul, hiso']

end Conjugation

section Descent

variable (r p k : ℕ) [Fact p.Prime] (A : Type) [Field A] [IsAlgClosed A] [CharP A p]

abbrev glMapGF (n : ℕ) : GL (Fin n) (GaloisField p (2 * k)) →* GL (Fin n) A :=
  GeneralLinearGroup.map (galoisEmbedding p A (2 * k))

theorem glMapGF_injective (n : ℕ) : Function.Injective (glMapGF p k A n) := fun X Y h => by
  ext i j
  exact (galoisEmbedding p A (2 * k)).injective
    (congrArg (fun M : GL (Fin n) A => (M : Matrix (Fin n) (Fin n) A) i j) h)

def unitaryFixedGroup : Subgroup (GL (Fin (r + 1)) (GaloisField p (2 * k))) :=
  ((fixedSubgroup (unitarySteinberg r p k A)).map SpecialLinearGroup.toGL).comap
    (glMapGF p k A (r + 1))

variable {r p k A}

theorem mem_unitaryFixedGroup_iff (g : GL (Fin (r + 1)) (GaloisField p (2 * k))) :
    g ∈ unitaryFixedGroup r p k A ↔
      (g : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))).det = 1 ∧
        conjTr (unitaryInvolution (GaloisField p (2 * k)) p k)
            (g : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) *
          (typeAGraphConjugator r (GaloisField p (2 * k)) :
            Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) *
          (g : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) =
        (typeAGraphConjugator r (GaloisField p (2 * k)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) := by
  set ι := galoisEmbedding p A (2 * k) with hι
  set F := GaloisField p (2 * k)
  set σ := unitaryInvolution F p k with hσ
  have hQ : (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
      (typeAGraphConjugator r F : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map ι :=
    (congrArg (fun g : GL (Fin (r + 1)) A => (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A))
      (map_typeAGraphConjugator ι r)).symm
  have hfrob : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) F,
      ((M.map ι).map (· ^ p ^ k))ᵀ = (conjTr σ M).map ι := by
    intro M
    ext i j
    simp only [conjTr, transpose_apply, map_apply, hσ, unitaryInvolution_apply, map_pow]
  rw [unitaryFixedGroup, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    have hxm : (x : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
        (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map ι :=
      congrArg (fun M : GL (Fin (r + 1)) A => (M : Matrix (Fin (r + 1)) (Fin (r + 1)) A)) hxg
    refine ⟨?_, ?_⟩
    · have h1 : ι (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = 1 := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hxm]
        exact x.2
      exact ι.injective (by rw [h1, map_one])
    · have h := (mem_fixedSubgroup_unitarySteinberg_iff x).mp hx
      rw [hxm, hfrob, hQ, ← Matrix.map_mul, ← Matrix.map_mul] at h
      exact Matrix.map_injective ι.injective h
  · rintro ⟨hdet, hiso⟩
    have hdet' : ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map ι).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    let x : SpecialLinearGroup (Fin (r + 1)) A :=
      ⟨(g : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map ι, hdet'⟩
    refine ⟨x, (mem_fixedSubgroup_unitarySteinberg_iff x).mpr ?_, ?_⟩
    · show (((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map ι).map (· ^ p ^ k))ᵀ *
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F).map ι) =
        (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
      rw [hfrob, hQ, ← Matrix.map_mul, ← Matrix.map_mul, hiso]
    · ext i j
      rfl

theorem map_toGL_le_range (hk : k ≠ 0) :
    (fixedSubgroup (unitarySteinberg r p k A)).map SpecialLinearGroup.toGL ≤
      (glMapGF p k A (r + 1)).range := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨M, hM⟩ := exists_map_galoisEmbedding_eq (p := p) (K := A) (k := 2 * k) (by omega)
    (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) (entry_pow_eq_self hg)
  have hdet : M.det = 1 := by
    apply (galoisEmbedding p A (2 * k)).injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, g.2, map_one]
  refine ⟨SpecialLinearGroup.toGL ⟨M, hdet⟩, ?_⟩
  ext i j
  exact congrArg (fun N : Matrix (Fin (r + 1)) (Fin (r + 1)) A => N i j) hM

def fixedEquivUnitaryFixedGroup (hk : k ≠ 0) :
    ↥(fixedSubgroup (unitarySteinberg r p k A)) ≃* ↥(unitaryFixedGroup r p k A) :=
  ((fixedSubgroup (unitarySteinberg r p k A)).equivMapOfInjective _
      SpecialLinearGroup.toGL_injective).trans
    ((MulEquiv.subgroupCongr (by
        rw [unitaryFixedGroup, Subgroup.map_comap_eq,
          inf_eq_right.mpr (map_toGL_le_range (r := r) (p := p) (A := A) hk)])).trans
      ((unitaryFixedGroup r p k A).equivMapOfInjective _
        (glMapGF_injective p k A (r + 1))).symm)

theorem conj_mem_SUid_iff (B : GL (Fin (r + 1)) (GaloisField p (2 * k))) (c : GaloisField p (2 * k))
    (hc : c ≠ 0)
    (hB : conjTr (unitaryInvolution (GaloisField p (2 * k)) p k)
        (B : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) *
      (c • (typeAGraphConjugator r (GaloisField p (2 * k)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k)))) *
      (B : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) = 1)
    (g : GL (Fin (r + 1)) (GaloisField p (2 * k))) :
    B⁻¹ * g * B ∈ SUid (unitaryInvolution (GaloisField p (2 * k)) p k) (r + 1) ↔
      g ∈ unitaryFixedGroup r p k A :=
  (conj_mem_SUid_iff_isometry _ _ B g c hc hB).trans (mem_unitaryFixedGroup_iff g).symm

def unitaryFixedEquivSUid (B : GL (Fin (r + 1)) (GaloisField p (2 * k)))
    (c : GaloisField p (2 * k)) (hc : c ≠ 0)
    (hB : conjTr (unitaryInvolution (GaloisField p (2 * k)) p k)
        (B : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) *
      (c • (typeAGraphConjugator r (GaloisField p (2 * k)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k)))) *
      (B : Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField p (2 * k))) = 1) :
    ↥(unitaryFixedGroup r p k A) ≃*
      SUid (unitaryInvolution (GaloisField p (2 * k)) p k) (r + 1) where
  toFun g := ⟨B⁻¹ * (g : GL (Fin (r + 1)) (GaloisField p (2 * k))) * B,
    (conj_mem_SUid_iff B c hc hB _).2 g.2⟩
  invFun h := ⟨B * (h : GL (Fin (r + 1)) (GaloisField p (2 * k))) * B⁻¹,
    (conj_mem_SUid_iff B c hc hB _).1
      (by rw [show B⁻¹ * (B * (h : GL (Fin (r + 1)) (GaloisField p (2 * k))) * B⁻¹) * B = h by
            group]
          exact h.2)⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

def unitaryCandidateEquivStatedProj (hk : k ≠ 0) (hn : 3 ≤ r + 1)
    (hnq : (r + 1, p ^ k) ≠ (3, 2)) :
    FixedPointCandidate (unitarySteinberg r p k A) ≃*
      StatedProj (StatedSU (r + 1) (p ^ k) (GaloisField p (2 * k))) :=
  have hF : Nat.card (GaloisField p (2 * k)) = (p ^ k) ^ 2 := by
    rw [GaloisField.card p (2 * k) (by omega), pow_mul']
  have hB := exists_orthonormalConjugator (F := GaloisField p (2 * k)) (p := p) (k := k) hF r
  let e : ↥(fixedSubgroup (unitarySteinberg r p k A)) ≃*
      StatedSU (r + 1) (p ^ k) (GaloisField p (2 * k)) :=
    (fixedEquivUnitaryFixedGroup hk).trans
      ((unitaryFixedEquivSUid hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.1
          hB.choose_spec.choose_spec.2).trans
        (MulEquiv.subgroupCongr (SUid_eq_statedSU hF (r + 1))))
  have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hn hnq
  have hsimple := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
    (GaloisField p (2 * k)) p k hF (r + 1) hn hnq
  have hZ := (isQuasisimple_statedSU hperf hsimple).2
  letI := hperf
  (DerivedCentralQuotient.congr e).trans
    ((CFSG.ClassicalModels.derivedCentralQuotientEquivCenterQuotient _).trans
      (QuotientGroup.quotientMulEquivOfEq hZ))

end Descent

end

end CFSG.QuasithinUnique.SQTK
