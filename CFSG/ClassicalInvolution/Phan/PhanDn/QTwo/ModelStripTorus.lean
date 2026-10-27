module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyGood
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Phan.PhanDn.ChamberMoves
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeGeom

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open Matrix QuadraticMap

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

private theorem diagHom_conj_stdConj (m : ℕ)
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1))
    (C : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        (stdConj E m).toMonoidHom C *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ =
      (stdConj E m).toMonoidHom
        ((stdConj E m).toMonoidHom (diagHom F (unitaryInvolution K 2 1) (m + 1) d) * C *
          ((stdConj E m).toMonoidHom
            (diagHom F (unitaryInvolution K 2 1) (m + 1) d))⁻¹) := by
  rw [map_mul, map_mul, map_inv]
  change diagHom F (unitaryInvolution K 2 1) (m + 1) d * stdConj E m C *
      (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ =
    stdConj E m (stdConj E m (diagHom F (unitaryInvolution K 2 1) (m + 1) d)) *
      stdConj E m C *
      (stdConj E m (stdConj E m
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)))⁻¹
  rw [stdConj_stdConj E m]

private theorem diagHom_conj_stdChainIota_mem (hK : Nat.card K = 4) {m : ℕ}
    (k : Fin m)
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) (A : Su K 2 1 2) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        stdChainIota (F := F) (f := 1) m k A *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      (stdChainIota (F := F) (f := 1) m k).range := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  refine ⟨conjDiag (K := K) (p := 2) (f := 1) hK'
    (fun x : Fin 2 => d (blockIdx k.val (by omega) x)) A, ?_⟩
  rw [stdChainIota, MonoidHom.comp_apply]
  exact (diagHom_mul_suEndN_blockEmb_mul_inv (F := F) (K := K) (f := 1) hK'
    (n := m + 1) (k := 2) (i := k.val) (by omega) d A).symm

private theorem diagHom_conj_stdChainTheta_mem (hK : Nat.card K = 4) {m : ℕ}
    (k : Fin m) (hk : k.val + 1 < m)
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) (A : Su K 2 1 3) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        stdChainTheta (F := F) (f := 1) m k hk A *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      (stdChainTheta (F := F) (f := 1) m k hk).range := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  refine ⟨conjDiag (K := K) (p := 2) (f := 1) hK'
    (fun x : Fin 3 => d (blockIdx k.val (by omega) x)) A, ?_⟩
  rw [stdChainTheta, MonoidHom.comp_apply]
  exact (diagHom_mul_suEndN_blockEmb_mul_inv (F := F) (K := K) (f := 1) hK'
    (n := m + 1) (k := 3) (i := k.val) (by omega) d A).symm

private theorem diagHom_conj_stdForkIota_mem (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m)
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) (A : Su K 2 1 2) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        stdForkIota E m hm A *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      (stdForkIota E m hm).range := by
  obtain ⟨A', hA'⟩ := diagHom_conj_stdChainIota_mem (F := F) hK
    (⟨m - 1, by omega⟩ : Fin m)
    (Function.update d (Fin.last m) ((d (Fin.last m))⁻¹)) A
  refine ⟨A', ?_⟩
  change (stdConj E m).toMonoidHom
      (stdChainIota (F := F) (f := 1) m ⟨m - 1, by omega⟩ A') =
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
      (stdConj E m).toMonoidHom
        (stdChainIota (F := F) (f := 1) m ⟨m - 1, by omega⟩ A) *
      (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹
  rw [diagHom_conj_stdConj E m d
      (stdChainIota (F := F) (f := 1) m ⟨m - 1, by omega⟩ A),
    stdConj_diagHom E m d, hA']

private theorem diagHom_conj_stdForkTheta_mem (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m)
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) (A : Su K 2 1 3) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        stdForkTheta E m hm A *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      (stdForkTheta E m hm).range := by
  obtain ⟨A', hA'⟩ := diagHom_conj_stdChainTheta_mem (F := F) hK
    (⟨m - 2, by omega⟩ : Fin m) (by rw [Fin.val_mk]; omega)
    (Function.update d (Fin.last m) ((d (Fin.last m))⁻¹)) A
  refine ⟨A', ?_⟩
  change (stdConj E m).toMonoidHom
      (stdChainTheta (F := F) (f := 1) m ⟨m - 2, by omega⟩
        (by rw [Fin.val_mk]; omega) A') =
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
      (stdConj E m).toMonoidHom
        (stdChainTheta (F := F) (f := 1) m ⟨m - 2, by omega⟩
          (by rw [Fin.val_mk]; omega) A) *
      (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹
  rw [diagHom_conj_stdConj E m d
      (stdChainTheta (F := F) (f := 1) m ⟨m - 2, by omega⟩
        (by rw [Fin.val_mk]; omega) A),
    stdConj_diagHom E m d, hA']

private theorem comap_subtype_range_stdFamilyV_ι {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m + 1)) :
    (((stdFamilyV E m hm).ι j).range).comap
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      (qTwoStdIota E m hm j).range := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, Subtype.ext ?_⟩
    change ((qTwoStdIota E m hm j A : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = _
    rw [coe_qTwoStdIota]
    exact hA
  · rintro ⟨A, rfl⟩
    refine ⟨A, ?_⟩
    change ((stdFamilyV E m hm).ι j) A =
      ((qTwoStdIota E m hm j A : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    rw [coe_qTwoStdIota]

private theorem comap_subtype_range_stdFamilyV_θ_of_lt {m : ℕ} (hm : 3 ≤ m)
    {j k : Fin (m + 1)} (hjk : j < k) :
    (((stdFamilyV E m hm).θ j k).range).comap
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      (qTwoStdTheta E m hm j k).range := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, Subtype.ext ?_⟩
    change ((qTwoStdTheta E m hm j k A :
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = _
    rw [coe_qTwoStdTheta_of_lt E m hm hjk]
    exact hA
  · rintro ⟨A, rfl⟩
    refine ⟨A, ?_⟩
    change ((stdFamilyV E m hm).θ j k) A =
      ((qTwoStdTheta E m hm j k A : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    rw [coe_qTwoStdTheta_of_lt E m hm hjk]

private theorem comap_subtype_range_stdFamilyV_θ_of_gt {m : ℕ} (hm : 3 ≤ m)
    {j k : Fin (m + 1)} (hkj : k < j) :
    (((stdFamilyV E m hm).θ k j).range).comap
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) =
      (qTwoStdTheta E m hm j k).range := by
  have hrange : (qTwoStdTheta E m hm j k).range = (qTwoStdTheta E m hm k j).range := by
    rw [qTwoStdTheta_of_gt E m hm hkj, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (revSU3 K 2 1).surjective, Subgroup.map_top]
  rw [hrange]
  exact comap_subtype_range_stdFamilyV_θ_of_lt (E := E) (m := m) hm hkj

private theorem diagHom_conj_stdFamilyV_ι_mem (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m) (j : Fin (m + 1))
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) (A : Su K 2 1 2) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        (stdFamilyV E m hm).ι j A *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      ((stdFamilyV E m hm).ι j).range := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨k, rfl⟩ | rfl
  · rw [stdFamilyV_ι_castSucc]
    exact diagHom_conj_stdChainIota_mem (F := F) hK k d A
  · rw [stdFamilyV_ι_last]
    exact diagHom_conj_stdForkIota_mem E hK hm d A

private theorem diagHom_conj_stdFamilyV_θ_mem (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m) (j k : Fin (m + 1))
    (d : Fin (m + 1) → normOne (unitaryInvolution K 2 1)) (A : Su K 2 1 3) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        (stdFamilyV E m hm).θ j k A *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      ((stdFamilyV E m hm).θ j k).range := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) k with ⟨k', rfl⟩ | rfl
  · rw [stdFamilyV_θ, stdTheta_castSucc]
    by_cases h : j.val + 1 = k'.val
    · have hk' : j.val + 1 < m := h.symm ▸ k'.isLt
      have hj' : j.val < m := Nat.lt_of_succ_lt hk'
      rw [stdThetaAt, dif_pos h]
      exact diagHom_conj_stdChainTheta_mem (F := F) hK
        (⟨j.val, hj'⟩ : Fin m) hk' d A
    · rw [stdThetaAt, dif_neg h]
      refine ⟨1, ?_⟩
      simp
  · rw [stdFamilyV_θ, stdTheta_last]
    exact diagHom_conj_stdForkTheta_mem E hK hm d A

private theorem qTwoTor_le_normalizer_node (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    qTwoTor E m hm i ≤ Subgroup.normalizer
      (((qTwoStdFamily E hK m hm).ι j).range :
        Set (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
  rw [Subgroup.le_normalizer_iff]
  intro t ht x hx
  have htD : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
    rw [← map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact Subgroup.mem_map_of_mem
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
      (Subgroup.mem_iSup_of_mem i ht)
  obtain ⟨d, hd⟩ := htD
  obtain ⟨A, rfl⟩ := hx
  have hxO : ((qTwoStdIota E m hm j) A :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      ((stdFamilyV E m hm).ι j).range := by
    refine ⟨A, ?_⟩
    change ((stdFamilyV E m hm).ι j) A =
      ((qTwoStdIota E m hm j A :
        CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    rw [coe_qTwoStdIota]
  have hmemO : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
        ((qTwoStdIota E m hm j) A :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
        (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹ ∈
      ((stdFamilyV E m hm).ι j).range := by
    rw [← hd]
    change diagHom F (unitaryInvolution K 2 1) (m + 1) d *
        ((qTwoStdIota E m hm j) A :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
        (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
      ((stdFamilyV E m hm).ι j).range
    rw [coe_qTwoStdIota]
    exact diagHom_conj_stdFamilyV_ι_mem E hK hm j d A
  have hmemΩ : t * (qTwoStdIota E m hm j) A * t⁻¹ ∈
      (((stdFamilyV E m hm).ι j).range).comap
        (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
    rw [Subgroup.mem_comap]
    simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] using hmemO
  rwa [comap_subtype_range_stdFamilyV_ι E hm j] at hmemΩ

private theorem qTwoTor_le_normalizer_edge (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m) (i j k : Fin (m + 1))
    (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3) :
    qTwoTor E m hm i ≤ Subgroup.normalizer
      (((qTwoStdFamily E hK m hm).θ j k).range :
        Set (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
  have hne : j ≠ k := by
    rintro rfl
    rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl] at h3
    omega
  rw [Subgroup.le_normalizer_iff]
  intro t ht x hx
  have htD : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
    rw [← map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact Subgroup.mem_map_of_mem
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
      (Subgroup.mem_iSup_of_mem i ht)
  obtain ⟨d, hd⟩ := htD
  obtain ⟨A, rfl⟩ := hx
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hmemO : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          ((qTwoStdTheta E m hm j k) A :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹ ∈
        ((stdFamilyV E m hm).θ j k).range := by
      rw [← hd]
      change diagHom F (unitaryInvolution K 2 1) (m + 1) d *
          ((qTwoStdTheta E m hm j k) A :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
        ((stdFamilyV E m hm).θ j k).range
      rw [coe_qTwoStdTheta_of_lt E m hm hjk]
      exact diagHom_conj_stdFamilyV_θ_mem E hK hm j k d A
    have hmemΩ : t * (qTwoStdTheta E m hm j k) A * t⁻¹ ∈
        (((stdFamilyV E m hm).θ j k).range).comap
          (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
      rw [Subgroup.mem_comap]
      simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] using hmemO
    rwa [comap_subtype_range_stdFamilyV_θ_of_lt E hm hjk] at hmemΩ
  · have hmemO : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          ((qTwoStdTheta E m hm j k) A :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))⁻¹ ∈
        ((stdFamilyV E m hm).θ k j).range := by
      rw [← hd]
      change diagHom F (unitaryInvolution K 2 1) (m + 1) d *
          ((qTwoStdTheta E m hm j k) A :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
          (diagHom F (unitaryInvolution K 2 1) (m + 1) d)⁻¹ ∈
        ((stdFamilyV E m hm).θ k j).range
      rw [qTwoStdTheta_of_gt E m hm hkj, MonoidHom.comp_apply,
        coe_qTwoStdTheta_of_lt E m hm hkj]
      exact diagHom_conj_stdFamilyV_θ_mem E hK hm k j d (revSU3 K 2 1 A)
    have hmemΩ : t * (qTwoStdTheta E m hm j k) A * t⁻¹ ∈
        (((stdFamilyV E m hm).θ k j).range).comap
          (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
      rw [Subgroup.mem_comap]
      simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] using hmemO
    rwa [comap_subtype_range_stdFamilyV_θ_of_gt E hm hkj] at hmemΩ

theorem qTwoTor_conj_mem_levi (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (C : Set (Fin (m + 1)))
    {t : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))}
    (ht : t ∈ ⨆ i, qTwoTor E m hm i)
    {l : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))}
    (hl : l ∈ (qTwoStdFamily E hK m hm).levi C) :
    t * l * t⁻¹ ∈ (qTwoStdFamily E hK m hm).levi C := by
  let S := qTwoStdFamily E hK m hm
  have hnode (j : Fin (m + 1)) :
      (⨆ i, qTwoTor E m hm i) ≤ Subgroup.normalizer ((S.ι j).range : Set _) :=
    iSup_le fun i => qTwoTor_le_normalizer_node E hK hm i j
  have hedge (j k : Fin (m + 1))
      (h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3) :
      (⨆ i, qTwoTor E m hm i) ≤ Subgroup.normalizer ((S.θ j k).range : Set _) :=
    iSup_le fun i => qTwoTor_le_normalizer_edge E hK hm i j k h3
  have hnodeSup : (⨆ i, qTwoTor E m hm i) ≤
      Subgroup.normalizer (↑(⨆ j ∈ C, (S.ι j).range) : Set _) :=
    CFSG.ClassicalInvolution.Phan.le_normalizer_iSup₂ (⨆ i, qTwoTor E m hm i)
      C (fun j => (S.ι j).range) hnode
  have hedgeSup : (⨆ i, qTwoTor E m hm i) ≤
      Subgroup.normalizer (↑(⨆ (j ∈ C) (k ∈ C) (_ : CFSG.StandardType.ggCoxeterMatrixD
        (m + 1) j k = 3), (S.θ j k).range) : Set _) := by
    refine CFSG.ClassicalInvolution.Phan.le_normalizer_iSup₂
      (⨆ i, qTwoTor E m hm i) C
      (fun j => ⨆ (k ∈ C) (_ : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3),
        (S.θ j k).range) (fun j => ?_)
    refine CFSG.ClassicalInvolution.Phan.le_normalizer_iSup₂
      (⨆ i, qTwoTor E m hm i) C
      (fun k => ⨆ (_ : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3),
        (S.θ j k).range) (fun k => ?_)
    refine CFSG.LieType.Steinberg.le_normalizer_iSup
      (A := ⨆ i, qTwoTor E m hm i)
      (B := fun _ : (CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3) =>
        (S.θ j k).range) ?_
    intro h
    exact hedge j k h
  have hT : (⨆ i, qTwoTor E m hm i) ≤ Subgroup.normalizer (S.levi C : Set _) := by
    rw [QTwoPhanFamily.levi]
    exact CFSG.LieType.Steinberg.le_normalizer_sup hnodeSup hedgeSup
  exact (Subgroup.le_normalizer_iff.mp hT) t ht l hl

theorem qTwoTor_le_levi (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (i : Fin (m + 1)) :
    qTwoTor E m hm i ≤ (qTwoStdFamily E hK m hm).levi {i} := by
  have hle : qTwoTor E m hm i ≤ ((qTwoStdFamily E hK m hm).ι i).range := by
    rintro x ⟨u, rfl⟩
    exact ⟨torusTwo (unitaryInvolution K 2 1) u, rfl⟩
  refine hle.trans ?_
  rw [QTwoPhanFamily.levi]
  refine le_sup_of_le_left ?_
  exact (le_iSup₂_of_le i (by simp) le_rfl : ((qTwoStdFamily E hK m hm).ι i).range ≤
    ⨆ j ∈ ({i} : Set (Fin (m + 1))), ((qTwoStdFamily E hK m hm).ι j).range)

theorem qTwoTor_iSup_commute (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {x y : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))}
    (hx : x ∈ ⨆ i, qTwoTor E m hm i) (hy : y ∈ ⨆ i, qTwoTor E m hm i) :
    x * y = y * x := by
  apply Subtype.ext
  have hx' : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
    rw [← map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact Subgroup.mem_map_of_mem
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) hx
  have hy' : (y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
    rw [← map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact Subgroup.mem_map_of_mem
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) hy
  obtain ⟨a, ha⟩ := hx'
  obtain ⟨b, hb⟩ := hy'
  change (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
      (y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
    (y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]

theorem qTwoTor_commute (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (i j : Fin (m + 1))
    {x y : CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))}
    (hx : x ∈ qTwoTor E m hm i) (hy : y ∈ qTwoTor E m hm j) : x * y = y * x :=
  qTwoTor_iSup_commute E hK m hm
    (Subgroup.mem_iSup_of_mem i hx) (Subgroup.mem_iSup_of_mem j hy)

theorem iSupIndep_qTwoTor (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    iSupIndep (qTwoTor E m hm) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hgood := (stdFamilyV_good E m hm hK').indep
  have hcomap := CFSG.RankThree.Classical.iSupIndep_comap_of_injective
    (f := Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (Subgroup.subtype_injective
      (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) hgood
  convert hcomap using 2 with i
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    change ((stdFamilyV E m hm).nodeTor i) u =
      ((qTwoStdIota E m hm i (torusTwo (unitaryInvolution K 2 1) u) :
        CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    rw [coe_qTwoStdIota]
    rfl
  · rintro ⟨u, hu⟩
    refine ⟨u, Subtype.ext ?_⟩
    change ((qTwoStdIota E m hm i (torusTwo (unitaryInvolution K 2 1) u) :
        CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = _
    rw [coe_qTwoStdIota]
    exact hu

theorem mem_iSup_qTwoTor_of_prod (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (C : Set (Fin (m + 1)))
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 1)}
    (hx : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F (unitaryInvolution K 2 1) (m + 1) t)
    (hpre : ∀ k : Fin (m + 1), k ∉ C → k.val + 2 ≤ m →
      ∏ c, (if c.val ≤ k.val then t c else 1) = 1)
    (htot : Fin.last m ∉ C → ∏ c, t c = 1)
    (htw : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C →
      ∏ c, Function.update t (Fin.last m) (t (Fin.last m))⁻¹ c = 1) :
    x ∈ ⨆ i ∈ C, qTwoTor E m hm i := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hA1 := diagHom_mem_iSup_nodeTor_of_prod (E := E) m hm hK' C t hpre htot htw
  let Ω := CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))
  have hmap_range (i : Fin (m + 1)) :
      (qTwoTor E m hm i).map (Subgroup.subtype Ω) =
        ((stdFamilyV E m hm).nodeTor i).range := by
    rw [qTwoTor, MonoidHom.map_range,
      CFSG.ClassicalInvolution.Phan.PhanE.PhanFamilyE.nodeTor]
    congr 1
  have hmap : (⨆ i ∈ C, qTwoTor E m hm i).map (Subgroup.subtype Ω) =
      ⨆ i ∈ C, ((stdFamilyV E m hm).nodeTor i).range := by
    rw [Subgroup.map_iSup]
    refine iSup_congr fun i => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun _ => hmap_range i
  have hxmem : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      ⨆ i ∈ C, ((stdFamilyV E m hm).nodeTor i).range := by
    rwa [hx]
  have hxmap : Subgroup.subtype Ω x ∈
      (⨆ i ∈ C, qTwoTor E m hm i).map (Subgroup.subtype Ω) := by
    rw [hmap]
    exact hxmem
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective Ω)).mp hxmap

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
