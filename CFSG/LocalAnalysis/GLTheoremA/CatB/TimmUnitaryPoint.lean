module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU7
public import CFSG.ClassicalGroups.Unitary.InvolutionTransvection
public import CFSG.LinearAlgebra.UnipotentRadical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremA.S8

theorem SUid_unitaryInvolution_eq (n : ℕ) :
    CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution F4 2 1) n = StatedSU n 2 F4 := by
  simpa using CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
    (F := F4) (p := 2) (f := 1) card_F4' n

private theorem mem_SUid_unitaryInvolution {w : ℕ} {t : GL (Fin (w + 2)) F4}
    (htS : t ∈ StatedSU (w + 2) 2 F4) :
    t ∈ CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution F4 2 1) (w + 2) := by
  rw [SUid_unitaryInvolution_eq]
  exact htS

private theorem unitaryInvolution_e0_apply (w : ℕ) (i : Fin (w + 2)) :
    CFSG.LieType.BorelTits.unitaryInvolution F4 2 1 (e0 w i) = e0 w i := by
  rcases e0_cases i with h | h <;> rw [h]
  · simp
  · rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num

private theorem herm_e0_eq_dot (w : ℕ) (x : Fin (w + 2) → F4) :
    CFSG.ClassicalGroups.Unitary.herm
      (CFSG.LieType.BorelTits.unitaryInvolution F4 2 1) (e0 w) x = e0 w ⬝ᵥ x := by
  unfold CFSG.ClassicalGroups.Unitary.herm dotProduct
  exact Finset.sum_congr rfl fun i _ => by rw [unitaryInvolution_e0_apply]

private theorem herm_e0_e0 (w : ℕ) :
    CFSG.ClassicalGroups.Unitary.herm
      (CFSG.LieType.BorelTits.unitaryInvolution F4 2 1) (e0 w) (e0 w) = 0 := by
  rw [herm_e0_eq_dot, e0_dot]

theorem tau0GL_mulVec (w : ℕ) (x : Fin (w + 2) → F4) :
    ((tau0GL w : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ x =
      x + CFSG.ClassicalGroups.Unitary.herm
        (CFSG.LieType.BorelTits.unitaryInvolution F4 2 1) (e0 w) x • e0 w := by
  rw [tau0GL_val, tau0, Matrix.add_mulVec, Matrix.one_mulVec, herm_e0_eq_dot,
    Matrix.vecMulVec_mulVec]
  simp

theorem exists_involution_lift {w : ℕ} {z : ↥(timmesfeldPSU (w + 2))} (hz : z * z = 1) :
    ∃ t : GL (Fin (w + 2)) F4, t ∈ StatedSU (w + 2) 2 F4 ∧
      (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) * t = 1 ∧
      ProjGenLinGroup.mk t = (z : ProjGenLinGroup (Fin (w + 2)) F4) := by
  obtain ⟨s, hsS, hsz⟩ := exists_mk_of_mem_timmesfeldPSU
    (z : ProjGenLinGroup (Fin (w + 2)) F4) z.2
  have hss1 : ProjGenLinGroup.mk (s * s) = 1 := by
    rw [map_mul, hsz]
    simpa using congrArg Subtype.val hz
  have hsc : s * s ∈ StatedScalars (Fin (w + 2)) F4 := mk_eq_one_mem_scalars _ hss1
  obtain ⟨c, hc⟩ := (mem_statedScalars_iff (w := w + 2) (s * s)).1 hsc
  have hSdet : ((s : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4).det = 1 :=
    ((mem_statedSU_iff s).1 hsS).1
  have hSU : (((s : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4).map fr)ᵀ *
      ((s : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) = 1 :=
    ((mem_statedSU_iff s).1 hsS).2
  have hSS : ((s : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *
      ((s : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) = (c : F4) • 1 := by
    simpa only [Units.val_mul] using hc
  have hcub : (c : F4) ^ 3 = 1 := pow_three_of_ne_zero c.ne_zero
  have hcn : (c : F4) ^ (w + 2) = 1 := by
    have hdet_ss : (((s * s : GL (Fin (w + 2)) F4) :
        Matrix (Fin (w + 2)) (Fin (w + 2)) F4)).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, hSdet, one_mul]
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet_ss
    exact hdet_ss
  have htval : (((Matrix.GeneralLinearGroup.scalar (Fin (w + 2)) c * s :
      GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4)) =
      (c : F4) • ((s : GL (Fin (w + 2)) F4) :
        Matrix (Fin (w + 2)) (Fin (w + 2)) F4) := by
    rw [Units.val_mul, scalar_val, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin (w + 2)) c * s, ?_, ?_, ?_⟩
  · rw [mem_statedSU_iff]
    constructor
    · rw [htval, Matrix.det_smul, Fintype.card_fin, hcn, hSdet, mul_one]
    · unfold IsUnitaryMat
      rw [htval]
      rw [Matrix.map_smul' fr (c : F4)
        ((s : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4)
        (fun a b => map_mul fr a b)]
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hSU]
      have hfr : fr (c : F4) * (c : F4) = 1 := by
        rw [fr_apply]
        calc (c : F4) ^ 2 * (c : F4) = (c : F4) ^ 3 := by ring
          _ = 1 := hcub
      rw [hfr, one_smul]
  · rw [htval, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hSS, smul_smul]
    have hc3 : (c : F4) * (c : F4) * (c : F4) = 1 := by
      calc (c : F4) * (c : F4) * (c : F4) = (c : F4) ^ 3 := by ring
        _ = 1 := hcub
    rw [hc3, one_smul]
  · rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul, hsz]

theorem exists_central_involution_of_isExtraSpec2 {w : ℕ}
    {M : Subgroup ↥(timmesfeldPSU (w + 2))} (hM : IsMaxTwoLocalSubgroup M)
    (hext : IsExtraSpec2 (pCoreOf 2 M)) :
    ∃ z : ↥(timmesfeldPSU (w + 2)), z ≠ 1 ∧ z * z = 1 ∧
      M = centralizer ({z} : Set ↥(timmesfeldPSU (w + 2))) := by
  have hc : Nat.card (center ↥(pCoreOf 2 M)) = 2 := hext.2.2.2
  have hPM : pCoreOf 2 M ≤ M := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hPn : ∀ m ∈ M, ∀ x ∈ pCoreOf 2 M, m * x * m⁻¹ ∈ pCoreOf 2 M := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(⟨m, hm⟩ : M) * y * (⟨m, hm⟩ : M)⁻¹,
      (inferInstance : (CFSG.pCore 2 ↥M).Normal).conj_mem y hy _, ?_⟩
    simp
  obtain ⟨z, hzP, hz1, hz2, hzc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Timm.exists_central_involution hc
  refine ⟨z, hz1, ?_,
    CFSG.LocalAnalysis.GLTheoremA.Timm.eq_centralizer_of_isMaxTwoLocal hM hPM hPn hc hzP hz1 hz2 hzc⟩
  have h := pow_orderOf_eq_one z
  rwa [hz2, pow_two] at h

theorem commute_of_mem_normalizer {w : ℕ} {M : Subgroup ↥(timmesfeldPSU (w + 2))}
    (hM : IsMaxTwoLocalSubgroup M) {t : GL (Fin (w + 2)) F4}
    (htS : t ∈ StatedSU (w + 2) 2 F4)
    (htt : (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) * t = 1)
    (hMt : M = centralizer {(⟨ProjGenLinGroup.mk t,
      mk_mem_timmesfeldPSU t htS⟩ : ↥(timmesfeldPSU (w + 2)))})
    (ht1 : ProjGenLinGroup.mk t ≠ 1) {R : Subgroup (GL (Fin (w + 2)) F4)}
    (hR : IsPGroup 2 R) (htR : t ∈ R)
    (hC : ∀ g ∈ StatedSU (w + 2) 2 F4, g * t = t * g →
      g ∈ normalizer (R : Set (GL (Fin (w + 2)) F4)))
    {g : GL (Fin (w + 2)) F4} (hgS : g ∈ StatedSU (w + 2) 2 F4)
    (hgR : g ∈ normalizer (R : Set (GL (Fin (w + 2)) F4))) : g * t = t * g := by
  let S : Subgroup (GL (Fin (w + 2)) F4) := StatedSU (w + 2) 2 F4
  let z : ↥(timmesfeldPSU (w + 2)) :=
    ⟨ProjGenLinGroup.mk t, mk_mem_timmesfeldPSU t htS⟩
  let K : Subgroup (ProjGenLinGroup (Fin (w + 2)) F4) := (R ⊓ S).map ProjGenLinGroup.mk
  let X : Subgroup ↥(timmesfeldPSU (w + 2)) := K.subgroupOf (timmesfeldPSU (w + 2))
  have hKle : K ≤ timmesfeldPSU (w + 2) := by
    rw [CFSG.GF2Type.timmesfeldPSU_eq_map]
    exact Subgroup.map_mono inf_le_right
  have hzK : (z : ProjGenLinGroup (Fin (w + 2)) F4) ∈ K := by
    refine Subgroup.mem_map.2 ⟨t, ⟨htR, htS⟩, rfl⟩
  have hzX : z ∈ X := by
    rw [Subgroup.mem_subgroupOf]
    exact hzK
  have hz1' : z ≠ 1 := by
    intro h
    exact ht1 (congrArg Subtype.val h)
  have hXne : X ≠ ⊥ := by
    intro h
    have hzbot : z ∈ (⊥ : Subgroup ↥(timmesfeldPSU (w + 2))) := h ▸ hzX
    rw [Subgroup.mem_bot] at hzbot
    exact hz1' hzbot
  have hRS : IsPGroup 2 ↥(R ⊓ S) := hR.to_inf_left
  have hKp : IsPGroup 2 ↥K := IsPGroup.map hRS ProjGenLinGroup.mk
  have hXp : IsPGroup 2 ↥X :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKle).symm
  have h2loc : IsTwoLocal (Subgroup.normalizer (X : Set ↥(timmesfeldPSU (w + 2)))) :=
    ⟨X, hXne, hXp, rfl⟩
  have hle : M ≤ Subgroup.normalizer (X : Set ↥(timmesfeldPSU (w + 2))) := by
    intro m hm
    obtain ⟨g', hg'S, hg'm⟩ := exists_mk_of_mem_timmesfeldPSU
      (m : ProjGenLinGroup (Fin (w + 2)) F4) m.2
    have hmC : m ∈ Subgroup.centralizer ({z} : Set ↥(timmesfeldPSU (w + 2))) := hMt ▸ hm
    have hcomm : ProjGenLinGroup.mk g' * ProjGenLinGroup.mk t =
        ProjGenLinGroup.mk t * ProjGenLinGroup.mk g' := by
      have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hmC)
      simp only [Subgroup.coe_mul] at h
      simpa [z, ← hg'm] using h
    have hg't : g' * t = t * g' := (mk_commute_iff g' t htt).1 hcomm.symm
    have hg'N : g' ∈ Subgroup.normalizer (R : Set (GL (Fin (w + 2)) F4)) := hC g' hg'S hg't
    have hg'NS : g' ∈ Subgroup.normalizer (S : Set (GL (Fin (w + 2)) F4)) :=
      S.le_normalizer hg'S
    have hg'NI : g' ∈ Subgroup.normalizer
        ((R ⊓ S : Subgroup (GL (Fin (w + 2)) F4)) : Set _) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := R) (K := S) ⟨hg'N, hg'NS⟩
    have hmK : (m : ProjGenLinGroup (Fin (w + 2)) F4) ∈
        Subgroup.normalizer (K : Set (ProjGenLinGroup (Fin (w + 2)) F4)) := by
      have h := Subgroup.le_normalizer_map (H := R ⊓ S) ProjGenLinGroup.mk
        (Subgroup.mem_map_of_mem ProjGenLinGroup.mk hg'NI)
      rwa [hg'm] at h
    have hmKsub : m ∈ (Subgroup.normalizer (K : Set _)).subgroupOf
        (timmesfeldPSU (w + 2)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hmK
    rwa [Subgroup.subgroupOf_normalizer_eq hKle] at hmKsub
  have hNX : Subgroup.normalizer (X : Set ↥(timmesfeldPSU (w + 2))) = M :=
    hM.2 _ h2loc hle
  have hmem : (⟨ProjGenLinGroup.mk g,
      mk_mem_timmesfeldPSU g hgS⟩ : ↥(timmesfeldPSU (w + 2))) ∈
      Subgroup.normalizer (X : Set _) := by
    have hgNI : g ∈ Subgroup.normalizer
        ((R ⊓ S : Subgroup (GL (Fin (w + 2)) F4)) : Set _) :=
      Subgroup.inf_normalizer_le_normalizer_inf (H := R) (K := S) ⟨hgR, S.le_normalizer hgS⟩
    have h1 : (⟨ProjGenLinGroup.mk g,
        mk_mem_timmesfeldPSU g hgS⟩ : ↥(timmesfeldPSU (w + 2))) ∈
        (Subgroup.normalizer (K : Set _)).subgroupOf (timmesfeldPSU (w + 2)) := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.le_normalizer_map (H := R ⊓ S) ProjGenLinGroup.mk
        (Subgroup.mem_map_of_mem ProjGenLinGroup.mk hgNI)
    rwa [Subgroup.subgroupOf_normalizer_eq hKle] at h1
  have hmemC : (⟨ProjGenLinGroup.mk g,
      mk_mem_timmesfeldPSU g hgS⟩ : ↥(timmesfeldPSU (w + 2))) ∈
      Subgroup.centralizer ({z} : Set ↥(timmesfeldPSU (w + 2))) := by
    rw [hNX] at hmem
    rwa [hMt] at hmem
  have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hmemC)
  simp only [Subgroup.coe_mul] at h
  exact (mk_commute_iff g t htt).1 (by simpa [z] using h.symm)

private noncomputable def rangeSubOne (w : ℕ) (t : GL (Fin (w + 2)) F4) :
    Submodule F4 (Fin (w + 2) → F4) :=
  LinearMap.range (Matrix.mulVecLin (((t : GL (Fin (w + 2)) F4) :
    Matrix (Fin (w + 2)) (Fin (w + 2)) F4) - 1))

private theorem mem_rangeSubOne_iff {w : ℕ} {t : GL (Fin (w + 2)) F4}
    {x : Fin (w + 2) → F4} :
    x ∈ rangeSubOne w t ↔
      ∃ y, (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ y - y = x := by
  simp only [rangeSubOne, LinearMap.mem_range, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

private theorem commute_of_mapsTo_range_sub_one {w : ℕ}
    {M : Subgroup ↥(timmesfeldPSU (w + 2))} (hM : IsMaxTwoLocalSubgroup M)
    {t : GL (Fin (w + 2)) F4} (htS : t ∈ StatedSU (w + 2) 2 F4)
    (htt : (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) * t = 1)
    (hMt : M = centralizer {(⟨ProjGenLinGroup.mk t, mk_mem_timmesfeldPSU t htS⟩ :
      ↥(timmesfeldPSU (w + 2)))})
    (ht1 : ProjGenLinGroup.mk t ≠ 1) {g : GL (Fin (w + 2)) F4}
    (hgS : g ∈ StatedSU (w + 2) 2 F4)
    (hgW : ∀ x ∈ rangeSubOne w t,
      (g : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ x ∈ rangeSubOne w t) :
    g * t = t * g := by
  let σ4 : F4 ≃+* F4 := CFSG.LieType.BorelTits.unitaryInvolution F4 2 1
  let t' : CFSG.LieType.Universal.Unitary.SUid σ4 (w + 2) :=
    ⟨t, mem_SUid_unitaryInvolution htS⟩
  have ht' : t' * t' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact Units.ext htt
  have hfix : ∀ y : Fin (w + 2) → F4,
      (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ
          ((t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ y - y) =
        (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ y - y := by
    intro y
    have h := CFSG.ClassicalGroups.Unitary.smul_sub_self_smul_sub_self
      (σ := σ4) (n := w + 2) (t := t') ht' y
    simp only [CFSG.ClassicalGroups.Unitary.smul_def] at h
    exact sub_eq_zero.mp (by simpa [t'] using h)
  let R : Subgroup (GL (Fin (w + 2)) F4) :=
    CFSG.LinearAlgebra.unipotentRadical (rangeSubOne w t)
  have htR : t ∈ R := by
    rw [CFSG.LinearAlgebra.mem_unipotentRadical_iff]
    constructor
    · intro x
      exact mem_rangeSubOne_iff.mpr ⟨x, rfl⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := mem_rangeSubOne_iff.mp hx
      exact hfix y
  have hC : ∀ g ∈ StatedSU (w + 2) 2 F4, g * t = t * g →
      g ∈ Subgroup.normalizer (R : Set (GL (Fin (w + 2)) F4)) := by
    intro g hgS hgt
    apply CFSG.LinearAlgebra.mem_normalizer_unipotentRadical
    intro x hx
    obtain ⟨y, hy⟩ := mem_rangeSubOne_iff.mp hx
    refine mem_rangeSubOne_iff.mpr ⟨g *ᵥ y, ?_⟩
    rw [← hy]
    have hgtM : ((g * t : GL (Fin (w + 2)) F4) :
        Matrix (Fin (w + 2)) (Fin (w + 2)) F4) =
        ((t * g : GL (Fin (w + 2)) F4) :
          Matrix (Fin (w + 2)) (Fin (w + 2)) F4) :=
      congrArg (fun x : GL (Fin (w + 2)) F4 =>
        (x : Matrix (Fin (w + 2)) (Fin (w + 2)) F4)) hgt
    rw [Matrix.mulVec_sub]
    congr 1
    calc (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ
          ((g : GL (Fin (w + 2)) F4) *ᵥ y) =
        ((t * g : GL (Fin (w + 2)) F4) : Matrix _ _ F4) *ᵥ y := by
          rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      _ = ((g * t : GL (Fin (w + 2)) F4) : Matrix _ _ F4) *ᵥ y := by rw [hgtM]
      _ = (g : GL (Fin (w + 2)) F4) *ᵥ
          ((t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ y) := by
          rw [Units.val_mul, Matrix.mulVec_mulVec]
  have hgN : g ∈ Subgroup.normalizer (R : Set (GL (Fin (w + 2)) F4)) :=
    CFSG.LinearAlgebra.mem_normalizer_unipotentRadical hgW
  exact commute_of_mem_normalizer hM htS htt hMt ht1
    (CFSG.LinearAlgebra.isPGroup_unipotentRadical (rangeSubOne w t)) htR hC hgS hgN

private theorem exists_conj_eq_tau0GL {w : ℕ} {t : GL (Fin (w + 2)) F4}
    (htS : t ∈ StatedSU (w + 2) 2 F4)
    (htt : (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) * t = 1)
    (ht1 : ProjGenLinGroup.mk t ≠ 1)
    (hcomm : ∀ g ∈ StatedSU (w + 2) 2 F4,
      (∀ x ∈ rangeSubOne w t,
        (g : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ x ∈ rangeSubOne w t) →
        g * t = t * g)
    (hw : 12 ≤ w) :
    ∃ g₀ : GL (Fin (w + 2)) F4, g₀ ∈ StatedSU (w + 2) 2 F4 ∧
      g₀ * t * g₀⁻¹ = tau0GL w := by
  let σ4 : F4 ≃+* F4 := CFSG.LieType.BorelTits.unitaryInvolution F4 2 1
  have hσ4 : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ4 :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution card_F4'
  let t' : CFSG.LieType.Universal.Unitary.SUid σ4 (w + 2) :=
    ⟨t, mem_SUid_unitaryInvolution htS⟩
  have ht' : t' * t' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact Units.ext htt
  have ht'1 : t' ≠ 1 := by
    intro h
    have h' : t = 1 := by simpa [t'] using congrArg Subtype.val h
    exact ht1 (by rw [h', map_one])
  have hW' : ∀ g : CFSG.LieType.Universal.Unitary.SUid σ4 (w + 2),
      (∀ x : Fin (w + 2) → F4, ∃ y : Fin (w + 2) → F4,
        g • (t' • x - x) = t' • y - y) → g * t' = t' * g := by
    intro g himg
    have hgS : (g : GL (Fin (w + 2)) F4) ∈ StatedSU (w + 2) 2 F4 := by
      rw [← SUid_unitaryInvolution_eq]
      exact g.2
    have hmap : ∀ x ∈ rangeSubOne w t,
        ((g : GL (Fin (w + 2)) F4) : Matrix _ _ F4) *ᵥ x ∈ rangeSubOne w t := by
      intro x hx
      obtain ⟨z, hz⟩ := mem_rangeSubOne_iff.mp hx
      obtain ⟨y, hy⟩ := himg z
      have hy' : ((g : GL (Fin (w + 2)) F4) :
          Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ
          ((t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ z - z) =
          (t : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ y - y := by
        simpa only [CFSG.ClassicalGroups.Unitary.smul_def] using hy
      exact mem_rangeSubOne_iff.mpr ⟨y, by rw [← hz, ← hy']⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simpa [t'] using hcomm (g : GL (Fin (w + 2)) F4) hgS hmap
  obtain ⟨g₀, hg₀⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_conj_smul_eq_of_forall_commute
      (σ := σ4) (n := w + 2) hσ4 (by omega) ht' ht'1 hW'
      (e := e0 w) (by
        intro h
        have h0 := congrFun h (Fin.natAdd w 0)
        rw [e0_natAdd_zero] at h0
        exact one_ne_zero h0)
      (herm_e0_e0 w)
  have hg0S : (g₀ : GL (Fin (w + 2)) F4) ∈ StatedSU (w + 2) 2 F4 := by
    rw [← SUid_unitaryInvolution_eq]
    exact g₀.2
  refine ⟨g₀, hg0S, ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have h1 := hg₀ (Pi.single j 1)
  rw [CFSG.ClassicalGroups.Unitary.smul_def] at h1
  have h2 := tau0GL_mulVec w (Pi.single j 1)
  have h1' : ((↑(g₀ * t' * g₀⁻¹) : GL (Fin (w + 2)) F4) :
      Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ Pi.single j 1 =
      ((tau0GL w : GL (Fin (w + 2)) F4) :
        Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ Pi.single j 1 :=
    h1.trans h2.symm
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, t'] using h1'

theorem unitaryPointIdentification : UnitaryPointIdentification := by
  intro w hw M hM hext _hcard
  obtain ⟨z, hz1, hz2, hMz⟩ := exists_central_involution_of_isExtraSpec2 hM hext
  obtain ⟨t, htS, htt, hzt⟩ := exists_involution_lift hz2
  have htz : z = ⟨ProjGenLinGroup.mk t, mk_mem_timmesfeldPSU t htS⟩ := by
    ext
    exact hzt.symm
  have hMt : M = centralizer {(⟨ProjGenLinGroup.mk t,
      mk_mem_timmesfeldPSU t htS⟩ : ↥(timmesfeldPSU (w + 2)))} := by
    rw [hMz, htz]
  have ht1 : ProjGenLinGroup.mk t ≠ 1 := by
    intro h
    exact hz1 (by rw [htz]; exact Subtype.ext h)
  obtain ⟨g₀, hg0S, hmat⟩ := exists_conj_eq_tau0GL htS htt ht1
    (fun g hgS hgW => commute_of_mapsTo_range_sub_one hM htS htt hMt ht1 hgS hgW) hw
  let p : ↥(timmesfeldPSU (w + 2)) :=
    ⟨ProjGenLinGroup.mk (g₀ : GL (Fin (w + 2)) F4), mk_mem_timmesfeldPSU _ hg0S⟩
  have hzval : (↑z : ProjGenLinGroup (Fin (w + 2)) F4) = ProjGenLinGroup.mk t := by
    rw [htz]
  have hpz : p * z * p⁻¹ = tP w := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzval]
    show ProjGenLinGroup.mk (g₀ : GL (Fin (w + 2)) F4) * ProjGenLinGroup.mk t *
        (ProjGenLinGroup.mk (g₀ : GL (Fin (w + 2)) F4))⁻¹ =
      ProjGenLinGroup.mk (tau0GL w)
    rw [← map_mul, ← map_inv, ← map_mul, hmat]
  have hzconj : z = p⁻¹ * tP w * p := by
    calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
      _ = p⁻¹ * tP w * p := by rw [hpz]
  have hMmap : M = (centralizer ({tP w} : Set ↥(timmesfeldPSU (w + 2)))).map
      (MulAut.conj p⁻¹).toMonoidHom := by
    rw [hMz, hzconj, CFSG.centralizer_singleton_map, MulAut.conj_apply, inv_inv]
  exact ⟨(MulEquiv.subgroupCongr hMmap).trans
    (MulEquiv.subgroupMap (MulAut.conj p⁻¹) _).symm⟩

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint
