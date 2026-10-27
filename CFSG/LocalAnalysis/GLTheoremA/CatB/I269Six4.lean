module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.Fischer

@[expose] def Vs (i1 i2 : Fin 6) : Submodule F4 (Fin 6 → F4) :=
  LinearMap.ker ((LinearMap.proj i1 : (Fin 6 → F4) →ₗ[F4] F4).prod
    (LinearMap.proj i2 : (Fin 6 → F4) →ₗ[F4] F4))

theorem mem_Vs {i1 i2 : Fin 6} {v : Fin 6 → F4} : v ∈ Vs i1 i2 ↔ v i1 = 0 ∧ v i2 = 0 := by
  simp [Vs, LinearMap.mem_ker, Prod.ext_iff]

theorem finrank_Vs {i1 i2 : Fin 6} (hne : i1 ≠ i2) : Module.finrank F4 (Vs i1 i2) = 4 := by
  set f := (LinearMap.proj i1 : (Fin 6 → F4) →ₗ[F4] F4).prod
    (LinearMap.proj i2 : (Fin 6 → F4) →ₗ[F4] F4) with hf
  have hsurj : Function.Surjective (f : (Fin 6 → F4) →ₗ[F4] F4 × F4) := by
    intro p
    refine ⟨Pi.single i1 p.1 + Pi.single i2 p.2, ?_⟩
    simp [hf, Pi.single_apply, hne, hne.symm]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_self] at h
  simp only [Module.finrank_fin_fun] at h
  change Module.finrank F4 (LinearMap.ker f) = 4
  omega

theorem finrank_ker_proj_le (i : Fin 6) :
    Module.finrank F4 (LinearMap.ker (LinearMap.proj i : (Fin 6 → F4) →ₗ[F4] F4)) ≤ 5 := by
  have hsurj : Function.Surjective (LinearMap.proj i : (Fin 6 → F4) →ₗ[F4] F4) := by
    intro t
    exact ⟨Pi.single i t, by simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj i : (Fin 6 → F4) →ₗ[F4] F4)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at h
  simp only [Module.finrank_fin_fun] at h
  omega

@[expose] def Ks (Y : Matrix (Fin 6) (Fin 6) F4) (i1 i2 : Fin 6) (c : F4) :
    Submodule F4 (Fin 6 → F4) :=
  LinearMap.ker (Matrix.mulVecLin (Y - Matrix.scalar (Fin 6) c)) ⊓ Vs i1 i2

theorem mem_Ks {Y : Matrix (Fin 6) (Fin 6) F4} {i1 i2 : Fin 6} {c : F4} {v : Fin 6 → F4} :
    v ∈ Ks Y i1 i2 c ↔ v i1 = 0 ∧ v i2 = 0 ∧ Y.mulVec v = c • v := by
  simp only [Ks, Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply, mem_Vs]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    ext i
    have hi := congrFun h i
    simp [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hi
  · rintro ⟨h1, h2, h⟩
    refine ⟨?_, h1, h2⟩
    ext i
    simp [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal, h]

theorem finrank_Ks_add_le {Y : Matrix (Fin 6) (Fin 6) F4} {i1 i2 : Fin 6} (hne : i1 ≠ i2)
    {c c' : F4} (hcc : c ≠ c') :
    Module.finrank F4 (Ks Y i1 i2 c) + Module.finrank F4 (Ks Y i1 i2 c') ≤ 4 := by
  have hinf : Ks Y i1 i2 c ⊓ Ks Y i1 i2 c' = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨-, -, e1⟩ := mem_Ks.1 hv1
    obtain ⟨-, -, e2⟩ := mem_Ks.1 hv2
    have : (c - c') • v = 0 := by
      rw [sub_smul, ← e1, ← e2, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hcc
    · exact (Submodule.mem_bot F4).2 h
  have hsup : Ks Y i1 i2 c ⊔ Ks Y i1 i2 c' ≤ Vs i1 i2 := by
    refine sup_le ?_ ?_
    · intro v hv; exact (mem_Ks.1 hv).1 |> fun h => mem_Vs.2 ⟨h, (mem_Ks.1 hv).2.1⟩
    · intro v hv; exact (mem_Ks.1 hv).1 |> fun h => mem_Vs.2 ⟨h, (mem_Ks.1 hv).2.1⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Ks Y i1 i2 c) (Ks Y i1 i2 c')
  rw [hinf, finrank_bot] at h1
  have h2 := Submodule.finrank_mono hsup
  rw [finrank_Vs hne] at h2
  omega

theorem exists_two_small (Y : Matrix (Fin 6) (Fin 6) F4) {i1 i2 : Fin 6} (hne : i1 ≠ i2) :
    ∃ x1 x2 : F4, x1 ≠ x2 ∧ x1 ≠ 0 ∧ x2 ≠ 0 ∧ Module.finrank F4 (Ks Y i1 i2 x1) ≤ 2 ∧
      Module.finrank F4 (Ks Y i1 i2 x2) ≤ 2 := by
  have hcard : ((Finset.univ : Finset F4).erase 0).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, F4.card]
  obtain ⟨x, y, z, hxy, hxz, hyz, hZ⟩ := Finset.card_eq_three.1 hcard
  have hx : x ∈ (Finset.univ : Finset F4).erase 0 := by rw [hZ]; simp
  have hy : y ∈ (Finset.univ : Finset F4).erase 0 := by rw [hZ]; simp
  have hz : z ∈ (Finset.univ : Finset F4).erase 0 := by rw [hZ]; simp
  have nz : ∀ w, w ∈ (Finset.univ : Finset F4).erase 0 → w ≠ 0 := fun w hw =>
    (Finset.mem_erase.1 hw).1
  have pxy := finrank_Ks_add_le (Y := Y) hne hxy
  have pxz := finrank_Ks_add_le (Y := Y) hne hxz
  have pyz := finrank_Ks_add_le (Y := Y) hne hyz
  by_cases ax : Module.finrank F4 (Ks Y i1 i2 x) ≤ 2 <;>
    by_cases ay : Module.finrank F4 (Ks Y i1 i2 y) ≤ 2 <;>
    by_cases az : Module.finrank F4 (Ks Y i1 i2 z) ≤ 2
  · exact ⟨x, y, hxy, nz x hx, nz y hy, ax, ay⟩
  · exact ⟨x, y, hxy, nz x hx, nz y hy, ax, ay⟩
  · exact ⟨x, z, hxz, nz x hx, nz z hz, ax, az⟩
  · omega
  · exact ⟨y, z, hyz, nz y hy, nz z hz, ay, az⟩
  · omega
  · omega
  · omega

theorem finrank_ker_le_three {M Y : Matrix (Fin 6) (Fin 6) F4} {i1 i2 : Fin 6} (hne : i1 ≠ i2)
    {x1 x2 : F4} (hx1 : x1 ≠ x2) (r1 : ∀ v : Fin 6 → F4, M.mulVec v i1 = x1 * v i1)
    (r2 : ∀ v : Fin 6 → F4, M.mulVec v i2 = x2 * v i2)
    (hMY : ∀ v : Fin 6 → F4, v i1 = 0 → v i2 = 0 → M.mulVec v = Y.mulVec v)
    (hns : ∀ c : F4, ∃ i j : Fin 6, i ≠ i1 ∧ i ≠ i2 ∧ j ≠ i1 ∧ j ≠ i2 ∧
      Y i j ≠ if i = j then c else 0)
    {c : F4} (hc1 : c ≠ x1) (hc2 : c ≠ x2) :
    Module.finrank F4 (LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) c))) ≤ 3 := by
  set K := LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) c)) with hKdef
  have hent : ∀ v ∈ K, ∀ i, M.mulVec v i = c * v i := by
    intro v hv i
    have h0 : (M - Matrix.scalar (Fin 6) c).mulVec v = 0 := hv
    have hi := congrFun h0 i
    simp [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal] at hi
    linear_combination hi
  have hKV : K ≤ Vs i1 i2 := by
    intro v hv
    rw [mem_Vs]
    have e1 := hent v hv i1
    rw [r1 v] at e1
    have e2 := hent v hv i2
    rw [r2 v] at e2
    constructor
    · have : (x1 - c) * v i1 = 0 := by linear_combination e1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h).symm hc1
      · exact h
    · have : (x2 - c) * v i2 = 0 := by linear_combination e2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h).symm hc2
      · exact h
  have hKne : K ≠ Vs i1 i2 := by
    intro heq
    obtain ⟨i, j, hi1, hi2, hj1, hj2, hYij⟩ := hns c
    have hv : (Pi.single j (1 : F4) : Fin 6 → F4) ∈ Vs i1 i2 := by
      rw [mem_Vs]
      simp [Pi.single_apply, Ne.symm hj1, Ne.symm hj2]
    have hvK : (Pi.single j (1 : F4) : Fin 6 → F4) ∈ K := heq ▸ hv
    have e := hent _ hvK i
    rw [hMY _ (by simp [Pi.single_apply, Ne.symm hj1]) (by simp [Pi.single_apply, Ne.symm hj2])]
      at e
    simp [Matrix.mulVec_single, Pi.single_apply] at e
    apply hYij
    split_ifs at e ⊢ <;> simp_all
  have hlt : K < Vs i1 i2 := lt_of_le_of_ne hKV hKne
  have := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_Vs hne] at this
  omega

theorem finrank_ker_le_three_x1 {M Y : Matrix (Fin 6) (Fin 6) F4} {i1 i2 : Fin 6} (hne : i1 ≠ i2)
    {x1 x2 : F4} (hx1 : x1 ≠ x2) (r2 : ∀ v : Fin 6 → F4, M.mulVec v i2 = x2 * v i2)
    (r1 : ∀ v : Fin 6 → F4, M.mulVec v i1 = x1 * v i1)
    (hMY : ∀ v : Fin 6 → F4, v i1 = 0 → v i2 = 0 → M.mulVec v = Y.mulVec v)
    (hsmall : Module.finrank F4 (Ks Y i1 i2 x1) ≤ 2) :
    Module.finrank F4 (LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) x1))) ≤ 3 := by
  set K := LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) x1)) with hKdef
  have hent : ∀ v ∈ K, ∀ i, M.mulVec v i = x1 * v i := by
    intro v hv i
    have h0 : (M - Matrix.scalar (Fin 6) x1).mulVec v = 0 := hv
    have hi := congrFun h0 i
    simp [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal] at hi
    linear_combination hi
  have hK2 : K ≤ LinearMap.ker (LinearMap.proj i2 : (Fin 6 → F4) →ₗ[F4] F4) := by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    have e1 := hent v hv i2
    rw [r2 v] at e1
    have : (x2 - x1) * v i2 = 0 := by linear_combination e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hx1.symm
    · exact h
  have hsup : K ⊔ Vs i1 i2 ≤ LinearMap.ker (LinearMap.proj i2 : (Fin 6 → F4) →ₗ[F4] F4) := by
    refine sup_le hK2 ?_
    intro v hv
    rw [mem_Vs] at hv
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    exact hv.2
  have hinf : K ⊓ Vs i1 i2 ≤ Ks Y i1 i2 x1 := by
    intro v hv
    obtain ⟨hvK, hvV⟩ := Submodule.mem_inf.1 hv
    rw [mem_Vs] at hvV
    rw [mem_Ks]
    refine ⟨hvV.1, hvV.2, ?_⟩
    ext i
    have e := hent v hvK i
    rw [hMY v hvV.1 hvV.2] at e
    simp only [Pi.smul_apply, smul_eq_mul]
    exact e
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq K (Vs i1 i2)
  have h2 := Submodule.finrank_mono hsup
  have h3 := Submodule.finrank_mono hinf
  have h4 := finrank_ker_proj_le i2
  rw [finrank_Vs hne] at h1
  omega

theorem three_le_rank {M : Matrix (Fin 6) (Fin 6) F4} {c : F4}
    (hK : Module.finrank F4 (LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) c))) ≤ 3) :
    3 ≤ (M - Matrix.scalar (Fin 6) c).rank := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) c))
  simp only [Module.finrank_fin_fun] at h
  show 3 ≤ Module.finrank F4 (LinearMap.range (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) c)))
  omega


theorem finrank_ker_le_three_x2 {M Y : Matrix (Fin 6) (Fin 6) F4} {i1 i2 : Fin 6} (hne : i1 ≠ i2)
    {x1 x2 : F4} (hx1 : x1 ≠ x2) (r1 : ∀ v : Fin 6 → F4, M.mulVec v i1 = x1 * v i1)
    (r2 : ∀ v : Fin 6 → F4, M.mulVec v i2 = x2 * v i2)
    (hMY : ∀ v : Fin 6 → F4, v i1 = 0 → v i2 = 0 → M.mulVec v = Y.mulVec v)
    (hsmall : Module.finrank F4 (Ks Y i1 i2 x2) ≤ 2) :
    Module.finrank F4 (LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) x2))) ≤ 3 := by
  set K := LinearMap.ker (Matrix.mulVecLin (M - Matrix.scalar (Fin 6) x2)) with hKdef
  have hent : ∀ v ∈ K, ∀ i, M.mulVec v i = x2 * v i := by
    intro v hv i
    have h0 : (M - Matrix.scalar (Fin 6) x2).mulVec v = 0 := hv
    have hi := congrFun h0 i
    simp [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal] at hi
    linear_combination hi
  have hK1 : K ≤ LinearMap.ker (LinearMap.proj i1 : (Fin 6 → F4) →ₗ[F4] F4) := by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    have e1 := hent v hv i1
    rw [r1 v] at e1
    have : (x1 - x2) * v i1 = 0 := by linear_combination e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hx1
    · exact h
  have hsup : K ⊔ Vs i1 i2 ≤ LinearMap.ker (LinearMap.proj i1 : (Fin 6 → F4) →ₗ[F4] F4) := by
    refine sup_le hK1 ?_
    intro v hv
    rw [mem_Vs] at hv
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    exact hv.1
  have hinf : K ⊓ Vs i1 i2 ≤ Ks Y i1 i2 x2 := by
    intro v hv
    obtain ⟨hvK, hvV⟩ := Submodule.mem_inf.1 hv
    rw [mem_Vs] at hvV
    rw [mem_Ks]
    refine ⟨hvV.1, hvV.2, ?_⟩
    ext i
    have e := hent v hvK i
    rw [hMY v hvV.1 hvV.2] at e
    simp only [Pi.smul_apply, smul_eq_mul]
    exact e
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq K (Vs i1 i2)
  have h2 := Submodule.finrank_mono hsup
  have h3 := Submodule.finrank_mono hinf
  have h4 := finrank_ker_proj_le i1
  rw [finrank_Vs hne] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.I269Six

end
