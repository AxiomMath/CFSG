module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Dickson
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson

variable {F : Type} [Field F]

theorem mem_normalizer_zpowers_of_conj_mem {G : Type} [Group G] [Finite G] {c g : G}
    (h : g * c * g⁻¹ ∈ Subgroup.zpowers c) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact h
  have hcard : Nat.card (Subgroup.zpowers c) ≤
      Nat.card ((Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

@[expose] def cSL : Matrix.SpecialLinearGroup (Fin 2) F := ⟨cMat, cMat_det⟩

theorem toGL_cSL : Matrix.SpecialLinearGroup.toGL (cSL (F := F)) = cGL := Units.ext rfl

theorem cSL_pow_three : (cSL (F := F)) ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_pow, toGL_cSL, cGL_pow_three, map_one]

theorem toGL_mem_Nt_of_mk_mem [Finite F] {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hx : QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x ∈
      Subgroup.normalizer ((Subgroup.zpowers
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) cSL) :
          Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F))) :
    Matrix.SpecialLinearGroup.toGL x ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have h1 := (Subgroup.mem_normalizer_iff.mp hx (π cSL)).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul] at hk
  have hz : (cSL ^ k)⁻¹ * (x * cSL * x⁻¹) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq).mp hk
  set z := (cSL ^ k)⁻¹ * (x * cSL * x⁻¹) with hzdef
  have hzc : ∀ y, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  have hxc : x * cSL * x⁻¹ = cSL ^ k * z := by rw [hzdef]; group
  have hz3 : z ^ 3 = 1 := by
    have h3 : (x * cSL * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, cSL_pow_three, mul_one, mul_inv_cancel]
    rw [hxc] at h3
    have hcomm : Commute (cSL ^ k) z := (hzc (cSL ^ k)).symm
    have hck : (cSL (F := F) ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        cSL_pow_three, _root_.one_zpow]
    rw [hcomm.mul_pow, hck, one_mul] at h3
    exact h3
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [Fintype.card_fin] at hr
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, Matrix.SpecialLinearGroup.coe_one]
    rw [show (Matrix.scalar (Fin 2) r) ^ 2 = Matrix.scalar (Fin 2) (r ^ 2) by
      rw [pow_two, pow_two, ← (Matrix.scalar (Fin 2)).map_mul], hr, map_one]
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2, inv_one, one_mul]
  rw [hz1, mul_one] at hxc
  apply mem_normalizer_zpowers_of_conj_mem
  refine ⟨k, ?_⟩
  simp only
  rw [← toGL_cSL, ← map_zpow, ← hxc, map_mul, map_mul, map_inv]

theorem toGL_center_mem_Nt {z : Matrix.SpecialLinearGroup (Fin 2) F}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    Matrix.SpecialLinearGroup.toGL z ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
  apply mem_Nt_of_comm
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F)) (Subgroup.mem_center_iff.mp hz cSL)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  exact this.symm

theorem gl2NonsplitMax [Finite F] (hq : Nat.card F % 3 = 2)
    (h5 : 5 ≤ Nat.card F) : GL2NonsplitMax F := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hroot := OrdinaryProofs.L3Leaves.sq_add_self_add_one_ne_zero hq
  have h3 : (3 : F) ≠ 0 := by
    have h := hroot 1
    norm_num at h
    exact h
  obtain ⟨S, hScyc, hScard, hNS, ⟨w, hwN, -, -, hwinv, -, hRN⟩, -, hconj⟩ :=
    h84_nonsplit_torus_data (F := F) hF
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have htr : (Matrix.trace (cSL (F := F) : Matrix (Fin 2) (Fin 2) F)) ^ 2 ≠ (4 : F) := by
    simp only [cSL, cMat, Matrix.trace_fin_two_of]
    intro h
    apply h3
    linear_combination -h
  have hev : ¬ ∃ (μ : F) (v : Fin 2 → F), v ≠ 0 ∧
      (cSL (F := F) : Matrix (Fin 2) (Fin 2) F).mulVec v = μ • v := by
    rintro ⟨μ, v, hv, hcv⟩
    exact mulVec_ne_smul hroot cMat_relation hv μ hcv
  obtain ⟨g, hg⟩ := hconj cSL htr hev
  obtain ⟨t, htS, htc⟩ := Subgroup.mem_map.mp hg
  have hc1 : π cSL ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have := congrFun (congrFun hr 0) 0
    have h' := congrFun (congrFun hr 0) 1
    simp [cSL, cMat] at this h'
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hc1
    rw [← htc]
    simp
  have hR : Subgroup.zpowers t ≤ S := (Subgroup.zpowers_le).mpr htS
  have hRb : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    exact ht1 ((Subgroup.zpowers_eq_bot).mp h)
  have hNRS : Subgroup.normalizer ((Subgroup.zpowers t : Subgroup (PSL2MatrixGroup F)) :
      Set (PSL2MatrixGroup F)) = Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) := by
    rw [hRN _ hR hRb, hRN S le_rfl (fun h => hRb (eq_bot_iff.mpr (h ▸ hR)))]
  have hct : π cSL = (MulAut.conj g) t := htc.symm
  have hNc : Subgroup.normalizer ((Subgroup.zpowers (π cSL) : Subgroup (PSL2MatrixGroup F)) :
      Set (PSL2MatrixGroup F)) =
      (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))).map (MulAut.conj g).toMonoidHom := by
    rw [← hNRS, Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
    rw [hct]
    rfl
  intro Y hY
  set Y₁ := Y.comap (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →*
    GL (Fin 2) F)
  set H := Y₁.map π
  have hNcH : Subgroup.normalizer ((Subgroup.zpowers (π cSL) : Subgroup (PSL2MatrixGroup F)) :
      Set (PSL2MatrixGroup F)) ≤ H := by
    intro xbar hxbar
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ xbar
    exact ⟨x, hY (toGL_mem_Nt_of_mk_mem hxbar), rfl⟩
  have hNSH : Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ≤
      H.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro y hy
    refine ⟨(MulAut.conj g) y, hNcH ?_, ?_⟩
    · rw [hNc]
      exact ⟨y, hy, rfl⟩
    · simp [MulAut.conj_apply]
      group
  have hcases := normalizer_nonsplit_maximal hF hq h5 hScyc hScard hNS hwN hwinv hNSH
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≤ Y₁ :=
    fun z hz => hY (toGL_center_mem_Nt hz)
  rcases hcases with h | h
  ·
    left
    have hH : H = Subgroup.normalizer ((Subgroup.zpowers (π cSL) :
        Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F)) := by
      have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
      rw [Subgroup.map_map] at this
      rw [hNc, ← this]
      have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ := by
        ext y
        simp
      rw [this, Subgroup.map_id]
    refine le_antisymm ?_ hY
    intro y hy
    have hdet : (y : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [← isUnit_iff_ne_zero]
      exact Matrix.isUnit_det_of_invertible _
    obtain ⟨s, hs, hsdet⟩ := exists_pairMat_det_eq h3 hdet
    set P := pairGL hroot cMat_relation hs
    have hPN : P ∈ (Nt : Subgroup (GL (Fin 2) F)) :=
      mem_Nt_of_comm (pairMat_mul_cMat cMat_relation s)
    have hdet1 : ((y * P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have h1 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
          (P : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      have h2 : (P : Matrix (Fin 2) (Fin 2) F).det = (y : Matrix (Fin 2) (Fin 2) F).det := hsdet
      rw [Units.val_mul, Matrix.det_mul, ← h2, mul_comm]
      exact h1
    set X : Matrix.SpecialLinearGroup (Fin 2) F := ⟨(y * P⁻¹ : GL (Fin 2) F), hdet1⟩
    have hXY : X ∈ Y₁ := by
      show Matrix.SpecialLinearGroup.toGL X ∈ Y
      have : Matrix.SpecialLinearGroup.toGL X = y * P⁻¹ := Units.ext rfl
      rw [this]
      exact Y.mul_mem hy (Y.inv_mem (hY hPN))
    have hXH : π X ∈ H := ⟨X, hXY, rfl⟩
    rw [hH] at hXH
    have hXN := toGL_mem_Nt_of_mk_mem hXH
    have : Matrix.SpecialLinearGroup.toGL X = y * P⁻¹ := Units.ext rfl
    rw [this] at hXN
    have := (Nt : Subgroup (GL (Fin 2) F)).mul_mem hXN hPN
    rwa [inv_mul_cancel_right] at this
  ·
    right
    have hH : H = ⊤ := by
      have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
      rw [Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at this
      rw [← this]
      have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ := by
        ext y
        simp
      rw [this, Subgroup.map_id]
    rintro _ ⟨X, rfl⟩
    have hXH : π X ∈ H := by rw [hH]; exact Subgroup.mem_top _
    obtain ⟨X', hX'Y, hX'X⟩ := hXH
    have hz : X'⁻¹ * X ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      QuotientGroup.eq.mp hX'X
    have : X = X' * (X'⁻¹ * X) := by group
    rw [this, map_mul]
    exact Y.mul_mem hX'Y (hcenter hz)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
