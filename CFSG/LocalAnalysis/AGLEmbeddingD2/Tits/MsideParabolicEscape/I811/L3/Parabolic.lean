module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Mat2
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F]

@[expose] noncomputable def cGL : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero cMat (by rw [cMat_det]; exact one_ne_zero)

theorem coe_cGL : ((cGL : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = cMat := rfl

abbrev Nt : Subgroup (GL (Fin 2) F) :=
  Subgroup.normalizer ((Subgroup.zpowers (cGL (F := F)) : Subgroup (GL (Fin 2) F)) :
    Set (GL (Fin 2) F))

noncomputable abbrev A0 : Subgroup (SL3 F) := Subgroup.zpowers (lev (cGL (F := F)))

@[expose] def GL2NonsplitMax (F : Type) [Field F] : Prop :=
  ∀ Y : Subgroup (GL (Fin 2) F), Nt ≤ Y →
    Y = Nt ∨ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≤ Y

theorem lev_mem_normalizer_A0 {X : GL (Fin 2) F} (hX : X ∈ (Nt : Subgroup (GL (Fin 2) F))) :
    lev X ∈ Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) := by
  have h : (Subgroup.zpowers (cGL (F := F))).map lev = A0 := MonoidHom.map_zpowers _ _
  rw [← h]
  exact Subgroup.le_normalizer_map lev ⟨X, hX, rfl⟩

theorem mem_Nt_of_comm {X : GL (Fin 2) F}
    (hX : (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F)) :
    X ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
  have hc : Commute X cGL := Units.ext hX
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (hc.zpow_right k).eq.symm

theorem isSolvable_Nt :
    Group.IsSolvable (Nt : Subgroup (GL (Fin 2) F)) := by
  set H := Subgroup.zpowers (cGL (F := F))
  set g := H.normalizerMonoidHom
  have : Group.IsSolvable (MulAut H) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    apply (IsCyclic.mulAutMulEquiv H).injective
    rw [map_mul, map_mul, mul_comm]
  have : Group.IsSolvable g.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hcomm : ∀ x : g.ker, x.1.1 * cGL = cGL * x.1.1 := by
      intro x
      have hx : (x : ↥(Subgroup.normalizer (H : Set (GL (Fin 2) F)))) ∈
          (Subgroup.centralizer (H : Set (GL (Fin 2) F))).subgroupOf
            (Subgroup.normalizer (H : Set (GL (Fin 2) F))) := by
        rw [← Subgroup.normalizerMonoidHom_ker]
        exact x.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx
      exact (hx cGL (Subgroup.mem_zpowers _)).symm
    have ha := congrArg Units.val (hcomm a)
    have hb := congrArg Units.val (hcomm b)
    simp only [Units.val_mul] at ha hb
    have := comm_of_comm_cMat (F := F) ha hb
    exact Subtype.ext (Subtype.ext (Units.ext this))
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

@[expose] noncomputable def transposeGL (Z : GL (Fin 2) F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero (Z : Matrix (Fin 2) (Fin 2) F)ᵀ (by
    rw [Matrix.det_transpose, ← isUnit_iff_ne_zero]
    exact Matrix.isUnit_det_of_invertible _)

theorem coe_transposeGL (Z : GL (Fin 2) F) :
    ((transposeGL Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (Z : Matrix (Fin 2) (Fin 2) F)ᵀ :=
  rfl

theorem exists_lev_conj_tv (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) {φ ψ : Fin 3 → F} (hφ : φ ⬝ᵥ e0 = 0)
    (hψ : ψ ⬝ᵥ e0 = 0) (hφ0 : φ ≠ 0) (hψ0 : ψ ≠ 0) :
    ∃ X : GL (Fin 2) F, (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix _ _ F) ∧
      lev X * tv e0 φ * (lev X)⁻¹ = tv e0 ψ := by
  have hφ0' : φ 0 = 0 := by simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using hφ
  have hψ0' : ψ 0 = 0 := by simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using hψ
  set r : Fin 2 → F := fun i => φ i.succ
  set r' : Fin 2 → F := fun i => ψ i.succ
  have hr : r ≠ 0 := by
    intro h
    apply hφ0
    funext i
    fin_cases i
    · exact hφ0'
    · exact congrFun h 0
    · exact congrFun h 1
  have hr' : r' ≠ 0 := by
    intro h
    apply hψ0
    funext i
    fin_cases i
    · exact hψ0'
    · exact congrFun h 0
    · exact congrFun h 1
  obtain ⟨Z, hZC, hZ⟩ := exists_comm_det_smul_mulVec_eq hroot hcube cMat_transpose_relation hr' hr
  refine ⟨transposeGL Z, ?_, ?_⟩
  · rw [coe_transposeGL]
    have := congrArg Matrix.transpose hZC
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    exact this.symm
  · rw [mul_inv_eq_iff_eq_mul]
    have hdet : (Z : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [← isUnit_iff_ne_zero]
      exact Matrix.isUnit_det_of_invertible _
    have h0 := congrFun hZ 0
    have h1 := congrFun hZ 1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, r, r',
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h0 h1
    have k0 : (Z : Matrix (Fin 2) (Fin 2) F).det⁻¹ * φ 1 =
        (Z : Matrix (Fin 2) (Fin 2) F) 0 0 * ψ 1 + (Z : Matrix (Fin 2) (Fin 2) F) 0 1 * ψ 2 := by
      rw [← h0, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    have k1 : (Z : Matrix (Fin 2) (Fin 2) F).det⁻¹ * φ 2 =
        (Z : Matrix (Fin 2) (Fin 2) F) 1 0 * ψ 1 + (Z : Matrix (Fin 2) (Fin 2) F) 1 1 * ψ 2 := by
      rw [← h1, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    ext i j
    change ((lev (transposeGL Z) * tv e0 φ : SL3 F) : Matrix (Fin 3) (Fin 3) F) i j =
      ((tv e0 ψ * lev (transposeGL Z) : SL3 F) : Matrix (Fin 3) (Fin 3) F) i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tv hφ, coe_tv hψ,
      coe_lev, coe_transposeGL]
    fin_cases i <;> fin_cases j <;>
      simp [levMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec_apply,
        Matrix.one_apply, Pi.single_apply, hφ0', hψ0', Matrix.det_transpose, k0, k1] <;>
      ring

theorem inf_Q1_eq_bot_or_le (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) {Y : Subgroup (SL3 F)}
    (hY : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ Y) :
    Y ⊓ Q1 = ⊥ ∨ Q1 ≤ Y := by
  rcases (Y ⊓ Q1).bot_or_exists_ne_one with h | ⟨u, ⟨huY, huQ⟩, hu1⟩
  · exact Or.inl h
  right
  obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp huQ
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact hu1 (tv_zero_right _)
  intro g hg
  obtain ⟨ψ, hψ, rfl⟩ := mem_pointGroup.mp hg
  by_cases hψ0 : ψ = 0
  · rw [hψ0, tv_zero_right]
    exact Y.one_mem
  obtain ⟨X, hX, hconj⟩ := exists_lev_conj_tv hroot hcube hφ hψ hφ0 hψ0
  rw [← hconj]
  exact Y.mul_mem (Y.mul_mem (hY X hX) huY) (Y.inv_mem (hY X hX))

theorem le_map_rho1 {Y : Subgroup (SL3 F)}
    (hNY : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ Y) :
    (Nt : Subgroup (GL (Fin 2) F)) ≤ (Y.subgroupOf P1).map rho1 := by
  intro X hX
  exact ⟨⟨lev X, lev_mem_P1 X⟩, Subgroup.mem_subgroupOf.mpr (hNY (lev_mem_normalizer_A0 hX)),
    rho1_lev X⟩

theorem isSolvable_of_map_rho1_le {Y : Subgroup (SL3 F)} (hYP : Y ≤ P1)
    (h : (Y.subgroupOf P1).map rho1 ≤ (Nt : Subgroup (GL (Fin 2) F))) : Group.IsSolvable Y := by
  set Y' := Y.subgroupOf P1
  set f : Y' →* (Nt : Subgroup (GL (Fin 2) F)) :=
    (rho1.comp Y'.subtype).codRestrict Nt (fun y => h ⟨y, y.2, rfl⟩)
  have : Group.IsSolvable (Nt : Subgroup (GL (Fin 2) F)) := isSolvable_Nt
  have : Group.IsSolvable f.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hker : ∀ x : f.ker, ((x : Y') : (P1 : Subgroup (SL3 F))).1 ∈ (Q1 : Subgroup (SL3 F)) := by
      intro x
      have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have hx' : rho1 ((x : Y') : (P1 : Subgroup (SL3 F))) = 1 :=
        congrArg Subtype.val hx
      exact mem_ker_rho1.mp hx'
    have := pointGroup_commute (hker a) (hker b)
    exact Subtype.ext (Subtype.ext (Subtype.ext this.eq))
  have hY' : Group.IsSolvable Y' := Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by rw [Subgroup.range_subtype])
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYP).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hYP).surjective

theorem map_rho1_eq_top [Finite F] (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (h3 : (3 : F) ≠ 0)
    {Y : Subgroup (GL (Fin 2) F)} (hNt : (Nt : Subgroup (GL (Fin 2) F)) ≤ Y)
    (hSL : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≤ Y) :
    Y = ⊤ := by
  classical
  have := Fintype.ofFinite F
  rw [eq_top_iff]
  intro g _
  have hg : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero]
    exact Matrix.isUnit_det_of_invertible _
  obtain ⟨s, hs, hdet⟩ := exists_pairMat_det_eq h3 hg
  set P := pairGL hroot cMat_relation hs
  have hP : P ∈ Y := hNt (mem_Nt_of_comm (pairMat_mul_cMat cMat_relation s))
  have hdet1 : ((g * P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have h1 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
        (P : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : (P : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := hdet
    rw [Units.val_mul, Matrix.det_mul, ← h2, mul_comm]
    exact h1
  have hgP : g * P⁻¹ ∈ Y := hSL ⟨⟨(g * P⁻¹ : GL (Fin 2) F), hdet1⟩, Units.ext rfl⟩
  have := Y.mul_mem hgP hP
  rwa [inv_mul_cancel_right] at this

theorem relIndex_sup_normal {X : Type} [Group X] [Finite X] (A Y : Subgroup X) [Y.Normal] :
    A.relIndex (Y ⊔ A) = A.relIndex Y := by
  have h1 := Subgroup.relIndex_sup_right A Y
  have e1 := Subgroup.relIndex_mul_card A (Y ⊔ A)
  have e2 := Subgroup.relIndex_mul_card Y (A ⊔ Y)
  have e3 := Subgroup.relIndex_mul_card Y A
  have e4 := Subgroup.relIndex_mul_card A Y
  rw [inf_of_le_left le_sup_right] at e1
  rw [inf_of_le_left le_sup_right, h1, sup_comm] at e2
  rw [inf_comm] at e3
  have hpos : 0 < Y.relIndex A * Nat.card ↥(A ⊓ Y) := by
    rw [e3]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc A.relIndex (Y ⊔ A) * (Y.relIndex A * Nat.card ↥(A ⊓ Y))
      = A.relIndex (Y ⊔ A) * Nat.card A := by rw [e3]
    _ = Y.relIndex A * Nat.card Y := by rw [e1, e2]
    _ = A.relIndex Y * (Y.relIndex A * Nat.card ↥(A ⊓ Y)) := by rw [← e4]; ring

theorem relIndex_P1_eq [Finite F] {Y : Subgroup (SL3 F)} (hY : (Y.subgroupOf P1).map rho1 = ⊤) :
    Y.relIndex P1 = Y.relIndex Q1 := by
  set Y' := Y.subgroupOf P1
  set K := (rho1 (F := F)).ker
  have hK : K.Normal := MonoidHom.normal_ker _
  have hidx := Subgroup.index_map (H := Y') rho1
  rw [hY, Subgroup.index_top, MonoidHom.range_eq_top.mpr rho1_surjective, Subgroup.index_top,
    mul_one] at hidx
  have hsup : Y' ⊔ K = ⊤ := Subgroup.index_eq_one.mp hidx.symm
  have h1 := relIndex_sup_normal Y' K
  rw [sup_comm, hsup, Subgroup.relIndex_top_right] at h1
  rw [Subgroup.relIndex, h1]
  change (Y.subgroupOf P1).relIndex (rho1 (F := F)).ker = Y.relIndex Q1
  rw [ker_rho1, Subgroup.relIndex_subgroupOf Q1_le_P1]

theorem index_of_le_P1 [Finite F] (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) (h3 : (3 : F) ≠ 0) (hmax : GL2NonsplitMax F)
    {W : Subgroup (SL3 F)} (hWP : W ≤ P1)
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (hW : ¬ Group.IsSolvable W) :
    W.index = Nat.card F ^ 2 + Nat.card F + 1 ∨
      W.index = Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1) := by
  have hNt := le_map_rho1 hNW
  rcases hmax _ hNt with h | h
  · exact absurd (isSolvable_of_map_rho1_le hWP h.le) hW
  have htop := map_rho1_eq_top hroot h3 hNt h
  have hrel := relIndex_P1_eq htop
  have hidx : W.index = W.relIndex P1 * (P1 : Subgroup (SL3 F)).index :=
    (Subgroup.relIndex_mul_index hWP).symm
  rw [hidx, hrel, index_P1]
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases inf_Q1_eq_bot_or_le hroot hcube hlev with hb | hle
  · right
    have : W.relIndex Q1 = Nat.card F ^ 2 := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hb),
        Subgroup.index_bot, card_Q1]
    rw [this]
  · left
    rw [Subgroup.relIndex_eq_one.mpr hle, one_mul]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
