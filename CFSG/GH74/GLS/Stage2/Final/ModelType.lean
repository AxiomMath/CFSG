module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelBlock
public import CFSG.GH74.GLS.Stage2.Final.ModelSpData

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def ZsTwo (M : ModelData F) : Prop := ∀ s ∈ Zs M, s = 1 ∨ s = M.xK

theorem ZsTwo.sq_eq_one {M : ModelData F} (h : ZsTwo M) {s : ↥M.K4} (hs : s ∈ Zs M) :
    s * s = 1 := by
  rcases h s hs with rfl | rfl
  · simp
  · exact M.xK_mul_self

@[expose] def HasSqLift (M : ModelData F) (u : PG M) (s : ↥M.K4) : Prop :=
  ∃ g : ↥M.K4, mkP M g = u ∧ g * g = s

theorem mkP_surjective (M : ModelData F) : Function.Surjective (mkP M) :=
  QuotientGroup.mk'_surjective _

theorem HasSqLift.conj {M : ModelData F} {u v : PG M} {s : ↥M.K4}
    (hs : s ∈ Subgroup.center ↥M.K4) (h : HasSqLift M u s) (hc : IsConj u v) : HasSqLift M v s := by
  obtain ⟨g, hg, hgs⟩ := h
  obtain ⟨c, hc'⟩ := isConj_iff.1 hc
  obtain ⟨k, rfl⟩ := mkP_surjective M c
  refine ⟨k * g * k⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hg, hc']
  · have hks : k * s = s * k := Subgroup.mem_center_iff.1 hs k
    calc k * g * k⁻¹ * (k * g * k⁻¹) = k * (g * g) * k⁻¹ := by group
      _ = k * s * k⁻¹ := by rw [hgs]
      _ = s := by rw [hks]; group

theorem sq_eq_of_mkP_eq {M : ModelData F} (hZ : ZsTwo M) {g g' : ↥M.K4} (h : mkP M g = mkP M g') :
    g * g = g' * g' := by
  have hmem : g⁻¹ * g' ∈ Zs M := by
    rw [← QuotientGroup.eq]
    exact h
  have hc : ∀ t : ↥M.K4, t * (g⁻¹ * g') = (g⁻¹ * g') * t := fun t =>
    Subgroup.mem_center_iff.1 (Zs_le_center M hmem) t
  have hcc : (g⁻¹ * g') * (g⁻¹ * g') = 1 := hZ.sq_eq_one hmem
  have hg' : g' = g * (g⁻¹ * g') := by group
  have key : g' * g' = g * g := by
    calc g' * g' = g * (g⁻¹ * g') * (g * (g⁻¹ * g')) := by rw [← hg']
      _ = g * (g * ((g⁻¹ * g') * (g⁻¹ * g'))) := by
          have := hc g
          calc g * (g⁻¹ * g') * (g * (g⁻¹ * g')) = g * ((g⁻¹ * g') * g) * (g⁻¹ * g') := by group
            _ = g * (g * (g⁻¹ * g')) * (g⁻¹ * g') := by rw [← this]
            _ = g * (g * ((g⁻¹ * g') * (g⁻¹ * g'))) := by group
      _ = g * g := by rw [hcc, mul_one]
  exact key.symm

theorem HasSqLift.unique {M : ModelData F} (hZ : ZsTwo M) {u : PG M} {s s' : ↥M.K4}
    (h : HasSqLift M u s) (h' : HasSqLift M u s') : s = s' := by
  obtain ⟨g, hg, hgs⟩ := h
  obtain ⟨g', hg', hgs'⟩ := h'
  rw [← hgs, ← hgs']
  exact sq_eq_of_mkP_eq hZ (hg.trans hg'.symm)

theorem sign_lemma {G : Type*} [Group G] {x T W Z : G} (hT : T * T = 1) (hW : W * W = 1)
    (hZ : Z * Z = 1) (hTW : (T * W) * (T * W) = 1) (hZW : (Z * W) * (Z * W) = 1)
    (hTZ : (T * Z) * (T * Z) = x) : (T * W * Z) * (T * W * Z) = x := by
  have hT' : T⁻¹ = T := inv_eq_of_mul_eq_one_right hT
  have hW' : W⁻¹ = W := inv_eq_of_mul_eq_one_right hW
  have hZ' : Z⁻¹ = Z := inv_eq_of_mul_eq_one_right hZ
  have hWT : W * T = T * W := by
    have h1 : (T * W)⁻¹ = T * W := inv_eq_of_mul_eq_one_right hTW
    rw [_root_.mul_inv_rev, hW', hT'] at h1
    exact h1
  have hWZ : W * Z = Z * W := by
    have h1 : (Z * W)⁻¹ = Z * W := inv_eq_of_mul_eq_one_right hZW
    rw [_root_.mul_inv_rev, hW', hZ'] at h1
    exact h1
  calc T * W * Z * (T * W * Z) = T * W * (Z * T * W * Z) := by group
    _ = T * W * (Z * (T * W) * Z) := by group
    _ = T * W * (Z * (W * T) * Z) := by rw [hWT]
    _ = T * W * ((Z * W) * T * Z) := by group
    _ = T * W * ((W * Z) * T * Z) := by rw [hWZ]
    _ = T * (W * W) * Z * T * Z := by group
    _ = (T * Z) * (T * Z) := by rw [hW]; group
    _ = x := hTZ

theorem hasSqLift_mul3 {M : ModelData F} (hZ : ZsTwo M) {t w z : PG M}
    (ht : HasSqLift M t 1) (hw : HasSqLift M w 1) (hz : HasSqLift M z 1)
    (htw : HasSqLift M (t * w) 1) (hzw : HasSqLift M (z * w) 1) (htz : HasSqLift M (t * z) M.xK) :
    HasSqLift M (t * w * z) M.xK := by
  obtain ⟨T, hT, hT2⟩ := ht
  obtain ⟨W, hW, hW2⟩ := hw
  obtain ⟨Z, hZ', hZ2⟩ := hz
  have hTW : (T * W) * (T * W) = 1 := by
    obtain ⟨g, hg, hg2⟩ := htw
    rw [← sq_eq_of_mkP_eq hZ (g := g) (g' := T * W) (by rw [hg, map_mul, hT, hW])]
    exact hg2
  have hZW : (Z * W) * (Z * W) = 1 := by
    obtain ⟨g, hg, hg2⟩ := hzw
    rw [← sq_eq_of_mkP_eq hZ (g := g) (g' := Z * W) (by rw [hg, map_mul, hZ', hW])]
    exact hg2
  have hTZ : (T * Z) * (T * Z) = M.xK := by
    obtain ⟨g, hg, hg2⟩ := htz
    rw [← sq_eq_of_mkP_eq hZ (g := g) (g' := T * Z) (by rw [hg, map_mul, hT, hZ'])]
    exact hg2
  exact ⟨T * W * Z, by rw [map_mul, map_mul, hT, hW, hZ'],
    sign_lemma hT2 hW2 hZ2 hTW hZW hTZ⟩


section Families

open CFSG.GH74.GLS.Stage2.Final.ModelSp

theorem blk4_entry (X Y : Matrix (Fin 2) (Fin 2) F) (a b : Fin 4) :
    blk4 X Y a b = fromBlocks X 0 0 Y (e4.symm a) (e4.symm b) := rfl

theorem blk4_J_zero_one : (blk4 (J2m F) (J2m F)) 0 1 = 1 := by
  rw [blk4_entry]
  have h0 : e4.symm (0 : Fin 4) = Sum.inl 0 := rfl
  have h1 : e4.symm (1 : Fin 4) = Sum.inl 1 := rfl
  rw [h0, h1]
  simp [J2m]

theorem scalar_mem_isoGL_J (c : Fˣ)
    (h : (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) ∈
      isoGL (blk4 (J2m F) (J2m F))) : c * c = 1 := by
  rw [mem_isoGL] at h
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hs] at h
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul] at h
  have h1 := congrFun (congrFun h 0) 1
  simp only [Matrix.smul_apply, smul_eq_mul, blk4_J_zero_one, mul_one] at h1
  exact Units.ext (by simpa using h1)

theorem zsTwo_sp : ZsTwo (ModelData.sp F) := by
  intro s hs
  obtain ⟨c, hc⟩ := mem_Zs.1 hs
  have hmem : (s : GL (Fin 4) F) ∈ isoGL (blk4 (J2m F) (J2m F)) := mem_K4_sp.1 s.2
  rw [← hc] at hmem
  rcases units_sq_eq_one (scalar_mem_isoGL_J c hmem) with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hc, map_one]
    rfl
  · right
    apply Subtype.ext
    rw [← hc]
    show _ = xGL F
    rw [xGL_eq_neg_one, CFSG.GH74.L5U5.scalar_neg_one_eq]

theorem zsTwo_lin [Finite F] (hF : Nat.card F % 4 = 3) : ZsTwo (ModelData.lin F) := by
  intro s hs
  rcases (mem_center_lin_iff hF s).1 (Zs_le_center _ hs) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem zsTwo_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) : ZsTwo (ModelData.uni hF) := by
  intro s hs
  rcases (mem_center_uni_iff hF hq s).1 (Zs_le_center _ hs) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end Families

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
