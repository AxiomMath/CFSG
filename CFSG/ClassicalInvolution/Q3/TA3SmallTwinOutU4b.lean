module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutU4
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.GH74.L5U5 Matrix CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem blkScalar_map (φ : F ≃+* F) (c d : F) :
    (blkScalar c d).map φ = blkScalar (φ c) (φ d) := by
  rw [blkScalar, blk4_map, blkScalar, Matrix.scalar_apply, Matrix.scalar_apply, diagonal_map
    (map_zero φ), diagonal_map (map_zero φ), Matrix.scalar_apply, Matrix.scalar_apply]

theorem sBlk_map (φ : F ≃+* F) :
    (blk4 !![0, 1; -1, 0] !![0, 1; -1, 0] : Matrix (Fin 4) (Fin 4) F).map φ =
      blk4 !![0, 1; -1, 0] !![0, 1; -1, 0] := by
  have h : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).map φ = !![0, 1; -1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [blk4_map, h]

theorem sInvBlk_map (φ : F ≃+* F) :
    (blk4 !![0, -1; 1, 0] !![0, -1; 1, 0] : Matrix (Fin 4) (Fin 4) F).map φ =
      blk4 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
  have h : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F).map φ = !![0, -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [blk4_map, h]

theorem eq_one_of_blkScalar_eq_one {c d : F} (h : blkScalar c d = 1) : c = 1 ∧ d = 1 := by
  rw [← blkScalar_one, blkScalar, blkScalar] at h
  obtain ⟨h1, h2⟩ := blk4_inj h
  exact ⟨by simpa using congrFun (congrFun h1 0) 0, by simpa using congrFun (congrFun h2 0) 0⟩

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem su4_form_bar (hF : Nat.card F = (p ^ f) ^ 2) (hq : 2 ≤ p ^ f) (h2 : (2 : F) ≠ 0)
    {G Gi : Matrix (Fin 4) (Fin 4) F} (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hiso : (G.map (unitaryInvolution F p f))ᵀ * G = 1)
    (hfix : ∀ a b : GL (Fin 2) F, a ∈ SUid (unitaryInvolution F p f) 2 →
      b ∈ SUid (unitaryInvolution F p f) 2 → (a = 1 ∨ b = 1) →
        G * (blk4 (a : Matrix (Fin 2) (Fin 2) F) b).map (unitaryInvolution F p f) * Gi =
          blk4 (a : Matrix (Fin 2) (Fin 2) F) b) :
    G * G.map (unitaryInvolution F p f) = -1 ∧ Gi.map (unitaryInvolution F p f) * Gi = -1 := by
  set σ := unitaryInvolution F p f with hσ
  set S : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0] with hS
  set Si : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0] with hSi
  have hDiDm : blk4 Si Si * blk4 S S = 1 := by rw [blk4_mul, sInv_mul_sMat, blk4_one]
  have hDmDi : blk4 S S * blk4 Si Si = 1 := by rw [blk4_mul, sMat_mul_sInv, blk4_one]
  obtain ⟨c, d, hcd⟩ := exists_blkScalar_of_comm_SUid hF hq h2 (B := G * blk4 Si Si)
    fun a b ha hb hab => by
      have := hfix a b ha hb hab
      rw [blk4_map_SUid σ ha hb] at this
      calc G * blk4 Si Si * blk4 (a : Matrix (Fin 2) (Fin 2) F) b =
          G * (blk4 Si Si * blk4 (a : Matrix (Fin 2) (Fin 2) F) b * blk4 S S) * Gi *
            (G * blk4 Si Si) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Gi G, hGiG, Matrix.one_mul, hDmDi, Matrix.mul_one]
        _ = blk4 (a : Matrix (Fin 2) (Fin 2) F) b * (G * blk4 Si Si) := by rw [this]
  obtain ⟨hc, hd, hCi⟩ := blkScalar_inv_eq (c := c) (d := d) (N := blk4 S S * Gi) (by
    rw [← hcd, Matrix.mul_assoc, ← Matrix.mul_assoc (blk4 Si Si), hDiDm, Matrix.one_mul, hGGi])
  have hG : G = blkScalar c d * blk4 S S := by rw [← hcd, Matrix.mul_assoc, hDiDm, Matrix.mul_one]
  have hGi : Gi = blk4 Si Si * blkScalar c⁻¹ d⁻¹ := by
    rw [← hCi, ← Matrix.mul_assoc, hDiDm, Matrix.one_mul]
  have hnorm : σ c * c = 1 ∧ σ d * d = 1 := by
    rw [hG, Matrix.map_mul, blkScalar_map, sBlk_map, Matrix.transpose_mul, blk4_transpose,
      sMat_transpose, blkScalar_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc
      (blkScalar (σ c) (σ d)), blkScalar_mul, ← Matrix.mul_assoc, ← blkScalar_comm_blk4,
      Matrix.mul_assoc, hDiDm, Matrix.mul_one] at hiso
    exact eq_one_of_blkScalar_eq_one hiso
  have hinv : σ c⁻¹ * c⁻¹ = 1 ∧ σ d⁻¹ * d⁻¹ = 1 := by
    rw [map_inv₀, map_inv₀, ← mul_inv, ← mul_inv, hnorm.1, hnorm.2, inv_one]
    exact ⟨rfl, rfl⟩
  constructor
  · rw [hG, Matrix.map_mul, blkScalar_map, sBlk_map, Matrix.mul_assoc, ← Matrix.mul_assoc
      (blk4 S S), ← blkScalar_comm_blk4, Matrix.mul_assoc, ← Matrix.mul_assoc (blkScalar c d),
      blkScalar_mul, mul_comm c, mul_comm d, hnorm.1, hnorm.2, blkScalar_one, Matrix.one_mul,
      blk4_mul, sMat_sq, blk4_neg, blk4_one]
  · rw [hGi, Matrix.map_mul, blkScalar_map, sInvBlk_map, Matrix.mul_assoc, ← Matrix.mul_assoc
      (blkScalar (σ c⁻¹) (σ d⁻¹)), blkScalar_comm_blk4, Matrix.mul_assoc, blkScalar_mul,
      hinv.1, hinv.2, blkScalar_one, Matrix.mul_one, blk4_mul, sInv_sq, blk4_neg, blk4_one]

theorem su4_aut_dichotomy (hF : Nat.card F = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (α : MulAut ↥(ModelData.uni hF).K4) (h₂ : ∀ j ∈ (ModelData.uni hF).J2, α j = j)
    (h₄ : ∀ j ∈ (ModelData.uni hF).J4, α j = j) :
    (∃ c d : F, c ≠ 0 ∧ d ≠ 0 ∧ ∀ x : ↥(ModelData.uni hF).K4,
      (((α x : ↥(ModelData.uni hF).K4) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        blkScalar c d * ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * blkScalar c⁻¹ d⁻¹) ∨
      α * α = 1 := by
  set σ := unitaryInvolution F p f with hσ
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have : 1 < Nat.card F := Finite.one_lt_card
      simp [hF] at this
    · exact hf
  have hp2 : p ≠ 2 := ne_two_of_pow_mod_four hf (Or.inr hq4)
  have hq2 : 2 ≤ p ^ f := by
    have := Nat.one_lt_pow (by omega : f ≠ 0) (Fact.out : p.Prime).one_lt
    omega
  have hq5 : 5 ≤ p ^ f := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by
    rw [hF]; exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow)
  let e : Phan.Su F p f 4 ≃* ↥(ModelData.uni hF).K4 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF 4)
  have he : ∀ x : Phan.Su F p f 4, (((e x : ↥(ModelData.uni hF).K4) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun x => rfl
  let σα : MulAut (Phan.Su F p f 4) := MulAut.congr e.symm α
  obtain ⟨α', g, φ, h1, hm, hiso, -⟩ :=
    ModelFacts.UnitaryAut.unitaryAutClassification_isometry_of_card hF hp2 hq5
      (by norm_num : 3 ≤ 4) (Phan.Su F p f 4) (MonoidHom.id _) Function.surjective_id
      (fun x hx => by rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx; rw [hx]; exact
        Subgroup.one_mem _) σα
  set G : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin 4) (Fin 4) F) with hGdef
  set Gi : Matrix (Fin 4) (Fin 4) F := ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    with hGidef
  have hGGi : G * Gi = 1 := by rw [hGdef, hGidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hGdef, hGidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hform : ∀ x : ↥(ModelData.uni hF).K4,
      (((α x : ↥(ModelData.uni hF).K4) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        G * ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map φ * Gi := fun x => by
    have h1x := h1 (e.symm x)
    simp only [MonoidHom.id_apply] at h1x
    have hmx := hm (e.symm x)
    rw [h1x, RingEquiv.mapMatrix_apply] at hmx
    rw [← e.apply_symm_apply (α x), he]
    exact hmx
  have hH2 : ∀ a : GL (Fin 2) F, a ∈ SUid σ 2 → a ∈ (ModelData.uni hF).H2 := fun a ha => by
    have h' : SUid σ 2 = (ModelData.uni hF).H2 := SUid_eq_statedSU hF 2
    rw [← h']
    exact ha
  have hfix : ∀ a b : GL (Fin 2) F, a ∈ SUid σ 2 → b ∈ SUid σ 2 → (a = 1 ∨ b = 1) →
      G * (blk4 (a : Matrix (Fin 2) (Fin 2) F) b).map φ * Gi =
        blk4 (a : Matrix (Fin 2) (Fin 2) F) b := by
    rintro a b ha hb (rfl | rfl)
    · have key := congrArg (fun y : ↥(ModelData.uni hF).K4 =>
        ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
        (h₄ _ ((ModelData.uni hF).blkR_mem_J4 (hH2 b hb)))
      simp only [hform] at key
      exact key
    · have key := congrArg (fun y : ↥(ModelData.uni hF).K4 =>
        ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
        (h₂ _ ((ModelData.uni hF).blkL_mem_J2 (hH2 a ha)))
      simp only [hform] at key
      exact key
  rcases field_eq_of_fix_SUid hF hGiG φ (fun a ha => by
      have := hfix a 1 ha (SUid _ 2).one_mem (Or.inr rfl)
      rwa [Units.val_one] at this) with rfl | rfl
  · left
    have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F, M.map (RingEquiv.refl F) = M := fun M => by
      ext; simp
    obtain ⟨c, d, hcd⟩ := exists_blkScalar_of_comm_SUid hF hq2 h2 (B := G)
      fun a b ha hb hab => by
        have := hfix a b ha hb hab
        rw [hmap] at this
        calc G * blk4 (a : Matrix (Fin 2) (Fin 2) F) b =
            G * blk4 (a : Matrix (Fin 2) (Fin 2) F) b * Gi * G := by
              rw [Matrix.mul_assoc _ Gi, hGiG, Matrix.mul_one]
          _ = blk4 (a : Matrix (Fin 2) (Fin 2) F) b * G := by rw [this]
    obtain ⟨hc, hd, hGi'⟩ :=
      blkScalar_inv_eq (c := c) (d := d) (N := Gi) (by rw [← hcd]; exact hGGi)
    exact ⟨c, d, hc, hd, fun x => by rw [hform, hmap, hcd, hGi']⟩
  · right
    obtain ⟨hG1, hG2⟩ := su4_form_bar hF hq2 h2 hGGi hGiG hiso hfix
    refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
    rw [MulAut.mul_apply, MulAut.one_apply, hform, hform, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_map]
    have hinvol : (⇑σ ∘ ⇑σ) = id := funext (unitaryInvolution_involutive hF)
    rw [hinvol, Matrix.map_id]
    calc G * (G.map σ * ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Gi.map σ) * Gi =
        (G * G.map σ) * ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Gi.map σ * Gi) := by
          simp only [Matrix.mul_assoc]
      _ = ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [hG1, hG2]; simp

theorem su4FrameOuterQ8Free_holds : SU4FrameOuterQ8Free := fun _ _ _ _ _ _ _ hF hq4 =>
  frameOuterQ8Free_of_dichotomy (blkTorus (ModelData.uni hF).K4) (blkTorus_comm _)
    fun α h₂ h₄ => su4_aut_dichotomy hF hq4 α h₂ h₄

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
