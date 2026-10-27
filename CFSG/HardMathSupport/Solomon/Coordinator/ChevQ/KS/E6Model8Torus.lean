module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Model8
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentFin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwE6ModelIndex
public import CFSG.LieType.Chevalley.E6SignedGraphRankOne

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical

section Torus

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

@[expose] noncomputable def Std8.F (D : Std8 L) : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
  twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) D.Fr

theorem Std8.step_eq (D : Std8 L) : D.S.D.step = D.F := by
  unfold LangDatum.step Std8.F
  rw [D.hΦ, D.hn]
  rfl

theorem Std8.F_rootDiagUnit (D : Std8 L) (a : Fin Tag.E6.rank → Lˣ) :
    D.F (rootDiagUnit Tag.E6 a) = (rootDiagUnit Tag.E6 a)⁻¹ ^ 8 :=
  twE6Eight_twFrob_rootDiagUnit D.hFr a

theorem Std8.mem_model_iff (D : Std8 L) {x : ModGL Tag.E6 L} :
    x ∈ D.S.D.model ↔ x ∈ adjointGroup Tag.E6 L ∧ D.F x = x := by
  rw [LangDatum.mem_model]
  have h : D.S.D.n * D.S.D.Φ x * D.S.D.n⁻¹ = D.S.D.step x := rfl
  rw [h, D.step_eq]

theorem Std8.mem_torus_iff (D : Std8 L) {x : ModGL Tag.E6 L} :
    x ∈ D.S.D.torus ↔ x ∈ torusGroup Tag.E6 L ∧ D.F x = x := by
  rw [LangDatum.torus, mem_twistedTorusOf]
  have h : D.S.D.n * D.S.D.Φ x * D.S.D.n⁻¹ = D.S.D.step x := rfl
  rw [h, D.step_eq]

theorem Std8.pow_nine_of_mem_torus (D : Std8 L) {x : ModGL Tag.E6 L}
    (hx : x ∈ D.S.D.torus) : x ^ 9 = 1 := by
  obtain ⟨hxT, hxF⟩ := D.mem_torus_iff.1 hx
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
  rw [D.F_rootDiagUnit, inv_pow] at hxF
  set y := rootDiagUnit Tag.E6 a
  calc y ^ 9 = y ^ 8 * y := pow_succ y 8
    _ = y ^ 8 * (y ^ 8)⁻¹ := by rw [hxF]
    _ = 1 := mul_inv_cancel _

theorem Std8.dV_mem_torus (D : Std8 L) {ω : Lˣ} (hω : ω ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) : dV ω x ∈ D.S.D.torus := by
  refine D.mem_torus_iff.2 ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
  have h3 := dV_pow_three (τ := Tag.E6) hω x
  have hF : D.F (dV ω x) = (dV ω x)⁻¹ ^ 8 := D.F_rootDiagUnit (torV ω x)
  rw [hF, inv_pow]
  apply inv_eq_of_mul_eq_one_left
  calc dV ω x ^ 8 * dV ω x = dV ω x ^ 9 := (pow_succ _ 8).symm
    _ = (dV ω x ^ 3) ^ 3 := by rw [← pow_mul]
    _ = 1 := by rw [h3, one_pow]

theorem twFix8_HSL (μ : Lˣ) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 8) {ζ : Lˣ} (hζ : ζ ^ 9 = 1) :
    conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
      (Matrix.SpecialLinearGroup.map Fr (HSL ζ)) = HSL ζ := by
  have hM : ((RankThree.Classical.swapGL * diagUnitOne μ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, 1; (μ : L), 0] := coe_swapGL_mul_diagUnitOne μ
  have hMi : (((RankThree.Classical.swapGL * diagUnitOne μ : GL (Fin 2) L)⁻¹ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, ((μ⁻¹ : Lˣ) : L); 1, 0] := by
    rw [Matrix.coe_units_inv, hM]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_fin_two]
    have hμ : ((μ⁻¹ : Lˣ) : L) * (μ : L) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm, hμ]
  have hinv : ζ⁻¹ = ζ ^ 8 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hζ])
  have h1 : (ζ : L) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have h64 : (ζ : L) ^ 64 = ζ := by
    have h63 : (ζ : L) ^ 63 = 1 := by rw [show 63 = 9 * 7 by rfl, pow_mul, h1, one_pow]
    calc (ζ : L) ^ 64 = (ζ : L) ^ 63 * ζ := pow_succ _ 63
      _ = ζ := by rw [h63, one_mul]
  have hH : ((HSL ζ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![(ζ : L), 0; 0, (ζ : L) ^ 8] := by
    change !![(ζ : L), 0; 0, ((ζ⁻¹ : Lˣ) : L)] = _
    rw [hinv, Units.val_pow_eq_pow_val]
  apply Subtype.ext
  rw [coe_conjSL, hM, hMi]
  change !![0, 1; (μ : L), 0] * ((HSL ζ : SL2 L) : Matrix (Fin 2) (Fin 2) L).map Fr *
    !![0, ((μ⁻¹ : Lˣ) : L); 1, 0] = _
  rw [hH]
  have hmap : (!![(ζ : L), 0; 0, (ζ : L) ^ 8] : Matrix (Fin 2) (Fin 2) L).map Fr =
      !![(ζ : L) ^ 8, 0; 0, (ζ : L) ^ 64] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hFr, ← pow_mul]
  rw [hmap, Matrix.mul_fin_two, Matrix.mul_fin_two]
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h64] <;> field_simp

theorem Std8.rootSL2_HSL_mem_model (D : Std8 L) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) {ζ : Lˣ} (hζ : ζ ^ 9 = 1) :
    rootSL2 Tag.E6 L α (HSL ζ) ∈ D.S.D.model := by
  obtain ⟨μ, hμ⟩ := exists_twE6Two_twFrob_rootSL2 D.Fr hα
  refine D.mem_model_iff.2 ⟨rootSpan_le_adjointGroup L {α, -α} (rootSL2_mem_rootSpan_pair hα _), ?_⟩
  have hμ' := hμ (HSL ζ)
  rw [twFix8_HSL μ D.hFr hζ] at hμ'
  exact hμ'

theorem nSL_sq_eq_one (c : Lˣ) : nSL c ^ 2 = 1 := by
  have hcc : (c : L) * ((c⁻¹ : Lˣ) : L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcc' : ((c⁻¹ : Lˣ) : L) * (c : L) = 1 := by rw [mul_comm, hcc]
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change !![0, (c : L); -((c⁻¹ : Lˣ) : L), 0] * !![0, (c : L); -((c⁻¹ : Lˣ) : L), 0] = 1
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, hcc, hcc']

theorem Std8.exists_nSL_mem_model (D : Std8 L) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ c : Lˣ, rootSL2 Tag.E6 L α (nSL c) ∈ D.S.D.model := by
  obtain ⟨μ, hμ⟩ := exists_twE6Two_twFrob_rootSL2 D.Fr hα
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-((μ⁻¹ : Lˣ) : L)) (n := 9) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num), zero_eq_neg] at hz
    exact Units.ne_zero _ hz
  set c : Lˣ := Units.mk0 z hz0 with hc
  refine ⟨c, D.mem_model_iff.2
    ⟨rootSpan_le_adjointGroup L {α, -α} (rootSL2_mem_rootSpan_pair hα _), ?_⟩⟩
  have hμ' := hμ (nSL c)
  rw [map_nSL, conjSL_swap_nSL] at hμ'
  have hfix : -(μ * Units.map D.Fr.toMonoidHom c)⁻¹ = c := by
    have hc9 : (c : L) ^ 9 = -((μ⁻¹ : Lˣ) : L) := by rw [hc, Units.val_mk0, hz]
    ext1
    rw [Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mul, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, D.hFr]
    have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
    have hcz : (c : L) ≠ 0 := Units.ne_zero c
    rw [Units.val_inv_eq_inv_val] at hc9
    have hc9' : (μ : L) * (c : L) ^ 9 = -1 := by rw [hc9, mul_neg, mul_inv_cancel₀ hμ0]
    field_simp
    linear_combination -hc9'
  rw [hfix] at hμ'
  exact hμ'

theorem Std8.exists_antidiag_mem_Γ (D : Std8 L) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ c : Lˣ, rootSL2 Tag.E6 L α (nSL c) ∈ D.S.Γ := by
  obtain ⟨c, hc⟩ := D.exists_nSL_mem_model hα
  refine ⟨c, ?_⟩
  obtain ⟨k, hk⟩ := twE6_model_pow_mem_Γ D.S D.hAlg D.Fr
    (fun c' => by rw [D.hq]; exact D.hFr c') D.hΦ
  refine mem_of_sq_mem_of_pow_mem D.S.Γ k (hk _ hc) ?_
  rw [← map_pow, nSL_sq_eq_one, map_one]
  exact one_mem _

theorem Std8.rootSL2_HSL_mem_Γ (D : Std8 L) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    {ζ : Lˣ} (hζ : ζ ^ 9 = 1) : rootSL2 Tag.E6 L α (HSL ζ) ∈ D.S.Γ := by
  obtain ⟨c, hc⟩ := D.exists_nSL_mem_model hα
  have hζ5 : (ζ ^ 5) ^ 9 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h1 := Subgroup.commutator_mem_commutator (D.rootSL2_HSL_mem_model hα hζ5) hc
  have hn0 : ((nSL c : SL2 L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := rfl
  have hn1 : ((nSL c : SL2 L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := rfl
  have h4 : (ζ ^ 5) ^ 2 = ζ := by
    rw [← pow_mul, show 5 * 2 = 9 + 1 by rfl, pow_succ, hζ, one_mul]
  rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    HSL_conj_antidiag (ζ ^ 5) hn0 hn1, h4] at h1
  exact h1

theorem Std8.dV_mem_Γ (D : Std8 L) {ω : Lˣ} (hω : ω ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3) :
    dV ω x ∈ D.S.Γ := by
  have hcube : ∀ i, ∃ u : Lˣ, u ^ 3 = torV ω x i := fun i => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((torV ω x i : Lˣ) : L) (n := 3)
      (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose b hb using hcube
  have hb9 : ∀ i, b i ^ 9 = 1 := fun i => by
    have h3 : torV ω x i ^ 3 = 1 := by
      rw [torV, ← pow_mul, mul_comm, pow_mul, hω, one_pow]
    rw [show 9 = 3 * 3 by rfl, pow_mul, hb i, h3]
  have hd : dV ω x = rootDiagUnit Tag.E6 b ^ 3 := by
    rw [rootDiagUnit_pow]
    unfold dV
    congr 1
    funext i
    exact (hb i).symm
  have e : dV ω x = ((List.finRange Tag.E6.rank).map fun i =>
      torusElt Tag.E6 L i (cubeParam b i)).prod := hd.trans (rootDiagUnit_pow_three b)
  rw [e]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  rw [twE6Two_torusElt_eq_rootSL2]
  refine D.rootSL2_HSL_mem_Γ (isRoot_single _ i) ?_
  unfold cubeParam
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb9 j, one_zpow]

theorem conj_rootSL2_nSL_rootDiagUnit (i : Fin Tag.E6.rank) (c : Lˣ) (a : Fin Tag.E6.rank → Lˣ) :
    rootSL2 Tag.E6 L (Pi.single i 1) (nSL c) * rootDiagUnit Tag.E6 a *
      (rootSL2 Tag.E6 L (Pi.single i 1) (nSL c))⁻¹ =
        rootDiagUnit Tag.E6 (fun j => a j * a i ^ (-Tag.E6.cartan i j)) := by
  have h1 : nSL c = nSL 1 * HSL c⁻¹ := by rw [nSL_mul_HSL, one_mul, inv_inv]
  have hn1 : rootSL2 Tag.E6 L (Pi.single i 1) (nSL 1) = weylElt Tag.E6 L i 1 := by
    rw [rootSL2_single]
    exact E6SignedGraph.simpleRootSL2_nSL i 1
  have ht : rootSL2 Tag.E6 L (Pi.single i 1) (HSL c⁻¹) =
      rootDiagUnit Tag.E6 (fun j => c⁻¹ ^ Tag.E6.cartan i j) := by
    rw [← twE6Two_torusElt_eq_rootSL2]
    exact torusElt_eq_rootDiagUnit i c⁻¹
  have hcomm : rootDiagUnit Tag.E6 (fun j => c⁻¹ ^ Tag.E6.cartan i j) * rootDiagUnit Tag.E6 a *
      (rootDiagUnit Tag.E6 (fun j => c⁻¹ ^ Tag.E6.cartan i j))⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  rw [h1, map_mul, hn1, ht]
  calc (weylElt Tag.E6 L i 1 * rootDiagUnit Tag.E6 (fun j => c⁻¹ ^ Tag.E6.cartan i j)) *
        rootDiagUnit Tag.E6 a * (weylElt Tag.E6 L i 1 * rootDiagUnit Tag.E6
          (fun j => c⁻¹ ^ Tag.E6.cartan i j))⁻¹ =
      weylElt Tag.E6 L i 1 * (rootDiagUnit Tag.E6 (fun j => c⁻¹ ^ Tag.E6.cartan i j) *
        rootDiagUnit Tag.E6 a * (rootDiagUnit Tag.E6 (fun j => c⁻¹ ^ Tag.E6.cartan i j))⁻¹) *
          (weylElt Tag.E6 L i 1)⁻¹ := by group
    _ = weylElt Tag.E6 L i 1 * rootDiagUnit Tag.E6 a * (weylElt Tag.E6 L i 1)⁻¹ := by rw [hcomm]
    _ = _ := weylElt_conj_rootDiagUnit a i

theorem Std8.exists_lift (D : Std8 L) (i : Fin Tag.E6.rank) :
    ∃ ν ∈ D.S.Γ, ∀ {ω : Lˣ}, ω ^ 3 = 1 → ∀ x : Fin Tag.E6.rank → ZMod 3,
      ν * dV ω x * ν⁻¹ = dV ω (reflV i x) := by
  obtain ⟨c, hc⟩ := D.exists_antidiag_mem_Γ (isRoot_single _ i)
  refine ⟨_, hc, fun {ω} hω x => ?_⟩
  unfold dV
  rw [conj_rootSL2_nSL_rootDiagUnit i c]
  congr 1
  funext j
  have h1 : ω ^ (x j - (Tag.E6.cartan i j : ZMod 3) * x i).val =
      ω ^ (((x j).val : ℤ) - Tag.E6.cartan i j * (x i).val) :=
    CFSG.RankThree.Chevalley.pow_val_eq_zpow_of_pow_eq_one hω _ _ (by
      push_cast
      simp [ZMod.natCast_zmod_val])
  have e : ((x j).val : ℤ) - Tag.E6.cartan i j * (x i).val =
      ((x j).val : ℤ) + ((x i).val : ℤ) * (-Tag.E6.cartan i j) := by ring
  simp only [torV, reflV]
  rw [h1, e, zpow_add, zpow_mul, zpow_natCast, zpow_natCast]

end Torus

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
