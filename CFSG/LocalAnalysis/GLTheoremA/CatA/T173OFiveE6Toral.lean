module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Lift
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical
open CFSG.RankThree.CentralCover CFSG.RankThree.ThinCatalog
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TableBExc.E6Three
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173


variable {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem conjSL_diagUnitOne_sl2Diag (a γ : Fˣ) :
    conjSL (diagUnitOne a) (sl2Diag γ) = sl2Diag γ := by
  apply Subtype.ext
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv, coe_sl2Diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

private theorem conjSL_diagUnitOne_sl2Upper (a : Fˣ) (c : F) :
    conjSL (diagUnitOne a) (CFSG.RankThree.CentralCover.sl2Upper c) =
      CFSG.RankThree.CentralCover.sl2Upper ((a : F) * c) := by
  apply Subtype.ext
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv,
    CFSG.RankThree.CentralCover.coe_sl2Upper, CFSG.RankThree.CentralCover.coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem exists_conj_hom_of_diag
    (hcfg : Cfg173 3 S B N D K x) (hq : 4 ≤ Nat.card F)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (i : Fin Tag.E6.rank)
    (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S)
    (hψ : ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (b : ↥B) {c : Fin Tag.E6.rank → Fˣ}
    (hc : ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) = rootDiagUnit Tag.E6 c) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S,
      (∀ A, ((φ A : ↥S) : Ω) = (b : Ω) * ((ψ A : ↥S) : Ω) * (b : Ω)⁻¹) ∧
      φ = ψ.comp (conjSL (diagUnitOne (rootChar c (Pi.single i 1)))) := by
  classical
  haveI hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hq
  let δ : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
    conjSL (diagUnitOne (rootChar c (Pi.single i 1)))
  let φ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S :=
    { toFun := fun A => ⟨(b : Ω) * ((ψ A : ↥S) : Ω) * (b : Ω)⁻¹,
        hcfg.normal.conj_mem ((ψ A : ↥S) : Ω) (ψ A).2 (b : Ω)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro A A'
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul]
        group }
  have hφcoe : ∀ A, ((φ A : ↥S) : Ω) = (b : Ω) * ((ψ A : ↥S) : Ω) * (b : Ω)⁻¹ :=
    fun A => rfl
  refine ⟨φ, hφcoe, ?_⟩
  refine CFSG.SeitzReduction.LinearPilot.eq_of_comp_eq_of_ker_le_center
    (p := M.π) (by rw [M.ker_π]) (φ := φ) (ψ := ψ.comp δ) ?_
  intro A
  apply Subtype.ext
  have hconj : ((M.π (φ A) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
      = ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F)
        * ((M.π (ψ A) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
        * (((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F))⁻¹ := by
    have hbcoev : ((b⁻¹ : ↥B) : Ω) = (b : Ω)⁻¹ := by simp
    have h := M.conj b⁻¹ (ψ A) (φ A) (by
      rw [hφcoe A, hbcoev, inv_inv])
    have hβinv : ((M.β b⁻¹ : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F)
        = (((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F))⁻¹ := by
      rw [map_inv]
      rfl
    rw [hβinv] at h
    simpa using h
  have hroot : ((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F)
        * ((M.π (ψ A) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
        * (((M.β b : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F))⁻¹
      = simpleRootSL2 Tag.E6 F i (δ A) := by
    rw [hc, hψ A]
    have h := rootDiagUnit_conj_rootSL2 (τ := Tag.E6) (K := F) c
      (isRoot_single Tag.E6 i) A
    simpa [δ, rootSL2_single] using h
  rw [hconj, hroot]
  exact (hψ (δ A)).symm

private theorem eq_sl2Diag_of_diagonal {g : SL2 F} {γ : Fˣ}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)]) : g = sl2Diag γ := by
  apply Subtype.ext
  rw [hg, coe_sl2Diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private noncomputable def upperLift
    (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S) : Subgroup Ω :=
  (sl2UpperGroup F).map ((S.subtype).comp ψ)

private theorem isPGroup_upperLift (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S) :
    IsPGroup 2 (upperLift (S := S) ψ) :=
  (isPGroup_sl2UpperGroup (K := F)).map ((S.subtype).comp ψ)

private theorem upperLift_ne_bot {ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S}
    (hinj : Function.Injective ψ) : upperLift (S := S) ψ ≠ ⊥ := by
  have hinj' : Function.Injective ((S.subtype).comp ψ) := by
    intro x y hxy
    exact hinj (Subtype.ext_iff.mpr hxy)
  change (sl2UpperGroup F).map ((S.subtype).comp ψ) ≠ ⊥
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj']
  exact sl2UpperGroup_ne_bot

private theorem conj_upperLift (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S)
    (h u : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((ψ h : ↥S) : Ω) * ((ψ u : ↥S) : Ω) * (((ψ h : ↥S)) : Ω)⁻¹ =
      ((ψ (h * u * h⁻¹) : ↥S) : Ω) := by
  have h1 : (ψ h) * (ψ u) * (ψ h)⁻¹ = ψ (h * u * h⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h1]

private theorem injective_lift
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (i : Fin Tag.E6.rank) (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S)
    (hψ : ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) : Function.Injective ψ := by
  intro A A' hAA'
  apply simpleRootSL2_injective_of_charTwo (K := F) i
  have h := congrArg (fun z : ↥S =>
    ((M.π z : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)) hAA'
  simpa [hψ] using h

private theorem mem_B_map_upper
    (hcfg : Cfg173 3 S B N D K x) (hq : 4 ≤ Nat.card F)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (i : Fin Tag.E6.rank) (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S)
    (hψ : ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c) :
    ∀ b ∈ B, ∀ z ∈ upperLift (S := S) ψ, (b : Ω) * z * (b : Ω)⁻¹ ∈ upperLift (S := S) ψ := by
  intro b hb z hz
  have hbβ : ((M.β ⟨b, hb⟩ : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈ M.barB :=
    Subgroup.mem_map_of_mem (hatGroup Tag.E6 F).subtype ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨c, -, hc⟩ := hdiag _ hbβ
  obtain ⟨φ, hφcoe, hφeq⟩ := exists_conj_hom_of_diag hcfg hq M i ψ hψ ⟨b, hb⟩ hc
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
  have hu' : conjSL (diagUnitOne (rootChar c (Pi.single i 1))) u ∈ sl2UpperGroup F := by
    obtain ⟨v, rfl⟩ := hu
    rw [sl2UpperHom_apply, conjSL_diagUnitOne_sl2Upper]
    exact ⟨Multiplicative.ofAdd ((rootChar c (Pi.single i 1) : F) * Multiplicative.toAdd v),
      by rw [sl2UpperHom_apply, toAdd_ofAdd]⟩
  refine Subgroup.mem_map.mpr ⟨conjSL (diagUnitOne (rootChar c (Pi.single i 1))) u, hu', ?_⟩
  have hφu : φ u = ψ (conjSL (diagUnitOne (rootChar c (Pi.single i 1))) u) := by
    simpa only [MonoidHom.comp_apply] using congrArg (fun f => f u) hφeq
  change ((ψ (conjSL (diagUnitOne (rootChar c (Pi.single i 1))) u) : ↥S) : Ω) =
    (b : Ω) * ((ψ u : ↥S) : Ω) * (b : Ω)⁻¹
  rw [← hφu, hφcoe u]

private theorem le_normalizer_upper_of_mem_B {ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S}
    (hBmap : ∀ b ∈ B, ∀ z ∈ upperLift (S := S) ψ,
      (b : Ω) * z * (b : Ω)⁻¹ ∈ upperLift (S := S) ψ) :
    B ≤ Subgroup.normalizer (upperLift (S := S) ψ : Set Ω) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨hBmap b hb z, fun hz => ?_⟩
  have h := hBmap b⁻¹ (B.inv_mem hb) ((b : Ω) * z * (b : Ω)⁻¹) hz
  have heq : (b : Ω)⁻¹ * ((b : Ω) * z * (b : Ω)⁻¹) * ((b : Ω)⁻¹)⁻¹ = z := by
    group
  rwa [heq] at h

private theorem mem_normalizer_upper_lift
    (hcfg : Cfg173 3 S B N D K x) (hq : 4 ≤ Nat.card F)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (i : Fin Tag.E6.rank) (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S)
    (hψ : ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c)
    {γ : Fˣ} {g : Matrix.SpecialLinearGroup (Fin 2) F} (hgdiag : g = sl2Diag γ) :
    ((ψ g : ↥S) : Ω) ∈ Subgroup.normalizer (upperLift (S := S) ψ : Set Ω) := by
  have hgN : g ∈ Subgroup.normalizer (sl2UpperGroup F : Set (SL2 F)) := by
    rw [hgdiag]
    exact sl2Diag_mem_normalizer_upper γ
  have hgen : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
      h ∈ Subgroup.normalizer (sl2UpperGroup F : Set (SL2 F)) →
      ∀ z ∈ upperLift (S := S) ψ,
        ((ψ h : ↥S) : Ω) * z * (((ψ h : ↥S)) : Ω)⁻¹ ∈ upperLift (S := S) ψ := by
    intro h hh z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_map.mpr ⟨h * u * h⁻¹,
      (Subgroup.mem_normalizer_iff.mp hh u).mp hu, (conj_upperLift ψ h u).symm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨hgen g hgN z, fun hz => ?_⟩
  have hginvN : g⁻¹ ∈ Subgroup.normalizer (sl2UpperGroup F : Set (SL2 F)) :=
    Subgroup.inv_mem _ hgN
  have h := hgen g⁻¹ hginvN (((ψ g : ↥S) : Ω) * z * (((ψ g : ↥S)) : Ω)⁻¹) hz
  have hcoe : ((ψ g⁻¹ : ↥S) : Ω) = (((ψ g : ↥S)) : Ω)⁻¹ := by
    rw [← Subgroup.coe_inv, map_inv]
  rw [hcoe] at h
  have heq : (((ψ g : ↥S)) : Ω)⁻¹ *
      ((((ψ g : ↥S)) : Ω) * z * ((((ψ g : ↥S)) : Ω))⁻¹) *
      ((((ψ g : ↥S)) : Ω)⁻¹)⁻¹ = z := by group
  rwa [heq] at h

private theorem commute_lift_of_diag
    (hcfg : Cfg173 3 S B N D K x) (hq : 4 ≤ Nat.card F)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (i : Fin Tag.E6.rank) (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥S)
    (hψ : ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c)
    (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hg : ∃ γ : Fˣ, γ ^ 3 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)]) :
    ∀ b ∈ B, (b : Ω) * ((ψ g : ↥S) : Ω) = ((ψ g : ↥S) : Ω) * (b : Ω) := by
  obtain ⟨γ, -, hγg⟩ := hg
  have hgdiag : g = sl2Diag γ := eq_sl2Diag_of_diagonal hγg
  intro b hb
  have hbβ : ((M.β ⟨b, hb⟩ : ↥(hatGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈ M.barB :=
    Subgroup.mem_map_of_mem (hatGroup Tag.E6 F).subtype ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨c, -, hc⟩ := hdiag _ hbβ
  obtain ⟨φ, hφcoe, hφeq⟩ := exists_conj_hom_of_diag hcfg hq M i ψ hψ ⟨b, hb⟩ hc
  have hδg : conjSL (diagUnitOne (rootChar c (Pi.single i 1))) g = g := by
    rw [hgdiag]
    exact conjSL_diagUnitOne_sl2Diag _ γ
  have hφg : φ g = ψ (conjSL (diagUnitOne (rootChar c (Pi.single i 1))) g) := by
    simpa only [MonoidHom.comp_apply] using congrArg (fun f => f g) hφeq
  have hconj : (b : Ω) * ((ψ g : ↥S) : Ω) * (b : Ω)⁻¹ = ((ψ g : ↥S) : Ω) := by
    calc (b : Ω) * ((ψ g : ↥S) : Ω) * (b : Ω)⁻¹ = ((φ g : ↥S) : Ω) := (hφcoe g).symm
      _ = ((ψ (conjSL (diagUnitOne (rootChar c (Pi.single i 1))) g) : ↥S) : Ω) := by
            rw [hφg]
      _ = ((ψ g : ↥S) : Ω) := by rw [hδg]
  calc (b : Ω) * ((ψ g : ↥S) : Ω) = ((b : Ω) * ((ψ g : ↥S) : Ω) * (b : Ω)⁻¹) * (b : Ω) := by
        group
    _ = ((ψ g : ↥S) : Ω) * (b : Ω) := by rw [hconj]

theorem lift_diag_mem_B (hcfg : Cfg173 3 S B N D K x)
    (hq : 4 ≤ Nat.card F) (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (ψ : Fin Tag.E6.rank → (Matrix.SpecialLinearGroup (Fin 2) F →* ↥S))
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c)
    (i : Fin Tag.E6.rank) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hg : ∃ γ : Fˣ, γ ^ 3 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)]) :
    ((ψ i g : ↥S) : Ω) ∈ B := by
  classical
  obtain ⟨γ, hγ3, hγg⟩ := hg
  have hgdiag : g = sl2Diag γ := eq_sl2Diag_of_diagonal hγg
  have hg3 : g ^ 3 = 1 := by
    rw [hgdiag, ← sl2DiagHom_apply]
    rw [← map_pow, hγ3, map_one]
  set y : Ω := ((ψ i g : ↥S) : Ω) with hydef
  have hy3 : y ^ 3 = 1 := by
    rw [hydef, ← Subgroup.coe_pow, ← map_pow, hg3, map_one, Subgroup.coe_one]
  have hcommB : ∀ b ∈ B, (b : Ω) * y = y * (b : Ω) := by
    intro b hb
    have h := commute_lift_of_diag hcfg hq M i (ψ i) (hψ i) hdiag g ⟨γ, hγ3, hγg⟩ b hb
    simpa only [hydef] using h
  have hYea : IsElemAbelian 3 (Subgroup.zpowers y) :=
    CFSG.Open.isElemAbelian_zpowers hy3
  have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute a y from hcommB a ha).zpow_right n |>.eq
  have hBmap := mem_B_map_upper hcfg hq M i (ψ i) (hψ i) hdiag
  have hBnorm : B ≤ Subgroup.normalizer (upperLift (S := S) (ψ i) : Set Ω) :=
    le_normalizer_upper_of_mem_B hBmap
  have hYnorm : y ∈ Subgroup.normalizer (upperLift (S := S) (ψ i) : Set Ω) := by
    have h := mem_normalizer_upper_lift hcfg hq M i (ψ i) (hψ i) hdiag (γ := γ) hgdiag
    simpa only [hydef] using h
  have hEN : B ⊔ Subgroup.zpowers y ≤
      Subgroup.normalizer (upperLift (S := S) (ψ i) : Set Ω) :=
    sup_le hBnorm (Subgroup.zpowers_le.mpr hYnorm)
  have hEea : IsElemAbelian 3 (B ⊔ Subgroup.zpowers y) :=
    IsElemAbelian.sup_of_commute hcfg.elem hYea hcomm
  have hU2 : IsPGroup 2 (upperLift (S := S) (ψ i)) := isPGroup_upperLift (ψ i)
  have hUne : upperLift (S := S) (ψ i) ≠ ⊥ :=
    upperLift_ne_bot (injective_lift M i (ψ i) (hψ i))
  have hEq : B ⊔ Subgroup.zpowers y = B :=
    GLAIsBmax.eq_of_le Nat.prime_three hcfg.bmax le_sup_left hEea hUne hU2 hEN
  have hyB : y ∈ B := by
    have h : y ∈ B ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rwa [hEq] at h
  simpa only [hydef] using hyB

theorem e6TorusThree_le_barB (hcfg : Cfg173 3 S B N D K x)
    (hq : 4 ≤ Nat.card F) (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c)
    {ζ : Fˣ} (hζ : orderOf ζ = 3) : e6TorusThree F ζ ≤ M.barB := by
  classical
  choose ψ hψ using fun i => exists_rootSL2_lift (F := F) hq M hZ i
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hgHSL : ∃ γ : Fˣ, γ ^ 3 = 1 ∧
      ((HSL ζ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)] := by
    refine ⟨ζ, hζ3, ?_⟩
    rw [coe_HSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal]
  have hgen : ∀ i, torusElt Tag.E6 F i ζ ∈ M.barB := by
    intro i
    have hmemB : ((ψ i (HSL ζ) : ↥S) : Ω) ∈ B :=
      lift_diag_mem_B hcfg hq M ψ hψ hdiag i (HSL ζ) hgHSL
    have hbar : ((M.β ⟨((ψ i (HSL ζ) : ↥S) : Ω), hmemB⟩ : ↥(hatGroup Tag.E6 F)) :
        ModGL Tag.E6 F) ∈ M.barB :=
      Subgroup.mem_map_of_mem (hatGroup Tag.E6 F).subtype
        ⟨⟨((ψ i (HSL ζ) : ↥S) : Ω), hmemB⟩, rfl⟩
    have hcoe := S172DModel.coe_β_eq_coe_π M (b := ⟨_, hmemB⟩) (s := ψ i (HSL ζ)) rfl
    rw [hcoe, hψ i (HSL ζ), simpleRootSL2_HSL] at hbar
    exact hbar
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact hgen i

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
