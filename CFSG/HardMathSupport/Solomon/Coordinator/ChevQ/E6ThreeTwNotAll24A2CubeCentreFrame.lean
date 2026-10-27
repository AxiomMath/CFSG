module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace CubeCentre

section Lattice


theorem iform_self_eq_two {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) : iform β β = 2 := by
  obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hβ
  simpa [Tag.symmetrizer] using hj

theorem corootPair_eq_iform {τ : Tag} {x : Fin τ.rank → ℤ} (hx : iform x x = 2)
    (v : Fin τ.rank → ℤ) : CFSG.LieType.Chevalley.corootPair x v = iform x v := by
  rw [CFSG.LieType.Chevalley.corootPair, hx]
  omega

theorem a2Exp_eq_iform {τ : Tag} {γ₁ γ₂ : Fin τ.rank → ℤ} (h₁ : iform γ₁ γ₁ = 2)
    (h₂ : iform γ₂ γ₂ = 2) (j : Fin τ.rank) :
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.a2Exp τ γ₁ γ₂ j =
      iform γ₁ (Pi.single j 1) + 2 * iform γ₂ (Pi.single j 1) := by
  simp only [CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.a2Exp,
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.cop, h₁, h₂]
  omega

theorem chainExp_pair {τ : Tag} {x y : Fin τ.rank → ℤ} (hx : iform x x = 2) (hy : iform y y = 2)
    (j : Fin τ.rank) :
    chainExp ![x, y] 2 j = iform x (Pi.single j 1) + 2 * iform y (Pi.single j 1) := by
  simp only [chainExp, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, corootPair_eq_iform hx, corootPair_eq_iform hy]
  norm_num

theorem exists_sign_three_dvd {τ : Tag} {γ₁ γ₂ x y : Fin τ.rank → ℤ}
    (h11 : iform γ₁ γ₁ = 2) (h22 : iform γ₂ γ₂ = 2) (h12 : iform γ₁ γ₂ = -1)
    (hx : x = γ₁ ∨ x = γ₂ ∨ x = γ₁ + γ₂ ∨ x = -γ₁ ∨ x = -γ₂ ∨ x = -(γ₁ + γ₂))
    (hy : y = γ₁ ∨ y = γ₂ ∨ y = γ₁ + γ₂ ∨ y = -γ₁ ∨ y = -γ₂ ∨ y = -(γ₁ + γ₂))
    (hxy : iform x y = -1) :
    ∃ η : ℤ, (η = 1 ∨ η = -1) ∧ ∀ v : Fin τ.rank → ℤ,
      (3 : ℤ) ∣ (iform x v + 2 * iform y v) - η * (iform γ₁ v + 2 * iform γ₂ v) := by
  have h21 : iform γ₂ γ₁ = -1 := by rw [iform_comm]; exact h12
  have hnl : ∀ u w : Fin τ.rank → ℤ, iform (-u) w = -iform u w := fun u w => by
    rw [← neg_one_smul ℤ u, iform_smul_left]; ring
  have hnr : ∀ u w : Fin τ.rank → ℤ, iform u (-w) = -iform u w := fun u w => by
    rw [← neg_one_smul ℤ w, iform_smul_right]; ring
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [iform_add_left, iform_add_right, hnl, hnr, h11, h22, h12, h21] at hxy ⊢ <;>
    first
    | omega
    | exact ⟨1, Or.inl rfl, fun v => by omega⟩
    | exact ⟨-1, Or.inr rfl, fun v => by omega⟩

end Lattice

section Group

theorem zpow_congr_mod_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) {m n : ℤ}
    (h : (3 : ℤ) ∣ m - n) : x ^ m = x ^ n := by
  rw [zpow_eq_zpow_emod' m hx, zpow_eq_zpow_emod' n hx]
  congr 1
  push_cast
  omega

variable {L : Type} [Field L]

theorem conjDiag3_scalar (d : Fin 3 → Lˣ) {X : SL(3, L)} {r : L}
    (hX : (X : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) r) :
    CFSG.RankThree.PartOne.KE.conjDiag3Hom d X = X := by
  apply Subtype.ext
  rw [CFSG.RankThree.PartOne.KE.conjDiag3Hom_apply, CFSG.RankThree.PartOne.KE.coe_conjDiag3, hX,
    ← (Matrix.scalar_commute r (fun r' => Commute.all r r')
      ((CFSG.RankThree.PartOne.KE.diagGL3 d : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).eq,
    Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

end Group

section Frame


theorem rootDiagUnit_zpow {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (n : ℤ) :
    rootDiagUnit Tag.E6 (a ^ n) = rootDiagUnit Tag.E6 a ^ n :=
  map_zpow (CFSG.LieType.Chevalley.rootDiagUnitHom Tag.E6 L) a n

theorem exists_normalized_slFrame {τ : Tag} {L : Type} [Field L] {ρ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h : IsSLFrame ρ σ) :
    ∃ d : Fin 3 → Lˣ,
      (ρ.comp (CFSG.RankThree.PartOne.KE.conjDiag3Hom d)).comp
          (CFSG.ClassicalInvolution.WeakCT.blockSL L 3 2 0 (by omega)) = rootSL2 τ L (σ 0 1) ∧
        (ρ.comp (CFSG.RankThree.PartOne.KE.conjDiag3Hom d)).comp
          (CFSG.ClassicalInvolution.WeakCT.blockSL L 3 2 1 (by omega)) = rootSL2 τ L (σ 1 2) := by
  obtain ⟨e01, h01⟩ := h.transv 0 1 (by decide)
  obtain ⟨e10, h10⟩ := h.transv 1 0 (by decide)
  obtain ⟨e12, h12⟩ := h.transv 1 2 (by decide)
  obtain ⟨e21, h21⟩ := h.transv 2 1 (by decide)
  obtain ⟨s0, hs0⟩ := exists_comp_conjSL_eq_rootSL2 (h.isRoot 0 1 (by decide))
    (ρ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL L 3 2 0 (by omega))) e01 e10
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk0_uSL, h01])
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk0_vSL, h10, h.neg])
  obtain ⟨s1, hs1⟩ := exists_comp_conjSL_eq_rootSL2 (h.isRoot 1 2 (by decide))
    (ρ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL L 3 2 1 (by omega))) e12 e21
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk1_uSL, h12])
    (fun t => by rw [MonoidHom.comp_apply, CFSG.RankThree.PartOne.KA5L.blk1_vSL, h21, h.neg])
  set d : Fin 3 → Lˣ := ![s0, 1, s1⁻¹] with hd
  refine ⟨d, ?_, ?_⟩
  · rw [MonoidHom.comp_assoc, conjDiag3_blk0, ← MonoidHom.comp_assoc]
    convert hs0 using 3
    simp [hd]
  · rw [MonoidHom.comp_assoc, conjDiag3_blk1, ← MonoidHom.comp_assoc]
    convert hs1 using 3
    simp [hd]

theorem exists_sign_map_blockTorusProd {L : Type} [Field L] {ψ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {γ₁ γ₂ : Fin Tag.E6.rank → ℤ}
    (hP : CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.IsA2Pair Tag.E6 γ₁ γ₂)
    (hσ : frameRoots σ = {γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)}) :
    ∃ η : ℤ, (η = 1 ∨ η = -1) ∧ ∀ ζ : Lˣ, ζ ^ 3 = 1 →
      ψ (blockTorusProd (m := 2) ζ 2) = rootDiagUnit Tag.E6
        (fun j => ζ ^ (η * CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.a2Exp Tag.E6 γ₁ γ₂ j)) := by
  have h11 : iform γ₁ γ₁ = 2 := iform_self_eq_two hP.1
  have h22 : iform γ₂ γ₂ = 2 := iform_self_eq_two hP.2.1
  have h12 : iform γ₁ γ₂ = -1 := by
    have := hP.2.2.2
    omega
  have hmem : ∀ a b : Fin 3, a ≠ b → (σ a b = γ₁ ∨ σ a b = γ₂ ∨ σ a b = γ₁ + γ₂ ∨
      σ a b = -γ₁ ∨ σ a b = -γ₂ ∨ σ a b = -(γ₁ + γ₂)) := by
    intro a b hab
    have h : σ a b ∈ frameRoots σ := ⟨a, b, hab, rfl⟩
    rw [hσ] at h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hx2 := iform_self_eq_two (hψ.isRoot 0 1 (by decide))
  have hy2 := iform_self_eq_two (hψ.isRoot 1 2 (by decide))
  have hxy : iform (σ 0 1) (σ 1 2) = -1 := by
    have h02 := iform_self_eq_two (hψ.isRoot 0 2 (by decide))
    rw [← hψ.add 0 1 2, iform_add_left, iform_add_right, iform_add_right,
      iform_comm (σ 1 2) (σ 0 1)] at h02
    omega
  obtain ⟨η, hη, hcong⟩ := exists_sign_three_dvd h11 h22 h12 (hmem 0 1 (by decide))
    (hmem 1 2 (by decide)) hxy
  obtain ⟨d, hd0, hd1⟩ := exists_normalized_slFrame hψ
  have hβ : ∀ c, IsRoot Tag.E6 (![σ 0 1, σ 1 2] c) :=
    Fin.forall_fin_two.2 ⟨hψ.isRoot 0 1 (by decide), hψ.isRoot 1 2 (by decide)⟩
  have hθβ : ∀ c, (ψ.comp (CFSG.RankThree.PartOne.KE.conjDiag3Hom d)).comp
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 L 2 c) = rootSL2 Tag.E6 L (![σ 0 1, σ 1 2] c) :=
    Fin.forall_fin_two.2 ⟨hd0, hd1⟩
  refine ⟨η, hη, fun ζ hζ => ?_⟩
  have hfix : CFSG.RankThree.PartOne.KE.conjDiag3Hom d (blockTorusProd (m := 2) ζ 2) =
      blockTorusProd (m := 2) ζ 2 :=
    conjDiag3_scalar d (coe_blockTorusProd_eq_scalar (m := 2) ζ hζ)
  calc ψ (blockTorusProd (m := 2) ζ 2)
      = (ψ.comp (CFSG.RankThree.PartOne.KE.conjDiag3Hom d)) (blockTorusProd (m := 2) ζ 2) := by
        rw [MonoidHom.comp_apply, hfix]
    _ = rootDiagUnit Tag.E6 (fun j => ζ ^ chainExp ![σ 0 1, σ 1 2] 2 j) :=
        chainHom_blockTorusProd hβ hθβ ζ 2 le_rfl
    _ = _ := by
        congr 1
        funext j
        apply zpow_congr_mod_three hζ
        rw [chainExp_pair hx2 hy2, a2Exp_eq_iform h11 h22]
        exact hcong (Pi.single j 1)

end Frame

end CubeCentre

section Centre


theorem map_center_frame_le_zpowers_rootDiagUnit {L : Type} [Field L]
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hi6 : (componentRoots (rootCharHom a) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    (Subgroup.center SL(3, L)).map ψ ≤ Subgroup.zpowers (rootDiagUnit Tag.E6 a) := by
  obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.glue_of_check2
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.noG2_E6 73
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.okE6 (by norm_num)
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.rdCheck2_E6 a ha i hi6
  obtain ⟨η, -, hηψ⟩ := CubeCentre.exists_sign_map_blockTorusProd hψ hP (hΨ.symm.trans hΨeq)
  intro y hy
  obtain ⟨X, hX, rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨r, hr, hrX⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hX
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := fun h => by
    rw [h, zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  set ζ : Lˣ := Units.mk0 r hr0 with hζ
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by simp [hζ, hr])
  have hXQ : X = blockTorusProd (m := 2) ζ 2 :=
    Subtype.ext (hrX.symm.trans (coe_blockTorusProd_eq_scalar (m := 2) ζ hζ3).symm)
  rw [hXQ, hηψ ζ hζ3]
  by_cases hζ1 : ζ = 1
  · have e : (fun j => ζ ^ (η * CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.a2Exp Tag.E6 γ₁ γ₂ j)) =
        1 := by
      funext j
      simp [hζ1]
    rw [e, CFSG.LieType.Chevalley.rootDiagUnit_one]
    exact one_mem _
  · obtain ⟨ε, hε, hglue⟩ := hglueAll ζ hζ3 hζ1
    refine Subgroup.mem_zpowers_iff.2 ⟨ε * η, ?_⟩
    rw [← CubeCentre.rootDiagUnit_zpow]
    congr 1
    funext j
    show a j ^ (ε * η) = _
    rw [hglue j, ← zpow_mul]
    congr 1
    rcases hε with rfl | rfl <;> ring

theorem map_center_frame_eq_zpowers_rootDiagUnit {L : Type} [Field L]
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) (hi6 : (componentRoots (rootCharHom a) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    (Subgroup.center SL(3, L)).map ψ = Subgroup.zpowers (rootDiagUnit Tag.E6 a) := by
  refine le_antisymm (map_center_frame_le_zpowers_rootDiagUnit ha i hi6 hψ hΨ) ?_
  rw [Subgroup.zpowers_le]
  obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.glue_of_check2
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.noG2_E6 73
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.okE6 (by norm_num)
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.RD.rdCheck2_E6 a ha i hi6
  obtain ⟨η, hη, hηψ⟩ := CubeCentre.exists_sign_map_blockTorusProd hψ hP (hΨ.symm.trans hΨeq)
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hcon
    apply h1
    have : a = 1 := funext fun j => Classical.byContradiction fun h => hcon ⟨j, h⟩
    rw [this, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨j0, hj0⟩ := ha1
  obtain ⟨ε, -, hglue⟩ := hglueAll (a j0) (ha j0) hj0
  set ζ : Lˣ := a j0 ^ (ε * η) with hζ
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζ, ← zpow_natCast, ← zpow_mul, mul_comm (ε * η), zpow_mul, zpow_natCast, ha j0,
      one_zpow]
  refine Subgroup.mem_map.2 ⟨blockTorusProd (m := 2) ζ 2,
    Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨(ζ : L), ?_,
      (coe_blockTorusProd_eq_scalar (m := 2) ζ hζ3).symm⟩, ?_⟩
  · rw [Fintype.card_fin, ← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  · rw [hηψ ζ hζ3]
    congr 1
    funext j
    rw [hglue j, hζ, ← zpow_mul]
    congr 1
    rcases hη with rfl | rfl <;> ring

end Centre

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
