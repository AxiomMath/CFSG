module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.GenerationEven
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.CubeTorsionRoots

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley

variable {L : Type} [Field L]

theorem exists_conj_rootDiagUnit {n : ModGL .G2 L} (hn : n ∈ monomialSubgroup .G2 L)
    (a : Fin Tag.G2.rank → Lˣ) :
    ∃ a' : Fin Tag.G2.rank → Lˣ, n * rootDiagUnit .G2 a * n⁻¹ = rootDiagUnit .G2 a' ∧
      ∀ γ, IsRoot .G2 γ →
        rootChar a' (weylQuotientHom .G2 L ⟨n, hn⟩ • γ) = rootChar a γ := by
  have hnorm := mem_normalizer_torusGroup_of_mem_monomialSubgroup hn
  have hT : n * rootDiagUnit .G2 a * n⁻¹ ∈ torusGroup .G2 L :=
    (Subgroup.mem_normalizer_iff.1 hnorm _).1 (rootDiagUnit_mem_torusGroup_G2 a)
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  refine ⟨a', ha', fun γ hγ => ?_⟩
  obtain ⟨μ, hμ⟩ := mapsRootLines_weylQuotientHom (τ := .G2) (R := L) ⟨n, hn⟩ γ hγ
  have hcomm : n * rootDiagUnit .G2 a = rootDiagUnit .G2 a' * n := by
    rw [← ha', mul_assoc, inv_mul_cancel, mul_one]
  have hwγ : IsRoot .G2 (weylQuotientHom .G2 L ⟨n, hn⟩ • γ) := IsRoot.smul hγ _
  have hne : rootVec .G2 L (weylQuotientHom .G2 L ⟨n, hn⟩ • γ) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hwγ]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h1 := congrArg (fun g : ModGL .G2 L =>
    (g : Module.End L (RootModule .G2 L)) (rootVec .G2 L γ)) hcomm
  simp only [Units.val_mul, Module.End.mul_apply] at h1
  have hd : ∀ b : Fin Tag.G2.rank → Lˣ, ∀ δ, IsRoot .G2 δ →
      (rootDiagUnit .G2 b : Module.End L (RootModule .G2 L)) (rootVec .G2 L δ) =
        ((rootChar b δ : Lˣ) : L) • rootVec .G2 L δ := fun b δ hδ =>
    rootDiag_rootVec b hδ
  rw [hd a γ hγ, map_smul, hμ, map_smul, hd a' _ hwγ] at h1
  simp only [smul_smul] at h1
  have h2 := smul_left_injective L hne h1
  have h3 : ((rootChar a' (weylQuotientHom .G2 L ⟨n, hn⟩ • γ) : Lˣ) : L) =
      ((rootChar a γ : Lˣ) : L) :=
    mul_left_cancel₀ μ.ne_zero (h2.symm.trans (mul_comm _ _))
  exact Units.ext h3

@[expose] def cubeAct (i j : ℤ) : ℤ × ℤ :=
  (cubeExp i j (rho (rho (vec 1 0))), cubeExp i j (rho (rho (vec 0 1))))

@[expose] def toFin3 (x : ℤ) : Fin 3 :=
  ⟨(x % 3).toNat, by
    have h1 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 3)
    have h2 := Int.emod_nonneg x (by norm_num : (3 : ℤ) ≠ 0)
    omega⟩

theorem cubeAct_eq : ∀ i j : Fin 3,
    (toFin3 (cubeAct i.val j.val).1, toFin3 (cubeAct i.val j.val).2) = (i, i + j) := by
  decide

theorem toFin3_val (x : ℤ) : ((toFin3 x).val : ℤ) = x % 3 := by
  simp only [toFin3]
  have h2 := Int.emod_nonneg x (by norm_num : (3 : ℤ) ≠ 0)
  omega

theorem cubeTuple_eq_cubeTuple3 {ζ : Lˣ} (hζ : orderOf ζ = 3) (x y : ℤ) :
    cubeTuple ζ x y = cubeTuple3 ζ (toFin3 x) (toFin3 y) := by
  have h : ∀ z : ℤ, ζ ^ z = ζ ^ ((toFin3 z).val : ℤ) := fun z => by
    rw [toFin3_val, ← zpow_mod_orderOf, hζ]
    norm_num
  rw [cubeTuple3]
  unfold cubeTuple
  rw [h x, h y]

theorem rootChar_single' (a : Fin Tag.G2.rank → Lˣ) (k : Fin Tag.G2.rank) :
    rootChar a (Pi.single k 1 : Fin Tag.G2.rank → ℤ) = a k := by
  rw [rootChar, Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem rho_rho_rho_vec10 : rho (rho (rho (vec 1 0))) = vec 1 0 := by decide

theorem rho_rho_rho_vec01 : rho (rho (rho (vec 0 1))) = vec 0 1 := by decide

theorem rho_rho_mem_rootList : rho (rho (vec 1 0)) ∈ rootList ∧ rho (rho (vec 0 1)) ∈ rootList := by
  decide

theorem conj_cubeTuple3 {ζ : Lˣ} (hζ : orderOf ζ = 3) {n : ModGL .G2 L}
    (hn : n ∈ monomialSubgroup .G2 L) (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = rho0)
    (i j : Fin 3) :
    n * rootDiagUnit .G2 (cubeTuple3 ζ i j) * n⁻¹ =
      rootDiagUnit .G2 (cubeTuple3 ζ i (i + j)) := by
  obtain ⟨a', h, hchar⟩ := exists_conj_rootDiagUnit hn (cubeTuple3 ζ i j)
  rw [h]
  congr 1
  have e0 : (vec 1 0 : Fin Tag.G2.rank → ℤ) = Pi.single ⟨0, by decide⟩ 1 := by
    funext k; fin_cases k <;> rfl
  have e1 : (vec 0 1 : Fin Tag.G2.rank → ℤ) = Pi.single ⟨1, by decide⟩ 1 := by
    funext k; fin_cases k <;> rfl
  have hr0 : IsRoot .G2 (rho (rho (vec 1 0))) := isRoot_of_mem_rootList rho_rho_mem_rootList.1
  have hr1 : IsRoot .G2 (rho (rho (vec 0 1))) := isRoot_of_mem_rootList rho_rho_mem_rootList.2
  have h0 := hchar _ hr0
  have h1 := hchar _ hr1
  have c0 : rootChar a' (vec 1 0) = a' ⟨0, by decide⟩ := by rw [e0, rootChar_single']
  have c1 : rootChar a' (vec 0 1) = a' ⟨1, by decide⟩ := by rw [e1, rootChar_single']
  rw [hw, rho0_smul, rho_rho_rho_vec10, c0] at h0
  rw [hw, rho0_smul, rho_rho_rho_vec01, c1] at h1
  have hfun : a' = cubeTuple ζ (cubeAct i.val j.val).1 (cubeAct i.val j.val).2 := by
    funext k
    fin_cases k
    · show a' ⟨0, _⟩ = _
      rw [h0, cubeTuple3, rootChar_cubeTuple]
      rfl
    · show a' ⟨1, _⟩ = _
      rw [h1, cubeTuple3, rootChar_cubeTuple]
      rfl
  rw [hfun, cubeTuple_eq_cubeTuple3 hζ]
  have := cubeAct_eq i j
  rw [Prod.mk.injEq] at this
  rw [this.1, this.2]

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
