module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllBasic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllDef

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Nu

variable {L : Type} [Field L]

def ellNuA (L : Type) [Field L] : ModGL TwistTag.D4.tag L :=
  mpRho0 L (mpN01 L) * mpRho0 L (mpN12 L)

theorem ellNuA_mem_rootSpan : ellNuA L ∈ rootSpan TwistTag.D4.tag L d4LongA2 := by
  have h : mpRho0 L (mpN01 L * mpN12 L) ∈ (mpRho0 L).range := ⟨_, rfl⟩
  rw [(mp_frame0 L).range, mp_sigma0_set] at h
  rwa [map_mul] at h

theorem ellNuA_weyl :
    ∃ hm : ellNuA L ∈ monomialSubgroup TwistTag.D4.tag L,
      ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ellNuA L, hm⟩ • x = d4MatThreeA *ᵥ x := by
  obtain ⟨m1, i1⟩ := mp_image_N01 L
  obtain ⟨m2, i2⟩ := mp_image_N12 L
  refine ⟨mul_mem m1 m2, fun x => ?_⟩
  have e : (⟨ellNuA L, mul_mem m1 m2⟩ : monomialSubgroup TwistTag.D4.tag L) =
      ⟨_, m1⟩ * ⟨_, m2⟩ := rfl
  rw [e, map_mul, i1, i2]
  exact mp_rot_A x

theorem exists_nu {M : D4Mat} (hM : M = d4MatThreeA ∨ M = d4MatThreeB) :
    ∃ ν ∈ rootSpan TwistTag.D4.tag L d4LongA2, ∃ hν : ν ∈ monomialSubgroup TwistTag.D4.tag L,
      ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ν, hν⟩ • x = M *ᵥ x := by
  obtain ⟨hm, hw⟩ := ellNuA_weyl (L := L)
  rcases hM with rfl | rfl
  · exact ⟨ellNuA L, ellNuA_mem_rootSpan, hm, hw⟩
  · refine ⟨(ellNuA L)⁻¹, inv_mem ellNuA_mem_rootSpan, inv_mem hm, fun x => ?_⟩
    have e : (⟨(ellNuA L)⁻¹, inv_mem hm⟩ : monomialSubgroup TwistTag.D4.tag L) =
        ⟨ellNuA L, hm⟩⁻¹ := rfl
    rw [e, map_inv]
    exact weyl_inv_smul_mulVec d4MatThree_mul hw x

end Nu

section Regular

variable {L : Type} [Field L]

theorem ell_cube_roots_aux (e y : Lˣ) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (h2 : y * e ≠ 1)
    (h2' : (y * e) ^ 3 = 1) (h3 : y * e ^ 2 ≠ 1) : y = 1 := by
  have hx3 : (e : L) ^ 3 = 1 := by simpa [Units.val_pow_eq_pow_val] using congrArg Units.val he3
  have hx1 : (e : L) ≠ 1 := fun h => he1 (Units.ext h)
  have hy3 : (y : L) ^ 3 = 1 := by
    have h := congrArg Units.val h2'
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one, mul_pow, hx3, mul_one] at h
    exact h
  have h2v : (y : L) * e ≠ 1 := fun h => h2 (Units.ext (by simpa using h))
  have h3v : (y : L) * (e : L) ^ 2 ≠ 1 := fun h => h3 (Units.ext (by simpa using h))
  by_contra hy1
  have hy1' : (y : L) ≠ 1 := fun h => hy1 (Units.ext h)
  have hxq : (e : L) ^ 2 + e + 1 = 0 := by
    have : ((e : L) - 1) * ((e : L) ^ 2 + e + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hx1
    · exact h
  have hyq : (y : L) ^ 2 + y + 1 = 0 := by
    have : ((y : L) - 1) * ((y : L) ^ 2 + y + 1) = 0 := by linear_combination hy3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hy1'
    · exact h
  have hprod : ((y : L) - e) * ((y : L) - e ^ 2) = 0 := by
    linear_combination hyq - (y : L) * hxq + hx3
  rcases mul_eq_zero.1 hprod with h | h
  · apply h3v
    have hyx : (y : L) = e := sub_eq_zero.1 h
    rw [hyx]
    linear_combination hx3
  · apply h2v
    have hyx : (y : L) = (e : L) ^ 2 := sub_eq_zero.1 h
    rw [hyx]
    linear_combination hx3

theorem ell_regular_aux (a0 a1 a2 a3 : Lˣ) (h1 : a2 ≠ 1 ∧ a2 ^ 3 = 1)
    (h2 : a0 * a1 * a2 * a3 ≠ 1 ∧ (a0 * a1 * a2 * a3) ^ 3 = 1)
    (h3 : a0 * a1 * a2 ^ 2 * a3 ≠ 1 ∧ (a0 * a1 * a2 ^ 2 * a3) ^ 3 = 1) :
    a2 ^ 3 = 1 ∧ a2 ≠ 1 ∧ a0 * a1 * a3 = 1 := by
  have e2 : a0 * a1 * a2 * a3 = (a0 * a1 * a3) * a2 := mul_right_comm _ _ _
  have e3 : a0 * a1 * a2 ^ 2 * a3 = (a0 * a1 * a3) * a2 ^ 2 := mul_right_comm _ _ _
  rw [e2] at h2
  rw [e3] at h3
  exact ⟨h1.2, h1.1, ell_cube_roots_aux a2 _ h1.2 h1.1 h2.1 h2.2 h3.1⟩

theorem ell_regular_data {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hreg : ∀ α ∈ d4LongA2, rootChar a α ≠ 1 ∧ rootChar a α ^ 3 = 1) :
    a 2 ^ 3 = 1 ∧ a 2 ≠ 1 ∧ a 0 * a 1 * a 3 = 1 := by
  have h1 := hreg (d4LongVec 0 1) (by rw [d4LongA2_eq]; simp)
  have h2 := hreg (d4LongVec 1 1) (by rw [d4LongA2_eq]; simp)
  have h3 := hreg (d4LongVec 1 2) (by rw [d4LongA2_eq]; simp)
  rw [rootChar_d4_apply] at h1 h2 h3
  simp [d4LongVec] at h1 h2 h3
  exact ell_regular_aux (a 0) (a 1) (a 2) (a 3) h1 h2 h3

end Regular

section Torus2

variable {L : Type} [Field L] [IsAlgClosed L]

theorem torus_normalize_two {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha : a 0 * a 1 * a 3 = 1) :
    ∃ u ∈ torusGroup TwistTag.D4.tag L,
      u * (rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L)⁻¹) * u⁻¹ =
        rotElt (a 2) := by
  set v : Fin TwistTag.D4.tag.rank → Lˣ := ![1, a 0, 1, a 0 * a 1] with hv
  refine ⟨rootDiagUnit TwistTag.D4.tag v, rootDiagUnit_mem_torusGroup v, ?_⟩
  have h1 : (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag v⁻¹ =
      rootDiagUnit TwistTag.D4.tag (fun i => v⁻¹ (TwistTag.D4.perm i)) *
        (diagramMap TwistTag.D4 L)⁻¹ := by
    calc (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag v⁻¹ =
        ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag v⁻¹ *
          diagramMap TwistTag.D4 L) * (diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = _ := by rw [d4Minus_h90_conj]
  have h2 : v * a * (fun i => v⁻¹ (TwistTag.D4.perm i)) =
      (![1, 1, a 2, 1] : Fin TwistTag.D4.tag.rank → Lˣ) := by
    funext i
    fin_cases i
    · show (1 : Lˣ) * a 0 * (a 0)⁻¹ = 1
      group
    · show a 0 * a 1 * (a 0 * a 1)⁻¹ = 1
      group
    · show (1 : Lˣ) * a 2 * 1⁻¹ = a 2
      group
    · show (a 0 * a 1) * a 3 * ((1 : Lˣ))⁻¹ = 1
      rw [mul_assoc]
      simpa using ha
  calc rootDiagUnit TwistTag.D4.tag v * (rootDiagUnit TwistTag.D4.tag a *
        (diagramMap TwistTag.D4 L)⁻¹) * (rootDiagUnit TwistTag.D4.tag v)⁻¹
      = rootDiagUnit TwistTag.D4.tag v * rootDiagUnit TwistTag.D4.tag a *
        ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag v⁻¹) := by
        rw [rootDiagUnit_inv]; group
    _ = rootDiagUnit TwistTag.D4.tag (v * a * (fun i => v⁻¹ (TwistTag.D4.perm i))) *
        (diagramMap TwistTag.D4 L)⁻¹ := by
        rw [h1, rootDiagUnit_mul, rootDiagUnit_mul]; group
    _ = rotElt (a 2) := by rw [h2]; rfl

end Torus2

section Geometric

variable {L : Type} [Field L] [IsAlgClosed L]

theorem ell_det_A : (d4PermMat * d4MatThreeA - 1 : D4Mat).det ≠ 0 := by decide +kernel

theorem ell_det_B : (d4PermMat * d4MatThreeB - 1 : D4Mat).det ≠ 0 := by decide +kernel

theorem mem_torus_of_weyl_eq_one {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ monomialSubgroup TwistTag.D4.tag L)
    (h : weylQuotientHom TwistTag.D4.tag L ⟨g, hg⟩ = 1) : g ∈ torusGroup TwistTag.D4.tag L := by
  have := canonicalRep_mul_inv_mem_torusGroup hg 1 h
  rw [canonicalRep_one, one_mul] at this
  simpa using inv_mem this

theorem diagramMap_pow_three : (diagramMap TwistTag.D4 L) ^ 3 = 1 :=
  diagramMap_pow_order TwistTag.D4 L

theorem ell_geometric_conj_of_rot {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    {M Mi : D4Mat} (hMMi : M * Mi = 1) (hM : M = d4MatThreeA ∨ M = d4MatThreeB)
    (hMn : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = M *ᵥ x)
    (hdet : (d4PermMat * Mi - 1 : D4Mat).det ≠ 0) (hM1 : ∃ x, M *ᵥ x ≠ x)
    (hx3 : (n * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) :
    ∃ b : Lˣ, b ^ 3 = 1 ∧ b ≠ 1 ∧ ∃ h ∈ leviGroup L,
      n * (diagramMap TwistTag.D4 L)⁻¹ = h * rotElt b * h⁻¹ := by
  set P := diagramMap TwistTag.D4 L with hP
  obtain ⟨ν, hνQ, hν, hνM⟩ := exists_nu (L := L) hM
  have hνT : ν ∉ torusGroup TwistTag.D4.tag L := fun h => by
    have h1 := (mp_iff_of_rot hν M hνM hM1).1 h
    obtain ⟨x, hx⟩ := hM1
    apply hx
    rw [← hνM x, h1, one_smul]
  have hweq : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ =
      weylQuotientHom TwistTag.D4.tag L ⟨ν, hν⟩ :=
    ext_single fun j => by rw [hMn, hνM]
  have hk : n * ν⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    refine mem_torus_of_weyl_eq_one (mul_mem hn (inv_mem hν)) ?_
    have e : (⟨n * ν⁻¹, mul_mem hn (inv_mem hν)⟩ : monomialSubgroup TwistTag.D4.tag L) =
        ⟨n, hn⟩ * ⟨ν, hν⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hweq, mul_inv_cancel]
  have hMi : ∀ x, (weylQuotientHom TwistTag.D4.tag L ⟨ν, hν⟩)⁻¹ • x = Mi *ᵥ x :=
    weyl_inv_smul_mulVec hMMi hνM
  obtain ⟨u₁, hu₁, hu₁eq⟩ := torus_normalize hν hMi hdet hk
  rw [inv_mul_cancel_right, ← hP] at hu₁eq
  have hPν : P * ν = ν * P := diagramMap_commute_of_mem_rootSpan hνQ
  have hcomPν : Commute ν P⁻¹ := ((Commute.symm (show Commute P ν from hPν)).inv_right)
  have hν3 : ν ^ 3 = 1 := by
    have h1 : (ν * P⁻¹) ^ 3 = 1 := by
      rw [← hu₁eq, conj_pow, hx3]
      group
    rw [hcomPν.mul_pow, inv_pow, diagramMap_pow_three, inv_one, mul_one] at h1
    exact h1
  have hνC : ν ∈ adjointGroup TwistTag.D4.tag L := rootSpan_le_adjointGroup L d4LongA2 hνQ
  have hcommν : ν * rootDiagUnit TwistTag.D4.tag
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) =
      rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) * ν :=
    Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer (τ := TwistTag.D4.tag)
      (K := L) (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) (S := d4LongA2)
      (fun α hα => (d4Minus_rootCharKernel hA3 hA1 α).2 hα) hνQ)
  obtain ⟨Y, hY, a, hYa, hreg⟩ := d4_toral_conj_A2 hA3 hA1 hν hνC hν3 hνT hcommν
  obtain ⟨ha23, ha21, ha013⟩ := ell_regular_data hreg
  have hPY : P⁻¹ * Y = Y * P⁻¹ := by
    have h : P * Y = Y * P := diagramMap_commute_of_mem_rootSpan hY
    have h2 : Commute Y P⁻¹ := (Commute.symm (show Commute P Y from h)).inv_right
    exact h2.symm.eq
  have hconj2 : Y⁻¹ * (ν * P⁻¹) * Y = rootDiagUnit TwistTag.D4.tag a * P⁻¹ := by
    calc Y⁻¹ * (ν * P⁻¹) * Y = Y⁻¹ * ν * (P⁻¹ * Y) := by group
      _ = (Y⁻¹ * ν * Y) * P⁻¹ := by rw [hPY]; group
      _ = _ := by rw [hYa]
  obtain ⟨u₂, hu₂, hu₂eq⟩ := torus_normalize_two (L := L) ha013
  rw [← hP] at hu₂eq
  have key : rotElt (a 2) = u₂ * Y⁻¹ * u₁ * (n * P⁻¹) * u₁⁻¹ * Y * u₂⁻¹ := by
    rw [← hu₂eq, ← hconj2, ← hu₁eq]
    group
  refine ⟨a 2, ha23, ha21, u₁⁻¹ * Y * u₂⁻¹, ?_, ?_⟩
  · exact mul_mem (mul_mem (torus_le_leviGroup (inv_mem hu₁)) (rootSpan_le_leviGroup hY))
      (torus_le_leviGroup (inv_mem hu₂))
  · rw [key]
    group

theorem ell_geometric_conj {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : n ∉ torusGroup TwistTag.D4.tag L)
    (hw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ ∈ relWeylTwist TwistTag.D4)
    (hx3 : (n * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1) :
    ∃ b : Lˣ, b ^ 3 = 1 ∧ b ≠ 1 ∧ ∃ h ∈ leviGroup L,
      n * (diagramMap TwistTag.D4 L)⁻¹ = h * rotElt b * h⁻¹ := by
  set P := diagramMap TwistTag.D4 L with hP
  have hcyc : n * (P⁻¹ * n * P) * (P⁻¹ * (P⁻¹ * n * P) * P) = 1 := by
    have h1 : n * (P⁻¹ * n * P) * (P⁻¹ * (P⁻¹ * n * P) * P) = (n * P⁻¹) ^ 3 * P ^ 3 := by
      rw [pow_three, pow_three]
      group
    rw [h1, hx3, hP, diagramMap_pow_three, one_mul]
  have hw3 : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ ^ 3 = 1 :=
    d4MnFL_weyl_cube (Q := P) (Or.inl rfl) hw (mapsRootLines_weylQuotientHom ⟨n, hn⟩) hcyc
  obtain ⟨M, hM, hMn⟩ := d4_relWeylTwist_order_three_smul hw hw3
  rcases hM with rfl | rfl | rfl
  · exfalso
    apply hnT
    refine mem_torus_of_weyl_eq_one hn (ext_single fun j => ?_)
    rw [hMn, one_smul, Matrix.one_mulVec]
  · exact ell_geometric_conj_of_rot hA3 hA1 hn d4MatThree_mul (Or.inl rfl) hMn ell_det_B
      ⟨Pi.single 0 1, by decide +kernel⟩ hx3
  · exact ell_geometric_conj_of_rot hA3 hA1 hn d4MatThree_mul' (Or.inr rfl) hMn ell_det_A
      ⟨Pi.single 0 1, by decide +kernel⟩ hx3

end Geometric

end CFSG.HardMathSupport.Lang.E6Descent
