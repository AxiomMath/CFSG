module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYBruhat
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUCorner
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUCover
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TFrame
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeUnique

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.RCKK1IIISU
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.SeitzReduction.E6Pilot (rootProd)
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.RankThree.Classical2 (statedSUToSL)
open CFSG.StandardType.RCKC1 (FourAt CoreCommAt ShortAt rckSU_exists_conj_suV_of_cover)


section Pair

variable {L : Type} [Field L]

theorem yAS_eq_pinnedX : yAS L = pinnedX .E7 L yφ 1 * pinnedX .E7 L yψ 1 := by
  simp [yAS, yFrame_eq, rootProd]

theorem exists_rootProd_yPsi_eq_pinnedX (a b : L) :
    ∃ c : (Fin Tag.E7.rank → ℤ) → L,
      rootProd .E7 L yPsi c = pinnedX .E7 L yφ a * pinnedX .E7 L yψ b := by
  let c : (Fin Tag.E7.rank → ℤ) → L :=
    fun γ => if γ ∈ yFrame then (if γ = yφ then a else b) else 0
  refine ⟨c, ?_⟩
  have hne : yψ ≠ yφ := yFrame_iform_ne.2.symm
  have hframe : (yFrame.map fun γ => pinnedX .E7 L γ (c γ)).prod =
      pinnedX .E7 L yφ a * pinnedX .E7 L yψ b := by
    simp [yFrame_eq, c, hne]
  have hlow : (yLow.map fun γ => pinnedX .E7 L γ (c γ)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
    have hc : c γ = 0 := by
      simp only [c]
      exact if_neg (yLowHigh_not_mem_yFrame.1 γ hγ)
    rw [hc, pinnedX_zero]
  have hhigh : (yHigh.map fun γ => pinnedX .E7 L γ (c γ)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
    have hc : c γ = 0 := by
      simp only [c]
      exact if_neg (yLowHigh_not_mem_yFrame.2 γ hγ)
    rw [hc, pinnedX_zero]
  rw [rootProd, yPsi, List.append_assoc, List.map_append, List.prod_append, hframe,
    List.map_append, List.prod_append, hlow, hhigh, mul_one, mul_one]

end Pair


theorem exists_conj_map_suCornerSL_eq_pinnedX {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}
    (hν : 4 ≤ ν) {ψ : SL(ν, L) →* ModGL .E7 L} {σ : Fin ν → Fin ν → Fin Tag.E7.rank → ℤ}
    (hψ : IsSLFrame ψ σ) {α β : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (hαβ : iform α β = 0) :
    ∃ x ∈ adjointGroup .E7 L, ∀ a b : L,
      x * ψ (suCornerSL hν a b) * x⁻¹ = pinnedX .E7 L α a * pinnedX .E7 L β b := by
  have h01 : sI0 hν ≠ Fin.rev (sI1 hν) := by
    simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega
  have h02 : sI0 hν ≠ sI1 hν := by simp [sI0, sI1]
  have h03 : sI0 hν ≠ Fin.rev (sI0 hν) := by
    simp [sI0, Fin.ext_iff, Fin.val_rev]; omega
  have h12 : Fin.rev (sI1 hν) ≠ sI1 hν := by
    simp [sI1, Fin.ext_iff, Fin.val_rev]; omega
  have h13 : Fin.rev (sI1 hν) ≠ Fin.rev (sI0 hν) := by
    simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega
  have h23 : sI1 hν ≠ Fin.rev (sI0 hν) := by
    simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega
  have hσ₀ : IsRoot .E7 (σ (sI0 hν) (Fin.rev (sI1 hν))) := hψ.isRoot _ _ h01
  have hσ₁ : IsRoot .E7 (σ (sI1 hν) (Fin.rev (sI0 hν))) := hψ.isRoot _ _ h23
  have hσ₀₁ : iform (σ (sI0 hν) (Fin.rev (sI1 hν))) (σ (sI1 hν) (Fin.rev (sI0 hν))) = 0 :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T.iform_sigma_disjoint hψ (κ := 1)
      (fun a b hab => by
        rw [mul_one]
        exact CFSG.ClassicalInvolution.ModelFacts.Levi.iform_self_isRoot_E7 (hψ.isRoot a b hab))
      h01 h23 h02 h03 h12 h13
  obtain ⟨w₁, hw₁₀, hw₁₁⟩ := exists_weyl_smul_orthPair hσ₀ hσ₁ hσ₀₁
  obtain ⟨w₂, hw₂₀, hw₂₁⟩ := exists_weyl_smul_orthPair hα hβ hαβ
  let w₀ : WeylGroup .E7 := w₂ * w₁⁻¹
  have hw₀₀ : w₀ • σ (sI0 hν) (Fin.rev (sI1 hν)) = α := by
    have h : w₁⁻¹ • σ (sI0 hν) (Fin.rev (sI1 hν)) = highRoot .E7 := by
      rw [← hw₁₀, inv_smul_smul]
    simp only [w₀, mul_smul, h, hw₂₀]
  have hw₀₁ : w₀ • σ (sI1 hν) (Fin.rev (sI0 hν)) = β := by
    have h : w₁⁻¹ • σ (sI1 hν) (Fin.rev (sI0 hν)) =
        (Pi.single 3 1 : Fin Tag.E7.rank → ℤ) := by
      rw [← hw₁₁, inv_smul_smul]
    simp only [w₀, mul_smul, h, hw₂₁]
  let n : ModGL .E7 L := canonicalRep (coxeterSystem .E7) L w₀
  obtain ⟨ε₀, ε₁, hε⟩ := (hψ.transport w₀).exists_map_suCornerSL hν
  have hε' : ∀ a b : L, n * ψ (suCornerSL hν a b) * n⁻¹ =
      pinnedX .E7 L α ((ε₀ : L) * a) * pinnedX .E7 L β ((ε₁ : L) * b) := by
    intro a b
    simpa [n, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hw₀₀, hw₀₁]
      using hε a b
  obtain ⟨D, hD⟩ := exists_conj_suCornerSL (L := L) hν ε₀⁻¹ ε₁⁻¹
  refine ⟨n * ψ D, ?_, fun a b => ?_⟩
  · exact mul_mem (canonicalRep_mem_adjointGroup _ L w₀)
      (hψ.range_le_adjointGroup ⟨D, rfl⟩)
  · calc
      (n * ψ D) * ψ (suCornerSL hν a b) * (n * ψ D)⁻¹
          = n * ψ (D * suCornerSL hν a b * D⁻¹) * n⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            group
      _ = n * ψ (suCornerSL hν (((ε₀⁻¹ : Lˣ) : L) * a)
            (((ε₁⁻¹ : Lˣ) : L) * b)) * n⁻¹ := by
            rw [hD]
      _ = pinnedX .E7 L α ((ε₀ : L) * (((ε₀⁻¹ : Lˣ) : L) * a)) *
            pinnedX .E7 L β ((ε₁ : L) * (((ε₁⁻¹ : Lˣ) : L) * b)) := hε' _ _
      _ = pinnedX .E7 L α a * pinnedX .E7 L β b := by
            have h₀ : (ε₀ : L) * (((ε₀⁻¹ : Lˣ) : L) * a) = a := by
              rw [Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ (Units.ne_zero ε₀)]
            have h₁ : (ε₁ : L) * (((ε₁⁻¹ : Lˣ) : L) * b) = b := by
              rw [Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ (Units.ne_zero ε₁)]
            rw [h₀, h₁]


theorem exists_conj_yAS_of_suCover {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} (hν : 4 ≤ ν)
    {ψ : SL(ν, L) →* ModGL .E7 L} {σ : Fin ν → Fin ν → Fin Tag.E7.rank → ℤ}
    (hψ : IsSLFrame ψ σ) {z : ModGL .E7 L} (hz : z ∈ adjointGroup .E7 L) {K : Subfield L}
    (hK : Nat.card K = 4) {C : Type} [Group C] [Finite C] {J : Subgroup C}
    {ι : C →* ModGL .E7 L} {Φ : StatedSU ν 2 K →* J}
    (hΦ : ∀ s, ι (Φ s) = z * ψ (statedSUToSL K ν 2 s) * z⁻¹) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center (StatedSU ν 2 K)) {V : Subgroup C} {r : C}
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    ∃ x ∈ adjointGroup .E7 L, x * yAS L * x⁻¹ = ι r ∧
      ∀ v ∈ V, ∃ c : (Fin Tag.E7.rank → ℤ) → L, x⁻¹ * ι v * x = rootProd .E7 L yPsi c := by
  obtain ⟨e, κ, P, hP⟩ := exists_statedSU_mulEquiv_SUG (ν := ν) hK
  let ψL : SUG ν →* C := J.subtype.comp (Φ.comp e.symm.toMonoidHom)
  have hrange : ψL.range = J := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨u, rfl⟩
      exact (Φ (e.symm u)).2
    · intro j hj
      obtain ⟨y, hy⟩ := hsurj ⟨j, hj⟩
      exact ⟨e y, by simpa [ψL] using congrArg Subtype.val hy⟩
  have hkerL : ψL.ker ≤ Subgroup.center (SUG ν) := by
    intro u hu
    have hu' : e.symm u ∈ Φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      simpa [ψL] using MonoidHom.mem_ker.1 hu
    have hmap : e (e.symm u) ∈ (Subgroup.center (StatedSU ν 2 K)).map
        e.toMonoidHom := ⟨e.symm u, hker hu', rfl⟩
    rw [show (Subgroup.center (StatedSU ν 2 K)).map e.toMonoidHom =
        Subgroup.center (SUG ν) from Subgroup.map_center_eq e] at hmap
    simpa using hmap
  obtain ⟨g, hr, hV⟩ := rckSU_exists_conj_suV_of_cover hν ψL hrange hkerL hFour hCore hShort
  let S : SUG ν →* SL(ν, L) := (statedSUToSL K ν 2).comp e.symm.toMonoidHom
  have hS_apply : ∀ w : SUG ν,
      ((S w : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        (P : Matrix (Fin ν) (Fin ν) L) *
          ((((w : SUG ν) : GL (Fin ν) SUF) : Matrix (Fin ν) (Fin ν) SUF).map κ) *
          ((P⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) := by
    intro w
    have h := hP (e.symm w)
    rw [e.apply_symm_apply] at h
    exact h
  have hιψL : ∀ u : SUG ν, ι (ψL u) = z * ψ (S u) * z⁻¹ := by
    intro u
    simpa [ψL, S] using hΦ (e.symm u)
  have hkey : ∀ (w : SUG ν) (a b : SUF),
      (((w : SUG ν) : GL (Fin ν) SUF) : Matrix (Fin ν) (Fin ν) SUF) =
        1 + single (sI0 hν) (Fin.rev (sI1 hν)) a + single (sI1 hν) (Fin.rev (sI0 hν)) b →
      S w = P * suCornerSL hν (κ a) (κ b) * P⁻¹ := by
    intro w a b hw
    apply Subtype.ext
    rw [hS_apply w, hw, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.map_add κ (map_add κ),
      Matrix.map_one κ (map_zero κ) (map_one κ), Matrix.map_single, coe_suCornerSL]
  have hιr : ι r = z * (ψ (S g * P) * ψ (suCornerSL hν 1 1) * (ψ (S g * P))⁻¹) * z⁻¹ := by
    rw [hr, hιψL (g * suR hν * g⁻¹)]
    simp only [map_mul, map_inv, map_one, hkey (suR hν) 1 1 (coe_suR hν)]
    group
  obtain ⟨x₀, hx₀, hpos⟩ := exists_conj_map_suCornerSL_eq_pinnedX hν hψ
    (isRoot_of_mem_yPsi (mem_yPsi_of_mem_yFrame (by simp [yFrame_eq])))
    (isRoot_of_mem_yPsi (mem_yPsi_of_mem_yFrame (by simp [yFrame_eq]))) yFrame_iform_ne.1
  refine ⟨z * ψ (S g * P) * x₀⁻¹, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem hz (hψ.range_le_adjointGroup ⟨S g * P, rfl⟩)) (inv_mem hx₀)
  · have hx1 : x₀⁻¹ * yAS L * x₀ = ψ (suCornerSL hν 1 1) := by
      rw [yAS_eq_pinnedX, ← hpos 1 1]
      group
    calc
      (z * ψ (S g * P) * x₀⁻¹) * yAS L * (z * ψ (S g * P) * x₀⁻¹)⁻¹
          = (z * ψ (S g * P)) * (x₀⁻¹ * yAS L * x₀) * (z * ψ (S g * P))⁻¹ := by group
      _ = z * (ψ (S g * P) * ψ (suCornerSL hν 1 1) * (ψ (S g * P))⁻¹) * z⁻¹ := by
            rw [hx1]; group
      _ = ι r := hιr.symm
  · intro v hv
    rw [hV] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨a, ha⟩ := exists_coe_eq_of_mem_suV hν hu
    obtain ⟨c, hc⟩ := exists_rootProd_yPsi_eq_pinnedX (κ a) (κ (SUσ a))
    refine ⟨c, ?_⟩
    have hu' : (ψL.comp (MulAut.conj g).toMonoidHom) u = ψL (g * u * g⁻¹) := rfl
    rw [hu', hιψL, hc, ← hpos]
    simp only [map_mul, map_inv, hkey u a (SUσ a) ha]
    group

end CFSG.SeitzReduction.E7Pilot

end
