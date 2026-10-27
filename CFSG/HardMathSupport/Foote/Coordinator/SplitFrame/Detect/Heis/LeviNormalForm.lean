module

public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

set_option linter.unusedSectionVars false


variable (τ : Tag) (K : Type) [Field K]

section Helpers

variable {τ K}

theorem smul_highRoot_of_mem_parabolicWeylGroup_Jθ {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ (Jθ τ)) : w • highRoot τ = highRoot τ := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [simple_smul]
    exact reflect_highRoot_of_ne τ j hj
  | one => exact one_smul _ _
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff]; exact hx.symm

theorem exists_normalForm_of_mem_parabolicLevi {J : Set (Fin τ.rank)} {l : ModGL τ K}
    (hl : l ∈ parabolicLevi τ K J) :
    ∃ w ∈ parabolicWeylGroup τ J, ∃ h ∈ torusGroup τ K, ∃ u ∈ parabolicLeviUnipotent τ K J,
      ∃ v ∈ rootSpan τ K (inversionSet w),
        l = h * u * canonicalRep (coxeterSystem τ) K w * v := by
  obtain ⟨w, h, hh, u, hu, v, hv, hlw⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.bruhat_factor_exists τ K l
      (parabolicLevi_le_adjointGroup τ K J hl)
  have hvU : v ∈ posUnipotent τ K :=
    rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα) hv
  have hw : w ∈ parabolicWeylGroup τ J := by
    have hP : l ∈ (parabolicSubgroup τ K J : Set (ModGL τ K)) :=
      parabolicLevi_le_parabolicSubgroup J hl
    rw [(standard_parabolic_cells τ K).1 J] at hP
    obtain ⟨w', hw', hcell⟩ := Set.mem_iUnion₂.1 hP
    have hcell' : l ∈ bruhatCell τ K w :=
      mem_bruhatCell.2 ⟨h * u, mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu), v,
        Subgroup.mem_sup_right hvU, hlw.symm⟩
    by_cases hww : w' = w
    · exact hww ▸ hw'
    · exact absurd hcell' (Set.disjoint_left.1 ((standard_parabolic_cells τ K).2.1 w' w hww) hcell)
  have hinv : inversionSet w ⊆ parabolicPosRoots τ J := inversionSet_subset_parabolicPosRoots hw
  have hu' : u ∈ (posUnipotent τ K : Set (ModGL τ K)) := hu
  rw [posUnipotent_eq_mul_parabolic J] at hu'
  obtain ⟨q, hq, v', hv', rfl⟩ := hu'
  have hhq : h * q * h⁻¹ ∈ parabolicRadical τ K J :=
    (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (fun _ hα => hα.1.1) hh) q).1 hq
  have hm : h * v' * canonicalRep (coxeterSystem τ) K w * v ∈ parabolicLevi τ K J :=
    mul_mem (mul_mem (mul_mem (torusGroup_le_parabolicLevi J hh)
      (parabolicLeviUnipotent_le_parabolicLevi J hv')) (canonicalRep_mem_parabolicLevi hw))
      (parabolicLeviUnipotent_le_parabolicLevi J (rootSpan_mono hinv hv))
  have hlq : (h * q * h⁻¹) * (h * v' * canonicalRep (coxeterSystem τ) K w * v) = 1 * l := by
    rw [one_mul, hlw]
    group
  obtain ⟨hq1, -⟩ := eq_of_mul_eq_of_parabolic hhq (one_mem _) hm hl hlq
  have hq1' : q = 1 := by
    calc q = h⁻¹ * (h * q * h⁻¹) * h := by group
      _ = 1 := by rw [hq1]; group
  subst hq1'
  exact ⟨w, hw, h, hh, v', hv', v, hv, by rw [hlw]; group⟩

theorem exists_canonicalRep_conj_eq_torus_mul (w₀ w' : WeylGroup τ) :
    ∃ k ∈ torusGroup τ K,
      canonicalRep (coxeterSystem τ) K w₀ * canonicalRep (coxeterSystem τ) K w' *
          (canonicalRep (coxeterSystem τ) K w₀)⁻¹ =
        k * canonicalRep (coxeterSystem τ) K (w₀ * w' * w₀⁻¹) := by
  obtain ⟨k₁, hk₁, h₁⟩ := canonicalRep_mul_mem (R := K) w₀ w'
  obtain ⟨k₂, hk₂, h₂⟩ := canonicalRep_mul_mem (R := K) (w₀ * w' * w₀⁻¹) w₀
  rw [inv_mul_cancel_right] at h₂
  refine ⟨k₁ * k₂⁻¹, mul_mem hk₁ (inv_mem hk₂), ?_⟩
  have h₃ : canonicalRep (coxeterSystem τ) K (w₀ * w') =
      k₂⁻¹ * (canonicalRep (coxeterSystem τ) K (w₀ * w' * w₀⁻¹) *
        canonicalRep (coxeterSystem τ) K w₀) := by
    rw [h₂]
    group
  rw [h₁, h₃]
  group

theorem canonicalRep_conj_mem_rootSpan_image (w : WeylGroup τ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ) {x : ModGL τ K} (hx : x ∈ rootSpan τ K S) :
    canonicalRep (coxeterSystem τ) K w * x * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      rootSpan τ K ((fun γ => w • γ) '' S) := by
  have h := Subgroup.mem_map_of_mem
    (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom hx
  rw [CFSG.RankThree.PartOne.KE.map_conj_rootSpan w hS] at h
  exact h

theorem conj_mul_assemble {G : Type*} [Group G] (n h' u' m v' k m₁ : G)
    (hk : n * m * n⁻¹ = k * m₁) :
    n * (h' * u' * m * v') * n⁻¹ =
      (n * h' * n⁻¹ * k) * (k⁻¹ * (n * u' * n⁻¹) * k) * m₁ * (n * v' * n⁻¹) := by
  calc n * (h' * u' * m * v') * n⁻¹
      = (n * h' * n⁻¹) * (n * u' * n⁻¹) * (n * m * n⁻¹) * (n * v' * n⁻¹) := by group
    _ = _ := by rw [hk]; group

end Helpers

theorem normalForm_conj_Lθ {w₀ : WeylGroup τ}
    (hmin : ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height (w₀ • β)) {g : ModGL τ K}
    (hg : g ∈ conjSub (canonicalRep (coxeterSystem τ) K w₀) (Lθ τ K)) :
    ∃ (w : WeylGroup τ) (h u v : ModGL τ K), h ∈ torusGroup τ K ∧
      u ∈ rootSpan τ K ((fun β => w₀ • β) '' parabolicPosRoots τ (Jθ τ)) ∧
      v ∈ rootSpan τ K ((fun β => w₀ • β) '' parabolicPosRoots τ (Jθ τ) ∩ inversionSet w) ∧
      w • (w₀ • highRoot τ) = w₀ • highRoot τ ∧
      g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
  rw [mem_conjSub_iff] at hg
  obtain ⟨w', hw', h', hh', u', hu', v', hv', hl⟩ := exists_normalForm_of_mem_parabolicLevi hg
  obtain ⟨k, hk, hkeq⟩ := exists_canonicalRep_conj_eq_torus_mul (K := K) w₀ w'
  have hinv : inversionSet w' ⊆ parabolicPosRoots τ (Jθ τ) :=
    inversionSet_subset_parabolicPosRoots hw'
  have hrootsJ : ∀ γ ∈ parabolicPosRoots τ (Jθ τ), IsRoot τ γ := fun γ hγ => hγ.1.1
  have hu₁ := canonicalRep_conj_mem_rootSpan_image w₀ hrootsJ hu'
  have hv₁ := canonicalRep_conj_mem_rootSpan_image w₀ (fun γ hγ => hrootsJ γ (hinv hγ)) hv'
  have hconj : ∀ x : Fin τ.rank → ℤ, (w₀ * w' * w₀⁻¹) • (w₀ • x) = w₀ • (w' • x) := fun x => by
    rw [mul_smul, inv_smul_smul, mul_smul]
  have hneg : ∀ α ∈ inversionSet w', height (w₀ • w' • α) < 0 := by
    intro α hα
    have hαJ := hinv hα
    have hJ : -(w' • α) ∈ parabolicPosRoots τ (Jθ τ) :=
      mem_parabolicPosRoots_of (neg_mem_parabolicRoots (smul_mem_parabolicRoots hw' hαJ.1))
        (by rw [height_neg]; have := hα.2.2.2; omega)
    have h1 := hmin _ hJ
    rwa [smul_neg, height_neg, Left.neg_pos_iff] at h1
  refine ⟨w₀ * w' * w₀⁻¹, canonicalRep (coxeterSystem τ) K w₀ * h' *
      (canonicalRep (coxeterSystem τ) K w₀)⁻¹ * k,
    k⁻¹ * (canonicalRep (coxeterSystem τ) K w₀ * u' * (canonicalRep (coxeterSystem τ) K w₀)⁻¹) * k,
    canonicalRep (coxeterSystem τ) K w₀ * v' * (canonicalRep (coxeterSystem τ) K w₀)⁻¹,
    mul_mem ((Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w₀) h').1 hh')
      hk, ?_, ?_, ?_, ?_⟩
  ·
    have hN := (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (K := K)
        (S := (fun β => w₀ • β) '' parabolicPosRoots τ (Jθ τ))
        (by rintro _ ⟨β, hβ, rfl⟩; exact IsRoot.smul (hrootsJ β hβ) w₀) (inv_mem hk)) _).1 hu₁
    rwa [inv_inv] at hN
  ·
    refine rootSpan_mono ?_ hv₁
    rintro _ ⟨α, hα, rfl⟩
    have hαJ := hinv hα
    refine ⟨⟨α, hαJ, rfl⟩, IsRoot.smul (hrootsJ α hαJ) w₀, hmin α hαJ,
      IsRoot.smul (IsRoot.smul (hrootsJ α hαJ) w₀) _, ?_⟩
    change height ((w₀ * w' * w₀⁻¹) • (w₀ • α)) < 0
    rw [hconj]
    exact hneg α hα
  · rw [hconj, smul_highRoot_of_mem_parabolicWeylGroup_Jθ hw']
  · calc g = canonicalRep (coxeterSystem τ) K w₀ * ((canonicalRep (coxeterSystem τ) K w₀)⁻¹ * g *
          canonicalRep (coxeterSystem τ) K w₀) * (canonicalRep (coxeterSystem τ) K w₀)⁻¹ := by
          group
      _ = canonicalRep (coxeterSystem τ) K w₀ * (h' * u' * canonicalRep (coxeterSystem τ) K w' *
          v') * (canonicalRep (coxeterSystem τ) K w₀)⁻¹ := by rw [hl]
      _ = _ := conj_mul_assemble _ _ _ _ _ _ _ hkeq

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
