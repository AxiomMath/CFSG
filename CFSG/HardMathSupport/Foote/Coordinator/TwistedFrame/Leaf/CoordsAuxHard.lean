module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.LeviNormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

section Field

variable {τ : Tag} {F : Type} [Field F]

private theorem rootSubgroup_le_parabolicLevi_of_mem {J : Set (Fin τ.rank)}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ parabolicRoots τ J) :
    rootSubgroup τ F γ ≤ parabolicLevi τ F J := by
  rcases IsRoot.height_pos_or_neg hγ.1 with hpos | hneg
  · exact (le_iSup₂_of_le γ ⟨hγ, hγ.1, hpos⟩ le_rfl :
      rootSubgroup τ F γ ≤ parabolicLeviUnipotent τ F J).trans
      (parabolicLeviUnipotent_le_parabolicLevi J)
  · have hmem : -γ ∈ parabolicPosRoots τ J :=
      mem_parabolicPosRoots_of (neg_mem_parabolicRoots hγ) (by rw [height_neg]; omega)
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-γ) rfl hmem
    have e : γ = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by rw [smul_neg, hwj, neg_neg]
    rw [e, ← CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := F) w (isRoot_neg_single τ j)]
    rintro _ ⟨x, hx, rfl⟩
    have hxM : x ∈ parabolicLevi τ F J := by
      refine (Subgroup.closure_le _).2 ?_ hx
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_parabolicLevi hj c
    have hn := canonicalRep_mem_parabolicLevi (K := F) hw
    exact mul_mem (mul_mem hn hxM) (inv_mem hn)

private theorem rootSpan_le_parabolicLevi_of_subset {J : Set (Fin τ.rank)}
    {T : Set (Fin τ.rank → ℤ)} (hT : T ⊆ parabolicRoots τ J) :
    rootSpan τ F T ≤ parabolicLevi τ F J :=
  iSup₂_le fun _ hγ => rootSubgroup_le_parabolicLevi_of_mem (hT hγ)

private theorem mem_parabolicRoots_Jθ_of_deg_zero {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h0 : γ (iθ τ) = 0) : γ ∈ parabolicRoots τ (Jθ τ) :=
  ⟨hγ, fun i hi => by
    have : i = iθ τ := by simpa [Jθ] using hi
    rw [this]
    exact h0⟩

private theorem rootSpan_le_conjSub_parabolicLevi {J : Set (Fin τ.rank)} {w₀ : WeylGroup τ}
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α, α ∈ S ↔ ∃ γ ∈ parabolicRoots τ J, w₀ • γ = α) :
    rootSpan τ F S ≤ conjSub (canonicalRep (coxeterSystem τ) F w₀) (parabolicLevi τ F J) := by
  have hS' : S = (fun γ => w₀ • γ) '' parabolicRoots τ J := Set.ext fun α => hS α
  rw [hS', ← CFSG.RankThree.PartOne.KE.map_conj_rootSpan w₀ (fun γ hγ => hγ.1)]
  exact Subgroup.map_mono (rootSpan_le_parabolicLevi_of_subset subset_rfl)

private theorem normalForm_conj_parabolicLevi {J : Set (Fin τ.rank)} {w₀ : WeylGroup τ}
    (hmin : ∀ β ∈ parabolicPosRoots τ J, 0 < height (w₀ • β)) {g : ModGL τ F}
    (hg : g ∈ conjSub (canonicalRep (coxeterSystem τ) F w₀) (parabolicLevi τ F J)) :
    ∃ (w : WeylGroup τ) (h u v : ModGL τ F), h ∈ torusGroup τ F ∧
      u ∈ rootSpan τ F ((fun β => w₀ • β) '' parabolicPosRoots τ J) ∧
      v ∈ rootSpan τ F ((fun β => w₀ • β) '' parabolicPosRoots τ J ∩ inversionSet w) ∧
      g = h * u * canonicalRep (coxeterSystem τ) F w * v := by
  rw [mem_conjSub_iff] at hg
  obtain ⟨w', hw', h', hh', u', hu', v', hv', hl⟩ := exists_normalForm_of_mem_parabolicLevi hg
  obtain ⟨k, hk, hkeq⟩ := exists_canonicalRep_conj_eq_torus_mul (K := F) w₀ w'
  have hinv : inversionSet w' ⊆ parabolicPosRoots τ J :=
    inversionSet_subset_parabolicPosRoots hw'
  have hrootsJ : ∀ γ ∈ parabolicPosRoots τ J, IsRoot τ γ := fun γ hγ => hγ.1.1
  have hu₁ := canonicalRep_conj_mem_rootSpan_image w₀ hrootsJ hu'
  have hv₁ := canonicalRep_conj_mem_rootSpan_image w₀ (fun γ hγ => hrootsJ γ (hinv hγ)) hv'
  have hconj : ∀ x : Fin τ.rank → ℤ, (w₀ * w' * w₀⁻¹) • (w₀ • x) = w₀ • (w' • x) := fun x => by
    rw [mul_smul, inv_smul_smul, mul_smul]
  have hneg : ∀ α ∈ inversionSet w', height (w₀ • w' • α) < 0 := by
    intro α hα
    have hαJ := hinv hα
    have hJ : -(w' • α) ∈ parabolicPosRoots τ J :=
      mem_parabolicPosRoots_of (neg_mem_parabolicRoots (smul_mem_parabolicRoots hw' hαJ.1))
        (by rw [height_neg]; have := hα.2.2.2; omega)
    have h1 := hmin _ hJ
    rwa [smul_neg, height_neg, Left.neg_pos_iff] at h1
  refine ⟨w₀ * w' * w₀⁻¹, canonicalRep (coxeterSystem τ) F w₀ * h' *
      (canonicalRep (coxeterSystem τ) F w₀)⁻¹ * k,
    k⁻¹ * (canonicalRep (coxeterSystem τ) F w₀ * u' * (canonicalRep (coxeterSystem τ) F w₀)⁻¹) * k,
    canonicalRep (coxeterSystem τ) F w₀ * v' * (canonicalRep (coxeterSystem τ) F w₀)⁻¹,
    mul_mem ((Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := F) w₀) h').1 hh')
      hk, ?_, ?_, ?_⟩
  ·
    have hN := (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (K := F)
        (S := (fun β => w₀ • β) '' parabolicPosRoots τ J)
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
  · calc g = canonicalRep (coxeterSystem τ) F w₀ * ((canonicalRep (coxeterSystem τ) F w₀)⁻¹ * g *
          canonicalRep (coxeterSystem τ) F w₀) * (canonicalRep (coxeterSystem τ) F w₀)⁻¹ := by
          group
      _ = canonicalRep (coxeterSystem τ) F w₀ * (h' * u' * canonicalRep (coxeterSystem τ) F w' *
          v') * (canonicalRep (coxeterSystem τ) F w₀)⁻¹ := by rw [hl]
      _ = _ := conj_mul_assemble _ _ _ _ _ _ _ hkeq

private theorem exists_mul_of_mem_rootSpan_deg {A : Set (Fin τ.rank → ℤ)}
    (hA : ∀ α ∈ A, IsRoot τ α ∧ 0 < height α)
    (hAc : ∀ α ∈ A, ∀ β ∈ A, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ A)
    {u : ModGL τ F} (hu : u ∈ rootSpan τ F A) :
    ∃ u₁ ∈ rootSpan τ F {α | α ∈ A ∧ 1 ≤ α (iθ τ)},
      ∃ u₀ ∈ rootSpan τ F {α | α ∈ A ∧ α (iθ τ) = 0}, u = u₁ * u₀ := by
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_list_of_finite (S := {α | α ∈ A ∧ 1 ≤ α (iθ τ)})
    ((finite_setOf_isRoot τ).subset fun α hα => (hA α hα.1).1)
  obtain ⟨l₀, hl₀, hm₀⟩ := exists_list_of_finite (S := {α | α ∈ A ∧ α (iθ τ) = 0})
    ((finite_setOf_isRoot τ).subset fun α hα => (hA α hα.1).1)
  have hnd : (l₁ ++ l₀).Nodup := by
    refine List.nodup_append.2 ⟨hl₁, hl₀, fun x hx y hy hxy => ?_⟩
    subst hxy
    have h1 := ((hm₁ x).1 hx).2
    have h0 := ((hm₀ x).1 hy).2
    omega
  have hmem : ∀ α, α ∈ l₁ ++ l₀ ↔ α ∈ A := by
    intro α
    rw [List.mem_append, hm₁, hm₀]
    refine ⟨fun h => h.elim (fun h => h.1) (fun h => h.1), fun h => ?_⟩
    have h0 := (IsRoot.height_pos_iff (hA α h).1).1 (hA α h).2 (iθ τ)
    by_cases h1 : 1 ≤ α (iθ τ)
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, by omega⟩
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F hA hAc hnd hmem hu
  refine ⟨(l₁.map fun α => pinnedX τ F α (c α)).prod,
    list_map_prod_pinnedX_mem_rootSpan F (fun α hα => (hm₁ α).1 hα) c,
    (l₀.map fun α => pinnedX τ F α (c α)).prod,
    list_map_prod_pinnedX_mem_rootSpan F (fun α hα => (hm₀ α).1 hα) c, ?_⟩
  rw [← hc, List.map_append, List.prod_append]

theorem factor_of_mem_rootSpan_of_mem_Pθ {J : Set (Fin τ.rank)} {w₀ : WeylGroup τ}
    (hmin : ∀ β ∈ parabolicPosRoots τ J, 0 < height (w₀ • β))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α, α ∈ S ↔ ∃ γ ∈ parabolicRoots τ J, w₀ • γ = α)
    {a : ModGL τ F} (ha : a ∈ rootSpan τ F S) (haP : a ∈ Pθ τ F) :
    ∃ q ∈ rootSpan τ F {α | α ∈ S ∧ 1 ≤ α (iθ τ)}, ∃ l ∈ Lθ τ F, a = q * l := by
  obtain ⟨w, h, u, v, hh, hu, hv, rfl⟩ :=
    normalForm_conj_parabolicLevi hmin (rootSpan_le_conjSub_parabolicLevi hS ha)
  have hApos : ∀ α ∈ (fun β => w₀ • β) '' parabolicPosRoots τ J, IsRoot τ α ∧ 0 < height α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨IsRoot.smul hβ.1.1 w₀, hmin β hβ⟩
  have hAc : ∀ α ∈ (fun β => w₀ • β) '' parabolicPosRoots τ J,
      ∀ β ∈ (fun β => w₀ • β) '' parabolicPosRoots τ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot τ (a • α + b • β) → a • α + b • β ∈ (fun β => w₀ • β) '' parabolicPosRoots τ J := by
    rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ a b ha hb hr
    have e : a • (w₀ • α) + b • (w₀ • β) = w₀ • (a • α + b • β) := by
      rw [smul_add, smul_comm w₀ a α, smul_comm w₀ b β]
    rw [e] at hr ⊢
    exact ⟨a • α + b • β, add_mem_parabolicPosRoots hα hβ ha hb ((isRoot_smul_iff w₀).1 hr), rfl⟩
  have hw : w ∈ parabolicWeylGroup τ (Jθ τ) := by
    have hP : h * u * canonicalRep (coxeterSystem τ) F w * v ∈
        (parabolicSubgroup τ F (Jθ τ) : Set (ModGL τ F)) := haP
    rw [(standard_parabolic_cells τ F).1 (Jθ τ)] at hP
    obtain ⟨w', hw', hcell⟩ := Set.mem_iUnion₂.1 hP
    have hcell' : h * u * canonicalRep (coxeterSystem τ) F w * v ∈ bruhatCell τ F w :=
      mem_bruhatCell.2 ⟨h * u, mul_mem (Subgroup.mem_sup_left hh)
        (Subgroup.mem_sup_right (rootSpan_le_posUnipotent hApos hu)), v,
        Subgroup.mem_sup_right (rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα.2) hv),
        rfl⟩
    by_cases hww : w' = w
    · exact hww ▸ hw'
    · exact absurd hcell' (Set.disjoint_left.1 ((standard_parabolic_cells τ F).2.1 w' w hww) hcell)
  have hvL : v ∈ Lθ τ F := rootSpan_le_parabolicLevi_of_subset
    (fun α hα => (inversionSet_subset_parabolicPosRoots hw hα.2).1) hv
  obtain ⟨u₁, hu₁, u₀, hu₀, rfl⟩ := exists_mul_of_mem_rootSpan_deg hApos hAc hu
  have hu₀L : u₀ ∈ Lθ τ F := rootSpan_le_parabolicLevi_of_subset
    (fun α hα => mem_parabolicRoots_Jθ_of_deg_zero (hApos α hα.1).1 hα.2) hu₀
  refine ⟨h * u₁ * h⁻¹, ?_, h * u₀ * canonicalRep (coxeterSystem τ) F w * v,
    mul_mem (mul_mem (mul_mem (torusGroup_le_parabolicLevi (Jθ τ) hh) hu₀L)
      (canonicalRep_mem_parabolicLevi hw)) hvL, by group⟩
  have hN := (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan (K := F)
    (S := {α | α ∈ (fun β => w₀ • β) '' parabolicPosRoots τ J ∧ 1 ≤ α (iθ τ)})
    (fun α hα => (hApos α hα.1).1) hh) u₁).1 hu₁
  refine rootSpan_mono ?_ hN
  rintro _ ⟨⟨β, hβ, rfl⟩, h1⟩
  exact ⟨(hS _).2 ⟨β, hβ.1, rfl⟩, h1⟩

end Field

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
