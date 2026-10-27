module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParPl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentBK

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q}

theorem Om6Par.extW_mem (D : Om6Par Q t) {a : OGroup (Q.restrict (commSp t))}
    (ha : a ∈ omegaGroup (nondegenerate_restrict_commSp D.nd D.htt)) :
    blockInr D.htt a ∈ D.L ⊔ D.R := by
  rw [← D.map_omega]
  refine ⟨(TauCeti.QuadraticMap.orthogonalGroupCongr D.e).symm a, ?_, ?_⟩
  · refine (mem_omegaGroup_orthogonalGroupCongr_iff detForm_nondegenerate
      (nondegenerate_restrict_commSp D.nd D.htt) (by rw [finrank_mat2]; norm_num) D.e _).mp ?_
    rw [MulEquiv.apply_symm_apply]
    exact ha
  · show blockInr D.htt ((TauCeti.QuadraticMap.orthogonalGroupCongr D.e)
      ((TauCeti.QuadraticMap.orthogonalGroupCongr D.e).symm a)) = blockInr D.htt a
    rw [MulEquiv.apply_symm_apply]

theorem Om6Par.cent_data (D : Om6Par Q t) {y : simGroup Q}
    (hy : ∀ u ∈ D.L ⊔ D.R, simAct Q y u = u) :
    (∀ p ∈ fixSp t, (y : V ≃ₗ[ZMod 3] V) p ∈ fixSp t) ∧
      (∃ c : ZMod 3, (c = 1 ∨ c = -1) ∧ ∀ w ∈ commSp t, (y : V ≃ₗ[ZMod 3] V) w = c • w) ∧
      (y : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  let S := FGSplit.comm D.nd D.htt
  have hc : ∀ a ∈ omegaGroup S.nondegW, simAct Q y (S.extW a) = S.extW a :=
    fun a ha => hy _ (D.extW_mem ha)
  have h3 : 3 ≤ Module.finrank (ZMod 3) S.W := by
    show 3 ≤ Module.finrank (ZMod 3) (commSp t)
    rw [D.dimW]
    norm_num
  have hP := fg_bk_preserve_P S h3 y hc
  obtain ⟨c, hc1, hcw⟩ := fg_bk_scalar S h3 y hc (fg_bk_preserve_W S y hP)
  exact ⟨hP, ⟨c, hc1, hcw⟩, fg_bk_orthogonal S h3 y hc1 hcw⟩

theorem Om6Par.exists_W (D : Om6Par Q t) : ∃ w ∈ commSp t, w ≠ 0 := by
  haveI : Nontrivial (commSp t) := Module.finrank_pos_iff.mp (by rw [D.dimW]; norm_num)
  obtain ⟨w, hw⟩ := exists_ne (0 : commSp t)
  exact ⟨w, w.2, fun h => hw (Subtype.ext h)⟩

theorem Om6Par.decomp (D : Om6Par Q t) (v : V) : ∃ p ∈ fixSp t, ∃ w ∈ commSp t, p + w = v := by
  have h : v ∈ fixSp t ⊔ commSp t := by
    rw [(isCompl_fixSp_commSp D.htt).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, w, hw, h⟩ := Submodule.mem_sup.mp h
  exact ⟨p, hp, w, hw, h⟩

theorem Om6Par.mem_piSim_of_scalar (D : Om6Par Q t) {k : simGroup Q} {ε : ZMod 3}
    (hε : ε = 1 ∨ ε = -1) (hW : ∀ w ∈ commSp t, (k : V ≃ₗ[ZMod 3] V) w = ε • w)
    (hP : ∀ p ∈ fixSp t, (k : V ≃ₗ[ZMod 3] V) p = ε • p) : k ∈ piSim Q := by
  have hk : ∀ v, (k : V ≃ₗ[ZMod 3] V) v = ε • v := fun v => by
    obtain ⟨p, hp, w, hw, rfl⟩ := D.decomp v
    rw [map_add, hP p hp, hW w hw, smul_add]
  rw [mem_piSim_iff]
  rcases hε with rfl | rfl
  · exact Or.inl (Subtype.ext (LinearEquiv.ext fun v => by rw [hk v, one_smul]; rfl))
  · refine Or.inr (Subtype.ext (LinearEquiv.ext fun v => ?_))
    rw [hk v, neg_one_smul]
    change -v = (piOrth Q : V ≃ₗ[ZMod 3] V) v
    rw [coe_piOrth_apply]

theorem Om6Par.mem_piSim_iff_P (D : Om6Par Q t) {k : simGroup Q} {ε : ZMod 3}
    (hε : ε = 1 ∨ ε = -1) (hW : ∀ w ∈ commSp t, (k : V ≃ₗ[ZMod 3] V) w = ε • w) :
    k ∈ piSim Q ↔ ∀ p ∈ fixSp t, (k : V ≃ₗ[ZMod 3] V) p = ε • p := by
  refine ⟨fun hk p hp => ?_, D.mem_piSim_of_scalar hε hW⟩
  obtain ⟨w, hw, hw0⟩ := D.exists_W
  rcases mem_piSim_iff.mp hk with rfl | rfl
  · have h2 : (1 : ZMod 3) • w = ε • w := by simpa using hW w hw
    rw [← smul_left_injective (ZMod 3) hw0 h2]
    simp
  · have h2 : (-1 : ZMod 3) • w = ε • w := by
      rw [neg_one_smul]
      simpa [coe_piOrth_apply] using hW w hw
    rw [← smul_left_injective (ZMod 3) hw0 h2, neg_one_smul]
    simp [coe_piOrth_apply]

theorem Om6Par.scalar_cases (D : Om6Par Q t) {y : simGroup Q} {c ε : ZMod 3}
    (hc : c = 1 ∨ c = -1) (hε : ε = 1 ∨ ε = -1)
    (hW : ∀ w ∈ commSp t, (y : V ≃ₗ[ZMod 3] V) w = c • w)
    (hP : ∀ p ∈ fixSp t, (y : V ≃ₗ[ZMod 3] V) p = ε • p) :
    y ∈ piSim Q ∨ y * orthToSim Q t ∈ piSim Q := by
  have hcε : c = ε ∨ c = -ε := by
    rcases hc with rfl | rfl <;> rcases hε with rfl | rfl <;> decide
  rcases hcε with rfl | rfl
  · exact Or.inl (D.mem_piSim_of_scalar hε hW hP)
  · refine Or.inr (D.mem_piSim_of_scalar hε (fun w hw => ?_) (fun p hp => ?_))
    · simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_orthToSim]
      rw [(mem_commSp_iff D.htt).mp hw, map_neg, hW w hw, ← neg_smul, neg_neg]
    · simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_orthToSim]
      rw [mem_fixSp_iff.mp hp, hP p hp]

theorem om6par_comm_apply (y g s : simGroup Q) (v u : V) :
    (((y * s)⁻¹ * (g⁻¹ * y * g) : simGroup Q) : V ≃ₗ[ZMod 3] V) v = u ↔
      (y : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) =
        (g : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) u)) := by
  change (s : V ≃ₗ[ZMod 3] V).symm ((y : V ≃ₗ[ZMod 3] V).symm ((g : V ≃ₗ[ZMod 3] V).symm
    ((y : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v)))) = u ↔ _
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq]

theorem Om6Par.rhs_iff (D : Om6Par Q t) {y g : simGroup Q} {c : (ZMod 3)ˣ}
    (hg : IsSimilitude Q (g : V ≃ₗ[ZMod 3] V) c) (hgt : simAct Q g t = t)
    (hy : ∀ u ∈ D.L ⊔ D.R, simAct Q y u = u) (hy2 : y * y ∈ piSim Q) (hy1 : y ∉ piSim Q)
    (hyt : y * orthToSim Q t ∉ piSim Q) :
    (y⁻¹ * (g⁻¹ * y * g) ∉ piSim Q ∧ (y * orthToSim Q t)⁻¹ * (g⁻¹ * y * g) ∉ piSim Q) ↔
      (c : ZMod 3) ≠ 1 := by
  obtain ⟨hyP, ⟨cy, hcy, hyW⟩, hyO⟩ := D.cent_data hy
  have hgW := D.preserve_W hgt
  have hgP := om6par_preserve_P hgt
  have hbb : ∀ p ∈ fixSp t, (y : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) p) = p := by
    rcases mem_piSim_iff.mp hy2 with h | h
    · intro p _
      simpa using congrArg (fun s : simGroup Q => (s : V ≃ₗ[ZMod 3] V) p) h
    · exfalso
      obtain ⟨w, hw, hw0⟩ := D.exists_W
      have h1 := congrArg (fun s : simGroup Q => (s : V ≃ₗ[ZMod 3] V) w) h
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_orthToSim, coe_piOrth_apply] at h1
      rw [hyW w hw, map_smul, hyW w hw, smul_smul, ← neg_one_smul (ZMod 3) w] at h1
      have h3 := smul_left_injective (ZMod 3) hw0 h1
      rcases hcy with rfl | rfl <;> revert h3 <;> decide
  have hb1 : ∃ p ∈ fixSp t, (y : V ≃ₗ[ZMod 3] V) p ≠ p := by
    by_contra h
    push Not at h
    exact (D.scalar_cases hcy (Or.inl rfl) hyW (fun p hp => by rw [h p hp, one_smul])).elim
      hy1 hyt
  have hb2 : ∃ p ∈ fixSp t, (y : V ≃ₗ[ZMod 3] V) p ≠ -p := by
    by_contra h
    push Not at h
    exact (D.scalar_cases hcy (Or.inr rfl) hyW (fun p hp => by rw [h p hp, neg_one_smul])).elim
      hy1 hyt
  have hplane := om6par_plane (P := fixSp t) (nondegenerate_restrict_fixSp D.nd D.htt) D.dimP
    D.signP c.ne_zero hyP hgP hbb
    (fun p _ => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hyO p) (fun p _ => hg p)
    hb1 hb2
  have hW0 : ∀ w ∈ commSp t, (y : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) w) =
      (g : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) w) := fun w hw => by
    rw [hyW w hw, map_smul, hyW _ (hgW w hw)]
  have hW₁ : ∀ w ∈ commSp t, (((y * 1)⁻¹ * (g⁻¹ * y * g) : simGroup Q) : V ≃ₗ[ZMod 3] V) w =
      (1 : ZMod 3) • w := fun w hw => by
    rw [one_smul, om6par_comm_apply]
    simpa using hW0 w hw
  have hW₂ : ∀ w ∈ commSp t,
      (((y * orthToSim Q t)⁻¹ * (g⁻¹ * y * g) : simGroup Q) : V ≃ₗ[ZMod 3] V) w =
      (-1 : ZMod 3) • w := fun w hw => by
    rw [neg_one_smul, om6par_comm_apply]
    simp only [coe_orthToSim, map_neg, (mem_commSp_iff D.htt).mp hw, neg_neg]
    exact hW0 w hw
  have h₁ : (y * 1)⁻¹ * (g⁻¹ * y * g) ∈ piSim Q ↔ ∀ p ∈ fixSp t,
      (y : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) p) =
        (g : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) p) := by
    rw [D.mem_piSim_iff_P (Or.inl rfl) hW₁]
    refine forall₂_congr fun p _ => ?_
    rw [one_smul, om6par_comm_apply]
    simp
  have h₂ : (y * orthToSim Q t)⁻¹ * (g⁻¹ * y * g) ∈ piSim Q ↔ ∀ p ∈ fixSp t,
      (y : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) p) =
        -(g : V ≃ₗ[ZMod 3] V) ((y : V ≃ₗ[ZMod 3] V) p) := by
    rw [D.mem_piSim_iff_P (Or.inr rfl) hW₂]
    refine forall₂_congr fun p hp => ?_
    rw [neg_one_smul, om6par_comm_apply]
    simp only [coe_orthToSim, map_neg, mem_fixSp_iff.mp hp]
  rw [show y⁻¹ * (g⁻¹ * y * g) = (y * 1)⁻¹ * (g⁻¹ * y * g) by rw [mul_one], h₁, h₂, ← not_or,
    hplane]

end CFSG.OddStandard.SmallF3.Omega
