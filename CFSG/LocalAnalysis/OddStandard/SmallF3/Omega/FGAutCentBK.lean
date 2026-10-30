module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentLin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentSplit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def fgIotaP (S : FGSplit Q) : OGroup (Q.restrict S.P) →* ProjSim Q :=
  (projOrthToProjSim Q).comp ((toProj Q).comp S.extP)

theorem fg_polar_of_isSimilitude {σ : V ≃ₗ[ZMod 3] V} {μ : (ZMod 3)ˣ} (h : IsSimilitude Q σ μ)
    (x y : V) : QuadraticMap.polar Q (σ x) (σ y) = (μ : ZMod 3) * QuadraticMap.polar Q x y := by
  have h1 := h (x + y)
  rw [map_add] at h1
  simp only [QuadraticMap.polar]
  rw [h1, h x, h y]
  ring

theorem fg_eq_zero_of_polar_zero {P : Submodule (ZMod 3) V} (hP : (Q.restrict P).Nondegenerate)
    {q : V} (hq : q ∈ P) (h : ∀ p ∈ P, QuadraticMap.polar Q q p = 0) : q = 0 := by
  have hB : (Q.restrict P).polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hP
  have h0 := hB.1 ⟨q, hq⟩ (fun y => by
    simpa [LinearMap.domRestrict₁₂_apply, QuadraticMap.polarBilin_apply_apply] using h y y.2)
  simpa using congrArg Subtype.val h0

private theorem fg_comm_central_mul_left {G : Type*} [Group G] {z : G}
    (hz : ∀ g : G, z * g = g * z) (x y : G) : ⁅z * x, y⁆ = ⁅x, y⁆ := by
  have h := hz (x * y * x⁻¹)
  calc ⁅z * x, y⁆ = (z * (x * y * x⁻¹)) * z⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ((x * y * x⁻¹) * z) * z⁻¹ * y⁻¹ := by rw [h]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

private theorem fg_comm_central_mul_right {G : Type*} [Group G] {z : G}
    (hz : ∀ g : G, z * g = g * z) (x y : G) : ⁅x, z * y⁆ = ⁅x, y⁆ := by
  have h := hz (x * y * x⁻¹ * y⁻¹)
  calc ⁅x, z * y⁆ = (x * z) * y * x⁻¹ * y⁻¹ * z⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (z * x) * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [hz x]
    _ = (z * (x * y * x⁻¹ * y⁻¹)) * z⁻¹ := by group
    _ = ((x * y * x⁻¹ * y⁻¹) * z) * z⁻¹ := by rw [h]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem fg_bk_commute (S : FGSplit Q) (hperf : Group.IsPerfect (omegaGroup S.nondegW))
    (g : simGroup Q)
    (hg : ∀ a ∈ omegaGroup S.nondegW,
      toProj Q (simAct Q g (S.extW a)) = toProj Q (S.extW a)) :
    ∀ a ∈ omegaGroup S.nondegW, simAct Q g (S.extW a) = S.extW a := by
  let E : omegaGroup S.nondegW →* OGroup Q := S.extW.comp (omegaGroup S.nondegW).subtype
  let K : Subgroup (omegaGroup S.nondegW) :=
    MonoidHom.eqLocus ((simAct Q g).toMonoidHom.comp E) E
  have hz : ∀ t : OGroup Q, piOrth Q * t = t * piOrth Q :=
    fun t => (Subgroup.mem_center_iff.mp piOrth_mem_center t).symm
  have hcomm : ⁅(⊤ : Subgroup (omegaGroup S.nondegW)), ⊤⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    show (simAct Q g) (E ⁅a, b⁆) = E ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha := toProj_eq_or_eq_piOrth (hg a a.2)
    have hb := toProj_eq_or_eq_piOrth (hg b b.2)
    show ⁅simAct Q g (S.extW a), simAct Q g (S.extW b)⁆ = ⁅S.extW a, S.extW b⁆
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · rw [fg_comm_central_mul_right hz]
    · rw [fg_comm_central_mul_left hz]
    · rw [fg_comm_central_mul_left hz, fg_comm_central_mul_right hz]
  have hK : K = ⊤ := by
    have h1 : ⁅(⊤ : Subgroup (omegaGroup S.nondegW)), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    rw [h1] at hcomm
    exact top_le_iff.mp hcomm
  intro a ha
  have hmem : (⟨a, ha⟩ : omegaGroup S.nondegW) ∈ K := by rw [hK]; exact Subgroup.mem_top _
  exact hmem

theorem fg_bk_apply_comm (S : FGSplit Q) (g : simGroup Q) {a : OGroup (Q.restrict S.W)}
    (hc : simAct Q g (S.extW a) = S.extW a) (v : V) :
    (g : V ≃ₗ[ZMod 3] V) (((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) v) =
      ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) := by
  have h1 := congrArg (fun t : OGroup Q => (t : V ≃ₗ[ZMod 3] V)) hc
  simp only [coe_simAct] at h1
  exact congrArg (fun t : V ≃ₗ[ZMod 3] V => t v) (mul_inv_eq_iff_eq_mul.mp h1)

theorem fg_bk_preserve_P (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W) (g : simGroup Q)
    (hc : ∀ a ∈ omegaGroup S.nondegW, simAct Q g (S.extW a) = S.extW a) :
    ∀ p ∈ S.P, (g : V ≃ₗ[ZMod 3] V) p ∈ S.P := by
  intro p hp
  have hfix : ∀ a ∈ omegaGroup S.nondegW,
      ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) p) =
        (g : V ≃ₗ[ZMod 3] V) p := by
    intro a ha
    rw [← fg_bk_apply_comm S g (hc a ha) p]
    have e2 : ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) p = p := S.extW_P a ⟨p, hp⟩
    rw [e2]
  have htop : (g : V ≃ₗ[ZMod 3] V) p ∈ S.W ⊔ S.P := by
    rw [S.isCompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, q, hq, hwq⟩ := Submodule.mem_sup.mp htop
  have hw0 : (⟨w, hw⟩ : S.W) = 0 := by
    refine fg_eq_zero_of_fixed_omega S.nondegW h3 (fun a ha => ?_)
    have h := hfix a ha
    have e1 : ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) w =
        (((a : OGroup (Q.restrict S.W)) : S.W ≃ₗ[ZMod 3] S.W) ⟨w, hw⟩ : V) :=
      S.extW_W a ⟨w, hw⟩
    have e2 : ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) q = q := S.extW_P a ⟨q, hq⟩
    rw [← hwq, map_add, e1, e2] at h
    exact Subtype.ext (add_right_cancel h)
  have hw0' : w = 0 := congrArg Subtype.val hw0
  rw [← hwq, hw0', zero_add]
  exact hq

theorem fg_bk_preserve_W (S : FGSplit Q) (g : simGroup Q)
    (hP : ∀ p ∈ S.P, (g : V ≃ₗ[ZMod 3] V) p ∈ S.P) :
    ∀ w ∈ S.W, (g : V ≃ₗ[ZMod 3] V) w ∈ S.W := by
  intro w hw
  obtain ⟨μ, hμ⟩ := g.2
  have hsurj : ∀ p'' ∈ S.P, ∃ p ∈ S.P, (g : V ≃ₗ[ZMod 3] V) p = p'' := by
    let M : S.P →ₗ[ZMod 3] S.P := ((g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict hP
    have hinj : Function.Injective M := by
      intro x y hxy
      exact Subtype.ext ((g : V ≃ₗ[ZMod 3] V).injective (congrArg Subtype.val hxy))
    have hs : Function.Surjective M := LinearMap.injective_iff_surjective.mp hinj
    intro p'' hp''
    obtain ⟨⟨p, hp⟩, hpp⟩ := hs ⟨p'', hp''⟩
    exact ⟨p, hp, congrArg Subtype.val hpp⟩
  have htop : (g : V ≃ₗ[ZMod 3] V) w ∈ S.W ⊔ S.P := by
    rw [S.isCompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w', hw', q, hq, hwq⟩ := Submodule.mem_sup.mp htop
  have hq0 : q = 0 := by
    refine fg_eq_zero_of_polar_zero S.nondegP hq (fun p'' hp'' => ?_)
    obtain ⟨p, hp, rfl⟩ := hsurj p'' hp''
    have h1 : QuadraticMap.polar Q ((g : V ≃ₗ[ZMod 3] V) w) ((g : V ≃ₗ[ZMod 3] V) p) = 0 := by
      rw [fg_polar_of_isSimilitude hμ, S.polar_zero w hw p hp, mul_zero]
    rw [← hwq, QuadraticMap.polar_add_left, S.polar_zero w' hw' _ (hP p hp), zero_add] at h1
    exact h1
  rw [← hwq, hq0, add_zero]
  exact hw'

theorem fg_bk_scalar (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W) (g : simGroup Q)
    (hc : ∀ a ∈ omegaGroup S.nondegW, simAct Q g (S.extW a) = S.extW a)
    (hW : ∀ w ∈ S.W, (g : V ≃ₗ[ZMod 3] V) w ∈ S.W) :
    ∃ c : ZMod 3, (c = 1 ∨ c = -1) ∧ ∀ w ∈ S.W, (g : V ≃ₗ[ZMod 3] V) w = c • w := by
  let M : S.W →ₗ[ZMod 3] S.W := ((g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict hW
  have hM : ∀ a ∈ omegaGroup S.nondegW,
      M ∘ₗ ((a : S.W ≃ₗ[ZMod 3] S.W) : S.W →ₗ[ZMod 3] S.W) =
        ((a : S.W ≃ₗ[ZMod 3] S.W) : S.W →ₗ[ZMod 3] S.W) ∘ₗ M := by
    intro a ha
    ext w
    have e1 : ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V) =
        (((a : OGroup (Q.restrict S.W)) : S.W ≃ₗ[ZMod 3] S.W) w : V) := S.extW_W a w
    have e2 : ((S.extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) ((M w : S.W) : V) =
        (((a : OGroup (Q.restrict S.W)) : S.W ≃ₗ[ZMod 3] S.W) (M w) : V) := S.extW_W a (M w)
    have h := fg_bk_apply_comm S g (hc a ha) (w : V)
    rw [e1] at h
    exact h.trans e2
  obtain ⟨c, hcM⟩ := fg_eq_smul_of_commute_omega S.nondegW h3 M hM
  have hcw : ∀ w ∈ S.W, (g : V ≃ₗ[ZMod 3] V) w = c • w := fun w hw => by
    have := congrArg (fun f : S.W →ₗ[ZMod 3] S.W => ((f ⟨w, hw⟩ : S.W) : V)) hcM
    exact this
  have hc0 : c ≠ 0 := by
    rintro rfl
    haveI : Nontrivial S.W := Module.finrank_pos_iff.mp (lt_of_lt_of_le (by norm_num) h3)
    obtain ⟨w, hw0⟩ := exists_ne (0 : S.W)
    apply hw0
    apply Subtype.ext
    apply (g : V ≃ₗ[ZMod 3] V).injective
    simp [hcw w w.2]
  refine ⟨c, ?_, hcw⟩
  revert hc0
  generalize c = c'
  revert c'
  decide

theorem fg_bk_orthogonal (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W) (g : simGroup Q)
    {c : ZMod 3} (hc1 : c = 1 ∨ c = -1) (hcw : ∀ w ∈ S.W, (g : V ≃ₗ[ZMod 3] V) w = c • w) :
    (g : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨μ, hμ⟩ := g.2
  have hc2 : c * c = 1 := by
    rcases hc1 with rfl | rfl <;> decide
  haveI : Nontrivial S.W := Module.finrank_pos_iff.mp (lt_of_lt_of_le (by norm_num) h3)
  obtain ⟨w1, hw1⟩ := exists_ne (0 : S.W)
  have hB : (Q.restrict S.W).polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr S.nondegW
  obtain ⟨w2, hw2⟩ : ∃ w2 : S.W, QuadraticMap.polar Q (w1 : V) (w2 : V) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hw1 (hB.1 w1 (fun y => ?_))
    simpa [LinearMap.domRestrict₁₂_apply, QuadraticMap.polarBilin_apply_apply] using hcon y
  have h1 := fg_polar_of_isSimilitude hμ (w1 : V) (w2 : V)
  rw [hcw w1 w1.2, hcw w2 w2.2] at h1
  simp only [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul] at h1
  rw [← mul_assoc, hc2, one_mul] at h1
  have hμ1 : μ = 1 := by
    refine Units.ext ?_
    rw [Units.val_one]
    exact mul_right_cancel₀ hw2 (h1.symm.trans (one_mul _).symm)
  rw [hμ1] at hμ
  exact isSimilitude_one_iff.mp hμ

theorem fg_bk (S : FGSplit Q) (h3 : 3 ≤ Module.finrank (ZMod 3) S.W)
    (hperf : Group.IsPerfect (omegaGroup S.nondegW)) (g : simGroup Q)
    (hg : ∀ a ∈ omegaGroup S.nondegW,
      toProj Q (simAct Q g (S.extW a)) = toProj Q (S.extW a)) :
    ∃ b : OGroup (Q.restrict S.P), (QuotientGroup.mk g : ProjSim Q) = fgIotaP S b := by
  have hc := fg_bk_commute S hperf g hg
  have hP := fg_bk_preserve_P S h3 g hc
  have hW := fg_bk_preserve_W S g hP
  obtain ⟨c, hc1, hcw⟩ := fg_bk_scalar S h3 g hc hW
  have hO := fg_bk_orthogonal S h3 g hc1 hcw
  let g₀ : OGroup Q := ⟨(g : V ≃ₗ[ZMod 3] V), hO⟩
  have hg₀ : (QuotientGroup.mk g : ProjSim Q) = projOrthToProjSim Q (toProj Q g₀) := rfl
  rcases hc1 with rfl | rfl
  · obtain ⟨b, hb⟩ := S.ext_surj g₀ (fun w => by simpa using hcw w w.2) (fun p => hP p p.2)
    refine ⟨b, ?_⟩
    rw [hg₀, fgIotaP, MonoidHom.comp_apply, MonoidHom.comp_apply, hb]
  · let g₁ : OGroup Q := piOrth Q * g₀
    obtain ⟨b, hb⟩ := S.ext_surj g₁
      (fun w => by
        change (piOrth Q : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (w : V)) = (w : V)
        rw [coe_piOrth_apply, hcw w w.2]
        simp)
      (fun p => by
        change (piOrth Q : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (p : V)) ∈ S.P
        rw [coe_piOrth_apply]
        exact S.P.neg_mem (hP p p.2))
    refine ⟨b, ?_⟩
    rw [hg₀, fgIotaP, MonoidHom.comp_apply, MonoidHom.comp_apply, hb]
    congr 1
    rw [show g₁ = piOrth Q * g₀ from rfl, map_mul, toProj_piOrth, one_mul]

end CFSG.OddStandard.SmallF3.Omega
