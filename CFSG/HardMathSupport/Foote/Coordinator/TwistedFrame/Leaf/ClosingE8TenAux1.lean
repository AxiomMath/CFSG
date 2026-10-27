module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LAData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false


abbrev Fn (F : Type) := (Fin Tag.E8.rank → ℤ) → F

variable {F : Type} [Field F]

theorem Qθ_le_of_gen {G₀ : Subgroup (ModGL Tag.E8 F)}
    (h1 : ∀ β ∈ Deg1 Tag.E8, ∀ c : F, pinnedX Tag.E8 F β c ∈ G₀)
    (h2 : ∀ c : F, pinnedX Tag.E8 F (highRoot Tag.E8) c ∈ G₀) : Qθ Tag.E8 F ≤ G₀ := by
  show rootSpan Tag.E8 F (parabolicRadicalRoots Tag.E8 (Jθ Tag.E8)) ≤ _
  refine iSup₂_le fun α hα => ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
  · exact h1 α h c
  · subst h
    exact h2 c

@[expose] def lactGood (g : ModGL Tag.E8 F) (M : Fn F →ₗ[F] Fn F) : Subgroup (ModGL Tag.E8 F) where
  carrier := {q | q ∈ Qθ Tag.E8 F ∧ g * q * g⁻¹ ∈ Qθ Tag.E8 F ∧
    heisCoord Tag.E8 F (g * q * g⁻¹) = M (heisCoord Tag.E8 F q)}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    have e : g * (q * q') * g⁻¹ = (g * q * g⁻¹) * (g * q' * g⁻¹) := by group
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [e]
      exact mul_mem hcq hcq'
    · rw [e, (heisCoord_spec Tag.E8 F).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec Tag.E8 F).mul _ hq _ hq', map_add]
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [mul_one, mul_inv_cancel, heisCoord_one, map_zero]
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    have e : g * q⁻¹ * g⁻¹ = (g * q * g⁻¹)⁻¹ := by group
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [e]
      exact inv_mem hcq
    · rw [e, heisCoord_inv hcq, hqe, heisCoord_inv hq, map_neg]

@[expose] def ActsBy (g : ModGL Tag.E8 F) (M : Fn F →ₗ[F] Fn F) : Prop :=
  ∀ q ∈ Qθ Tag.E8 F, g * q * g⁻¹ ∈ Qθ Tag.E8 F ∧
    heisCoord Tag.E8 F (g * q * g⁻¹) = M (heisCoord Tag.E8 F q)

theorem actsBy_iff_le {g : ModGL Tag.E8 F} {M : Fn F →ₗ[F] Fn F} :
    ActsBy g M ↔ Qθ Tag.E8 F ≤ lactGood g M :=
  ⟨fun h q hq => ⟨hq, h q hq⟩, fun h q hq => (h hq).2⟩

@[expose] def Eop (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ) (γ : Fin Tag.E8.rank → ℤ) :
    Fn F →ₗ[F] Fn F where
  toFun c := fun ν => (a γ (ν - γ) : F) * c (ν - γ)
  map_add' c c' := by
    funext ν
    simp only [Pi.add_apply]
    ring
  map_smul' t c := by
    funext ν
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem Eop_apply (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (c : Fn F) (ν : Fin Tag.E8.rank → ℤ) :
    Eop a γ c ν = (a γ (ν - γ) : F) * c (ν - γ) := rfl

theorem actFun_eq (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : F) (c : Fn F) : actFun a γ t c = c + t • Eop a γ c := by
  funext ν
  simp only [actFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Eop_apply]
  ring

@[expose] def actOp (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ) (γ : Fin Tag.E8.rank → ℤ)
    (t : F) : Fn F →ₗ[F] Fn F :=
  LinearMap.id + t • Eop a γ

theorem actOp_apply (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : F) (c : Fn F) : actOp a γ t c = actFun a γ t c := by
  rw [actFun_eq]
  rfl

section Action

theorem ne_of_deg' {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1) :
    γ ≠ μ ∧ γ ≠ -μ := by
  constructor
  · intro h
    rw [h] at hγ0
    omega
  · intro h
    rw [h] at hγ0
    simp [hμ1] at hγ0

theorem add_mem_Deg1' {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1)
    (h : IsRoot .E8 (γ + μ)) : γ + μ ∈ Deg1 .E8 :=
  ⟨h, show (γ + μ) 7 = 1 by simp [hγ0, hμ1]⟩

open Classical in
@[expose] def aE8 (γ μ : Fin Tag.E8.rank → ℤ) : ℤ :=
  if γ + μ ∈ rootFinset .E8 then commConst .E8 γ μ (1, 1) else 0

theorem conj_of_root' {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1)
    (hγr : IsRoot .E8 γ) (hμr : IsRoot .E8 μ) (h : IsRoot .E8 (γ + μ)) (t c : F) :
    pinnedX .E8 F γ t * pinnedX .E8 F μ c * (pinnedX .E8 F γ t)⁻¹ =
      pinnedX .E8 F (γ + μ) ((commConst .E8 γ μ (1, 1) : F) * t * c) * pinnedX .E8 F μ c := by
  obtain ⟨hne, hne'⟩ := ne_of_deg' hγ0 hμ1
  obtain ⟨-, hform⟩ := (simply_laced_root_commutator_unit.{0} .E8 (Or.inr (Or.inr (Or.inr rfl)))
    hγr hμr hne hne').1 h
  have hf := hform F t c
  rw [commutatorElement_def] at hf
  rw [← hf]
  group

theorem conj_of_not_root' {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1)
    (hγr : IsRoot .E8 γ) (hμr : IsRoot .E8 μ) (h : ¬IsRoot .E8 (γ + μ)) (t c : F) :
    pinnedX .E8 F γ t * pinnedX .E8 F μ c * (pinnedX .E8 F γ t)⁻¹ = pinnedX .E8 F μ c := by
  obtain ⟨hne, hne'⟩ := ne_of_deg' hγ0 hμ1
  have hcomm : Commute (pinnedX .E8 F γ t) (pinnedX .E8 F μ c) :=
    (simply_laced_root_commutator_unit.{0} .E8 (Or.inr (Or.inr (Or.inr rfl)))
      hγr hμr hne hne').2 h F (pinnedX .E8 F γ t) (mem_rootSubgroup.2 ⟨t, rfl⟩)
        (pinnedX .E8 F μ c) (mem_rootSubgroup.2 ⟨c, rfl⟩)
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem actFun_single' (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ μ : Fin Tag.E8.rank → ℤ) (t c : F) :
    actFun a γ t (Pi.single μ c : (Fin Tag.E8.rank → ℤ) → F) =
      (Pi.single μ c : (Fin Tag.E8.rank → ℤ) → F) +
        (Pi.single (μ + γ) (t * (a γ μ : F) * c) : (Fin Tag.E8.rank → ℤ) → F) := by
  funext ν
  simp only [actFun, Pi.add_apply]
  congr 1
  by_cases h : ν - γ = μ
  · have h' : ν = μ + γ := sub_eq_iff_eq_add.1 h
    subst h'
    rw [h]
    simp
  · have h' : ν ≠ μ + γ := fun e => h (sub_eq_iff_eq_add.2 e)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    simp

theorem conj_gen_deg1' {γ μ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset .E8) (hγ0 : γ 7 = 0)
    (hμ : μ ∈ deg1Roots) (t c : F) :
    pinnedX .E8 F γ t * pinnedX .E8 F μ c * (pinnedX .E8 F γ t)⁻¹ ∈ Qθ .E8 F ∧
    heisCoord .E8 F (pinnedX .E8 F γ t * pinnedX .E8 F μ c * (pinnedX .E8 F γ t)⁻¹) =
      actFun aE8 γ t (heisCoord .E8 F (pinnedX .E8 F μ c)) := by
  obtain ⟨hμr, hμ1⟩ := mem_deg1Roots.1 hμ
  have hγr : IsRoot .E8 γ := mem_rootFinset.1 hγ
  have hμD : μ ∈ Deg1 .E8 := mem_deg1Roots.1 hμ
  have hμQ : pinnedX .E8 F μ c ∈ Qθ .E8 F := pinnedX_mem_Qθ_of_mem_Deg1 hμD c
  have hμc : heisCoord .E8 F (pinnedX .E8 F μ c) = Pi.single μ c :=
    (heisCoord_spec .E8 F).pinnedX_deg1 μ hμD c
  by_cases h : IsRoot .E8 (γ + μ)
  · have hD : γ + μ ∈ Deg1 .E8 := add_mem_Deg1' hγ0 hμ1 h
    have hP : pinnedX .E8 F (γ + μ) ((commConst .E8 γ μ (1, 1) : F) * t * c) ∈ Qθ .E8 F :=
      pinnedX_mem_Qθ_of_mem_Deg1 hD _
    have hconj := conj_of_root' hγ0 hμ1 hγr hμr h t c
    have he : t * (aE8 γ μ : F) * c = (commConst .E8 γ μ (1, 1) : F) * t * c := by
      rw [aE8, if_pos (mem_rootFinset.2 h)]
      ring
    constructor
    · rw [hconj]
      exact mul_mem hP hμQ
    · rw [hconj, (heisCoord_spec .E8 F).mul _ hP _ hμQ, (heisCoord_spec .E8 F).pinnedX_deg1 _ hD,
        hμc, actFun_single', he, add_comm μ γ]
      exact add_comm _ _
  · have hconj := conj_of_not_root' hγ0 hμ1 hγr hμr h t c
    have hn : γ + μ ∉ rootFinset .E8 := fun h' => h (mem_rootFinset.1 h')
    constructor
    · rw [hconj]
      exact hμQ
    · rw [hconj, hμc, actFun_single', aE8, if_neg hn]
      simp

theorem commute_theta' {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset .E8) (hγ0 : γ 7 = 0)
    (t c : F) : Commute (pinnedX .E8 F γ t) (pinnedX .E8 F (highRoot .E8) c) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg γ hγ (Or.inl hγ0)
  have hnil : commPairs .E8 theta γ = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun p hp =>
      commCandidates_theta_data γ hγ (Or.inl hγ0) p (mem_commPairs.1 hp).1
        (mem_rootFinset.2 (mem_commPairs.1 hp).2)
  exact (commute_pinnedX_of_commPairs_nil .E8 F (mem_rootFinset.1 theta_mem)
    (mem_rootFinset.1 hγ) hne hne' hnil c t).symm

theorem actFun_zero' (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : F) :
    actFun a γ t (0 : (Fin Tag.E8.rank → ℤ) → F) = 0 := by
  funext ν
  simp [actFun]

theorem actsBy_pinnedX {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0)
    (t : F) : ActsBy (pinnedX Tag.E8 F γ t) (actOp aE8 γ t) := by
  rw [actsBy_iff_le]
  refine Qθ_le_of_gen (fun β hβ c => ?_) (fun c => ?_)
  · have hα1 : β ∈ deg1Roots := mem_deg1Roots.2 hβ
    obtain ⟨hmem, heq⟩ := conj_gen_deg1' hγ hγ0 hα1 t c
    refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hβ c, hmem, ?_⟩
    rw [heq, actOp_apply]
  · have hQ : pinnedX Tag.E8 F (highRoot .E8) c ∈ Qθ Tag.E8 F := pinnedX_mem_rootSpan
      (by
        rw [mem_parabolicRadicalRoots_iff]
        refine ⟨isRoot_highRoot _, height_highRoot_pos _, iθ _, fun h => h rfl, ?_⟩
        rw [CoordAux.highRoot_degree]
        omega) c
    have hc := commute_theta' (F := F) hγ hγ0 t c
    have hconj : pinnedX Tag.E8 F γ t * pinnedX Tag.E8 F (highRoot .E8) c *
        (pinnedX Tag.E8 F γ t)⁻¹ = pinnedX Tag.E8 F (highRoot .E8) c := by
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨hQ, ?_, ?_⟩
    · rw [hconj]
      exact hQ
    · rw [hconj, (heisCoord_spec _ F).pinnedX_highRoot, map_zero]

end Action

@[expose] def diagOp (b : Fin Tag.E8.rank → Fˣ) : Fn F →ₗ[F] Fn F where
  toFun c := fun ν => ((rootChar b ν : Fˣ) : F) * c ν
  map_add' c c' := by
    funext ν
    simp only [Pi.add_apply]
    ring
  map_smul' t c := by
    funext ν
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem diagOp_apply (b : Fin Tag.E8.rank → Fˣ) (c : Fn F) (ν : Fin Tag.E8.rank → ℤ) :
    diagOp b c ν = ((rootChar b ν : Fˣ) : F) * c ν := rfl

theorem actsBy_torus (b : Fin Tag.E8.rank → Fˣ) : ActsBy (rootDiagUnit Tag.E8 b) (diagOp b) := by
  rw [actsBy_iff_le]
  refine Qθ_le_of_gen (fun β hβ c => ?_) (fun c => ?_)
  · have hc := rootDiagUnit_conj_pinnedX b hβ.1 c
    refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hβ c, ?_, ?_⟩
    · rw [hc]
      exact pinnedX_mem_Qθ_of_mem_Deg1 hβ _
    · rw [hc, (heisCoord_spec _ F).pinnedX_deg1 β hβ, (heisCoord_spec _ F).pinnedX_deg1 β hβ]
      funext ν
      by_cases h : ν = β
      · subst h
        simp [diagOp_apply]
      · simp [diagOp_apply, Pi.single_apply, h]
  · have hθ : pinnedX Tag.E8 F (highRoot .E8) c ∈ Qθ Tag.E8 F := pinnedX_mem_rootSpan
      (by
        rw [mem_parabolicRadicalRoots_iff]
        refine ⟨isRoot_highRoot _, height_highRoot_pos _, iθ _, fun h => h rfl, ?_⟩
        rw [CoordAux.highRoot_degree]
        omega) c
    have hc := rootDiagUnit_conj_pinnedX b (isRoot_highRoot Tag.E8) c
    refine ⟨hθ, ?_, ?_⟩
    · rw [hc]
      exact pinnedX_mem_rootSpan
        (by
          rw [mem_parabolicRadicalRoots_iff]
          refine ⟨isRoot_highRoot _, height_highRoot_pos _, iθ _, fun h => h rfl, ?_⟩
          rw [CoordAux.highRoot_degree]
          omega) _
    · rw [hc, (heisCoord_spec _ F).pinnedX_highRoot, (heisCoord_spec _ F).pinnedX_highRoot,
        map_zero]

theorem rootDiagUnit_inv (b : Fin Tag.E8.rank → Fˣ) :
    (rootDiagUnit Tag.E8 b : ModGL Tag.E8 F)⁻¹ = rootDiagUnit Tag.E8 b⁻¹ :=
  Units.ext rfl

@[expose] def actSub : Subgroup (ModGL Tag.E8 F) where
  carrier := {g | (∃ M, ActsBy g M) ∧ ∃ M', ActsBy g⁻¹ M'}
  mul_mem' := by
    rintro g₁ g₂ ⟨⟨M₁, h₁⟩, ⟨M₁', h₁'⟩⟩ ⟨⟨M₂, h₂⟩, ⟨M₂', h₂'⟩⟩
    refine ⟨⟨M₁ ∘ₗ M₂, ?_⟩, ⟨M₂' ∘ₗ M₁', ?_⟩⟩
    · intro q hq
      obtain ⟨hq2, hc2⟩ := h₂ q hq
      obtain ⟨hq1, hc1⟩ := h₁ _ hq2
      have e : g₁ * g₂ * q * (g₁ * g₂)⁻¹ = g₁ * (g₂ * q * g₂⁻¹) * g₁⁻¹ := by group
      rw [e]
      exact ⟨hq1, by rw [hc1, hc2]; rfl⟩
    · intro q hq
      obtain ⟨hq2, hc2⟩ := h₁' q hq
      obtain ⟨hq1, hc1⟩ := h₂' _ hq2
      have e : (g₁ * g₂)⁻¹ * q * ((g₁ * g₂)⁻¹)⁻¹ = g₂⁻¹ * (g₁⁻¹ * q * g₁⁻¹⁻¹) * g₂⁻¹⁻¹ := by group
      rw [e]
      exact ⟨hq1, by rw [hc1, hc2]; rfl⟩
  one_mem' := by
    have h : ActsBy (1 : ModGL Tag.E8 F) LinearMap.id := fun q hq => by simpa using hq
    exact ⟨⟨_, h⟩, ⟨_, by simpa using h⟩⟩
  inv_mem' := by
    rintro g ⟨⟨M, h⟩, ⟨M', h'⟩⟩
    exact ⟨⟨M', h'⟩, ⟨M, by simpa using h⟩⟩

theorem mem_actSub {g : ModGL Tag.E8 F} :
    g ∈ actSub ↔ (∃ M, ActsBy g M) ∧ ∃ M', ActsBy g⁻¹ M' := Iff.rfl

theorem pinnedX_mem_actSub {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0)
    (t : F) : pinnedX Tag.E8 F γ t ∈ actSub := by
  refine ⟨⟨_, actsBy_pinnedX hγ hγ0 t⟩, ⟨actOp aE8 γ (-t), ?_⟩⟩
  rw [pinnedX_neg]
  exact actsBy_pinnedX hγ hγ0 (-t)

theorem Lθ_le_actSub : Lθ Tag.E8 F ≤ actSub := by
  show parabolicLevi Tag.E8 F (Jθ Tag.E8) ≤ actSub
  unfold parabolicLevi
  refine sup_le ?_ ?_
  · intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    refine ⟨⟨_, actsBy_torus b⟩, ⟨diagOp b⁻¹, ?_⟩⟩
    rw [rootDiagUnit_inv]
    exact actsBy_torus b⁻¹
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      refine pinnedX_mem_actSub (mem_rootFinset.2 (isRoot_single _ j)) ?_ c
      exact Pi.single_eq_of_ne (Ne.symm hj) _
    · rw [← pinnedX_neg_single]
      refine pinnedX_mem_actSub (mem_rootFinset.2 (isRoot_neg_single _ j)) ?_ c
      have h7 : (Pi.single j (1 : ℤ) : Fin Tag.E8.rank → ℤ) 7 = 0 :=
        Pi.single_eq_of_ne (Ne.symm hj) _
      rw [Pi.neg_apply, h7, neg_zero]

theorem exists_actsBy {g : ModGL Tag.E8 F} (hg : g ∈ Lθ Tag.E8 F) : ∃ M, ActsBy g M :=
  (Lθ_le_actSub hg).1

open Classical in
@[expose] def linAct (g : ModGL Tag.E8 F) : Fn F →ₗ[F] Fn F :=
  if h : ∃ M, ActsBy g M then h.choose else 0

theorem actsBy_linAct {g : ModGL Tag.E8 F} (hg : g ∈ Lθ Tag.E8 F) : ActsBy g (linAct g) := by
  have h := exists_actsBy hg
  rw [linAct, dif_pos h]
  exact h.choose_spec

theorem actsBy_unique {g : ModGL Tag.E8 F} {M M' : Fn F →ₗ[F] Fn F} (h : ActsBy g M)
    (h' : ActsBy g M') {v : Fn F} (hv : v ∈ HeisSpace Tag.E8 F) : M v = M' v := by
  obtain ⟨q, hq, rfl⟩ := (heisCoord_spec Tag.E8 F).surj v hv
  rw [← (h q hq).2, ← (h' q hq).2]

theorem ActsBy.mul {g₁ g₂ : ModGL Tag.E8 F} {M₁ M₂ : Fn F →ₗ[F] Fn F} (h₁ : ActsBy g₁ M₁)
    (h₂ : ActsBy g₂ M₂) : ActsBy (g₁ * g₂) (M₁ ∘ₗ M₂) := by
  intro q hq
  obtain ⟨hq2, hc2⟩ := h₂ q hq
  obtain ⟨hq1, hc1⟩ := h₁ _ hq2
  have e : g₁ * g₂ * q * (g₁ * g₂)⁻¹ = g₁ * (g₂ * q * g₂⁻¹) * g₁⁻¹ := by group
  rw [e]
  exact ⟨hq1, by rw [hc1, hc2]; rfl⟩

theorem actsBy_one : ActsBy (1 : ModGL Tag.E8 F) LinearMap.id := fun q hq => by simpa using hq

theorem linAct_mul {g₁ g₂ : ModGL Tag.E8 F} (h₁ : g₁ ∈ Lθ Tag.E8 F) (h₂ : g₂ ∈ Lθ Tag.E8 F)
    {v : Fn F} (hv : v ∈ HeisSpace Tag.E8 F) :
    linAct (g₁ * g₂) v = linAct g₁ (linAct g₂ v) :=
  actsBy_unique (actsBy_linAct (mul_mem h₁ h₂)) ((actsBy_linAct h₁).mul (actsBy_linAct h₂)) hv

theorem linAct_one {v : Fn F} (hv : v ∈ HeisSpace Tag.E8 F) :
    linAct (1 : ModGL Tag.E8 F) v = v :=
  actsBy_unique (actsBy_linAct (one_mem _)) actsBy_one hv

theorem linAct_mem {g : ModGL Tag.E8 F} (hg : g ∈ Lθ Tag.E8 F) {v : Fn F}
    (hv : v ∈ HeisSpace Tag.E8 F) : linAct g v ∈ HeisSpace Tag.E8 F := by
  obtain ⟨q, hq, rfl⟩ := (heisCoord_spec Tag.E8 F).surj v hv
  obtain ⟨h1, h2⟩ := actsBy_linAct hg q hq
  rw [← h2]
  exact fun β hβ => (heisCoord_spec Tag.E8 F).support _ h1 β hβ

theorem linAct_inv_linAct {g : ModGL Tag.E8 F} (hg : g ∈ Lθ Tag.E8 F) {v : Fn F}
    (hv : v ∈ HeisSpace Tag.E8 F) : linAct g⁻¹ (linAct g v) = v := by
  rw [← linAct_mul (inv_mem hg) hg hv, inv_mul_cancel, linAct_one hv]

theorem linAct_linAct_inv {g : ModGL Tag.E8 F} (hg : g ∈ Lθ Tag.E8 F) {v : Fn F}
    (hv : v ∈ HeisSpace Tag.E8 F) : linAct g (linAct g⁻¹ v) = v := by
  rw [← linAct_mul hg (inv_mem hg) hv, mul_inv_cancel, linAct_one hv]

theorem adm_aE8 : Adm aE8 := by
  intro γ hγ hγ0 μ hμ
  obtain ⟨hμr, hμ1⟩ := mem_deg1Roots.1 hμ
  obtain ⟨hne, hne'⟩ := ne_of_deg' hγ0 hμ1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hε, -⟩ := (simply_laced_root_commutator_unit.{0} .E8
      (Or.inr (Or.inr (Or.inr rfl))) (mem_rootFinset.1 hγ) hμr hne hne').1 (mem_rootFinset.1 h)
    rw [aE8, if_pos h]
    rcases hε with h' | h' <;> simp [h']
  · rw [aE8, if_neg h]

theorem Eop_single (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ μ : Fin Tag.E8.rank → ℤ) (c : F) :
    Eop a γ (Pi.single μ c : Fn F) = (Pi.single (μ + γ) ((a γ μ : F) * c) : Fn F) := by
  funext ν
  rw [Eop_apply]
  by_cases h : ν = μ + γ
  · subst h
    simp
  · have h' : ν - γ ≠ μ := fun e => h (by rw [← e]; abel)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    simp

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
