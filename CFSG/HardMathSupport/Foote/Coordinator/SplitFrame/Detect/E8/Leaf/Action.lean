module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LAData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


namespace ActionAux

theorem ne_of_deg {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1) :
    γ ≠ μ ∧ γ ≠ -μ := by
  constructor
  · intro h
    rw [h] at hγ0
    omega
  · intro h
    rw [h] at hγ0
    simp [hμ1] at hγ0

theorem mem_Deg1_of_mem_deg1Roots {μ : Fin Tag.E8.rank → ℤ} (hμ : μ ∈ deg1Roots) :
    μ ∈ Deg1 .E8 :=
  mem_deg1Roots.1 hμ

theorem add_mem_Deg1 {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1)
    (h : IsRoot .E8 (γ + μ)) : γ + μ ∈ Deg1 .E8 :=
  ⟨h, show (γ + μ) 7 = 1 by simp [hγ0, hμ1]⟩

section Act

variable {K : Type} [Field K]

theorem actFun_add (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : K) (c c' : (Fin Tag.E8.rank → ℤ) → K) :
    actFun a γ t (c + c') = actFun a γ t c + actFun a γ t c' := by
  funext ν
  simp only [actFun, Pi.add_apply]
  ring

theorem actFun_zero (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : K) :
    actFun a γ t (0 : (Fin Tag.E8.rank → ℤ) → K) = 0 := by
  funext ν
  simp [actFun]

theorem actFun_neg (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ : Fin Tag.E8.rank → ℤ) (t : K) (c : (Fin Tag.E8.rank → ℤ) → K) :
    actFun a γ t (-c) = -actFun a γ t c := by
  funext ν
  simp only [actFun, Pi.neg_apply]
  ring

theorem actFun_single (a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ)
    (γ μ : Fin Tag.E8.rank → ℤ) (t c : K) :
    actFun a γ t (Pi.single μ c : (Fin Tag.E8.rank → ℤ) → K) =
      (Pi.single μ c : (Fin Tag.E8.rank → ℤ) → K) +
        (Pi.single (μ + γ) (t * (a γ μ : K) * c) : (Fin Tag.E8.rank → ℤ) → K) := by
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

end Act

open Classical in
def aE8 (γ μ : Fin Tag.E8.rank → ℤ) : ℤ :=
  if γ + μ ∈ rootFinset .E8 then commConst .E8 γ μ (1, 1) else 0

section Gen

variable {K : Type} [Field K]

theorem conj_of_root {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1)
    (hγr : IsRoot .E8 γ) (hμr : IsRoot .E8 μ) (h : IsRoot .E8 (γ + μ)) (t c : K) :
    pinnedX .E8 K γ t * pinnedX .E8 K μ c * (pinnedX .E8 K γ t)⁻¹ =
      pinnedX .E8 K (γ + μ) ((commConst .E8 γ μ (1, 1) : K) * t * c) * pinnedX .E8 K μ c := by
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  obtain ⟨-, hform⟩ := (simply_laced_root_commutator_unit.{0} .E8 (Or.inr (Or.inr (Or.inr rfl)))
    hγr hμr hne hne').1 h
  have hf := hform K t c
  rw [commutatorElement_def] at hf
  rw [← hf]
  group

theorem conj_of_not_root {γ μ : Fin Tag.E8.rank → ℤ} (hγ0 : γ 7 = 0) (hμ1 : μ 7 = 1)
    (hγr : IsRoot .E8 γ) (hμr : IsRoot .E8 μ) (h : ¬IsRoot .E8 (γ + μ)) (t c : K) :
    pinnedX .E8 K γ t * pinnedX .E8 K μ c * (pinnedX .E8 K γ t)⁻¹ = pinnedX .E8 K μ c := by
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  have hcomm : Commute (pinnedX .E8 K γ t) (pinnedX .E8 K μ c) :=
    (simply_laced_root_commutator_unit.{0} .E8 (Or.inr (Or.inr (Or.inr rfl)))
      hγr hμr hne hne').2 h K (pinnedX .E8 K γ t) (mem_rootSubgroup.2 ⟨t, rfl⟩)
        (pinnedX .E8 K μ c) (mem_rootSubgroup.2 ⟨c, rfl⟩)
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_gen_deg1 {γ μ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset .E8) (hγ0 : γ 7 = 0)
    (hμ : μ ∈ deg1Roots) (t c : K) :
    pinnedX .E8 K γ t * pinnedX .E8 K μ c * (pinnedX .E8 K γ t)⁻¹ ∈ Qθ .E8 K ∧
    heisCoord .E8 K (pinnedX .E8 K γ t * pinnedX .E8 K μ c * (pinnedX .E8 K γ t)⁻¹) =
      actFun aE8 γ t (heisCoord .E8 K (pinnedX .E8 K μ c)) := by
  obtain ⟨hμr, hμ1⟩ := mem_deg1Roots.1 hμ
  have hγr : IsRoot .E8 γ := mem_rootFinset.1 hγ
  have hμD : μ ∈ Deg1 .E8 := mem_Deg1_of_mem_deg1Roots hμ
  have hμQ : pinnedX .E8 K μ c ∈ Qθ .E8 K := pinnedX_mem_Qθ_of_mem_Deg1 hμD c
  have hμc : heisCoord .E8 K (pinnedX .E8 K μ c) = Pi.single μ c :=
    (heisCoord_spec .E8 K).pinnedX_deg1 μ hμD c
  by_cases h : IsRoot .E8 (γ + μ)
  · have hD : γ + μ ∈ Deg1 .E8 := add_mem_Deg1 hγ0 hμ1 h
    have hP : pinnedX .E8 K (γ + μ) ((commConst .E8 γ μ (1, 1) : K) * t * c) ∈ Qθ .E8 K :=
      pinnedX_mem_Qθ_of_mem_Deg1 hD _
    have hconj := conj_of_root hγ0 hμ1 hγr hμr h t c
    have he : t * (aE8 γ μ : K) * c = (commConst .E8 γ μ (1, 1) : K) * t * c := by
      rw [aE8, if_pos (mem_rootFinset.2 h)]
      ring
    constructor
    · rw [hconj]
      exact mul_mem hP hμQ
    · rw [hconj, (heisCoord_spec .E8 K).mul _ hP _ hμQ, (heisCoord_spec .E8 K).pinnedX_deg1 _ hD,
        hμc, actFun_single, he, add_comm μ γ]
      exact add_comm _ _
  · have hconj := conj_of_not_root hγ0 hμ1 hγr hμr h t c
    have hn : γ + μ ∉ rootFinset .E8 := fun h' => h (mem_rootFinset.1 h')
    constructor
    · rw [hconj]
      exact hμQ
    · rw [hconj, hμc, actFun_single, aE8, if_neg hn]
      simp

end Gen

theorem adm : Adm aE8 := by
  intro γ hγ hγ0 μ hμ
  obtain ⟨hμr, hμ1⟩ := mem_deg1Roots.1 hμ
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hε, -⟩ := (simply_laced_root_commutator_unit.{0} .E8
      (Or.inr (Or.inr (Or.inr rfl))) (mem_rootFinset.1 hγ) hμr hne hne').1 (mem_rootFinset.1 h)
    rw [aE8, if_pos h]
    rcases hε with h' | h' <;> simp [h']
  · rw [aE8, if_neg h]

section Main

variable {K : Type} [Field K]

def actGood (γ : Fin Tag.E8.rank → ℤ) (t : K) : Subgroup (ModGL .E8 K) where
  carrier := {q | q ∈ Qθ .E8 K ∧ pinnedX .E8 K γ t * q * (pinnedX .E8 K γ t)⁻¹ ∈ Qθ .E8 K ∧
    heisCoord .E8 K (pinnedX .E8 K γ t * q * (pinnedX .E8 K γ t)⁻¹) =
      actFun aE8 γ t (heisCoord .E8 K q)}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    have e : pinnedX .E8 K γ t * (q * q') * (pinnedX .E8 K γ t)⁻¹ =
        (pinnedX .E8 K γ t * q * (pinnedX .E8 K γ t)⁻¹) *
          (pinnedX .E8 K γ t * q' * (pinnedX .E8 K γ t)⁻¹) := by group
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [e]
      exact mul_mem hcq hcq'
    · rw [e, (heisCoord_spec .E8 K).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec .E8 K).mul _ hq _ hq', actFun_add]
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [mul_one, mul_inv_cancel, heisCoord_one, actFun_zero]
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    have e : pinnedX .E8 K γ t * q⁻¹ * (pinnedX .E8 K γ t)⁻¹ =
        (pinnedX .E8 K γ t * q * (pinnedX .E8 K γ t)⁻¹)⁻¹ := by group
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [e]
      exact inv_mem hcq
    · rw [e, heisCoord_inv hcq, hqe, heisCoord_inv hq, actFun_neg]

theorem commute_theta {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset .E8) (hγ0 : γ 7 = 0)
    (t c : K) : Commute (pinnedX .E8 K γ t) (pinnedX .E8 K (highRoot .E8) c) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg γ hγ (Or.inl hγ0)
  have hnil : commPairs .E8 theta γ = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun p hp =>
      commCandidates_theta_data γ hγ (Or.inl hγ0) p (mem_commPairs.1 hp).1
        (mem_rootFinset.2 (mem_commPairs.1 hp).2)
  exact (commute_pinnedX_of_commPairs_nil .E8 K (mem_rootFinset.1 theta_mem)
    (mem_rootFinset.1 hγ) hne hne' hnil c t).symm

end Main

end ActionAux

theorem exists_action_data (K : Type) [Field K] :
    ∃ a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ, Adm a ∧
      ∀ γ ∈ rootFinset .E8, γ 7 = 0 → ∀ t : K, ∀ q ∈ Qθ Tag.E8 K,
        heisCoord Tag.E8 K (pinnedX Tag.E8 K γ t * q * (pinnedX Tag.E8 K γ t)⁻¹) =
          actFun a γ t (heisCoord Tag.E8 K q) := by
  refine ⟨ActionAux.aE8, ActionAux.adm, ?_⟩
  intro γ hγ hγ0 t q hq
  have hle : Qθ Tag.E8 K ≤ ActionAux.actGood γ t := by
    show rootSpan Tag.E8 K (parabolicRadicalRoots Tag.E8 (Jθ Tag.E8)) ≤ _
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
    · have hαD : α ∈ Deg1 Tag.E8 := h
      have hα1 : α ∈ deg1Roots := mem_deg1Roots.2 hαD
      obtain ⟨hmem, heq⟩ := ActionAux.conj_gen_deg1 hγ hγ0 hα1 t c
      exact ⟨pinnedX_mem_Qθ_of_mem_Deg1 hαD c, hmem, heq⟩
    · subst h
      have hc := ActionAux.commute_theta hγ hγ0 t c
      have hconj : pinnedX Tag.E8 K γ t * pinnedX Tag.E8 K (highRoot .E8) c *
          (pinnedX Tag.E8 K γ t)⁻¹ = pinnedX Tag.E8 K (highRoot .E8) c := by
        rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
      have hQ : pinnedX Tag.E8 K (highRoot .E8) c ∈ Qθ Tag.E8 K := pinnedX_mem_rootSpan hα c
      refine ⟨hQ, ?_, ?_⟩
      · rw [hconj]
        exact hQ
      · rw [hconj, (heisCoord_spec _ K).pinnedX_highRoot, ActionAux.actFun_zero]
  exact (hle hq).2.2

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
