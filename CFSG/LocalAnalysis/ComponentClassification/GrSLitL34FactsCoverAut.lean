
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable Subgroup

theorem exists_ker_preimage {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    {l : Cover →* E} (hl : q.comp l = sigma) (hls : Function.Surjective l) {e : E}
    (he : e ∈ q.ker) : ∃ c ∈ sigma.ker, l c = e := by
  obtain ⟨c, rfl⟩ := hls e
  refine ⟨c, ?_, rfl⟩
  rw [MonoidHom.mem_ker, ← hl, MonoidHom.comp_apply]
  exact he

theorem exists_autLift
    (ρ : Equiv.Perm (Fin 42))
    {uA uB : List (Fin 2 × Bool)} (hA : abPerm uA = ρ * aS * ρ⁻¹)
    (hB : abPerm uB = ρ * bS * ρ⁻¹) :
    ∃ α : Cover →* Cover, (∀ w, α (cv w) = cv (substWord (autWs uA uB) w)) ∧
      ∀ c, sigma (α c) = ρ * sigma c * ρ⁻¹ := by
  set q : Cover →* Equiv.Perm (Fin 42) := (MulAut.conj ρ⁻¹).toMonoidHom.comp sigma with hq
  have hker : q.ker ≤ center Cover := by
    intro c hc
    apply ker_sigma_le_center
    rw [MonoidHom.mem_ker] at hc ⊢
    simp only [hq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv] at hc
    have e : sigma c = ρ * (ρ⁻¹ * sigma c * ρ) * ρ⁻¹ := by group
    rw [e, hc]
    group
  set y : Fin 2 → Cover := fun i => cv ([uA, uB].getD i []) with hy
  have hyq : ∀ i, q (y i) = genAB i := by
    intro i
    fin_cases i
    · simp [hq, hy, sigma_cv, hA, genAB, aS, mul_assoc]
    · simp [hq, hy, sigma_cv, hB, genAB, bS, mul_assoc]
  obtain ⟨α, hα, hαof⟩ := exists_coverLift q hker y hyq
  have hαgen : ∀ i, α (PresentedGroup.of i) = cv ((autWs uA uB).getD i []) := by
    intro i
    rw [hαof, hy, cv_substWord]
    fin_cases i <;> rfl
  refine ⟨α, fun w => ?_, fun c => ?_⟩
  · have h : α.comp (PresentedGroup.mk _) =
        FreeGroup.lift (fun i : Fin 2 => cv ((autWs uA uB).getD i [])) :=
      FreeGroup.ext_hom _ _ fun i => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
        exact hαgen i
    rw [← cv_substWord, ← h]
    rfl
  · have h := congrArg (fun f => f c) hα
    simp only [MonoidHom.comp_apply, hq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv] at h
    rw [← h]
    group

theorem abPerm_conj_of {ρ : Equiv.Perm (Fin 42)} {ρT : Tab}
    (hρ : TabRep ρT ρ) (hρρ : ρ * ρ = 1) {u : List (Fin 2 × Bool)} {xT : Tab}
    {x : Equiv.Perm (Fin 42)} (hx : TabRep xT x) (h : abTab u = conjTab 42 ρT ρT xT) :
    abPerm u = ρ * x * ρ⁻¹ := by
  have hρi : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ
  have hc := hρ.conjTab hx (by rw [hρi]; exact hρ)
  exact (tabRep_abTab u).perm_eq (h ▸ hc)

section Extension

variable {E : Type*} [Group E]

theorem exists_lam
    (hE : commutator E = ⊤)
    (q : E →* Equiv.Perm (Fin 42)) (hqr : ∀ e, q e ∈ S) (hqS : ∀ s ∈ S, ∃ e, q e = s)
    (hC : q.ker ≤ center E) :
    ∃ l : Cover →* E, q.comp l = sigma ∧ Function.Surjective l := by
  have hgen : ∀ i, genAB i ∈ S := fun i => by
    unfold genAB
    split_ifs
    · exact wordPerm_mem wa
    · exact wordPerm_mem wb
  choose y hy using fun i => hqS (genAB i) (hgen i)
  obtain ⟨l, hl, -⟩ := exists_coverLift q hC y hy
  refine ⟨l, hl, ?_⟩
  have hdec : ∀ e : E, ∃ c : Cover, (l c)⁻¹ * e ∈ center E := by
    intro e
    have hqe : q e ∈ sigma.range := by rw [range_sigma]; exact hqr e
    obtain ⟨c, hc⟩ := hqe
    refine ⟨c, hC ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, hl, hc, inv_mul_cancel]
  have hle : commutator E ≤ l.range := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨c, hc⟩ := hdec a
    obtain ⟨d, hd⟩ := hdec b
    have ha : a = l c * ((l c)⁻¹ * a) := by group
    have hb : b = l d * ((l d)⁻¹ * b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ hc hd,
      ← map_commutatorElement]
    exact ⟨_, rfl⟩
  intro e
  have he : e ∈ commutator E := by rw [hE]; trivial
  exact hle he

theorem lam_z₃
    {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} (hl : q.comp l = sigma)
    (h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) : l z₃ = 1 := by
  apply h3
  · rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hl, sigma_z₃]
  · rw [← map_pow, z₃_pow, map_one]

theorem mem_ker_iff
    {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}
    (hl : q.comp l = sigma) (hls : Function.Surjective l)
    (h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) {e : E} :
    e ∈ q.ker ↔ ∃ i j : ℕ, e = l z₁ ^ i * l z₂ ^ j := by
  constructor
  · intro he
    obtain ⟨c, hc, rfl⟩ := exists_ker_preimage hl hls he
    rw [← range_zHom] at hc
    obtain ⟨d, rfl⟩ := hc
    refine ⟨d.1.toAdd.val, d.2.1.toAdd.val, ?_⟩
    rw [zHom_apply, map_mul, map_mul, map_pow, map_pow, map_pow, lam_z₃ hl h3, one_pow, mul_one]
  · rintro ⟨i, j, rfl⟩
    have h1 : q (l z₁) = 1 := by rw [← MonoidHom.comp_apply, hl, sigma_z₁]
    have h2 : q (l z₂) = 1 := by rw [← MonoidHom.comp_apply, hl, sigma_z₂]
    rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow, h1, h2, one_pow, one_pow, mul_one]

end Extension

end CFSG.ComponentClassification.GrSLit.L34Facts
