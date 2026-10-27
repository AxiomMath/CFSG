module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypesClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PermSix
public import Certificates.Certificate442007

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace MoInv

open Certificates.OmegaInv

theorem fixCnt_conj (g t : P45) : fixCnt (g * t * g⁻¹) = fixCnt t := by
  unfold fixCnt
  refine Finset.card_bij (fun i _ => g⁻¹ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h := congrArg (fun x => g⁻¹ x) hi
    simpa [Equiv.Perm.mul_apply] using h
  · intro i _ j _ h
    exact g⁻¹.injective h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨g j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    show g (t (g.symm (g j))) = g j
    rw [g.symm_apply_apply, hj]

theorem check_parts :
    repChk (elemsT QA45) (elemsT QP45) = true ∧
      coverAll (reps ()) (elemsT QA45) (elemsT QP45) = true ∧
      layerChk (elemsT QP45) (r4 ()) = true := by
  have h := Certificates.certificate442007
  simp only [check, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem repChk_sound :
    (∀ r ∈ reps (), r ∈ QA45.originalSubgroup ∧ r * r = 1 ∧ r ≠ 1) ∧
      Certificates.OmegaT0.z0 () ∈ QP45.originalSubgroup ∧
      Certificates.OmegaT0.yB () ∈ QP45.originalSubgroup ∧
      r3 () ∉ QP45.originalSubgroup ∧ r4 () ∉ QP45.originalSubgroup ∧
      (centCount (Certificates.OmegaT0.z0 ()) = 1152 ∧
        centCount (Certificates.OmegaT0.yB ()) = 192 ∧ centCount (r3 ()) = 96 ∧
        centCount (r4 ()) = 1440) ∧
      (fixCnt (Certificates.OmegaT0.z0 ()) = 13 ∧ fixCnt (Certificates.OmegaT0.yB ()) = 5 ∧
        fixCnt (r3 ()) = 7 ∧ fixCnt (r4 ()) = 15) := by
  have h := check_parts.1
  simp only [repChk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, mem_elemsT QA45 QA45_ok, mem_elemsT QP45 QP45_ok] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem exists_cover {t : P45}
    (ht : t ∈ QA45.originalSubgroup) (hsq : t * t = 1) (hne : t ≠ 1) :
    ∃ g ∈ QP45.originalSubgroup, ∃ r ∈ reps (), g * t * g⁻¹ = r := by
  have h := check_parts.2.1
  simp only [coverAll, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq,
    mem_elemsT QP45 QP45_ok] at h
  rcases h t ((mem_elemsT QA45 QA45_ok t).2 ht) with h1 | ⟨g, hg, r, hr, hgr⟩
  · exact absurd ⟨hsq, hne⟩ h1
  · exact ⟨g, hg, r, hr, hgr⟩

theorem class_cases {t : P45}
    (ht : t ∈ QA45.originalSubgroup) (hsq : t * t = 1) (hne : t ≠ 1) :
    ((∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = Certificates.OmegaT0.z0 ()) ∧
        t ∈ QP45.originalSubgroup ∧ centCount t = 1152 ∧ fixCnt t = 13) ∨
      ((∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = Certificates.OmegaT0.yB ()) ∧
        t ∈ QP45.originalSubgroup ∧ centCount t = 192 ∧ fixCnt t = 5) ∨
      ((∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = r3 ()) ∧
        t ∉ QP45.originalSubgroup ∧ centCount t = 96 ∧ fixCnt t = 7) ∨
      ((∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = r4 ()) ∧
        t ∉ QP45.originalSubgroup ∧ centCount t = 1440 ∧ fixCnt t = 15) := by
  obtain ⟨g, hg, r, hr, hgr⟩ := exists_cover ht hsq hne
  obtain ⟨-, hz, hy, ha, hb, hcent, hfix⟩ := repChk_sound
  have hgA : g ∈ QA45.originalSubgroup := QP45_le_QA45 hg
  have hc : centCount r = centCount t := by
    rw [← hgr]
    exact Ty.centCount_conj hgA t
  have hf : fixCnt r = fixCnt t := by
    rw [← hgr]
    exact fixCnt_conj g t
  have hP : t ∈ QP45.originalSubgroup ↔ r ∈ QP45.originalSubgroup := by
    rw [← hgr]
    constructor
    · intro h
      exact QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.mul_mem hg h)
        (QP45.originalSubgroup.inv_mem hg)
    · intro h
      have h' := QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.mul_mem
        (QP45.originalSubgroup.inv_mem hg) h) hg
      rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h'
  simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨⟨g, hg, hgr⟩, hP.2 hz, hc.symm.trans hcent.1, hf.symm.trans hfix.1⟩
  · exact Or.inr (Or.inl ⟨⟨g, hg, hgr⟩, hP.2 hy, hc.symm.trans hcent.2.1,
      hf.symm.trans hfix.2.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨g, hg, hgr⟩, fun h => ha (hP.1 h),
      hc.symm.trans hcent.2.2.1, hf.symm.trans hfix.2.2.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨g, hg, hgr⟩, fun h => hb (hP.1 h),
      hc.symm.trans hcent.2.2.2, hf.symm.trans hfix.2.2.2⟩))

section Consequences

variable {t : P45}

theorem invCent_cases (ht : t ∈ QA45.originalSubgroup) (hsq : t * t = 1) (hne : t ≠ 1) :
    InvCent 1152 t ∨ InvCent 192 t ∨ InvCent 96 t ∨ InvCent 1440 t := by
  rcases class_cases ht hsq hne with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
  · exact Or.inl ⟨ht, hsq, hne, h⟩
  · exact Or.inr (Or.inl ⟨ht, hsq, hne, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ht, hsq, hne, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ht, hsq, hne, h⟩))

theorem mem_P_iff_of_invCent {n : ℕ} (h : InvCent n t) :
    t ∈ QP45.originalSubgroup ↔ n = 1152 ∨ n = 192 := by
  obtain ⟨ht, hsq, hne, hc⟩ := h
  rcases class_cases ht hsq hne with ⟨-, hP, h1, -⟩ | ⟨-, hP, h1, -⟩ | ⟨-, hP, h1, -⟩ |
    ⟨-, hP, h1, -⟩
  · simp only [hP, true_iff]
    omega
  · simp only [hP, true_iff]
    omega
  · simp only [hP, false_iff]
    omega
  · simp only [hP, false_iff]
    omega

theorem exists_conj_yB (h : InvCent 192 t) :
    ∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = Certificates.OmegaT0.yB () := by
  obtain ⟨ht, hsq, hne, hc⟩ := h
  rcases class_cases ht hsq hne with ⟨-, -, h1, -⟩ | ⟨hg, -, -, -⟩ | ⟨-, -, h1, -⟩ |
    ⟨-, -, h1, -⟩
  · omega
  · exact hg
  · omega
  · omega

theorem exists_conj_r3 (h : InvCent 96 t) : ∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = r3 () := by
  obtain ⟨ht, hsq, hne, hc⟩ := h
  rcases class_cases ht hsq hne with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨hg, -, -, -⟩ |
    ⟨-, -, h1, -⟩
  · omega
  · omega
  · exact hg
  · omega

theorem exists_conj_r4 (h : InvCent 1440 t) : ∃ g ∈ QP45.originalSubgroup, g * t * g⁻¹ = r4 () := by
  obtain ⟨ht, hsq, hne, hc⟩ := h
  rcases class_cases ht hsq hne with ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ |
    ⟨hg, -, -, -⟩
  · omega
  · omega
  · omega
  · exact hg

theorem invCent_1440_of_fixCnt (ht : t ∈ QA45.originalSubgroup) (hsq : t * t = 1) (hne : t ≠ 1)
    (hf : fixCnt t = 15) : InvCent 1440 t := by
  rcases class_cases ht hsq hne with ⟨-, -, -, h1⟩ | ⟨-, -, -, h1⟩ | ⟨-, -, -, h1⟩ |
    ⟨-, -, h1, -⟩
  · omega
  · omega
  · omega
  · exact ⟨ht, hsq, hne, h1⟩

end Consequences

theorem mem_d0List {y x : P45} :
    x ∈ d0List (elemsT QP45) y ↔ x ∈ QP45.originalSubgroup ∧ x * y = y * x := by
  simp only [d0List, List.mem_filter, decide_eq_true_eq, mem_elemsT QP45 QP45_ok]

theorem equiv_perm_six :
    Nonempty (↥(QP45.originalSubgroup ⊓ Subgroup.centralizer ({r4 ()} : Set P45)) ≃*
      Equiv.Perm (Fin 6)) := by
  have h := check_parts.2.2
  simp only [layerChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hD, hK⟩, hK1⟩, hKcl⟩, hKD⟩, hcore⟩ := h
  let Ksub : Subgroup P45 :=
    { carrier := {x | x ∈ k0List ()}
      mul_mem' := fun {a b} ha hb => ((hKcl a ha).2 b hb)
      one_mem' := hK1
      inv_mem' := fun {a} ha => (hKcl a ha).1 }
  have hmemD : ∀ x : P45, x ∈ d0List (elemsT QP45) (r4 ()) ↔
      x ∈ QP45.originalSubgroup ⊓ Subgroup.centralizer ({r4 ()} : Set P45) := by
    intro x
    rw [mem_d0List, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hKD' : Ksub ≤ QP45.originalSubgroup ⊓ Subgroup.centralizer ({r4 ()} : Set P45) :=
    fun x hx => (hmemD x).1 (hKD x hx)
  have hcardD : Nat.card ↥(QP45.originalSubgroup ⊓
      Subgroup.centralizer ({r4 ()} : Set P45)) = 720 := by
    rw [card_inf_centralizer QP45 QP45_ok]
    exact hD
  have hcardK : Nat.card Ksub = 120 := by
    have h' := card_eq_length (fun g : P45 => g ∈ Ksub) id Function.injective_id (k0List ())
      hK.2 (fun b => ⟨fun hb => ⟨b, hb, rfl⟩, fun ⟨a, ha, hab⟩ => hab ▸ ha⟩)
    exact h'.trans hK.1
  refine nonempty_mulEquiv_perm_six hKD' hcardD hcardK fun d hd hdK => ?_
  rcases hcore d ((hmemD d).2 hd) with h1 | ⟨g, hg, hgd⟩
  · exact h1
  · exact absurd (hdK g ((hmemD g).1 hg)) hgd

end MoInv

end CFSG.OddStandard.SmallF3.Omega
