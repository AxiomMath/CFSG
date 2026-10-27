module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem blockW_le (E : Subgroup Γ) : blockW E ≤ E := by
  have h1 : omegaOneCenterOf (pCoreOf 2 E) ≤ E :=
    (omegaOneCenter_le_pCoreOf E).trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E)
  refine Subgroup.commutator_le.mpr fun a ha e he => ?_
  have : ⁅a, e⁆ = a * e * a⁻¹ * e⁻¹ := rfl
  rw [this]
  exact E.mul_mem (E.mul_mem (E.mul_mem (h1 ha) he) (E.inv_mem (h1 ha))) (E.inv_mem he)

theorem le_normalizer_blockW (E : Subgroup Γ) : E ≤ Subgroup.normalizer (blockW E : Set Γ) :=
  fun _ hg => mem_normalizer_commutator (le_normalizer_omegaOneCenter_pCoreOf E hg)
    (Subgroup.le_normalizer hg)

theorem exists_mul_of_mem_sup_centralizer {E : Subgroup Γ} {z : Γ}
    (hz : z ∈ E ⊔ Subgroup.centralizer (blockW E : Set Γ)) :
    ∃ e ∈ E, ∃ c ∈ Subgroup.centralizer (blockW E : Set Γ), z = e * c := by
  have hEC : E ≤ Subgroup.normalizer
      ((Subgroup.centralizer (blockW E : Set Γ) : Subgroup Γ) : Set Γ) := fun g hg =>
    B6.le_normalizer_centralizer (le_normalizer_blockW E) hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hEC] at hz
  obtain ⟨e, he, c, hc, rfl⟩ := hz
  exact ⟨e, he, c, hc, rfl⟩

theorem mem_centralizer_biSup {P : Finset (Subgroup Γ)} {e : Γ}
    (h : ∀ F ∈ P, e ∈ Subgroup.centralizer (blockW F : Set Γ)) :
    e ∈ Subgroup.centralizer ((⨆ F ∈ P, blockW F : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hle : (⨆ F ∈ P, blockW F : Subgroup Γ) ≤ Subgroup.centralizer ({e} : Set Γ) :=
    iSup₂_le fun F hF x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (h F hF) x hx)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

open scoped Classical in
theorem inter_sup_centralizer_aux (Ω₀ : Finset (Subgroup Γ))
    (hcomm : ∀ E ∈ Ω₀, ∀ F ∈ Ω₀, E ≠ F → ∀ x ∈ E, ∀ y ∈ F, x * y = y * x)
    (S : Finset (Subgroup Γ)) :
    S ⊆ Ω₀ → ∀ (P : Finset (Subgroup Γ)), P ⊆ Ω₀ → Disjoint S P → ∀ z : Γ,
      z ∈ Subgroup.centralizer ((⨆ F ∈ P, blockW F : Subgroup Γ) : Set Γ) →
      (∀ E ∈ S, z ∈ E ⊔ Subgroup.centralizer (blockW E : Set Γ)) →
      z ∈ (⨆ E ∈ S, E) ⊔ Subgroup.centralizer ((⨆ F ∈ S ∪ P, blockW F : Subgroup Γ) : Set Γ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ P _ _ z hzP _
    simpa using hzP
  | insert E S hES ih =>
    intro hS P hP hdisj z hzP hz
    have hEΩ : E ∈ Ω₀ := hS (Finset.mem_insert_self E S)
    have hSΩ : S ⊆ Ω₀ := (Finset.subset_insert E S).trans hS
    have hEP : E ∉ P := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self E S)
    have hSP : Disjoint S P := Finset.disjoint_of_subset_left (Finset.subset_insert E S) hdisj
    obtain ⟨e, he, c, hc, rfl⟩ :=
      exists_mul_of_mem_sup_centralizer (hz E (Finset.mem_insert_self E S))
    have heC : ∀ F ∈ Ω₀, F ≠ E → e ∈ Subgroup.centralizer (blockW F : Set Γ) := by
      intro F hF hFE
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (hcomm E hEΩ F hF (Ne.symm hFE) e he w (blockW_le F hw)).symm
    have heP : e ∈ Subgroup.centralizer ((⨆ F ∈ P, blockW F : Subgroup Γ) : Set Γ) :=
      mem_centralizer_biSup fun F hF => heC F (hP hF) (fun h => hEP (h ▸ hF))
    have hcP : c ∈ Subgroup.centralizer ((⨆ F ∈ P, blockW F : Subgroup Γ) : Set Γ) := by
      have h1 : c = e⁻¹ * (e * c) := by group
      rw [h1]
      exact mul_mem ((Subgroup.centralizer _).inv_mem heP) hzP
    have hcPE : c ∈ Subgroup.centralizer
        ((⨆ F ∈ insert E P, blockW F : Subgroup Γ) : Set Γ) := by
      refine mem_centralizer_biSup fun F hF => ?_
      rcases Finset.mem_insert.mp hF with hFE | hFP
      · rw [hFE]
        exact hc
      · exact Subgroup.centralizer_le (le_iSup₂_of_le (f := fun (F' : Subgroup Γ)
          (_ : F' ∈ P) => blockW F') F hFP le_rfl) hcP
    have hcS : ∀ F ∈ S, c ∈ F ⊔ Subgroup.centralizer (blockW F : Set Γ) := by
      intro F hF
      have hFE : F ≠ E := fun h => hES (h ▸ hF)
      have hzF := hz F (Finset.mem_insert_of_mem hF)
      have h1 : c = e⁻¹ * (e * c) := by group
      rw [h1]
      refine mul_mem ?_ hzF
      exact (le_sup_right (a := F)) ((Subgroup.centralizer _).inv_mem (heC F (hSΩ hF) hFE))
    have hdisj' : Disjoint S (insert E P) := by
      rw [Finset.disjoint_insert_right]
      exact ⟨hES, hSP⟩
    have hPE : insert E P ⊆ Ω₀ := Finset.insert_subset hEΩ hP
    have hih := ih hSΩ (insert E P) hPE hdisj' c hcPE hcS
    have hunion : (insert E S ∪ P) = (S ∪ insert E P) := by
      ext F
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hunion, Finset.iSup_insert]
    have he' : e ∈ (E ⊔ ⨆ E' ∈ S, E') ⊔
        Subgroup.centralizer ((⨆ F ∈ S ∪ insert E P, blockW F : Subgroup Γ) : Set Γ) :=
      (le_sup_left : (E ⊔ ⨆ E' ∈ S, E') ≤ _) ((le_sup_left : E ≤ E ⊔ ⨆ E' ∈ S, E') he)
    have hc' : c ∈ (E ⊔ ⨆ E' ∈ S, E') ⊔
        Subgroup.centralizer ((⨆ F ∈ S ∪ insert E P, blockW F : Subgroup Γ) : Set Γ) :=
      sup_le_sup_right (le_sup_right : (⨆ E' ∈ S, E') ≤ E ⊔ ⨆ E' ∈ S, E') _ hih
    exact mul_mem he' hc'

open scoped Classical in
theorem inter_sup_centralizer_le (S : Finset (Subgroup Γ))
    (hcomm : ∀ E ∈ S, ∀ F ∈ S, E ≠ F → ∀ x ∈ E, ∀ y ∈ F, x * y = y * x) {z : Γ}
    (hz : ∀ E ∈ S, z ∈ E ⊔ Subgroup.centralizer (blockW E : Set Γ)) :
    z ∈ (⨆ E ∈ S, E) ⊔ Subgroup.centralizer ((⨆ F ∈ S, blockW F : Subgroup Γ) : Set Γ) := by
  classical
  have := inter_sup_centralizer_aux S hcomm S (Finset.Subset.refl S) ∅
    (Finset.empty_subset S) (Finset.disjoint_empty_right S) z
    (by simp [Subgroup.mem_centralizer_iff]) hz
  simpa using this

end CFSG.CGT.PushingUpLit.BHS7
