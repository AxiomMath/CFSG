module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Lhat
public import Certificates.Certificate25002
public import Certificates.Certificate25003

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup
open scoped commutatorElement

section Main

structure JFacts : Prop where
  abv : abGS.valid = true
  jv : jGS.valid = true
  cv : cGS.valid = true
  nc : nComm = 2
  ngS4 : ngS = 4
  gens : ∀ k < 5, cGS.eval (genInComm k) = jMats.getD k oneM
  central : ∀ k < 5, mulM (jMats.getD k oneM) x1M = mulM x1M (jMats.getD k oneM) ∧
    mulM (jMats.getD k oneM) x2M = mulM x2M (jMats.getD k oneM)

theorem j_facts : JFacts := by
  have h := Certificates.certificate25003
  simp only [jCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

structure SylowFacts : Prop where
  card : Nat.card Certificates.Cert25002.S = 2 ^ 14
  negOne_mem : (-1 : GL12) ∈ Certificates.Cert25002.S
  x1_mem : ∀ u : GL12, vm u = ofMt x1M → u ∈ Certificates.Cert25002.S
  x2_mem : ∀ u : GL12, vm u = ofMt x2M → u ∈ Certificates.Cert25002.S
  rootCount_negOne : rootCount Certificates.Cert25002.S (-1) = 1056
  rootCount_x1 : ∀ u : GL12, vm u = ofMt x1M → rootCount Certificates.Cert25002.S u = 384
  rootCount_x2 : ∀ u : GL12, vm u = ofMt x2M → rootCount Certificates.Cert25002.S u = 352
  x2_eq : ofMt x2M = -ofMt x1M
  cover : ∀ s ∈ Certificates.Cert25002.S, s * s = 1 → s ≠ 1 → s ≠ -1 →
    ∃ g ∈ Certificates.Cert25002.AB, vm (g * s * g⁻¹) = ofMt x1M ∨ vm (g * s * g⁻¹) = ofMt x2M
  enum : ∀ s ∈ Certificates.Cert25002.S, ∃ i < (buildE sMats treePar).size,
    ofMt ((buildE sMats treePar).getD i oneM) = vm s
  enum_mem : ∀ i < (buildE sMats treePar).size,
    ∃ u ∈ Certificates.Cert25002.S, vm u = ofMt ((buildE sMats treePar).getD i oneM)

theorem sylow_facts : SylowFacts := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := Certificates.certificate25002
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem jMats_getD (k : ℕ) : jMats.getD k oneM = abGS.eval (jWords.getD k []) := by
  rw [jMats, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  rcases h : jWords[k]? with _ | w
  · simp [GenSys.eval]
  · simp

theorem jMats_size : jMats.size = 5 := by
  simp only [jMats, List.size_toArray, List.length_map, jWords, sGenWords, List.length_append,
    List.length_range, List.length_singleton, j_facts.ngS4]

theorem jMats_getD_large {k : ℕ} (hk : 5 ≤ k) : jMats.getD k oneM = oneM :=
  getD_oneM_of_le _ (by have := jMats_size; omega)

theorem jGS_mats : jGS.mats = jMats := rfl

noncomputable def jU (k : ℕ) : GL12 := jGS.letterU j_facts.jv (2 * k)

theorem vm_jU (k : ℕ) : vm (jU k) = ofMt (jMats.getD k oneM) := by
  unfold jU
  rw [GenSys.vm_letterU, GenSys.letter, ite_eq_left (by omega), show 2 * k / 2 = k by omega]
  rfl

theorem jU_mem_Lhat (k : ℕ) : jU k ∈ (Lhat : Subgroup GL12) := by
  by_cases hk : k < 5
  · have : jU k = abGS.evalU j_facts.abv (jWords.getD k []) :=
      vm_inj (by rw [vm_jU, jMats_getD]; exact GenSys.ofMt_eval abGS j_facts.abv _)
    rw [this]
    exact abGS_evalU_mem _ _
  · have : jU k = 1 := vm_inj (by rw [vm_jU, jMats_getD_large (by omega), ofMt_oneM]; rfl)
    rw [this]
    exact one_mem _

theorem jLetterU_mem (S : Subgroup GL12) (hS : ∀ k < 5, jU k ∈ S) (c : ℕ) :
    jGS.letterU j_facts.jv c ∈ S := by
  have even : ∀ k, jGS.letterU j_facts.jv (2 * k) ∈ S := by
    intro k
    by_cases hk : k < 5
    · exact hS k hk
    · have : jGS.letterU j_facts.jv (2 * k) = 1 := by
        refine vm_inj ?_
        rw [GenSys.vm_letterU, GenSys.letter, ite_eq_left (by omega), show 2 * k / 2 = k by omega,
          jGS_mats, jMats_getD_large (by omega), ofMt_oneM]
        rfl
      rw [this]
      exact one_mem _
  rcases Nat.even_or_odd' c with ⟨k, rfl | rfl⟩
  · exact even k
  · rw [GenSys.letterU_odd]
    exact inv_mem (even k)

noncomputable abbrev Ssub : Subgroup GL12 := genSub jU 4

noncomputable abbrev Jsub : Subgroup GL12 := genSub jU 5

theorem Ssub_le_Lhat : Ssub ≤ (Lhat : Subgroup GL12) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, -, rfl⟩
  exact jU_mem_Lhat k

theorem Jsub_le_Lhat : Jsub ≤ (Lhat : Subgroup GL12) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, -, rfl⟩
  exact jU_mem_Lhat k

theorem Ssub_le_Jsub : Ssub ≤ Jsub :=
  Subgroup.closure_mono (Set.image_mono (fun k (hk : k < 4) => (by omega : k < 5)))

theorem jU_mem_Jsub {k : ℕ} (hk : k < 5) : jU k ∈ Jsub := mem_genSub hk

theorem jEvalU_mem_Jsub (w : List ℕ) : jGS.evalU j_facts.jv w ∈ Jsub := by
  unfold GenSys.evalU
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact jLetterU_mem Jsub (fun k hk => jU_mem_Jsub hk) c

theorem Ssub_eq : Ssub = Certificates.Cert25002.S := by
  refine congrArg Subgroup.closure (Set.ext fun u => ⟨?_, ?_⟩)
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, vm_jU k⟩
  · rintro ⟨k, hk, hu⟩
    exact ⟨k, hk, vm_inj (by rw [hu, vm_jU])⟩

theorem Ssub_card : Nat.card Ssub = 2 ^ 14 := by
  rw [Ssub_eq]
  exact sylow_facts.card

noncomputable def x1U : GL12 := jGS.evalU j_facts.jv wx1

noncomputable def x2U : GL12 := jGS.evalU j_facts.jv wx2

theorem vm_x1U : vm x1U = ofMt x1M := (GenSys.ofMt_eval jGS j_facts.jv wx1).symm

theorem vm_x2U : vm x2U = ofMt x2M := (GenSys.ofMt_eval jGS j_facts.jv wx2).symm

theorem x1U_mem : x1U ∈ Ssub := by
  rw [Ssub_eq]
  exact sylow_facts.x1_mem _ vm_x1U

theorem x2U_mem : x2U ∈ Ssub := by
  rw [Ssub_eq]
  exact sylow_facts.x2_mem _ vm_x2U

theorem negOne_mem_Ssub : (-1 : GL12) ∈ Ssub := by
  rw [Ssub_eq]
  exact sylow_facts.negOne_mem

theorem Ssub_rootCount_negOne : rootCount Ssub (-1) = 1056 := by
  rw [Ssub_eq]
  exact sylow_facts.rootCount_negOne

theorem Ssub_rootCount_x1 : rootCount Ssub x1U = 384 := by
  rw [Ssub_eq]
  exact sylow_facts.rootCount_x1 _ vm_x1U

theorem Ssub_rootCount_x2 : rootCount Ssub x2U = 352 := by
  rw [Ssub_eq]
  exact sylow_facts.rootCount_x2 _ vm_x2U

theorem AB_le_Lhat : Certificates.Cert25002.AB ≤ (Lhat : Subgroup GL12) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u (hu | hu)
  · obtain ⟨v, hv, hve⟩ := matA_mem
    rw [vm_inj (hu.trans hve.symm)]
    exact hv
  · obtain ⟨v, hv, hve⟩ := matB_mem
    rw [vm_inj (hu.trans hve.symm)]
    exact hv

theorem cover_class :
    ∀ s ∈ Ssub, s * s = 1 → s ≠ 1 → s ≠ -1 →
      ∃ g ∈ (Lhat : Subgroup GL12), g * s * g⁻¹ = x1U ∨ g * s * g⁻¹ = x2U := by
  intro s hs hss hs1 hsz
  rw [Ssub_eq] at hs
  obtain ⟨g, hg, h | h⟩ := sylow_facts.cover s hs hss hs1 hsz
  · exact ⟨g, AB_le_Lhat hg, Or.inl (vm_inj (h.trans vm_x1U.symm))⟩
  · exact ⟨g, AB_le_Lhat hg, Or.inr (vm_inj (h.trans vm_x2U.symm))⟩

theorem Jsub_central (x : GL12) (hx : ∀ k < 5, vm (jU k) * vm x = vm x * vm (jU k)) :
    ∀ j ∈ Jsub, j * x = x * j := by
  have hle : Jsub ≤ Subgroup.centralizer ({x} : Set GL12) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (vm_inj (by rw [vm_mul, vm_mul]; exact hx k hk))
  exact fun j hj => Subgroup.mem_centralizer_singleton_iff.1 (hle hj)

theorem Jsub_central_x1 : ∀ j ∈ Jsub, j * x1U = x1U * j := by
  refine Jsub_central _ fun k hk => ?_
  have := (j_facts.central k hk).1
  rw [vm_jU, vm_x1U, ← ofMt_mulM, ← ofMt_mulM, this]

theorem Jsub_central_x2 : ∀ j ∈ Jsub, j * x2U = x2U * j := by
  refine Jsub_central _ fun k hk => ?_
  have := (j_facts.central k hk).2
  rw [vm_jU, vm_x2U, ← ofMt_mulM, ← ofMt_mulM, this]

theorem cGS_mats_getD {j : ℕ} (hj : j < nComm) : cGS.mats.getD j oneM = commM j := by
  simp [cGS, hj]

theorem cGS_letterU_mem (c : ℕ) : cGS.letterU j_facts.cv c ∈ ⁅(Jsub : Subgroup GL12), Jsub⁆ := by
  have h := j_facts
  have even : ∀ j, cGS.letterU h.cv (2 * j) ∈ ⁅(Jsub : Subgroup GL12), Jsub⁆ := by
    intro j
    by_cases hj : j < nComm
    · have e : cGS.letterU h.cv (2 * j) =
          ⁅jGS.evalU j_facts.jv (commU j), jGS.evalU j_facts.jv (commV j)⁆ := by
        refine vm_inj ?_
        rw [GenSys.vm_letterU, GenSys.letter, ite_eq_left (by omega), show 2 * j / 2 = j by omega,
          cGS_mats_getD hj, commM, GenSys.ofMt_eval]
        exact congrArg vm (by
          rw [commutatorElement_def, GenSys.evalU_append, GenSys.evalU_append,
            GenSys.evalU_append, GenSys.evalU_invWord, GenSys.evalU_invWord])
      rw [e]
      exact Subgroup.commutator_mem_commutator (jEvalU_mem_Jsub _) (jEvalU_mem_Jsub _)
    · have hs : cGS.mats.size = nComm ∧ cGS.invs.size = nComm := by simp [cGS]
      have h1 : cGS.mats.getD (2 * j / 2) oneM = oneM := by
        rw [show 2 * j / 2 = j by omega]
        exact getD_oneM_of_le _ (by omega)
      have h2 : cGS.invs.getD (2 * j / 2) oneM = oneM := by
        rw [show 2 * j / 2 = j by omega]
        exact getD_oneM_of_le _ (by omega)
      rw [GenSys.letterU_one cGS h.cv h1 h2]
      exact one_mem _
  rcases Nat.even_or_odd' c with ⟨j, rfl | rfl⟩
  · exact even j
  · rw [GenSys.letterU_odd]
    exact inv_mem (even j)

theorem Jsub_perfect : Jsub ≤ ⁅(Jsub : Subgroup GL12), Jsub⁆ := by
  have h := j_facts
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk5 : k < 5 := hk
  have e : jU k = cGS.evalU h.cv (genInComm k) :=
    vm_inj (by
      rw [vm_jU, ← h.gens k hk5]
      exact (GenSys.ofMt_eval cGS h.cv _))
  rw [SetLike.mem_coe, e]
  unfold GenSys.evalU
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact cGS_letterU_mem c

theorem model_inner :
    ∃ (S J : Subgroup GL12) (x₁ x₂ : GL12), S ≤ (Lhat : Subgroup GL12) ∧
      J ≤ (Lhat : Subgroup GL12) ∧ Nat.card S = 2 ^ 14 ∧ (-1 : GL12) ∈ S ∧ S ≤ J ∧ x₁ ∈ S ∧
      x₂ ∈ S ∧ (∀ j ∈ J, j * x₁ = x₁ * j) ∧ (∀ j ∈ J, j * x₂ = x₂ * j) ∧ J ≤ ⁅J, J⁆ ∧
      (∀ s ∈ S, s * s = 1 → s ≠ 1 → s ≠ -1 →
        ∃ g ∈ (Lhat : Subgroup GL12), g * s * g⁻¹ = x₁ ∨ g * s * g⁻¹ = x₂) ∧
      rootCount S (-1) = 1056 ∧ rootCount S x₁ ≠ 1056 ∧ rootCount S x₂ ≠ 1056 :=
  ⟨Ssub, Jsub, x1U, x2U, Ssub_le_Lhat, Jsub_le_Lhat, Ssub_card, negOne_mem_Ssub, Ssub_le_Jsub,
    x1U_mem, x2U_mem, Jsub_central_x1, Jsub_central_x2, Jsub_perfect, cover_class,
    Ssub_rootCount_negOne, by rw [Ssub_rootCount_x1]; norm_num,
    by rw [Ssub_rootCount_x2]; norm_num⟩

end Main

end CFSG.EvenSporadicStandard.TwoSuz
