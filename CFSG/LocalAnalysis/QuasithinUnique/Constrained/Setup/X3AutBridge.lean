module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutCheck

public section

namespace CFSG.QuasithinUnique.Setup.X3Aut

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

abbrev AutA6 : Type := ↥A6Models.autA6

@[expose] def cd (x : AutA6) : List ℕ := code (x : P10)

theorem cd_mul (x y : AutA6) : cd (x * y) = Core.cmul (cd x) (cd y) := code_mul _ _

theorem cd_one : cd (1 : AutA6) = Core.cid := code_one

theorem cd_injective : Function.Injective cd := fun _ _ h => Subtype.ext (code_injective h)

theorem code_nodup (σ : P10) : (code σ).Nodup := by
  unfold code
  rw [List.nodup_ofFn]
  intro i j h
  exact σ.injective (Fin.ext (by simpa using h))

theorem code_inv (σ : P10) : code σ⁻¹ = invC (code σ) := by
  apply List.ext_getElem
  · simp [code, invC]
  · intro j h1 h2
    have hj : j < 10 := by simpa [code] using h1
    have hk : (σ⁻¹ ⟨j, hj⟩ : Fin 10).val < (code σ).length := by simp [code]
    have hLHS : (code σ⁻¹)[j] = (σ⁻¹ ⟨j, hj⟩ : Fin 10).val := by
      simp only [code, List.getElem_ofFn]
    have h3 : (code σ)[(σ⁻¹ ⟨j, hj⟩ : Fin 10).val]'hk = j := by
      simp only [code, List.getElem_ofFn]; simp
    have hmem : j ∈ code σ := h3 ▸ List.getElem_mem hk
    have hlt : (code σ).idxOf j < (code σ).length := List.idxOf_lt_length_of_mem hmem
    have e1 : (code σ)[(code σ).idxOf j]'hlt = j := List.getElem_idxOf hlt
    have e2 : (code σ).idxOf j = (σ⁻¹ ⟨j, hj⟩ : Fin 10).val :=
      (List.Nodup.getElem_inj_iff (code_nodup σ)).mp (e1.trans h3.symm)
    simp only [invC, List.getElem_map, List.getElem_range]
    exact hLHS.trans e2.symm

theorem cd_inv (x : AutA6) : cd x⁻¹ = invC (cd x) := code_inv _


theorem cd_mem_autL (x : AutA6) : cd x ∈ Core.autL := code_mem_autL x.2

theorem exists_of_mem_autL {c : List ℕ} (hc : c ∈ Core.autL) : ∃ x : AutA6, cd x = c := by
  unfold Core.autL at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨y, hy, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  rw [← autRepsP_code] at hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hr'mem : r' ∈ A6Models.autA6 := by rw [autA6_eq]; exact autReps_mem_closure r' hr'
  have hy'mem : y' ∈ A6Models.autA6 := psl29_le_autA6 hy'
  refine ⟨⟨y' * r', A6Models.autA6.mul_mem hy'mem hr'mem⟩, ?_⟩
  show code (y' * r') = _
  rw [code_mul]

theorem exists_cd_getD (i : ℕ) : ∃ y : AutA6, cd y = Core.autL.getD i Core.cid := by
  by_cases h : i < Core.autL.length
  · rw [List.getD_eq_getElem _ _ h]
    exact exists_of_mem_autL (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (not_lt.mp h)]
    exact ⟨1, cd_one⟩

theorem exists_psl_getD (i : ℕ) :
    ∃ y : P10, y ∈ A6Models.psl29 ∧ code y = Core.pslLit.getD i Core.cid := by
  by_cases h : i < Core.pslLit.length
  · rw [List.getD_eq_getElem _ _ h]
    exact exists_psl29_of_code (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (not_lt.mp h)]
    exact ⟨1, Subgroup.one_mem _, code_one⟩

theorem exists_of_all_zip {α β : Type*} (p : α → β → Bool) :
    ∀ (l₁ : List α) (l₂ : List β), (l₁.zip l₂).all (fun q => p q.1 q.2) = true →
      l₁.length = l₂.length → ∀ x ∈ l₁, ∃ y ∈ l₂, p x y = true
  | [], _, _, _, x, hx => by simp at hx
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: l₁, b :: l₂, h, hl, x, hx => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, h.1⟩
    · obtain ⟨y, hy, hp⟩ := exists_of_all_zip p l₁ l₂ h.2 (by simpa using hl) x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hp⟩


theorem repsC_length_eq : repsC.length = repRank.length := by
  have h := repsCheck_true
  unfold repsCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem zip_getD_mem {α β : Type*} : ∀ (l₁ : List α) (l₂ : List β) (a : α) (b : β) (j : ℕ),
    j < l₁.length → j < l₂.length → (l₁.getD j a, l₂.getD j b) ∈ l₁.zip l₂
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | x :: l₁, y :: l₂, a, b, 0, _, _ => by simp
  | x :: l₁, y :: l₂, a, b, j + 1, h1, h2 => by
    simp only [List.getD_cons_succ, List.zip_cons_cons, List.mem_cons]
    right
    exact zip_getD_mem l₁ l₂ a b j (by simpa using h1) (by simpa using h2)

theorem rep_spec {j : ℕ} (hj : j < repsC.length) :
    (rep j).Nodup ∧ Core.cid ∈ rep j ∧ (rep j).length = 2 ^ repRank.getD j 0 ∧
      (∀ e ∈ rep j, e ∈ Core.autL ∧ Core.cmul e e = Core.cid) ∧
      (∀ e ∈ rep j, ∀ f ∈ rep j, Core.cmul e f = Core.cmul f e ∧ Core.cmul e f ∈ rep j) ∧
      repRank.getD j 0 ≤ 3 := by
  have h := repsCheck_true
  unfold repsCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hall⟩, hrank⟩, -⟩ := h
  have hj' : j < repRank.length := repsC_length_eq ▸ hj
  have hmem : (rep j, repRank.getD j 0) ∈ repsC.zip repRank := zip_getD_mem repsC repRank [] 0 j hj hj'
  have hok := hall _ hmem
  have hr3 := hrank (repRank.getD j 0) (by
    rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj')
  unfold repOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.contains_eq_any_beq,
    List.any_eq_true] at hok
  obtain ⟨⟨⟨⟨hnd, hid⟩, hlen2⟩, hinv⟩, hcomm⟩ := hok
  refine ⟨hnd, ?_, hlen2, ?_, ?_, hr3⟩
  · obtain ⟨x, hx, hxe⟩ := hid
    rw [hxe]; exact hx
  · intro e he
    obtain ⟨⟨x, hx, hxe⟩, hsq⟩ := hinv e he
    exact ⟨hxe ▸ hx, hsq⟩
  · intro e he f hf
    obtain ⟨hc, x, hx, hxe⟩ := hcomm e he f hf
    exact ⟨hc, hxe ▸ hx⟩

theorem rep_zero : rep 0 = [Core.cid] := by
  have h := repsCheck_true
  unfold repsCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2


theorem mem_invsC_iff (c : List ℕ) : c ∈ invsC ↔ c ∈ Core.autL ∧ Core.cmul c c = Core.cid ∧ c ≠ Core.cid := by
  unfold invsC isInvC
  simp [List.mem_filter, Bool.and_eq_true]

theorem mem_keysC_of {j : ℕ} {c : List ℕ} (hj : j < repsC.length) (hc : c ∈ invsC)
    (hnot : c ∉ rep j) (hcomm : ∀ e ∈ rep j, Core.cmul c e = Core.cmul e c) : (j, c) ∈ keysC := by
  unfold keysC
  rw [List.mem_flatMap]
  refine ⟨j, List.mem_range.mpr hj, ?_⟩
  rw [List.mem_map]
  refine ⟨c, ?_, rfl⟩
  rw [List.mem_filter]
  refine ⟨hc, ?_⟩
  have h1 : (rep j).contains c = false :=
    Bool.eq_false_iff.mpr (fun h => hnot (by simpa [List.contains_eq_any_beq] using h))
  have h2 : commAll c (rep j) = true := by
    unfold commAll; simpa [List.all_eq_true] using hcomm
  rw [h1, h2]; rfl

theorem step_spec {j : ℕ} {c : List ℕ} (hk : (j, c) ∈ keysC) :
    (rep j).length < 8 ∧ ∃ i k, k < repsC.length ∧
      (∀ e ∈ rep j ++ [c], Core.cmul (Core.cmul (Core.autL.getD i Core.cid) e)
        (invC (Core.autL.getD i Core.cid)) ∈ rep k) ∧ (rep k).length = 2 * (rep j).length := by
  have h := stepCheck_true
  unfold stepCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hzip⟩, hlt⟩ := h
  refine ⟨hlt _ hk, ?_⟩
  obtain ⟨ent, -, hent⟩ := exists_of_all_zip (fun key ent => stepOK key ent) keysC stepTbl
    (by simpa [List.all_eq_true] using hzip) hlen _ hk
  obtain ⟨i, k⟩ := ent
  unfold stepOK at hent
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_eq_any_beq,
    List.any_eq_true] at hent
  obtain ⟨hall, hlen2⟩ := hent
  have hk' : k < repsC.length := by
    by_contra hnk
    have hnil : rep k = [] := by
      unfold rep; exact List.getD_eq_default _ _ (not_lt.mp hnk)
    obtain ⟨x, hx, -⟩ := hall c (by simp)
    simp [hnil] at hx
  refine ⟨i, k, hk', ?_, hlen2⟩
  intro e he
  obtain ⟨x, hx, hxe⟩ := hall e he
  exact hxe ▸ hx

theorem wit_spec {j : ℕ} (hj : j < repsC.length) (hr : repRank.getD j 0 ≠ 0) :
    witOK (rep j) (repRank.getD j 0) (witS.getD j []) (witW.getD j []) = true := by
  have h := witCheck_true
  unfold witCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨-, -⟩, hall⟩ := h
  rcases hall j hj with h0 | h1
  · exact absurd (by simpa using h0) hr
  · exact h1

end CFSG.QuasithinUnique.Setup.X3Aut
