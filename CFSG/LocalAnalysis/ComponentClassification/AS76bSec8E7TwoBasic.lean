module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8TwoBasic

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem mem_posUnipotent_of_mem_borelGroup_card_two
    (hK : Nat.card K = 2) {g : ModGL τ K}
    (hg : g ∈ borelGroup τ K) : g ∈ posUnipotent τ K := by
  have hT : torusGroup τ K = ⊥ := by
    rw [torusGroup, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    have ht : t = 1 :=
      Units.ext ((E8.eq_zero_or_eq_one_of_card_two_e8 hK (t : K)).resolve_left t.ne_zero)
    subst ht
    show torusElt τ K i 1 ∈ ({1} : Set (ModGL τ K))
    rw [torusElt_one]
    exact Set.mem_singleton 1
  rw [borelGroup, hT, bot_sup_eq] at hg
  exact hg

theorem height_le_of_isRoot_e7 {γ : Fin Tag.E7.rank → ℤ}
    (hγ : IsRoot .E7 γ) : height γ ≤ 17 := by
  have h : ∀ l ∈ Tag.artifactRoots .E7, l.sum ≤ 17 := by
    decide +kernel
  have h1 := h _ (isRoot_iff_mem_artifactRoots.1 hγ)
  rw [List.sum_ofFn] at h1
  exact h1

theorem exists_eq_prod_of_mem_rootSpan
    {H h : ℤ} (hH : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → height γ ≤ H) (hHh : H < 2 * h)
    {L : List (Fin τ.rank → ℤ)} (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α)
    (hht : ∀ α ∈ L, h ≤ height α) {z : ModGL τ K}
    (hz : z ∈ rootSpan τ K {γ | γ ∈ L}) :
    ∃ c : (Fin τ.rank → ℤ) → K, z = (L.map fun α => pinnedX τ K α (c α)).prod := by
  classical
  have hclosed : ∀ α ∈ {γ | γ ∈ L}, ∀ β ∈ {γ | γ ∈ L}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ {γ | γ ∈ L} := by
    intro α hα β hβ a b ha hb hr
    exfalso
    have h1 := hH _ hr
    have hpt : ∀ x, (a • α + b • β) x = a * α x + b * β x := fun x => by
      simp [nsmul_eq_mul]
    have h2 : height (a • α + b • β) = a * height α + b * height β := by
      simp only [height, hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h3 := hht α hα
    have h4 := hht β hβ
    have h5 : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have h6 : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h7 := (hL α hα).2
    have h8 := (hL β hβ).2
    nlinarith
  have hinj : Function.Injective L.get := List.nodup_iff_injective_get.1 hnd
  have hrange : Set.range L.get = {γ | γ ∈ L} := by
    ext γ
    rw [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K (fun α hα => hL α hα) hclosed L.get hinj
    hrange).surjOn hz
  refine ⟨Function.extend L.get d 0, ?_⟩
  rw [← hd]
  have e : (List.ofFn fun i => pinnedX τ K (L.get i) (d i)) =
      (List.ofFn L.get).map fun α => pinnedX τ K α (Function.extend L.get d 0 α) := by
    rw [List.map_ofFn]
    refine List.ofFn_inj.2 (funext fun i => ?_)
    rw [Function.comp_apply, hinj.extend_apply]
  simp only
  rw [e, List.ofFn_get]

theorem coeff_eq_zero_of_commute_neg
    [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L₁ L₂ : List (Fin τ.rank → ℤ)} {lam ρ : Fin τ.rank → ℤ}
    (hnd : (L₁ ++ [lam - ρ, lam] ++ L₂).Nodup)
    (hpos : ∀ α ∈ L₁ ++ [lam - ρ, lam] ++ L₂, IsRoot τ α ∧ 0 < height α)
    (hρ : IsRoot τ ρ) (hne : -ρ ≠ lam ∧ -ρ ≠ -lam)
    (hL : ∀ α ∈ L₁ ++ L₂, -ρ ≠ α ∧ -ρ ≠ -α ∧ ¬ IsRoot τ (-ρ + α))
    (c : (Fin τ.rank → ℤ) → K)
    (hcomm : pinnedX τ K (-ρ) 1 *
        ((L₁ ++ [lam] ++ L₂).map fun α => pinnedX τ K α (c α)).prod =
      ((L₁ ++ [lam] ++ L₂).map fun α => pinnedX τ K α (c α)).prod * pinnedX τ K (-ρ) 1) :
    c lam = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hnρ : IsRoot τ (-ρ) := IsRoot.neg hρ
  have hlam : IsRoot τ lam := (hpos lam (by simp)).1
  have hroot : IsRoot τ (-ρ + lam) := by
    rw [neg_add_eq_sub]
    exact (hpos (lam - ρ) (by simp)).1
  have hL' : ∀ α ∈ L₁ ++ L₂, pinnedX τ K (-ρ) 1 * pinnedX τ K α (c α) *
      (pinnedX τ K (-ρ) 1)⁻¹ = pinnedX τ K α (c α) := fun α hα =>
    EvenOddRadical.pinnedX_conj_of_not hτ hnρ
      (hpos α (by rcases List.mem_append.1 hα with h | h <;> simp [h])).1 (hL α hα).1
      (hL α hα).2.1 (hL α hα).2.2 1 (c α)
  have hL₁' := fun α (hα : α ∈ L₁) => hL' α (List.mem_append_left _ hα)
  have hL₂' := fun α (hα : α ∈ L₂) => hL' α (List.mem_append_right _ hα)
  have hlam' : pinnedX τ K (-ρ) 1 * pinnedX τ K lam (c lam) * (pinnedX τ K (-ρ) 1)⁻¹ =
      pinnedX τ K (lam - ρ) (c lam) * pinnedX τ K lam (c lam) := by
    rw [EvenOddRadical.pinnedX_conj_of_isRoot hτ h2 hnρ hlam hne.1 hne.2 hroot 1 (c lam),
      one_mul, neg_add_eq_sub]
  set P₁ := (L₁.map fun α => pinnedX τ K α (c α)).prod with hP₁
  set P₂ := (L₂.map fun α => pinnedX τ K α (c α)).prod with hP₂
  have hconj : P₁ * (pinnedX τ K (lam - ρ) (c lam) * pinnedX τ K lam (c lam)) * P₂ =
      P₁ * pinnedX τ K lam (c lam) * P₂ := by
    have h1 := E8.conj_list_prod_map_e8 (pinnedX τ K (-ρ) 1)
      (fun α => pinnedX τ K α (c α)) (L₁ ++ [lam] ++ L₂)
    rw [hcomm, mul_inv_cancel_right, List.map_append, List.map_append, List.map_append,
      List.map_append, List.prod_append, List.prod_append, List.prod_append, List.prod_append,
      List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton,
      List.map_congr_left hL₁', List.map_congr_left hL₂', hlam'] at h1
    exact h1.symm
  have hnot : lam - ρ ∉ L₁ ++ L₂ := by
    intro h
    rcases List.mem_append.1 h with h | h
    · exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ h _ (by simp) rfl
    · exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ h rfl
  have hne' : lam ≠ lam - ρ := by
    intro h
    have h3 := (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.1
    rw [← h] at h3
    simp at h3
  set c₁ : (Fin τ.rank → ℤ) → K := Function.update c (lam - ρ) (c lam) with hc₁
  set c₂ : (Fin τ.rank → ℤ) → K := Function.update c (lam - ρ) 0 with hc₂
  have hof : ∀ (L : List (Fin τ.rank → ℤ)), (∀ α ∈ L, α ∈ L₁ ++ L₂) → ∀ v : K,
      (L.map fun α => pinnedX τ K α (Function.update c (lam - ρ) v α)) =
        L.map fun α => pinnedX τ K α (c α) := fun L hL v =>
    List.map_congr_left fun α hα => by
      rw [Function.update_of_ne (fun h => hnot (by rw [← h]; exact hL α hα))]
  have heq : ((L₁ ++ [lam - ρ, lam] ++ L₂).map fun α => pinnedX τ K α (c₁ α)).prod =
      ((L₁ ++ [lam - ρ, lam] ++ L₂).map fun α => pinnedX τ K α (c₂ α)).prod := by
    have e : ∀ v : K, ((L₁ ++ [lam - ρ, lam] ++ L₂).map fun α =>
        pinnedX τ K α (Function.update c (lam - ρ) v α)).prod =
          P₁ * (pinnedX τ K (lam - ρ) v * pinnedX τ K lam (c lam)) * P₂ := fun v => by
      rw [List.map_append, List.map_append, List.prod_append, List.prod_append,
        hof L₁ (fun α hα => List.mem_append_left _ hα) v,
        hof L₂ (fun α hα => List.mem_append_right _ hα) v, List.map_cons, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil, mul_one,
        Function.update_self, Function.update_of_ne hne']
    rw [hc₁, hc₂, e, e, pinnedX_zero, one_mul]
    exact hconj
  have h := pinnedX_list_prod_injective (L₁ ++ [lam - ρ, lam] ++ L₂) hnd hpos c₁ c₂ heq (lam - ρ)
    (by simp)
  rw [hc₁, hc₂, Function.update_self, Function.update_self] at h
  exact h

theorem coeff_eq_zero_of_commute_neg_mem
    [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : List (Fin τ.rank → ℤ)}
    (hnd : L.Nodup) (hpos : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α) {lam ρ : Fin τ.rank → ℤ}
    (hlam : lam ∈ L) (hρ : IsRoot τ ρ) (hlr : IsRoot τ (lam - ρ) ∧ 0 < height (lam - ρ))
    (hlrL : lam - ρ ∉ L) (hne : -ρ ≠ lam ∧ -ρ ≠ -lam)
    (hL : ∀ α ∈ L, α ≠ lam → -ρ ≠ α ∧ -ρ ≠ -α ∧ ¬ IsRoot τ (-ρ + α))
    (c : (Fin τ.rank → ℤ) → K)
    (hcomm : pinnedX τ K (-ρ) 1 * (L.map fun α => pinnedX τ K α (c α)).prod =
      (L.map fun α => pinnedX τ K α (c α)).prod * pinnedX τ K (-ρ) 1) :
    c lam = 0 := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hlam
  have e : L₁ ++ lam :: L₂ = L₁ ++ [lam] ++ L₂ := by simp
  have e' : L₁ ++ [lam - ρ, lam] ++ L₂ = L₁ ++ (lam - ρ) :: (lam :: L₂) := by simp
  have hlam' : lam ∉ L₁ ++ L₂ := (List.nodup_cons.1 (List.perm_middle.nodup_iff.1 hnd)).1
  refine coeff_eq_zero_of_commute_neg hτ (L₁ := L₁) (L₂ := L₂) ?_ ?_ hρ hne ?_ c ?_
  · rw [e', List.perm_middle.nodup_iff]
    exact List.nodup_cons.2 ⟨hlrL, hnd⟩
  · intro α hα
    rw [e', List.perm_middle.mem_iff, List.mem_cons] at hα
    rcases hα with rfl | hα
    · exact hlr
    · exact hpos α hα
  · intro α hα
    have hαL : α ∈ L₁ ++ lam :: L₂ := by
      rcases List.mem_append.1 hα with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    refine hL α hαL fun h => hlam' ?_
    rw [← h]
    exact hα
  · rw [← e]
    exact hcomm

theorem wordProd_smul_eq_foldr
    (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (reflect τ) v := by
  induction ω with
  | nil => simp
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

@[expose] noncomputable def e7WordElt
    (ω : List (Fin Tag.E7.rank)) : adjointGroup .E7 K :=
  ⟨(ω.map fun i => weylElt .E7 K i 1).prod, list_prod_mem fun _ hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup i 1⟩

theorem coeff_smul_eq_of_commute_word
    [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {F : List (Fin τ.rank → ℤ)}
    (hnd : F.Nodup) (hF : ∀ σ ∈ F, IsRoot τ σ ∧ 0 < height σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (ω : List (Fin τ.rank)) (hperm : (F.map fun σ => ω.foldr (reflect τ) σ).Perm F)
    (hinv : ∀ σ ∈ F, ω.foldr (reflect τ) (ω.foldr (reflect τ) σ) = σ)
    (c : (Fin τ.rank → ℤ) → K)
    (hcomm : (ω.map fun i => weylElt τ K i 1).prod *
        (F.map fun σ => pinnedX τ K σ (c σ)).prod =
      (F.map fun σ => pinnedX τ K σ (c σ)).prod * (ω.map fun i => weylElt τ K i 1).prod) :
    ∀ σ ∈ F, c (ω.foldr (reflect τ) σ) = c σ := by
  set n := (ω.map fun i => weylElt τ K i 1).prod with hn
  set act : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) := fun σ => ω.foldr (reflect τ) σ with hact
  set F' := F.map act with hF'
  have hconj : n * (F.map fun σ => pinnedX τ K σ (c σ)).prod * n⁻¹ =
      (F'.map fun μ => pinnedX τ K μ (c (act μ))).prod := by
    rw [E8.conj_list_prod_map_e8, hF', List.map_map]
    refine congrArg List.prod (List.map_congr_left fun σ hσ => ?_)
    simp only [Function.comp_apply]
    rw [hn, CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo ω (hF σ hσ).1 (c σ),
      wordProd_smul_eq_foldr]
    show pinnedX τ K (act σ) (c σ) = pinnedX τ K (act σ) (c (act (act σ)))
    rw [show act (act σ) = σ from hinv σ hσ]
  have hw : (F.map fun σ => pinnedX τ K σ (c σ)).prod =
      (F'.map fun μ => pinnedX τ K μ (c μ)).prod :=
    classD4_frame_prod_perm hτ (fun σ hσ => (hF σ hσ).1) horth hperm.symm c
  have heq : (F'.map fun μ => pinnedX τ K μ (c (act μ))).prod =
      (F'.map fun μ => pinnedX τ K μ (c μ)).prod := by
    rw [← hconj, ← hw, hcomm, mul_inv_cancel_right]
  have hnd' : F'.Nodup := hperm.nodup_iff.2 hnd
  have hF'' : ∀ μ ∈ F', IsRoot τ μ ∧ 0 < height μ := fun μ hμ => hF μ (hperm.subset hμ)
  have h := pinnedX_list_prod_injective F' hnd' hF'' (fun μ => c (act μ)) c heq
  intro σ hσ
  have h1 := h (act σ) (List.mem_map_of_mem hσ)
  simp only [hact] at h1 ⊢
  rw [hinv σ hσ] at h1
  exact h1.symm

theorem wordProd_comm_framePt
    [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ σ ∈ F, IsRoot τ σ) (horth : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (ω : List (Fin τ.rank)) (hperm : (F.map fun σ => ω.foldr (reflect τ) σ).Perm F) :
    (ω.map fun i => weylElt τ K i 1).prod * (F.map fun σ => pinnedX τ K σ 1).prod =
      (F.map fun σ => pinnedX τ K σ 1).prod * (ω.map fun i => weylElt τ K i 1).prod := by
  set n := (ω.map fun i => weylElt τ K i 1).prod with hn
  set P := (F.map fun σ => pinnedX τ K σ 1).prod with hP
  have hconj : n * P * n⁻¹ = P := by
    rw [hP, E8.conj_list_prod_map_e8]
    have e : (F.map fun σ => n * pinnedX τ K σ 1 * n⁻¹) =
        (F.map fun σ => ω.foldr (reflect τ) σ).map fun μ => pinnedX τ K μ 1 := by
      rw [List.map_map]
      refine List.map_congr_left fun σ hσ => ?_
      simp only [Function.comp_apply]
      rw [hn, CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo ω (hF σ hσ) 1,
        wordProd_smul_eq_foldr]
    rw [e]
    exact (classD4_frame_prod_perm hτ hF horth hperm.symm fun _ => (1 : K)).symm
  calc n * P = n * P * n⁻¹ * n := by group
    _ = P * n := by rw [hconj]

theorem conj_link_eq
    [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {σ₁ σ₂ a b μ : Fin τ.rank → ℤ} {F' : List (Fin τ.rank → ℤ)}
    (hσ₁ : IsRoot τ σ₁) (hσ₂ : IsRoot τ σ₂) (hF' : ∀ σ ∈ F', IsRoot τ σ)
    (ha : IsRoot τ a) (hb : IsRoot τ b) (haμ : a + σ₁ = μ) (hbμ : b + σ₂ = μ)
    (ha₁ : iform a σ₁ = -1) (hb₂ : iform b σ₂ = -1) (hb₁ : 0 ≤ iform b σ₁)
    (ha₂ : 0 ≤ iform a σ₂) (haμ' : 0 ≤ iform a μ) (hμ₁ : 0 ≤ iform μ σ₁)
    (haF : ∀ σ ∈ F', 0 ≤ iform a σ) (hbF : ∀ σ ∈ F', 0 ≤ iform b σ)
    (c : (Fin τ.rank → ℤ) → K) :
    pinnedX τ K a 1 * pinnedX τ K b 1 *
        ((σ₁ :: σ₂ :: F').map fun σ => pinnedX τ K σ (c σ)).prod *
          (pinnedX τ K a 1 * pinnedX τ K b 1)⁻¹ =
      pinnedX τ K μ (c σ₁ + c σ₂) * ((σ₁ :: σ₂ :: F').map fun σ => pinnedX τ K σ (c σ)).prod := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hμ : IsRoot τ μ := by
    rw [← haμ]
    exact (classD4_isRoot_add hτ ha hσ₁ ha₁).1
  set P' := (F'.map fun σ => pinnedX τ K σ (c σ)).prod with hP'
  have hcP : ∀ {d : Fin τ.rank → ℤ}, IsRoot τ d → (∀ σ ∈ F', 0 ≤ iform d σ) →
      Commute (pinnedX τ K d 1) P' := fun hd hdF =>
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
      exact classD4_commute_pinnedX hτ hd (hF' σ hσ) (hdF σ hσ) 1 (c σ)
  have hb1 : pinnedX τ K b 1 * pinnedX τ K σ₁ (c σ₁) * (pinnedX τ K b 1)⁻¹ =
      pinnedX τ K σ₁ (c σ₁) := by
    rw [(classD4_commute_pinnedX hτ hb hσ₁ hb₁ 1 (c σ₁)).eq, mul_inv_cancel_right]
  have hb2 : pinnedX τ K b 1 * pinnedX τ K σ₂ (c σ₂) * (pinnedX τ K b 1)⁻¹ =
      pinnedX τ K μ (c σ₂) * pinnedX τ K σ₂ (c σ₂) := by
    obtain ⟨hr, hne, hne'⟩ := classD4_isRoot_add hτ hb hσ₂ hb₂
    rw [EvenOddRadical.pinnedX_conj_of_isRoot hτ h2 hb hσ₂ hne hne' hr 1 (c σ₂), hbμ, one_mul]
  have ha1 : pinnedX τ K a 1 * pinnedX τ K σ₁ (c σ₁) * (pinnedX τ K a 1)⁻¹ =
      pinnedX τ K μ (c σ₁) * pinnedX τ K σ₁ (c σ₁) := by
    obtain ⟨hr, hne, hne'⟩ := classD4_isRoot_add hτ ha hσ₁ ha₁
    rw [EvenOddRadical.pinnedX_conj_of_isRoot hτ h2 ha hσ₁ hne hne' hr 1 (c σ₁), haμ, one_mul]
  have ha2 : pinnedX τ K a 1 * (pinnedX τ K μ (c σ₂) * pinnedX τ K σ₂ (c σ₂)) *
      (pinnedX τ K a 1)⁻¹ = pinnedX τ K μ (c σ₂) * pinnedX τ K σ₂ (c σ₂) := by
    have e1 : pinnedX τ K a 1 * pinnedX τ K μ (c σ₂) * (pinnedX τ K a 1)⁻¹ =
        pinnedX τ K μ (c σ₂) := by
      rw [(classD4_commute_pinnedX hτ ha hμ haμ' 1 (c σ₂)).eq, mul_inv_cancel_right]
    have e2 : pinnedX τ K a 1 * pinnedX τ K σ₂ (c σ₂) * (pinnedX τ K a 1)⁻¹ =
        pinnedX τ K σ₂ (c σ₂) := by
      rw [(classD4_commute_pinnedX hτ ha hσ₂ ha₂ 1 (c σ₂)).eq, mul_inv_cancel_right]
    calc pinnedX τ K a 1 * (pinnedX τ K μ (c σ₂) * pinnedX τ K σ₂ (c σ₂)) * (pinnedX τ K a 1)⁻¹
        = (pinnedX τ K a 1 * pinnedX τ K μ (c σ₂) * (pinnedX τ K a 1)⁻¹) *
            (pinnedX τ K a 1 * pinnedX τ K σ₂ (c σ₂) * (pinnedX τ K a 1)⁻¹) := by group
      _ = _ := by rw [e1, e2]
  have hμσ₁ : Commute (pinnedX τ K μ (c σ₂)) (pinnedX τ K σ₁ (c σ₁)) :=
    classD4_commute_pinnedX hτ hμ hσ₁ hμ₁ (c σ₂) (c σ₁)
  set g := pinnedX τ K a 1 * pinnedX τ K b 1 with hg
  have hgP : g * P' * g⁻¹ = P' := by
    rw [hg, mul_inv_rev, show pinnedX τ K a 1 * pinnedX τ K b 1 * P' *
        ((pinnedX τ K b 1)⁻¹ * (pinnedX τ K a 1)⁻¹) =
        pinnedX τ K a 1 * (pinnedX τ K b 1 * P' * (pinnedX τ K b 1)⁻¹) *
          (pinnedX τ K a 1)⁻¹ by group, (hcP hb hbF).eq, mul_inv_cancel_right,
      (hcP ha haF).eq, mul_inv_cancel_right]
  have hg1 : g * pinnedX τ K σ₁ (c σ₁) * g⁻¹ = pinnedX τ K μ (c σ₁) * pinnedX τ K σ₁ (c σ₁) := by
    rw [hg, mul_inv_rev, show pinnedX τ K a 1 * pinnedX τ K b 1 * pinnedX τ K σ₁ (c σ₁) *
        ((pinnedX τ K b 1)⁻¹ * (pinnedX τ K a 1)⁻¹) =
        pinnedX τ K a 1 * (pinnedX τ K b 1 * pinnedX τ K σ₁ (c σ₁) * (pinnedX τ K b 1)⁻¹) *
          (pinnedX τ K a 1)⁻¹ by group, hb1, ha1]
  have hg2 : g * pinnedX τ K σ₂ (c σ₂) * g⁻¹ = pinnedX τ K μ (c σ₂) * pinnedX τ K σ₂ (c σ₂) := by
    rw [hg, mul_inv_rev, show pinnedX τ K a 1 * pinnedX τ K b 1 * pinnedX τ K σ₂ (c σ₂) *
        ((pinnedX τ K b 1)⁻¹ * (pinnedX τ K a 1)⁻¹) =
        pinnedX τ K a 1 * (pinnedX τ K b 1 * pinnedX τ K σ₂ (c σ₂) * (pinnedX τ K b 1)⁻¹) *
          (pinnedX τ K a 1)⁻¹ by group, hb2, ha2]
  simp only [List.map_cons, List.prod_cons]
  rw [← hP']
  calc g * (pinnedX τ K σ₁ (c σ₁) * (pinnedX τ K σ₂ (c σ₂) * P')) * g⁻¹
      = (g * pinnedX τ K σ₁ (c σ₁) * g⁻¹) * (g * pinnedX τ K σ₂ (c σ₂) * g⁻¹) *
          (g * P' * g⁻¹) := by group
    _ = pinnedX τ K μ (c σ₁) * pinnedX τ K σ₁ (c σ₁) *
          (pinnedX τ K μ (c σ₂) * pinnedX τ K σ₂ (c σ₂)) * P' := by rw [hg1, hg2, hgP]
    _ = pinnedX τ K μ (c σ₁) * pinnedX τ K μ (c σ₂) *
          (pinnedX τ K σ₁ (c σ₁) * (pinnedX τ K σ₂ (c σ₂) * P')) := by
        rw [mul_assoc (pinnedX τ K μ (c σ₁)), ← mul_assoc (pinnedX τ K σ₁ (c σ₁)),
          ← hμσ₁.eq]
        group
    _ = pinnedX τ K μ (c σ₁ + c σ₂) *
          (pinnedX τ K σ₁ (c σ₁) * (pinnedX τ K σ₂ (c σ₂) * P')) := by rw [pinnedX_add]

theorem coeff_eq_of_commute_link
    [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {σ₁ σ₂ a b μ : Fin τ.rank → ℤ} {F' : List (Fin τ.rank → ℤ)}
    (hσ₁ : IsRoot τ σ₁) (hσ₂ : IsRoot τ σ₂) (hF' : ∀ σ ∈ F', IsRoot τ σ)
    (ha : IsRoot τ a) (hb : IsRoot τ b) (haμ : a + σ₁ = μ) (hbμ : b + σ₂ = μ)
    (ha₁ : iform a σ₁ = -1) (hb₂ : iform b σ₂ = -1) (hb₁ : 0 ≤ iform b σ₁)
    (ha₂ : 0 ≤ iform a σ₂) (haμ' : 0 ≤ iform a μ) (hμ₁ : 0 ≤ iform μ σ₁)
    (haF : ∀ σ ∈ F', 0 ≤ iform a σ) (hbF : ∀ σ ∈ F', 0 ≤ iform b σ) (hμp : 0 < height μ)
    (c : (Fin τ.rank → ℤ) → K)
    (hcomm : pinnedX τ K a 1 * pinnedX τ K b 1 *
        ((σ₁ :: σ₂ :: F').map fun σ => pinnedX τ K σ (c σ)).prod =
      ((σ₁ :: σ₂ :: F').map fun σ => pinnedX τ K σ (c σ)).prod *
        (pinnedX τ K a 1 * pinnedX τ K b 1)) :
    c σ₁ = c σ₂ := by
  have hμ : IsRoot τ μ := by
    rw [← haμ]
    exact (classD4_isRoot_add hτ ha hσ₁ ha₁).1
  have h := conj_link_eq (K := K) hτ hσ₁ hσ₂ hF' ha hb haμ hbμ ha₁ hb₂ hb₁ ha₂ haμ' hμ₁ haF hbF c
  rw [hcomm, mul_inv_cancel_right] at h
  have h1 : pinnedX τ K μ (c σ₁ + c σ₂) = 1 := by
    have h' := congrArg (· * (((σ₁ :: σ₂ :: F').map fun σ => pinnedX τ K σ (c σ)).prod)⁻¹) h
    simpa using h'.symm
  have h0 : ([μ].map fun σ => pinnedX τ K σ ((fun _ => c σ₁ + c σ₂) σ)).prod =
      ([μ].map fun σ => pinnedX τ K σ ((fun _ => (0 : K)) σ)).prod := by
    simp [h1, pinnedX_zero]
  have h2 := pinnedX_list_prod_injective [μ] (List.nodup_singleton μ)
    (fun σ hσ => by rw [List.mem_singleton.1 hσ]; exact ⟨hμ, hμp⟩) _ _ h0 μ (by simp)
  rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
  exact h2

theorem eq_one_or_eq_of_coeffs
    (hK : Nat.card K = 2) {F : List (Fin τ.rank → ℤ)} (c : (Fin τ.rank → ℤ) → K)
    (hc : ∀ σ ∈ F, ∀ σ' ∈ F, c σ = c σ') :
    (F.map fun σ => pinnedX τ K σ (c σ)).prod = 1 ∨
      (F.map fun σ => pinnedX τ K σ (c σ)).prod = (F.map fun σ => pinnedX τ K σ 1).prod := by
  rcases F.eq_nil_or_concat with rfl | ⟨L, σ₀, rfl⟩
  · exact Or.inl (by simp)
  have hσ₀ : σ₀ ∈ L.concat σ₀ := by simp
  rcases E8.eq_zero_or_eq_one_of_card_two_e8 hK (c σ₀) with h0 | h1
  · refine Or.inl (List.prod_eq_one fun x hx => ?_)
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    rw [hc σ hσ σ₀ hσ₀, h0, pinnedX_zero]
  · refine Or.inr (congrArg List.prod (List.map_congr_left fun σ hσ => ?_))
    rw [hc σ hσ σ₀ hσ₀, h1]

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
