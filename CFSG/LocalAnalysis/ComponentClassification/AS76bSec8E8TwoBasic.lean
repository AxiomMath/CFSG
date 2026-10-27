module

public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open scoped commutatorElement

variable {K : Type} [Field K]

theorem eq_zero_or_eq_one_of_card_two_e8 (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  by_contra h
  rw [not_or] at h
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have h3 : ({0, 1, c} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)]
  have hle := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem mem_posUnipotent_of_mem_borelGroup_two
    (hK : Nat.card K = 2) {g : ModGL .E8 K}
    (hg : g ∈ borelGroup .E8 K) : g ∈ posUnipotent .E8 K := by
  have hT : torusGroup .E8 K = ⊥ := by
    rw [torusGroup, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    have ht : t = 1 :=
      Units.ext ((eq_zero_or_eq_one_of_card_two_e8 hK (t : K)).resolve_left t.ne_zero)
    subst ht
    show torusElt .E8 K i 1 ∈ ({1} : Set (ModGL .E8 K))
    rw [torusElt_one]
    exact Set.mem_singleton 1
  rw [borelGroup, hT, bot_sup_eq] at hg
  exact hg

theorem height_le_of_isRoot_e8 {γ : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot .E8 γ) : height γ ≤ 29 := by
  have h : ∀ l ∈ Tag.artifactRoots .E8, l.sum ≤ 29 := by
    decide +kernel
  have h1 := h _ (isRoot_iff_mem_artifactRoots.1 hγ)
  rw [List.sum_ofFn] at h1
  exact h1

theorem exists_eq_prod_of_mem_rootSpan_e8
    {L : List (Fin Tag.E8.rank → ℤ)} (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot .E8 α ∧ 0 < height α)
    (hht : ∀ α ∈ L, 15 ≤ height α) {z : ModGL .E8 K}
    (hz : z ∈ rootSpan .E8 K {γ | γ ∈ L}) :
    ∃ c : (Fin Tag.E8.rank → ℤ) → K, z = (L.map fun α => pinnedX .E8 K α (c α)).prod := by
  classical
  have hclosed : ∀ α ∈ {γ | γ ∈ L}, ∀ β ∈ {γ | γ ∈ L}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot .E8 (a • α + b • β) → a • α + b • β ∈ {γ | γ ∈ L} := by
    intro α hα β hβ a b ha hb hr
    exfalso
    have h1 := height_le_of_isRoot_e8 hr
    have hpt : ∀ x, (a • α + b • β) x = a * α x + b * β x := fun x => by
      simp [nsmul_eq_mul]
    have h2 : height (a • α + b • β) = a * height α + b * height β := by
      simp only [height, hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h3 := hht α hα
    have h4 := hht β hβ
    have h5 : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have h6 : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hinj : Function.Injective L.get := List.nodup_iff_injective_get.1 hnd
  have hrange : Set.range L.get = {γ | γ ∈ L} := by
    ext γ
    rw [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K (fun α hα => hL α hα) hclosed L.get hinj
    hrange).surjOn hz
  refine ⟨Function.extend L.get d 0, ?_⟩
  rw [← hd]
  have e : (List.ofFn fun i => pinnedX .E8 K (L.get i) (d i)) =
      (List.ofFn L.get).map fun α => pinnedX .E8 K α (Function.extend L.get d 0 α) := by
    rw [List.map_ofFn]
    refine List.ofFn_inj.2 (funext fun i => ?_)
    rw [Function.comp_apply, hinj.extend_apply]
  simp only
  rw [e, List.ofFn_get]

theorem conj_list_prod_map_e8 {G ι : Type*} [Group G] (g : G) (f : ι → G) (l : List ι) :
    g * (l.map f).prod * g⁻¹ = (l.map fun i => g * f i * g⁻¹).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← ih]
    group

theorem coeff_eq_zero_of_commute_neg_e8
    [CharP K 2] {L₁ L₂ : List (Fin Tag.E8.rank → ℤ)} {lam ρ : Fin Tag.E8.rank → ℤ}
    (hnd : (L₁ ++ [lam - ρ, lam] ++ L₂).Nodup)
    (hpos : ∀ α ∈ L₁ ++ [lam - ρ, lam] ++ L₂, IsRoot .E8 α ∧ 0 < height α)
    (hρ : IsRoot .E8 ρ) (hne : -ρ ≠ lam ∧ -ρ ≠ -lam)
    (hL : ∀ α ∈ L₁ ++ L₂, -ρ ≠ α ∧ -ρ ≠ -α ∧ ¬ IsRoot .E8 (-ρ + α))
    (c : (Fin Tag.E8.rank → ℤ) → K)
    (hcomm : pinnedX .E8 K (-ρ) 1 *
        ((L₁ ++ [lam] ++ L₂).map fun α => pinnedX .E8 K α (c α)).prod =
      ((L₁ ++ [lam] ++ L₂).map fun α => pinnedX .E8 K α (c α)).prod * pinnedX .E8 K (-ρ) 1) :
    c lam = 0 := by
  classical
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hnρ : IsRoot .E8 (-ρ) := IsRoot.neg hρ
  have hlam : IsRoot .E8 lam := (hpos lam (by simp)).1
  have hroot : IsRoot .E8 (-ρ + lam) := by
    rw [neg_add_eq_sub]
    exact (hpos (lam - ρ) (by simp)).1
  have hL' : ∀ α ∈ L₁ ++ L₂, pinnedX .E8 K (-ρ) 1 * pinnedX .E8 K α (c α) *
      (pinnedX .E8 K (-ρ) 1)⁻¹ = pinnedX .E8 K α (c α) := fun α hα =>
    EvenOddRadical.pinnedX_conj_of_not hτ hnρ
      (hpos α (by rcases List.mem_append.1 hα with h | h <;> simp [h])).1 (hL α hα).1
      (hL α hα).2.1 (hL α hα).2.2 1 (c α)
  have hL₁' := fun α (hα : α ∈ L₁) => hL' α (List.mem_append_left _ hα)
  have hL₂' := fun α (hα : α ∈ L₂) => hL' α (List.mem_append_right _ hα)
  have hlam' : pinnedX .E8 K (-ρ) 1 * pinnedX .E8 K lam (c lam) * (pinnedX .E8 K (-ρ) 1)⁻¹ =
      pinnedX .E8 K (lam - ρ) (c lam) * pinnedX .E8 K lam (c lam) := by
    rw [EvenOddRadical.pinnedX_conj_of_isRoot hτ h2 hnρ hlam hne.1 hne.2 hroot 1 (c lam),
      one_mul, neg_add_eq_sub]
  set P₁ := (L₁.map fun α => pinnedX .E8 K α (c α)).prod with hP₁
  set P₂ := (L₂.map fun α => pinnedX .E8 K α (c α)).prod with hP₂
  have hconj : P₁ * (pinnedX .E8 K (lam - ρ) (c lam) * pinnedX .E8 K lam (c lam)) * P₂ =
      P₁ * pinnedX .E8 K lam (c lam) * P₂ := by
    have h1 := conj_list_prod_map_e8 (pinnedX .E8 K (-ρ) 1)
      (fun α => pinnedX .E8 K α (c α)) (L₁ ++ [lam] ++ L₂)
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
  set c₁ : (Fin Tag.E8.rank → ℤ) → K := Function.update c (lam - ρ) (c lam) with hc₁
  set c₂ : (Fin Tag.E8.rank → ℤ) → K := Function.update c (lam - ρ) 0 with hc₂
  have hof : ∀ (L : List (Fin Tag.E8.rank → ℤ)), (∀ α ∈ L, α ∈ L₁ ++ L₂) → ∀ v : K,
      (L.map fun α => pinnedX .E8 K α (Function.update c (lam - ρ) v α)) =
        L.map fun α => pinnedX .E8 K α (c α) := fun L hL v =>
    List.map_congr_left fun α hα => by
      rw [Function.update_of_ne (fun h => hnot (by rw [← h]; exact hL α hα))]
  have heq : ((L₁ ++ [lam - ρ, lam] ++ L₂).map fun α => pinnedX .E8 K α (c₁ α)).prod =
      ((L₁ ++ [lam - ρ, lam] ++ L₂).map fun α => pinnedX .E8 K α (c₂ α)).prod := by
    have e : ∀ v : K, ((L₁ ++ [lam - ρ, lam] ++ L₂).map fun α =>
        pinnedX .E8 K α (Function.update c (lam - ρ) v α)).prod =
          P₁ * (pinnedX .E8 K (lam - ρ) v * pinnedX .E8 K lam (c lam)) * P₂ := fun v => by
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

theorem coeff_eq_zero_of_commute_neg_mem_e8
    [CharP K 2] {L : List (Fin Tag.E8.rank → ℤ)} (hnd : L.Nodup)
    (hpos : ∀ α ∈ L, IsRoot .E8 α ∧ 0 < height α) {lam ρ : Fin Tag.E8.rank → ℤ} (hlam : lam ∈ L)
    (hρ : IsRoot .E8 ρ) (hlr : IsRoot .E8 (lam - ρ) ∧ 0 < height (lam - ρ)) (hlrL : lam - ρ ∉ L)
    (hne : -ρ ≠ lam ∧ -ρ ≠ -lam)
    (hL : ∀ α ∈ L, α ≠ lam → -ρ ≠ α ∧ -ρ ≠ -α ∧ ¬ IsRoot .E8 (-ρ + α))
    (c : (Fin Tag.E8.rank → ℤ) → K)
    (hcomm : pinnedX .E8 K (-ρ) 1 * (L.map fun α => pinnedX .E8 K α (c α)).prod =
      (L.map fun α => pinnedX .E8 K α (c α)).prod * pinnedX .E8 K (-ρ) 1) :
    c lam = 0 := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hlam
  have e : L₁ ++ lam :: L₂ = L₁ ++ [lam] ++ L₂ := by simp
  have e' : L₁ ++ [lam - ρ, lam] ++ L₂ = L₁ ++ (lam - ρ) :: (lam :: L₂) := by simp
  have hlam' : lam ∉ L₁ ++ L₂ := (List.nodup_cons.1 (List.perm_middle.nodup_iff.1 hnd)).1
  refine coeff_eq_zero_of_commute_neg_e8 (L₁ := L₁) (L₂ := L₂) ?_ ?_ hρ hne ?_ c ?_
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

theorem wordProd_smul_eq_foldr_e8
    (ω : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem .E8).wordProd ω • v = ω.foldr (reflect .E8) v := by
  induction ω with
  | nil => simp
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

@[expose] noncomputable def e8WordElt
    (ω : List (Fin Tag.E8.rank)) : adjointGroup .E8 K :=
  ⟨(ω.map fun i => weylElt .E8 K i 1).prod, list_prod_mem fun _ hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup i 1⟩

theorem coeff_smul_eq_of_commute_word_e8
    [CharP K 2] {F : List (Fin Tag.E8.rank → ℤ)} (hnd : F.Nodup)
    (hF : ∀ σ ∈ F, IsRoot .E8 σ ∧ 0 < height σ) (horth : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (ω : List (Fin Tag.E8.rank)) (hperm : (F.map fun σ => ω.foldr (reflect .E8) σ).Perm F)
    (hinv : ∀ σ ∈ F, ω.foldr (reflect .E8) (ω.foldr (reflect .E8) σ) = σ)
    (c : (Fin Tag.E8.rank → ℤ) → K)
    (hcomm : (ω.map fun i => weylElt .E8 K i 1).prod *
        (F.map fun σ => pinnedX .E8 K σ (c σ)).prod =
      (F.map fun σ => pinnedX .E8 K σ (c σ)).prod * (ω.map fun i => weylElt .E8 K i 1).prod) :
    ∀ σ ∈ F, c (ω.foldr (reflect .E8) σ) = c σ := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  set n := (ω.map fun i => weylElt .E8 K i 1).prod with hn
  set act : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) := fun σ => ω.foldr (reflect .E8) σ
    with hact
  set F' := F.map act with hF'
  have hconj : n * (F.map fun σ => pinnedX .E8 K σ (c σ)).prod * n⁻¹ =
      (F'.map fun μ => pinnedX .E8 K μ (c (act μ))).prod := by
    rw [conj_list_prod_map_e8, hF', List.map_map]
    refine congrArg List.prod (List.map_congr_left fun σ hσ => ?_)
    simp only [Function.comp_apply]
    rw [hn, CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo ω (hF σ hσ).1 (c σ),
      wordProd_smul_eq_foldr_e8]
    show pinnedX .E8 K (act σ) (c σ) = pinnedX .E8 K (act σ) (c (act (act σ)))
    rw [show act (act σ) = σ from hinv σ hσ]
  have hw : (F.map fun σ => pinnedX .E8 K σ (c σ)).prod =
      (F'.map fun μ => pinnedX .E8 K μ (c μ)).prod :=
    classD4_frame_prod_perm hτ (fun σ hσ => (hF σ hσ).1) horth hperm.symm c
  have heq : (F'.map fun μ => pinnedX .E8 K μ (c (act μ))).prod =
      (F'.map fun μ => pinnedX .E8 K μ (c μ)).prod := by
    rw [← hconj, ← hw, hcomm, mul_inv_cancel_right]
  have hnd' : F'.Nodup := hperm.nodup_iff.2 hnd
  have hF'' : ∀ μ ∈ F', IsRoot .E8 μ ∧ 0 < height μ := fun μ hμ => hF μ (hperm.subset hμ)
  have h := pinnedX_list_prod_injective F' hnd' hF'' (fun μ => c (act μ)) c heq
  intro σ hσ
  have h1 := h (act σ) (List.mem_map_of_mem hσ)
  simp only [hact] at h1 ⊢
  rw [hinv σ hσ] at h1
  exact h1.symm

theorem wordProd_comm_framePt_e8
    [CharP K 2] {F : List (Fin Tag.E8.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E8 σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (ω : List (Fin Tag.E8.rank))
    (hperm : (F.map fun σ => ω.foldr (reflect .E8) σ).Perm F) :
    (ω.map fun i => weylElt .E8 K i 1).prod * (F.map fun σ => pinnedX .E8 K σ 1).prod =
      (F.map fun σ => pinnedX .E8 K σ 1).prod * (ω.map fun i => weylElt .E8 K i 1).prod := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  set n := (ω.map fun i => weylElt .E8 K i 1).prod with hn
  set P := (F.map fun σ => pinnedX .E8 K σ 1).prod with hP
  have hconj : n * P * n⁻¹ = P := by
    rw [hP, conj_list_prod_map_e8]
    have e : (F.map fun σ => n * pinnedX .E8 K σ 1 * n⁻¹) =
        (F.map fun σ => ω.foldr (reflect .E8) σ).map fun μ => pinnedX .E8 K μ 1 := by
      rw [List.map_map]
      refine List.map_congr_left fun σ hσ => ?_
      simp only [Function.comp_apply]
      rw [hn, CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo ω (hF σ hσ) 1,
        wordProd_smul_eq_foldr_e8]
    rw [e]
    exact (classD4_frame_prod_perm hτ hF horth hperm.symm fun _ => (1 : K)).symm
  calc n * P = n * P * n⁻¹ * n := by group
    _ = P * n := by rw [hconj]

theorem coeff_eq_of_zipWith_eq_tail {V W R : Type*} (act : W → V → V) (c : V → R) :
    ∀ (a : V) (F : List V) (ws : List W), List.zipWith act ws (a :: F) = F →
      (∀ ω ∈ ws, ∀ σ ∈ a :: F, c (act ω σ) = c σ) → ∀ σ ∈ a :: F, c σ = c a
  | a, [], _, _, _, σ, hσ => by rw [List.mem_singleton.1 hσ]
  | a, b :: F, [], h, _, _, _ => by simp at h
  | a, b :: F, ω :: ws, h, hc, σ, hσ => by
    rw [List.zipWith_cons_cons, List.cons.injEq] at h
    have hb : c b = c a := by
      rw [← h.1]
      exact hc ω List.mem_cons_self a List.mem_cons_self
    have ih := coeff_eq_of_zipWith_eq_tail act c b F ws h.2 fun ω' hω' σ' hσ' =>
      hc ω' (List.mem_cons_of_mem _ hω') σ' (List.mem_cons_of_mem _ hσ')
    rcases List.mem_cons.1 hσ with rfl | hσ
    · rfl
    · rw [ih σ hσ, hb]

theorem coeff_eq_coeff_of_zipWith_eq_tail {V W R : Type*} (act : W → V → V) (c : V → R)
    {F : List V} {ws : List W} (h : List.zipWith act ws F = F.tail)
    (hc : ∀ ω ∈ ws, ∀ σ ∈ F, c (act ω σ) = c σ) : ∀ σ ∈ F, ∀ σ' ∈ F, c σ = c σ' := by
  cases F with
  | nil => exact fun σ hσ => absurd hσ List.not_mem_nil
  | cons a F =>
    intro σ hσ σ' hσ'
    rw [coeff_eq_of_zipWith_eq_tail act c a F ws h hc σ hσ,
      coeff_eq_of_zipWith_eq_tail act c a F ws h hc σ' hσ']

theorem eq_one_or_eq_of_coeffs_e8
    (hK : Nat.card K = 2) {F : List (Fin Tag.E8.rank → ℤ)} (c : (Fin Tag.E8.rank → ℤ) → K)
    (hc : ∀ σ ∈ F, ∀ σ' ∈ F, c σ = c σ') :
    (F.map fun σ => pinnedX .E8 K σ (c σ)).prod = 1 ∨
      (F.map fun σ => pinnedX .E8 K σ (c σ)).prod = (F.map fun σ => pinnedX .E8 K σ 1).prod := by
  rcases F.eq_nil_or_concat with rfl | ⟨L, σ₀, rfl⟩
  · exact Or.inl (by simp)
  have hσ₀ : σ₀ ∈ L.concat σ₀ := by simp
  rcases eq_zero_or_eq_one_of_card_two_e8 hK (c σ₀) with h0 | h1
  · refine Or.inl (List.prod_eq_one fun x hx => ?_)
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    rw [hc σ hσ σ₀ hσ₀, h0, pinnedX_zero]
  · refine Or.inr (congrArg List.prod (List.map_congr_left fun σ hσ => ?_))
    rw [hc σ hσ σ₀ hσ₀, h1]

end CFSG.ComponentClassification.RankTwoExceptional.E8
