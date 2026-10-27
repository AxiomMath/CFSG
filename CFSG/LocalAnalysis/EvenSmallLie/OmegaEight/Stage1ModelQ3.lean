module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelNorm
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Final
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelLink

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Transport

variable {G X Y : Type*} [Group G] [Group X] [Group Y] {L : Subgroup G} {L' : Subgroup X}
  {L'' : Subgroup Y}

theorem pullE_trans (θ : L ≃* L') (τ : L' ≃* L'') {y : Y} (hy : y ∈ L'') :
    pullE (θ.trans τ) y hy = pullE θ (τ.symm ⟨y, hy⟩ : X) (τ.symm ⟨y, hy⟩).2 := rfl

theorem pull_trans (θ : L ≃* L') (τ : L' ≃* L'') (H : Subgroup Y) :
    pull (θ.trans τ) H = pull θ (pull τ H) := by
  ext g
  rw [mem_pull, mem_pull]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, mem_pull.2 ⟨(θ ⟨g, hg⟩).2, h⟩⟩
  · rintro ⟨hg, h⟩
    obtain ⟨_, h'⟩ := mem_pull.1 h
    exact ⟨hg, h'⟩

theorem closure_pullE_le (θ : L ≃* L') {ι : Type*} (f : ι → X) (hf : ∀ i, f i ∈ L') :
    closure (Set.range fun i => pullE θ (f i) (hf i)) ≤ pull θ (closure (Set.range f)) := by
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  exact (pullE_mem_pull (hf i)).2 (subset_closure ⟨i, rfl⟩)

theorem pull_inf_bot (θ : L ≃* L') {A B : Subgroup X} (h : A ⊓ B = ⊥) :
    pull θ A ⊓ pull θ B = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hA, hB⟩
  obtain ⟨hgL, hA'⟩ := mem_pull.1 hA
  obtain ⟨_, hB'⟩ := mem_pull.1 hB
  have hAB : ((θ ⟨g, hgL⟩ : L') : X) ∈ A ⊓ B := ⟨hA', hB'⟩
  rw [h, mem_bot] at hAB
  have h1 : θ ⟨g, hgL⟩ = 1 := Subtype.ext hAB
  have h2 : (⟨g, hgL⟩ : L) = 1 := θ.injective (by rw [h1, map_one])
  exact mem_bot.2 (congrArg Subtype.val h2)

theorem mem_pull_of_normalizes [Finite X] (θ : L ≃* L') {U' : Subgroup X} (hU : U' ≤ L')
    (h : ∀ x ∈ L', x ∈ normalizer (U' : Set X) → x ∈ U') {g : G} (hg : g ∈ L)
    (hgN : g ∈ normalizer (pull θ U' : Set G)) : g ∈ pull θ U' := by
  refine mem_pull.2 ⟨hg, h _ (θ ⟨g, hg⟩).2 (OmegaEight.mem_normalizer_of_conj_mem fun y hy => ?_)⟩
  have h1 : pullE θ y (hU hy) ∈ pull θ U' := (pullE_mem_pull (hU hy)).2 hy
  have h2 := (mem_normalizer_iff.1 hgN _).1 h1
  have h3 := theta_mem_of_mem_pull h2
  rw [theta_conj hg (pullE_mem_L _), theta_pullE] at h3
  exact h3

end Transport

namespace Model

@[expose] noncomputable def rho2 : OmegaEight.autT :=
  ⟨OmegaEight.gen 8 * OmegaEight.gen 8,
    mul_mem (OmegaEight.gen_mem_autT (by norm_num)) (OmegaEight.gen_mem_autT (by norm_num))⟩

theorem rep_rho2 : Rep 360 rho2Arr (rho2 : Equiv.Perm (Fin 360)) :=
  rep_compA (OmegaEight.rep_gen (by norm_num)) (OmegaEight.rep_gen (by norm_num))

theorem rep_rho2_inv : Rep 360 (invCand 360 rho2Arr) (rho2 : Equiv.Perm (Fin 360))⁻¹ :=
  rep_inv_of_isInvA rep_rho2 q3_parts.2.2.2.2.2.2.2.2.2.1

@[expose] noncomputable def sigL : MulAut (Lm .plus) :=
  (OmegaEight.omegaRestrictEquiv.symm.trans (OmegaEight.autConj rho2)).trans
    OmegaEight.omegaRestrictEquiv

theorem rep_sig {x : Lm .plus} {x' : OmegaEight.omegaT}
    (hx : (OmegaEight.omegaRestrictEquiv x' : Lm .plus) = x) {t : Array ℕ}
    (ht : Rep 360 t (x' : Equiv.Perm (Fin 360))) :
    Rep (deg .plus) (sigArr t) (sigL x : Equiv.Perm (Fin (deg .plus))) := by
  subst hx
  have e : sigL (OmegaEight.omegaRestrictEquiv x') =
      OmegaEight.omegaRestrictEquiv (OmegaEight.autConj rho2 x') := by
    change OmegaEight.omegaRestrictEquiv (OmegaEight.autConj rho2
      (OmegaEight.omegaRestrictEquiv.symm (OmegaEight.omegaRestrictEquiv x'))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [e]
  intro j
  have hj' : (j : ℕ) < 120 := j.2
  have hrep : Rep 360 (conjA 360 rho2Arr t)
      ((rho2 : Equiv.Perm (Fin 360)) * x' * (rho2 : Equiv.Perm (Fin 360))⁻¹) :=
    rep_compA (rep_compA rep_rho2 ht) rep_rho2_inv
  rw [sigArr, OmegaEight.copy0Arr_getElem! _ hj', hrep.apply (by omega)]
  change _ = ((OmegaEight.omegaRes (OmegaEight.autConj rho2 x') ⟨j, hj'⟩ : Fin 120) : ℕ)
  rw [OmegaEight.omegaRes_apply_val, OmegaEight.autConj_apply]

theorem lettersOK_uWords (k : Fin 6) : lettersOK 17 (uWordsPlus.getD k []) = true := by
  fin_cases k <;> decide

@[expose] noncomputable def utL (k : Fin 6) : OmegaEight.omegaT :=
  ⟨permOfArr 360 (utArr k), (OmegaEight.omegaW_spec (lettersOK_uWords k)).2⟩

theorem rep_utL (k : Fin 6) : Rep 360 (utArr k) ((utL k : OmegaEight.omegaT) : Equiv.Perm (Fin 360)) :=
  (OmegaEight.omegaW_spec (lettersOK_uWords k)).1

theorem restrict_utL (k : Fin 6) :
    (OmegaEight.omegaRestrictEquiv (utL k) : Lm .plus) = ⟨uM .plus k, uM_mem_L (ε := .plus) k⟩ := by
  have hk := (q3_parts.2.2.2.2.2.2.2.2.2.2.1 k k.2).1
  apply Subtype.ext
  apply Equiv.ext
  intro j
  apply Fin.ext
  change ((OmegaEight.omegaRes (utL k) j : Fin 120) : ℕ) = ((uM .plus k) j : ℕ)
  rw [OmegaEight.omegaRes_apply_val]
  have h1 := (rep_utL k).apply (show (j : ℕ) < 360 by have := j.2; omega)
  have h2 := (rep_uM (ε := .plus) k).1.apply j.2
  have h3 := allLt_spec hk j.2
  rw [beq_iff_eq, OmegaEight.copy0Arr_getElem! _ j.2] at h3
  rw [← h1, h3, h2]
  rfl

@[expose] noncomputable def sigTargetM : Fin 6 → Equiv.Perm (Fin (deg .plus))
  | 0 => psiM .plus (Pi.single 0 1)
  | 1 => psiM .plus (Pi.single 1 1)
  | 2 => uM .plus 3
  | 3 => psiM .plus (Pi.single 2 1)
  | 4 => uM .plus 4
  | 5 => uM .plus 5

theorem rep_sigTarget (j : Fin 6) : Rep (deg .plus) (sigTarget j) (sigTargetM j) := by
  have hp : ∀ i : Fin 6, Rep (deg .plus) (psiArr .plus (2 ^ (i : ℕ))) (psiM .plus (Pi.single i 1)) :=
    fun i => by
      have := (rep_psiM (ε := .plus) (Pi.single i 1)).1
      rwa [vecBits_single] at this
  fin_cases j
  · exact hp 0
  · exact hp 1
  · exact (rep_uM (ε := .plus) 3).1
  · exact hp 2
  · exact (rep_uM (ε := .plus) 4).1
  · exact (rep_uM (ε := .plus) 5).1

theorem sigL_psiM (j : Fin 6) :
    (sigL ⟨psiM .plus (Pi.single j 1), psiM_mem_L _⟩ : Equiv.Perm (Fin (deg .plus))) =
      sigTargetM j := by
  have ht : Rep 360 (psiTT .plus (2 ^ (j : ℕ))) (psiTMp (Pi.single j 1)) := by
    have := (rep_psiTM (ε := .plus) (Pi.single j 1)).1
    rwa [vecBits_single] at this
  have h1 := rep_sig (restrict_psiTMp (Pi.single j 1)) ht
  exact eq_of_eqA h1 (rep_sigTarget j) (q3_parts.2.2.2.2.2.2.2.2.2.2.2 j j.2)

theorem sigL_uM_mem (k : Fin 6) :
    (sigL ⟨uM .plus k, uM_mem_L (ε := .plus) k⟩ : Equiv.Perm (Fin (deg .plus))) ∈ UQm .plus :=
  (memU_iff (rep_sig (restrict_utL k) (rep_utL k))).1
    (q3_parts.2.2.2.2.2.2.2.2.2.2.1 k k.2).2

theorem sigTargetM_mem (j : Fin 6) : sigTargetM j ∈ UQm .plus := by
  fin_cases j
  · exact psiM_mem_U _
  · exact psiM_mem_U _
  · exact uM_mem_U 3
  · exact psiM_mem_U _
  · exact uM_mem_U 4
  · exact uM_mem_U 5

theorem UQm_le_pull_sigL : UQm .plus ≤ pull sigL (UQm .plus) := by
  refine (UQm_eq (ε := .plus)).le.trans ((closure_le _).2 ?_)
  rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
  · exact mem_pull.2 ⟨psiM_mem_L _, by rw [sigL_psiM j]; exact sigTargetM_mem j⟩
  · exact mem_pull.2 ⟨uM_mem_L (ε := .plus) k, sigL_uM_mem k⟩

theorem sigL_mem_UQm_iff (z : Lm .plus) :
    (sigL z : Equiv.Perm (Fin (deg .plus))) ∈ UQm .plus ↔
      (z : Equiv.Perm (Fin (deg .plus))) ∈ UQm .plus := by
  have hUL : UQm .plus ≤ Lm .plus := (modelLinkFacts .plus).U_le_L
  have heq : UQm .plus = pull sigL (UQm .plus) :=
    eq_of_le_of_card_ge UQm_le_pull_sigL (by rw [card_pull hUL])
  constructor
  · intro h
    rw [heq]
    exact mem_pull.2 ⟨z.2, h⟩
  · intro h
    have := heq ▸ h
    obtain ⟨_, h'⟩ := mem_pull.1 this
    exact h'

theorem pull_sigL_symm_UQm : pull sigL.symm (UQm .plus) = UQm .plus := by
  ext y
  rw [mem_pull]
  constructor
  · rintro ⟨hy, h⟩
    have := (sigL_mem_UQm_iff (sigL.symm ⟨y, hy⟩)).2 h
    simpa using this
  · intro hy
    refine ⟨(modelLinkFacts .plus).U_le_L hy, ?_⟩
    apply (sigL_mem_UQm_iff _).1
    simpa using hy

theorem sigL_aM : sigL ⟨aM .plus, (modelLinkFacts .plus).a_mem_L⟩ =
    ⟨aM .plus, (modelLinkFacts .plus).a_mem_L⟩ :=
  Subtype.ext (sigL_psiM 0)

end Model


variable {G : Type} [Group G]

theorem exists_link_plus_two {L : Subgroup G} (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) :
    ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G)
      (Q₃ P₃ : Subgroup G) (ψ₃ : V6 → G) (p₃ u₃ : Fin 6 → G),
      RadicalData .plus L U Q P a ψ p ∧ UGens .plus U Q ψ u ∧
        LinkFacts .plus L U Q P a ψ p u ∧ AutCent L Q ∧
      closure (Set.range u) ⊓ Q = ⊥ ∧ (∀ x ∈ L, x ∈ normalizer (U : Set G) → x ∈ U) ∧
      RadicalData .plus L U Q₃ P₃ a ψ₃ p₃ ∧ UGens .plus U Q₃ ψ₃ u₃ ∧
        LinkFacts .plus L U Q₃ P₃ a ψ₃ p₃ u₃ ∧ AutCent L Q₃ ∧
      ψ₃ (Pi.single 0 1) = ψ (Pi.single 0 1) ∧ ψ₃ (Pi.single 1 1) = ψ (Pi.single 1 1) ∧
      ψ₃ (Pi.single 2 1) = u 3 ∧ ψ₃ (Pi.single 3 1) = ψ (Pi.single 2 1) ∧
      ψ₃ (Pi.single 4 1) = u 4 ∧ ψ₃ (Pi.single 5 1) = u 5 := by
  obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT hL
  set θ : L ≃* Model.Lm .plus :=
    (OmegaEight.mulEquivQuotientCenter hZ).symm.trans (e.trans OmegaEight.omegaRestrictEquiv)
  set θ₃ : L ≃* Model.Lm .plus := θ.trans Model.sigL.symm
  have hM := Model.modelLinkFacts .plus
  have hodd := OmegaEight.involutionsInOddPart_of_center_eq_bot hZ hL
  have hF := hM.transport θ
  have hA := (Model.autCent .plus).transport hM.Q_le_L θ
  have hF₃ := hM.transport θ₃
  have hA₃ := (Model.autCent .plus).transport hM.Q_le_L θ₃
  have hU₃ : pull θ₃ (Model.UQm .plus) = pull θ (Model.UQm .plus) := by
    rw [pull_trans, Model.pull_sigL_symm_UQm]
  have ha₃ : pullE θ₃ (Model.aM .plus) hM.a_mem_L = pullE θ (Model.aM .plus) hM.a_mem_L := by
    rw [pullE_trans, MulEquiv.symm_symm, Model.sigL_aM]
  rw [hU₃, ha₃] at hF₃
  have hψ₃ : ∀ j : Fin 6, pullE θ₃ (Model.psiM .plus (Pi.single j 1)) (hM.ψ_mem_L _) =
      pullE θ (Model.sigTargetM j) (by
        rw [← Model.sigL_psiM j]
        exact (Model.sigL ⟨Model.psiM .plus (Pi.single j 1), _⟩).2) := by
    intro j
    rw [pullE_trans, MulEquiv.symm_symm]
    exact pullE_congr (Model.sigL_psiM j) _ _
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF.radicalData hodd, ⟨hF.u_mem, hF.u_act, hF.U_le⟩,
    hF, hA, ?_, ?_, hF₃.radicalData hodd, ⟨hF₃.u_mem, hF₃.u_act, hF₃.U_le⟩, hF₃, hA₃,
    hψ₃ 0, hψ₃ 1, hψ₃ 2, hψ₃ 3, hψ₃ 4, hψ₃ 5⟩
  · rw [eq_bot_iff]
    refine le_trans (inf_le_inf_right _ (closure_pullE_le θ (Model.uM .plus) hM.u_mem_L)) ?_
    rw [pull_inf_bot θ Model.closure_uM_inf_QMm]
  · intro x hx hxN
    exact mem_pull_of_normalizes θ hM.U_le_L (fun y hy hyN => Model.normalizer_UQm hy hyN) hx hxN


theorem normalizer_sup_of_shapeA [Finite G] {t : G} {L U : Subgroup G} (hA : ShapeA t L)
    (hUL : U ≤ L) (hN : ∀ x ∈ L, x ∈ normalizer (U : Set G) → x ∈ U) :
    ∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), x * t = t * x →
      x ∈ U ⊔ zpowers t := by
  have hcomm : ∀ y ∈ U, ∀ c ∈ zpowers t, y * c = c * y := fun y hy c hc => by
    rcases hA.mem_zpowers_iff.1 hc with rfl | rfl
    · rw [mul_one, one_mul]
    · exact hA.commute_of_mem (hUL hy)
  have hsup : ∀ z ∈ (U ⊔ zpowers t : Subgroup G), z ∈ L → z ∈ U := by
    intro z hz hzL
    obtain ⟨y, hy, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hz
    rcases hA.mem_zpowers_iff.1 hc with rfl | rfl
    · rwa [mul_one]
    · exfalso
      apply hA.not_mem
      have := mul_mem (inv_mem (hUL hy)) hzL
      rwa [inv_mul_cancel_left] at this
  have htN : t ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) :=
    le_normalizer (mem_sup_right (mem_zpowers t))
  intro x hxN hxt
  obtain ⟨l, hl, hxl⟩ := hA.mem_iff.1 (mem_centralizer_singleton_iff.2 hxt)
  have hlN : l ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) := by
    rcases hxl with rfl | rfl
    · exact hxN
    · have := mul_mem hxN (inv_mem htN)
      rwa [mul_inv_cancel_right] at this
  have hlU : l ∈ normalizer (U : Set G) :=
    OmegaEight.mem_normalizer_of_conj_mem fun y hy =>
      hsup _ ((mem_normalizer_iff.1 hlN y).1 (mem_sup_left hy))
        (mul_mem (mul_mem hl (hUL hy)) (inv_mem hl))
  have hlU' := hN l hl hlU
  rcases hxl with rfl | rfl
  · exact mem_sup_left hlU'
  · exact mul_mem (mem_sup_left hlU') (mem_sup_right (mem_zpowers t))

theorem exists_link_plus' [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {L : Subgroup G} (hZ : center L = ⊥)
    (hL : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {t : G} (hA : ShapeA t L) :
    ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G),
      Setup .plus t L U Q P a ψ p ∧ UGens .plus U Q ψ u ∧ LinkFacts .plus L U Q P a ψ p u ∧
        AutCent L Q ∧
      closure (Set.range u) ⊓ Q = ⊥ ∧
      (∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), x * t = t * x →
        x ∈ U ⊔ zpowers t) ∧
      ∃ (Q₃ P₃ : Subgroup G) (ψ₃ : V6 → G) (p₃ : Fin 6 → G) (W₃ : Subgroup G),
        Setup .plus t L U Q₃ P₃ a ψ₃ p₃ ∧ Q₃ ≤ W₃ ∧ t ∉ W₃ ∧ Nat.card W₃ = 4096 ∧
        (∀ x ∈ W₃, ∀ y ∈ W₃, x * y = y * x) ∧
        (∀ n ∈ normalizer ((Q₃ ⊔ zpowers t : Subgroup G) : Set G), ∀ w ∈ W₃, n * w * n⁻¹ ∈ W₃) ∧
        ({ψ (Pi.single 0 1), ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} : Set G) ⊆
          Q₃ := by
  obtain ⟨U, Q, P, a, ψ, p, u, Q₃, P₃, ψ₃, p₃, u₃, hR, hU, hF, hAc, hR1, hR3, hR₃, -, hF₃, -,
    h0, h1, h2, h3, h4, h5⟩ := exists_link_plus_two hZ hL
  obtain ⟨hS, -⟩ := setup_of_linkFacts hA hF hR.odd
  obtain ⟨hS₃, -⟩ := setup_of_linkFacts hA hF₃ hR₃.odd
  have hZ₃ := hS₃.mem_Zset hG hnab
  refine ⟨U, Q, P, a, ψ, p, u, hS, hU, hF, hAc, hR1,
    normalizer_sup_of_shapeA hA hF.U_le_L hR3, Q₃, P₃, ψ₃, p₃, hS₃.Wsub hZ₃, hS₃,
    hS₃.Q_le_Wsub hZ₃, hS₃.t_not_mem_Wsub hZ₃, hS₃.card_Wsub hZ₃,
    fun x hx y hy => hS₃.Wsub_comm hZ₃ hx hy,
    fun n hn w hw => (mem_normalizer_iff.1 (hS₃.normalizer_E_le_normalizer_Wsub hZ₃ hn) w).1 hw,
    ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← h0]; exact hF₃.ψ_mem _
  · rw [← h1]; exact hF₃.ψ_mem _
  · rw [← h3]; exact hF₃.ψ_mem _
  · rw [← h2]; exact hF₃.ψ_mem _
  · rw [← h4]; exact hF₃.ψ_mem _
  · rw [← h5]; exact hF₃.ψ_mem _

end CFSG.EvenSmallLie.OmegaEight.Stage1
