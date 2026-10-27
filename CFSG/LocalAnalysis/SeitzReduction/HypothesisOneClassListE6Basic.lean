module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassCascade
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEClasses

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

inductive FrameWalkMove where
  | word (ω : List ℕ)
  | d4 (a b c d θ : ℕ)

@[expose] def frameWalkRest (F : List ℕ) (a b d θ : ℕ) : List ℕ :=
  F.filter fun k => !(k == a || k == b || k == d || k == θ)

@[expose] def frameWalkD4B (τ : Tag) (F : List ℕ) (a b c d θ : ℕ) : Bool :=
  decide (c < τ.rootCertificate.roots.length) &&
    decide (iform (τ.rootCertificate.root a) (τ.rootCertificate.root c) = -1) &&
    decide (iform (τ.rootCertificate.root b) (τ.rootCertificate.root c) = -1) &&
    decide (iform (τ.rootCertificate.root d) (τ.rootCertificate.root c) = -1) &&
    decide (iform (τ.rootCertificate.root a) (τ.rootCertificate.root b) = 0) &&
    decide (iform (τ.rootCertificate.root a) (τ.rootCertificate.root d) = 0) &&
    decide (iform (τ.rootCertificate.root b) (τ.rootCertificate.root d) = 0) &&
    (List.ofFn (τ.rootCertificate.root θ) ==
      List.ofFn (τ.rootCertificate.root a + τ.rootCertificate.root b +
        2 • τ.rootCertificate.root c + τ.rootCertificate.root d)) &&
    F.isPerm (a :: b :: d :: θ :: frameWalkRest F a b d θ)

@[expose] def frameWalkStep (τ : Tag) (F : List ℕ) : FrameWalkMove → Option (List ℕ)
  | .word ω => some (F.map (wordPos τ.rootCertificate ω))
  | .d4 a b c d θ =>
      if frameWalkD4B τ F a b c d θ then some (a :: b :: d :: frameWalkRest F a b d θ) else none

@[expose] def frameWalkRun (τ : Tag) : List ℕ → List FrameWalkMove → Option (List ℕ)
  | F, [] => some F
  | F, m :: ms => (frameWalkStep τ F m).bind fun F' => frameWalkRun τ F' ms

@[expose] def frameWalkEnds (τ : Tag) (F : List ℕ) (ms : List FrameWalkMove) (T : List ℕ) :
    Bool :=
  match frameWalkRun τ F ms with
  | some F' => F'.isPerm T
  | none => false

@[expose] def frameWalkSublists : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: l => frameWalkSublists l ++ (frameWalkSublists l).map (a :: ·)

@[expose] def frameWalkCheck (τ : Tag) (casc : List ℕ) (targets : List (List ℕ))
    (data : List (List ℕ × List FrameWalkMove × ℕ)) : Bool :=
  casc.all (fun k => decide (k < τ.rootCertificate.roots.length)) &&
    (frameWalkSublists casc).all fun S => S.isEmpty || data.any fun e =>
      (e.1 == S) && decide (e.2.2 < targets.length) &&
        frameWalkEnds τ S e.2.1 (targets.getD e.2.2 [])

theorem mem_frameWalkSublists {l S : List ℕ} (h : S.Sublist l) : S ∈ frameWalkSublists l := by
  induction h with
  | slnil => simp [frameWalkSublists]
  | cons a _ ih => exact List.mem_append_left _ ih
  | cons_cons a _ ih => exact List.mem_append_right _ (List.mem_map_of_mem ih)

theorem frameWalk_eq_one_of_mul_self {K : Type} [Field K] [CharP K 2] {η : K} (h : η * η = 1) :
    η = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (η - 1) * (η - 1) = 0 := by linear_combination h + (1 - η) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 this)

theorem frameWalk_sq_eq_one_of_orderOf_conj {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) {t : G} (ht : orderOf (MulAut.conj t) = 2) :
    t ^ 2 = 1 ∧ t ≠ 1 := by
  refine ⟨?_, fun h => by rw [h, map_one, orderOf_one] at ht; exact absurd ht (by norm_num)⟩
  have h1 : MulAut.conj (t ^ 2) = 1 := by rw [map_pow, ← ht, pow_orderOf_eq_one]
  have hc : t ^ 2 ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
    have h := congrArg (fun α : MulAut G => α x) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * t ^ 2 = t ^ 2 * x * (t ^ 2)⁻¹ * t ^ 2 := by rw [h]
      _ = t ^ 2 * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem frameWalkCascade_pairwise (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (cascadeRoots τ).Pairwise fun σ σ' => iform σ σ' = 0 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem frameWalkCascade_isRoot (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ σ ∈ cascadeRoots τ, IsRoot τ σ := by
  rcases hτ with rfl | rfl | rfl | rfl <;>
    exact fun σ hσ => RootOps.isRootB_iff.1 (List.all_eq_true.1 (by decide +kernel) σ hσ)

section Conj


variable (τ) (K : Type) [Field K] in
@[expose] def FrameProdConj (F F' : List (Fin τ.rank → ℤ)) : Prop :=
  ∃ g ∈ adjointGroup τ K, g * (F.map fun σ => pinnedX τ K σ 1).prod * g⁻¹ =
    (F'.map fun σ => pinnedX τ K σ 1).prod

variable {K : Type} [Field K]

theorem FrameProdConj.refl (F : List (Fin τ.rank → ℤ)) : FrameProdConj τ K F F :=
  ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem FrameProdConj.trans {F F' F'' : List (Fin τ.rank → ℤ)} (h₁ : FrameProdConj τ K F F')
    (h₂ : FrameProdConj τ K F' F'') : FrameProdConj τ K F F'' := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [← e₂, ← e₁]
  group

end Conj

section Moves


variable {K : Type} [Field K]

theorem frameProdConj_of_perm (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {F F' : List (Fin τ.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot τ σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (hp : F.Perm F') :
    FrameProdConj τ K F F' :=
  ⟨1, one_mem _, by
    rw [one_mul, inv_one, mul_one]
    exact classD4_frame_prod_perm hτ hF horth hp fun _ => (1 : K)⟩

theorem frameProdConj_map_reflect [CharP K 2] (j : Fin τ.rank) {F : List (Fin τ.rank → ℤ)}
    (hF : ∀ σ ∈ F, IsRoot τ σ) : FrameProdConj τ K F (F.map (reflect τ j)) := by
  obtain ⟨η, hη, h⟩ := classDescent_exists_sign_conj_list_prod (K := K) j
  refine ⟨weylElt τ K j 1, weylElt_mem_adjointGroup j 1, ?_⟩
  have h' := h (fun _ => 1) F hF
  simp only [mul_one] at h'
  rw [h', List.map_map]
  refine congrArg List.prod (List.map_congr_left fun σ hσ => ?_)
  rw [frameWalk_eq_one_of_mul_self (hη σ (hF σ hσ))]
  rfl

theorem frameProdConj_d4 [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a b c d θ : Fin τ.rank → ℤ} (hp : IsD4Pattern τ a b c d) (hθ : a + b + 2 • c + d = θ)
    {F P : List (Fin τ.rank → ℤ)} (hFP : F.Perm (a :: b :: d :: θ :: P))
    (hF : ∀ σ ∈ F, IsRoot τ σ) (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    FrameProdConj τ K F (a :: b :: d :: P) := by
  have horth' : (a :: b :: d :: θ :: P).Pairwise fun σ σ' => iform σ σ' = 0 :=
    hFP.pairwise horth fun h => by rw [iform_comm]; exact h
  have hF' : ∀ σ ∈ a :: b :: d :: θ :: P, IsRoot τ σ := fun σ hσ => hF σ (hFP.mem_iff.2 hσ)
  refine (frameProdConj_of_perm hτ hF horth hFP).trans ?_
  have hP : ∀ ρ ∈ P, IsRoot τ ρ ∧ iform ρ a = 0 ∧ iform ρ b = 0 ∧ iform ρ d = 0 ∧
      iform ρ θ = 0 := by
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at horth'
    obtain ⟨⟨-, -, -, hPa⟩, ⟨-, -, hPb⟩, ⟨-, hPd⟩, hPθ, -⟩ := horth'
    intro ρ hρ
    refine ⟨hF' ρ (by simp [hρ]), ?_, ?_, ?_, ?_⟩ <;> rw [iform_comm]
    exacts [hPa ρ hρ, hPb ρ hρ, hPd ρ hρ, hPθ ρ hρ]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key := classD4_conj_frame hτ h2 hp hθ hP fun _ => (1 : K)
  refine ⟨pinnedX τ K (c + d) 1 * pinnedX τ K (b + c) 1 * pinnedX τ K (a + c) 1 *
    pinnedX τ K (b + c + d) 1, mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
        (pinnedX_mem_adjointGroup _ _), ?_⟩
  simp only [List.map_cons, List.prod_cons] at key ⊢
  simpa only [mul_assoc] using key

theorem frameWalk_word_sound [CharP K 2] (ω : List ℕ) : ∀ {F : List ℕ},
    (∀ k ∈ F, k < τ.rootCertificate.roots.length) →
    (F.map τ.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) →
    (∀ k ∈ F.map (wordPos τ.rootCertificate ω), k < τ.rootCertificate.roots.length) ∧
      ((F.map (wordPos τ.rootCertificate ω)).map τ.rootCertificate.root).Pairwise
        (fun σ σ' => iform σ σ' = 0) ∧
      FrameProdConj τ K (F.map τ.rootCertificate.root)
        ((F.map (wordPos τ.rootCertificate ω)).map τ.rootCertificate.root) := by
  induction ω with
  | nil =>
    intro F hF horth
    have e : F.map (wordPos τ.rootCertificate []) = F := by
      conv_rhs => rw [← List.map_id F]
      rfl
    rw [e]
    exact ⟨hF, horth, .refl _⟩
  | cons i ω ih =>
    intro F hF horth
    have hC := τ.rootCertificate_check
    have e : F.map (wordPos τ.rootCertificate (i :: ω)) =
        (F.map fun k => τ.rootCertificate.image k (τ.idx i)).map
          (wordPos τ.rootCertificate ω) := by
      rw [List.map_map]
      rfl
    have hF₁ : ∀ k ∈ F.map fun k => τ.rootCertificate.image k (τ.idx i),
        k < τ.rootCertificate.roots.length := by
      intro k hk
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
      exact (image_spec_of_check hC (hF k' hk') (τ.idx i)).1
    have e₁ : (F.map fun k => τ.rootCertificate.image k (τ.idx i)).map τ.rootCertificate.root =
        (F.map τ.rootCertificate.root).map (reflect τ (τ.idx i)) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun k hk => (image_spec_of_check hC (hF k hk) (τ.idx i)).2
    have horth₁ : ((F.map fun k => τ.rootCertificate.image k (τ.idx i)).map
        τ.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) := by
      rw [e₁, List.pairwise_map]
      exact horth.imp fun h => by rw [iform_reflect]; exact h
    obtain ⟨h₁, h₂, h₃⟩ := ih hF₁ horth₁
    have hroots : ∀ σ ∈ F.map τ.rootCertificate.root, IsRoot τ σ := by
      intro σ hσ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
      exact RootCertificate.isRoot_root hC k (hF k hk)
    rw [e]
    refine ⟨h₁, h₂, ?_⟩
    have h₀ := frameProdConj_map_reflect (K := K) (τ.idx i) hroots
    rw [← e₁] at h₀
    exact h₀.trans h₃

theorem frameWalkStep_sound [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {F F' : List ℕ} {m : FrameWalkMove}
    (hF : ∀ k ∈ F, k < τ.rootCertificate.roots.length)
    (horth : (F.map τ.rootCertificate.root).Pairwise fun σ σ' => iform σ σ' = 0)
    (h : frameWalkStep τ F m = some F') :
    (∀ k ∈ F', k < τ.rootCertificate.roots.length) ∧
      (F'.map τ.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      FrameProdConj τ K (F.map τ.rootCertificate.root) (F'.map τ.rootCertificate.root) := by
  have hC := τ.rootCertificate_check
  cases m with
  | word ω =>
    simp only [frameWalkStep, Option.some.injEq] at h
    subst h
    exact frameWalk_word_sound ω hF horth
  | d4 a b c d θ =>
    simp only [frameWalkStep] at h
    split_ifs at h with hB
    simp only [Option.some.injEq] at h
    subst h
    simp only [frameWalkD4B, Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hac⟩, hbc⟩, hdc⟩, hab⟩, had⟩, hbd⟩, hθ⟩, hperm⟩ := hB
    have hperm' := List.isPerm_iff.1 hperm
    set P := frameWalkRest F a b d θ
    have hmem : ∀ k ∈ a :: b :: d :: θ :: P, k ∈ F := fun k hk => hperm'.mem_iff.2 hk
    have hroot : ∀ k ∈ F, IsRoot τ (τ.rootCertificate.root k) := fun k hk =>
      RootCertificate.isRoot_root hC k (hF k hk)
    have hpat : IsD4Pattern τ (τ.rootCertificate.root a) (τ.rootCertificate.root b)
        (τ.rootCertificate.root c) (τ.rootCertificate.root d) :=
      ⟨hroot a (hmem a (by simp)), hroot b (hmem b (by simp)),
        RootCertificate.isRoot_root hC c hc, hroot d (hmem d (by simp)), hac, hbc, hdc, hab,
        had, hbd⟩
    have hθ' : τ.rootCertificate.root a + τ.rootCertificate.root b +
        2 • τ.rootCertificate.root c + τ.rootCertificate.root d = τ.rootCertificate.root θ :=
      (RootCertificate.eq_of_ofFn_beq hθ).symm
    have hFP : (F.map τ.rootCertificate.root).Perm
        ((a :: b :: d :: θ :: P).map τ.rootCertificate.root) := hperm'.map _
    have hFr : ∀ σ ∈ F.map τ.rootCertificate.root, IsRoot τ σ := by
      intro σ hσ
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
      exact hroot k hk
    refine ⟨fun k hk => hF k ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hmem _ (by simp)
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hmem _ (by simp)
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hmem _ (by simp)
      exact hmem _ (by simp [hk])
    · have horth' := hFP.pairwise horth fun h => by rw [iform_comm]; exact h
      refine horth'.sublist ?_
      simp only [List.map_cons]
      exact ((((List.Sublist.refl _).cons _).cons_cons _).cons_cons _).cons_cons _
    · exact frameProdConj_d4 hτ hpat hθ' hFP hFr horth

theorem frameWalkRun_sound [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ (ms : List FrameWalkMove) {F F' : List ℕ},
      (∀ k ∈ F, k < τ.rootCertificate.roots.length) →
      (F.map τ.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) →
      frameWalkRun τ F ms = some F' →
      (∀ k ∈ F', k < τ.rootCertificate.roots.length) ∧
        (F'.map τ.rootCertificate.root).Pairwise (fun σ σ' => iform σ σ' = 0) ∧
        FrameProdConj τ K (F.map τ.rootCertificate.root) (F'.map τ.rootCertificate.root)
  | [], F, F', hF, horth, h => by
    simp only [frameWalkRun, Option.some.injEq] at h
    subst h
    exact ⟨hF, horth, .refl _⟩
  | m :: ms, F, F', hF, horth, h => by
    simp only [frameWalkRun, Option.bind_eq_some_iff] at h
    obtain ⟨F₁, h₁, h₂⟩ := h
    obtain ⟨hF₁, horth₁, hc₁⟩ := frameWalkStep_sound (K := K) hτ hF horth h₁
    obtain ⟨hF₂, horth₂, hc₂⟩ := frameWalkRun_sound hτ ms hF₁ horth₁ h₂
    exact ⟨hF₂, horth₂, hc₁.trans hc₂⟩

theorem frameWalkEnds_sound [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {F T : List ℕ} {ms : List FrameWalkMove}
    (hF : ∀ k ∈ F, k < τ.rootCertificate.roots.length)
    (horth : (F.map τ.rootCertificate.root).Pairwise fun σ σ' => iform σ σ' = 0)
    (h : frameWalkEnds τ F ms T = true) :
    FrameProdConj τ K (F.map τ.rootCertificate.root) (T.map τ.rootCertificate.root) := by
  unfold frameWalkEnds at h
  split at h
  · rename_i F' hrun
    obtain ⟨hF', horth', hc⟩ := frameWalkRun_sound (K := K) hτ ms hF horth hrun
    have hp : F'.Perm T := List.isPerm_iff.1 h
    refine hc.trans (frameProdConj_of_perm hτ (fun σ hσ => ?_) horth' (hp.map _))
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
    exact RootCertificate.isRoot_root τ.rootCertificate_check k (hF' k hk)
  · exact absurd h Bool.false_ne_true

theorem frameWalkCheck_sound [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {casc : List ℕ} {targets : List (List ℕ)} {data : List (List ℕ × List FrameWalkMove × ℕ)}
    (h : frameWalkCheck τ casc targets data = true)
    (horth : (casc.map τ.rootCertificate.root).Pairwise fun σ σ' => iform σ σ' = 0)
    {S : List ℕ} (hS : S.Sublist casc) (hne : S ≠ []) :
    ∃ T ∈ targets,
      FrameProdConj τ K (S.map τ.rootCertificate.root) (T.map τ.rootCertificate.root) := by
  simp only [frameWalkCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hcasc, hall⟩ := h
  rcases hall S (mem_frameWalkSublists hS) with he | ⟨e, -, ⟨⟨rfl, hi⟩, hend⟩⟩
  · exact absurd (List.isEmpty_iff.1 he) hne
  · refine ⟨targets.getD e.2.2 [], ?_, frameWalkEnds_sound hτ (fun k hk => hcasc k (hS.subset hk))
      ((horth.sublist (hS.map _))) hend⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

theorem exists_conj_eq_frame_prod_of_walks [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {reps : List (List (Fin τ.rank → ℤ))}
    (hcl : ∀ S : List (Fin τ.rank → ℤ), S.Sublist (cascadeRoots τ) → S ≠ [] →
      ∃ T ∈ reps, FrameProdConj τ K S T)
    {t : adjointGroup τ K} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ g : adjointGroup τ K, ∃ T ∈ reps,
      ((g * t * g⁻¹ : adjointGroup τ K) : ModGL τ K) = (T.map fun σ => pinnedX τ K σ 1).prod := by
  obtain ⟨g, S, hS, c, hc, he⟩ := exists_conj_eq_cascade_prod hτ ht2
  have hne : S ≠ [] := by
    rintro rfl
    apply ht1
    have h1 : g * t * g⁻¹ = 1 := Subtype.ext (by rw [he]; rfl)
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hSr : ∀ σ ∈ S, IsRoot τ σ := fun σ hσ => frameWalkCascade_isRoot hτ σ (hS.subset hσ)
  have hSo : S.Pairwise fun σ σ' => iform σ σ' = 0 := (frameWalkCascade_pairwise hτ).sublist hS
  obtain ⟨h, hh, -, -, hprod⟩ := exists_torus_conj_frame_prod (classD4_noG2 hτ) hSr hSo c hc
  obtain ⟨T, hT, g₂, hg₂, e₂⟩ := hcl S hS hne
  refine ⟨⟨g₂, hg₂⟩ * ⟨h, hh⟩ * g, T, hT, ?_⟩
  have e : (((⟨g₂, hg₂⟩ * ⟨h, hh⟩ * g) * t * (⟨g₂, hg₂⟩ * ⟨h, hh⟩ * g)⁻¹ : adjointGroup τ K) :
      ModGL τ K) = g₂ * (h * ((g * t * g⁻¹ : adjointGroup τ K) : ModGL τ K) * h⁻¹) * g₂⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, he, hprod, e₂]

theorem exists_conj_mem_of_frame_walks [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {reps : List (List (Fin τ.rank → ℤ))}
    (hcl : ∀ S : List (Fin τ.rank → ℤ), S.Sublist (cascadeRoots τ) → S ≠ [] →
      ∃ T ∈ reps, FrameProdConj τ K S T)
    {R : Set (adjointGroup τ K)}
    (hR : ∀ T ∈ reps, (⟨(T.map fun σ => pinnedX τ K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup T⟩ : adjointGroup τ K) ∈ R)
    {t : adjointGroup τ K} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ g : adjointGroup τ K, g * t * g⁻¹ ∈ R := by
  obtain ⟨g, T, hT, he⟩ := exists_conj_eq_frame_prod_of_walks hτ hcl ht2 ht1
  refine ⟨g, ?_⟩
  have e : g * t * g⁻¹ = ⟨(T.map fun σ => pinnedX τ K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup T⟩ := Subtype.ext he
  rw [e]
  exact hR T hT

theorem exists_mulAut_eq_of_frame_walks [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {reps : List (List (Fin τ.rank → ℤ))}
    (hcl : ∀ S : List (Fin τ.rank → ℤ), S.Sublist (cascadeRoots τ) → S ≠ [] →
      ∃ T ∈ reps, FrameProdConj τ K S T)
    {R : Set (adjointGroup τ K)}
    (hR : ∀ T ∈ reps, (⟨(T.map fun σ => pinnedX τ K σ 1).prod,
      list_prod_map_pinnedX_mem_adjointGroup T⟩ : adjointGroup τ K) ∈ R) :
    ∀ t : adjointGroup τ K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup τ K), ∃ s ∈ R, ψ s = t := by
  intro t ht
  obtain ⟨ht2, ht1⟩ := frameWalk_sq_eq_one_of_orderOf_conj center_adjointGroup_eq_bot ht
  obtain ⟨g, hg⟩ := exists_conj_mem_of_frame_walks hτ hcl hR ht2 ht1
  refine ⟨MulAut.conj g⁻¹, _, hg, ?_⟩
  rw [MulAut.conj_apply]
  group

end Moves

end CFSG.SeitzReduction
