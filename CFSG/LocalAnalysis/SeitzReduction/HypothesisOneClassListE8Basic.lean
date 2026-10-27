module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def classListE8WordElt : List ℕ → ModGL τ K
  | [] => 1
  | i :: ω => classListE8WordElt ω * weylElt τ K (τ.idx i) 1

theorem classListE8WordElt_mem_adjointGroup (ω : List ℕ) :
    classListE8WordElt τ K ω ∈ adjointGroup τ K := by
  induction ω with
  | nil => exact one_mem _
  | cons i ω ih => exact mul_mem ih (weylElt_mem_adjointGroup _ 1)


theorem classListE8_weylElt_conj_pinnedX [CharP K 2] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    weylElt τ K i 1 * pinnedX τ K α c * (weylElt τ K i 1)⁻¹ = pinnedX τ K (reflect τ i α) c := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hα
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [h, hε1, one_mul]

theorem classListE8_wordElt_conj_pinnedX [CharP K 2] (ω : List ℕ) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) (c : K) :
    classListE8WordElt τ K ω * pinnedX τ K (τ.rootCertificate.root k) c *
        (classListE8WordElt τ K ω)⁻¹ =
      pinnedX τ K (τ.rootCertificate.root (wordPos τ.rootCertificate ω k)) c := by
  induction ω generalizing k with
  | nil => simp [classListE8WordElt, wordPos]
  | cons i ω ih =>
    obtain ⟨h1, h2⟩ := image_spec_of_check τ.rootCertificate_check hk (τ.idx i)
    have hr := RootCertificate.isRoot_root τ.rootCertificate_check k hk
    calc classListE8WordElt τ K (i :: ω) * pinnedX τ K (τ.rootCertificate.root k) c *
          (classListE8WordElt τ K (i :: ω))⁻¹
        = classListE8WordElt τ K ω * (weylElt τ K (τ.idx i) 1 *
            pinnedX τ K (τ.rootCertificate.root k) c * (weylElt τ K (τ.idx i) 1)⁻¹) *
              (classListE8WordElt τ K ω)⁻¹ := by
          simp only [classListE8WordElt]
          group
      _ = classListE8WordElt τ K ω *
            pinnedX τ K (τ.rootCertificate.root (τ.rootCertificate.image k (τ.idx i))) c *
              (classListE8WordElt τ K ω)⁻¹ := by
          rw [classListE8_weylElt_conj_pinnedX _ hr, h2]
      _ = _ := ih h1

theorem classListE8_wordElt_conj_posProd [CharP K 2] (ω : List ℕ) {L : List ℕ}
    (hL : ∀ k ∈ L, k < τ.rootCertificate.roots.length) :
    classListE8WordElt τ K ω * (L.map fun k => pinnedX τ K (τ.rootCertificate.root k) 1).prod *
        (classListE8WordElt τ K ω)⁻¹ =
      ((L.map (wordPos τ.rootCertificate ω)).map
        fun k => pinnedX τ K (τ.rootCertificate.root k) 1).prod := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.map_cons, List.prod_cons,
      ← ih fun k' h => hL k' (List.mem_cons_of_mem _ h),
      ← classListE8_wordElt_conj_pinnedX ω (hL k List.mem_cons_self) 1]
    group

theorem classListE8_forall_isRoot {L : List ℕ} (hL : ∀ k ∈ L, k < τ.rootCertificate.roots.length) :
    ∀ σ ∈ L.map τ.rootCertificate.root, IsRoot τ σ := by
  intro σ hσ
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
  exact RootCertificate.isRoot_root τ.rootCertificate_check k (hL k hk)


theorem classListE8_posProd_perm (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L L' : List ℕ}
    (hL : ∀ k ∈ L, k < τ.rootCertificate.roots.length)
    (horth : L.Pairwise fun k k' =>
      iform (τ.rootCertificate.root k) (τ.rootCertificate.root k') = 0)
    (hperm : L.Perm L') :
    (L.map fun k => pinnedX τ K (τ.rootCertificate.root k) 1).prod =
      (L'.map fun k => pinnedX τ K (τ.rootCertificate.root k) 1).prod := by
  have h := classD4_frame_prod_perm (R := K) hτ (classListE8_forall_isRoot hL)
    (List.pairwise_map.2 horth) (hperm.map τ.rootCertificate.root) fun _ => 1
  simpa only [List.map_map, Function.comp_def] using h

theorem classListE8_exists_conj_posProd_erase [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c d θ : ℕ}
    (hpat : IsD4Pattern τ (τ.rootCertificate.root a) (τ.rootCertificate.root b)
      (τ.rootCertificate.root c) (τ.rootCertificate.root d))
    (hθ : τ.rootCertificate.root a + τ.rootCertificate.root b + 2 • τ.rootCertificate.root c +
      τ.rootCertificate.root d = τ.rootCertificate.root θ)
    {L : List ℕ} (hL : ∀ k ∈ L, k < τ.rootCertificate.roots.length)
    (horth : L.Pairwise fun k k' =>
      iform (τ.rootCertificate.root k) (τ.rootCertificate.root k') = 0)
    (ha : a ∈ L) (hb : b ∈ L) (hd : d ∈ L) (hθL : θ ∈ L)
    (haθ : a ≠ θ) (hbθ : b ≠ θ) (hdθ : d ≠ θ) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ∃ g ∈ adjointGroup τ K,
      g * (L.map fun k => pinnedX τ K (τ.rootCertificate.root k) 1).prod * g⁻¹ =
        ((L.erase θ).map fun k => pinnedX τ K (τ.rootCertificate.root k) 1).prod := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set C := τ.rootCertificate with hC
  set L₁ := L.erase θ with hL₁
  set L₂ := L₁.erase a with hL₂
  set L₃ := L₂.erase b with hL₃
  set P := L₃.erase d with hP
  have ha₁ : a ∈ L₁ := (List.mem_erase_of_ne haθ).2 ha
  have hb₂ : b ∈ L₂ := (List.mem_erase_of_ne (Ne.symm hab)).2 ((List.mem_erase_of_ne hbθ).2 hb)
  have hd₃ : d ∈ L₃ := (List.mem_erase_of_ne (Ne.symm hbd)).2
    ((List.mem_erase_of_ne (Ne.symm had)).2 ((List.mem_erase_of_ne hdθ).2 hd))
  have hp₁ : L₁.Perm (a :: b :: d :: P) :=
    (List.perm_cons_erase ha₁).trans (((List.perm_cons_erase hb₂).trans
      ((List.perm_cons_erase hd₃).cons b)).cons a)
  have hp : L.Perm (a :: b :: d :: θ :: P) := by
    refine (List.perm_cons_erase hθL).trans ?_
    refine ((hp₁.cons θ).trans ?_)
    exact (List.Perm.swap a θ _).trans (((List.Perm.swap b θ _).trans
      ((List.Perm.swap d θ _).cons b)).cons a)
  have horth' := hp.pairwise horth fun h => by rw [iform_comm]; exact h
  have hL' : ∀ k ∈ a :: b :: d :: θ :: P, k < C.roots.length := fun k hk => hL k (hp.mem_iff.2 hk)
  have hPo : ∀ ρ ∈ P.map C.root, IsRoot τ ρ ∧ iform ρ (C.root a) = 0 ∧
      iform ρ (C.root b) = 0 ∧ iform ρ (C.root d) = 0 ∧ iform ρ (C.root θ) = 0 := by
    intro ρ hρ
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hρ
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at horth'
    obtain ⟨⟨-, -, -, hPa⟩, ⟨-, -, hPb⟩, ⟨-, hPd⟩, hPθ, -⟩ := horth'
    refine ⟨RootCertificate.isRoot_root τ.rootCertificate_check k
      (hL' k (by simp [hk])), ?_, ?_, ?_, ?_⟩ <;> rw [iform_comm]
    exacts [hPa k hk, hPb k hk, hPd k hk, hPθ k hk]
  have key := classD4_conj_frame (R := K) hτ h2 hpat hθ hPo fun _ => (1 : K)
  have hg : pinnedX τ K (C.root c + C.root d) 1 * pinnedX τ K (C.root b + C.root c) 1 *
      pinnedX τ K (C.root a + C.root c) 1 * pinnedX τ K (C.root b + C.root c + C.root d) 1 ∈
        adjointGroup τ K :=
    mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _)
  refine ⟨_, hg, ?_⟩
  rw [classListE8_posProd_perm hτ hL horth hp,
    classListE8_posProd_perm hτ (fun k hk => hL k ((List.erase_sublist).subset hk))
      (horth.sublist List.erase_sublist) hp₁]
  simp only [List.map_cons, List.prod_cons, List.map_map, Function.comp_def] at key ⊢
  simpa only [mul_assoc] using key

end CFSG.SeitzReduction
