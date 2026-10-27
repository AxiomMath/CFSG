module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux26
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux21

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement
open E8TenTwo

set_option linter.unusedSectionVars false


section A2

variable {R : Type} [Field R] [CharP R 2]

theorem pinnedX_A2_rel2 {β₁ β₂ β₃ : Fin Tag.E8.rank → ℤ}
    (h₁ : β₁ ∈ rootFinset Tag.E8) (h₂ : β₂ ∈ rootFinset Tag.E8) (h₃ : β₃ = β₁ + β₂)
    (hs : β₃ ∈ rootFinset Tag.E8) (hne : β₁ ≠ β₂) (hne' : β₁ ≠ -β₂)
    (h31 : β₃ + β₁ ∉ rootFinset Tag.E8) (h32 : β₃ + β₂ ∉ rootFinset Tag.E8)
    (n31 : β₃ ≠ β₁) (n31' : β₃ ≠ -β₁) (n32 : β₃ ≠ β₂) (n32' : β₃ ≠ -β₂) (a b : R) :
    pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₁ b =
      pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₃ (a * b) := by
  have hs' : β₂ + β₁ ∈ rootFinset Tag.E8 := by
    rw [add_comm, ← h₃]
    exact hs
  have hne2' : β₂ ≠ -β₁ := fun h => hne' (by rw [h, neg_neg])
  have hc := comm_root2 (R := R) h₂ h₁ hne.symm hne2' hs' a b
  rw [commutatorElement_def] at hc
  have hβ : β₂ + β₁ = β₃ := by rw [h₃, add_comm]
  rw [hβ] at hc
  have hc1 : ∀ s : R, pinnedX Tag.E8 R β₃ s * pinnedX Tag.E8 R β₁ b =
      pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₃ s := fun s =>
    pinnedX_commute_of_not_root hs h₁ n31 n31' h31 s b
  have hc2 : ∀ s : R, pinnedX Tag.E8 R β₃ s * pinnedX Tag.E8 R β₂ a =
      pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₃ s := fun s =>
    pinnedX_commute_of_not_root hs h₂ n32 n32' h32 s a
  calc pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₁ b
      = (pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₁ b * (pinnedX Tag.E8 R β₂ a)⁻¹ *
          (pinnedX Tag.E8 R β₁ b)⁻¹) * (pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a) := by group
    _ = pinnedX Tag.E8 R β₃ (a * b) * (pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a) := by rw [hc]
    _ = pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₃ (a * b) := by
      rw [← mul_assoc, hc1, mul_assoc, hc2, ← mul_assoc]

end A2

section Gen

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem exists_omega (hK : Nat.card K = 2) : ∃ ω : D.L, ω ^ 2 + ω + 1 = 0 := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial D.L).degree ≠ 0 := by
    have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial D.L).degree = 2 := by
      compute_degree!
    rw [this]
    norm_num
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨ω, ?_⟩
  simpa [Polynomial.IsRoot] using hω

theorem exists_gen (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0) {t : ℕ} (ht : t < 4) :
    ∃ ℓ : ModGL Tag.E8 K, ℓ ∈ TwClass.e8Ten.X₂ D ∧
      ΨE D ℓ = pinnedX Tag.E8 D.L (trRoot t 0) 1 * pinnedX Tag.E8 D.L (trRoot t 1) 1 *
        pinnedX Tag.E8 D.L (trRoot t 2) ω := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set S := toSetup D ⊥ with hS
  have ht' : t ∈ List.range 4 := List.mem_range.2 ht
  obtain ⟨hr0, hd0⟩ := trRoot_P1 t ht' 0 (List.mem_range.2 (by norm_num))
  obtain ⟨hr1, hd1⟩ := trRoot_P1 t ht' 1 (List.mem_range.2 (by norm_num))
  obtain ⟨hr2, hd2⟩ := trRoot_P1 t ht' 2 (List.mem_range.2 (by norm_num))
  have hs0 := trRoot_P2 t ht' 0 (List.mem_range.2 (by norm_num))
  have hs1 := trRoot_P2 t ht' 1 (List.mem_range.2 (by norm_num))
  have hs2 := trRoot_P2 t ht' 2 (List.mem_range.2 (by norm_num))
  obtain ⟨hw0, hw1, hw2, hsum⟩ := trRoot_P3 t ht'
  obtain ⟨n01, n01', h20, h21, n20, n20', n21, n21'⟩ := trRoot_P4 t ht'
  have hsg0 : S.sg (trRoot t 0) = 1 := sg_eq_one D hK (mem_rootFinset.1 hr0)
  have hsg1 : S.sg (trRoot t 1) = 1 := sg_eq_one D hK (mem_rootFinset.1 hr1)
  have hsg2 : S.sg (trRoot t 2) = 1 := sg_eq_one D hK (mem_rootFinset.1 hr2)
  obtain ⟨-, hc₁⟩ := S.hm _ (mem_rootFinset.1 hr0)
  obtain ⟨-, hc₂⟩ := S.hm _ (mem_rootFinset.1 hr1)
  obtain ⟨-, hc₃⟩ := S.hm _ (mem_rootFinset.1 hr2)
  have hw0' : S.w • trRoot t 0 = trRoot t 1 := by rw [toSetup_hw]; exact hw0
  have hw1' : S.w • trRoot t 1 = trRoot t 0 := by rw [toSetup_hw]; exact hw1
  have hw2' : S.w • trRoot t 2 = trRoot t 2 := by rw [toSetup_hw]; exact hw2
  have hrel := pinnedX_A2_rel2 (R := D.L) hr0 hr1 hsum.symm hr2 n01 n01' h20 h21 n20 n20' n21 n21' 1 1
  have h2 : (2 : D.L) = 0 := CharP.cast_eq_zero D.L 2
  have hσ : S.n * Frob S.Fr (pinnedX Tag.E8 D.L (trRoot t 0) 1 * pinnedX Tag.E8 D.L (trRoot t 1) 1 *
      pinnedX Tag.E8 D.L (trRoot t 2) ω) * S.n⁻¹ =
      pinnedX Tag.E8 D.L (trRoot t 0) 1 * pinnedX Tag.E8 D.L (trRoot t 1) 1 *
        pinnedX Tag.E8 D.L (trRoot t 2) ω := by
    have e : S.n * (pinnedX Tag.E8 D.L (trRoot t 0) (S.Fr 1) * pinnedX Tag.E8 D.L (trRoot t 1) (S.Fr 1) *
        pinnedX Tag.E8 D.L (trRoot t 2) (S.Fr ω)) * S.n⁻¹ =
        (S.n * pinnedX Tag.E8 D.L (trRoot t 0) (S.Fr 1) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 D.L (trRoot t 1) (S.Fr 1) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 D.L (trRoot t 2) (S.Fr ω) * S.n⁻¹) := by group
    rw [map_mul, map_mul, Frob_pinnedX, Frob_pinnedX, Frob_pinnedX, e, hc₁ (S.Fr 1),
      hc₂ (S.Fr 1), hc₃ (S.Fr ω), hw0', hw1', hw2', hsg0, hsg1, hsg2, map_one,
      show S.Fr ω = ω ^ 2 from Fr_sq D hK ω, one_mul, one_mul, hrel, mul_assoc
        (pinnedX Tag.E8 D.L (trRoot t 0) 1 * pinnedX Tag.E8 D.L (trRoot t 1) 1), ← pinnedX_add]
    have hzz : (1 : D.L) * 1 + ω ^ 2 = ω := by linear_combination hω - ω * h2
    rw [hzz]
  have hxA : pinnedX Tag.E8 D.L (trRoot t 0) 1 * pinnedX Tag.E8 D.L (trRoot t 1) 1 *
      pinnedX Tag.E8 D.L (trRoot t 2) ω ∈ adjointGroup Tag.E8 D.L :=
    mul_mem (mul_mem (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨1, rfl⟩)))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨ω, rfl⟩))
  obtain ⟨l, hlA, hl⟩ := S.rat_of_sfixed hxA hσ
  have hl' : baseChangeGL (algebraMap K D.L) l = gE D * (pinnedX Tag.E8 D.L (trRoot t 0) 1 *
      pinnedX Tag.E8 D.L (trRoot t 1) 1 * pinnedX Tag.E8 D.L (trRoot t 2) ω) * (gE D)⁻¹ := hl
  have hΨ : ΨE D l = pinnedX Tag.E8 D.L (trRoot t 0) 1 * pinnedX Tag.E8 D.L (trRoot t 1) 1 *
      pinnedX Tag.E8 D.L (trRoot t 2) ω := by
    unfold ΨE
    rw [hl']
    group
  refine ⟨l, ?_, hΨ⟩
  refine (mem_frame_iff' D TwClass.e8Ten.S₂ l).2 ⟨hlA, ?_⟩
  have h1' : ΨE D l ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₂ := by
    rw [hΨ]
    exact mul_mem (mul_mem (pinnedX_mem_S₂ D hr0 hs0 1) (pinnedX_mem_S₂ D hr1 hs1 1))
      (pinnedX_mem_S₂ D hr2 hs2 ω)
  exact h1'

end Gen

section Rz

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem X₂_mul {x y : ModGL Tag.E8 K} (hx : x ∈ TwClass.e8Ten.X₂ D) (hy : y ∈ TwClass.e8Ten.X₂ D) :
    x * y ∈ TwClass.e8Ten.X₂ D := (TwClass.e8Ten.X₂ D).mul_mem hx hy

theorem X₂_inv {x : ModGL Tag.E8 K} (hx : x ∈ TwClass.e8Ten.X₂ D) : x⁻¹ ∈ TwClass.e8Ten.X₂ D :=
  (TwClass.e8Ten.X₂ D).inv_mem hx

theorem X₂_le_adjoint {x : ModGL Tag.E8 K} (hx : x ∈ TwClass.e8Ten.X₂ D) :
    x ∈ adjointGroup Tag.E8 K :=
  ((mem_frame_iff' D TwClass.e8Ten.S₂ x).1 hx).1

@[expose] def Rz (ω : D.L) (f : ℕ → ℕ) : Prop :=
  ∃ h : ModGL Tag.E8 K, h ∈ TwClass.e8Ten.X₂ D ∧ ΨE D h ∈ Lθ Tag.E8 D.L ∧
    ∃ T : Fn D.L →ₗ[D.L] Fn D.L, ActsBy (ΨE D h) T ∧
      ∀ b, b < 2 ^ 20 → f b < 2 ^ 20 ∧ T (decv ω b) = decv ω (f b)

theorem Rz_id (ω : D.L) : Rz D ω id := by
  refine ⟨1, one_mem _, ?_, LinearMap.id, ?_, fun b hb => ⟨hb, rfl⟩⟩
  · rw [ΨE_one]
    exact one_mem _
  · intro q hq
    rw [ΨE_one, one_mul, inv_one, mul_one]
    exact ⟨hq, rfl⟩

theorem Rz_comp {ω : D.L} {f₁ f₂ : ℕ → ℕ} (h₁ : Rz D ω f₁) (h₂ : Rz D ω f₂) : Rz D ω (f₁ ∘ f₂) := by
  obtain ⟨y₁, hy₁, hL₁, T₁, hT₁, hf₁⟩ := h₁
  obtain ⟨y₂, hy₂, hL₂, T₂, hT₂, hf₂⟩ := h₂
  refine ⟨y₁ * y₂, X₂_mul D hy₁ hy₂, ?_, T₁ ∘ₗ T₂, ?_, fun b hb => ?_⟩
  · rw [ΨE_mul]
    exact mul_mem hL₁ hL₂
  · rw [ΨE_mul]
    exact hT₁.mul hT₂
  · obtain ⟨hb2, hT2⟩ := hf₂ b hb
    obtain ⟨hb1, hT1⟩ := hf₁ _ hb2
    exact ⟨hb1, by rw [LinearMap.comp_apply, hT2, hT1]; rfl⟩

theorem Rz_gen (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0)
    (hrat : ratOk () = true) (hcols : colsOk () = true) {g : ℕ} (hg : g < 8) :
    Rz D ω (applyCols (gcols g)) := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  have hbound : ∀ j, (gcols g).getD j 0 < 2 ^ 20 := by
    intro j
    have := colsOk_spec hcols g j
    rwa [gmats_getD hg] at this
  have hsem : ∀ b, b < 2 ^ 20 → genOp ω g (decv ω b) = decv ω (applyCols (gcols g) b) := by
    apply lin_induct
    · rw [decv_zero hω, map_zero, applyCols_zero, decv_zero hω]
    · intro j hj
      have h1 : genOp ω g (decv ω (1 <<< j)) = decvX ω (modelGen g (expandV (1 <<< j))) :=
        genOp_decvX hω hg (expandV_lt _)
      rw [h1, ← ratOk_spec hrat g hg j hj, applyCols_pow _ hj, gcols_getD hj]
      rfl
    · intro x y hx hy
      rw [decv_xor hω, map_add, hx, hy, applyCols_xor, decv_xor hω]
  have ht : g % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have ht' : g % 4 ∈ List.range 4 := List.mem_range.2 ht
  obtain ⟨hr0, hd0⟩ := trRoot_P1 (g % 4) ht' 0 (List.mem_range.2 (by norm_num))
  obtain ⟨hr1, hd1⟩ := trRoot_P1 (g % 4) ht' 1 (List.mem_range.2 (by norm_num))
  obtain ⟨hr2, hd2⟩ := trRoot_P1 (g % 4) ht' 2 (List.mem_range.2 (by norm_num))
  have hL0 := fun c : D.L => pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 hr0) hd0 c
  have hL1 := fun c : D.L => pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 hr1) hd1 c
  have hL2 := fun c : D.L => pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 hr2) hd2 c
  obtain ⟨ℓ, hℓ, hΨ⟩ := exists_gen D hK hω ht
  by_cases hg4 : g < 4
  · rw [Nat.mod_eq_of_lt hg4] at hΨ
    refine ⟨ℓ, hℓ, ?_, genOp ω g, ?_, fun b hb => ⟨applyCols_lt _ hbound b, hsem b hb⟩⟩
    · rw [hΨ]
      rw [Nat.mod_eq_of_lt hg4] at hL0 hL1 hL2
      exact mul_mem (mul_mem (hL0 1) (hL1 1)) (hL2 ω)
    · rw [hΨ]
      unfold genOp
      rw [if_pos hg4]
      simp only [emb_one, emb_two]
      rw [Nat.mod_eq_of_lt hg4] at hr0 hr1 hr2 hd0 hd1 hd2
      have h := ((actsBy_pinnedX hr0 hd0 (1 : D.L)).mul (actsBy_pinnedX hr1 hd1 (1 : D.L))).mul
        (actsBy_pinnedX hr2 hd2 ω)
      rw [LinearMap.comp_assoc] at h
      exact h
  · refine ⟨ℓ⁻¹, X₂_inv D hℓ, ?_, genOp ω g, ?_, fun b hb => ⟨applyCols_lt _ hbound b, hsem b hb⟩⟩
    · rw [ΨE_inv]
      exact inv_mem (by rw [hΨ]; exact mul_mem (mul_mem (hL0 1) (hL1 1)) (hL2 ω))
    · have hinv : ΨE D ℓ⁻¹ = pinnedX Tag.E8 D.L (trRoot (g % 4) 2) ω *
          (pinnedX Tag.E8 D.L (trRoot (g % 4) 1) 1 * pinnedX Tag.E8 D.L (trRoot (g % 4) 0) 1) := by
        rw [ΨE_inv, hΨ, mul_inv_rev, mul_inv_rev, pinnedX_neg, pinnedX_neg, pinnedX_neg,
          CharTwo.neg_eq, CharTwo.neg_eq]
      rw [hinv]
      unfold genOp
      rw [if_neg hg4]
      simp only [emb_one, emb_two]
      exact (actsBy_pinnedX hr2 hd2 ω).mul ((actsBy_pinnedX hr1 hd1 (1 : D.L)).mul
        (actsBy_pinnedX hr0 hd0 (1 : D.L)))

theorem Rz_word (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0)
    (hrat : ratOk () = true) (hcols : colsOk () = true) :
    ∀ w : List ℕ, (∀ g ∈ w, g < 8) → Rz D ω (applyWord (gmats ()) w) := by
  intro w
  induction w with
  | nil =>
    intro _
    have : applyWord (gmats ()) [] = id := funext fun v => applyWord_nil _ v
    rw [this]
    exact Rz_id D ω
  | cons g w ih =>
    intro hw
    have hg : g < 8 := hw g List.mem_cons_self
    have h1 := Rz_gen D hK hω hrat hcols hg
    have h2 := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have e : applyWord (gmats ()) (g :: w) = applyCols (gcols g) ∘ applyWord (gmats ()) w := by
      funext v
      rw [applyWord_cons, gmats_getD hg]
      rfl
    rw [e]
    exact Rz_comp D h1 h2

theorem Rz_bfs (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0)
    (hrat : ratOk () = true) (hcols : colsOk () = true) (hbfs : bfsOk () = true) :
    ∀ e, e < bfsTab.length →
      ∃ f, Rz D ω f ∧ ∃ s ∈ stdVecs (), f s = (bfsTab.getD e (0, 0, 0)).1 := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    obtain ⟨-, hroot, hchild⟩ := bfsOk_spec hbfs e he
    by_cases hr : (bfsTab.getD e (0, 0, 0)).2.1 = 1000
    · exact ⟨id, Rz_id D ω, _, hroot hr, rfl⟩
    · obtain ⟨hp, hg, hvec⟩ := hchild hr
      have hp' : (bfsTab.getD e (0, 0, 0)).2.1 < bfsTab.length := lt_trans hp he
      obtain ⟨f₀, hf₀, s, hs, hfs⟩ := ih _ hp hp'
      refine ⟨applyCols (gcols (bfsTab.getD e (0, 0, 0)).2.2) ∘ f₀,
        Rz_comp D (Rz_gen D hK hω hrat hcols hg) hf₀, s, hs, ?_⟩
      show applyCols _ (f₀ s) = _
      rw [hfs, hvec, gmats_getD hg]

end Rz

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
