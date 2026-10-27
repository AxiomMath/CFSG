module

public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives
public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootSpace
  CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*} [CommGroup M]

@[expose] def StrOrth (γ δ : Fin τ.rank → ℤ) : Prop :=
  iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ) ∧ ¬ IsRoot τ (γ - δ)

structure IsA2Pair (α β : Fin τ.rank → ℤ) : Prop where
  isRoot_fst : IsRoot τ α
  isRoot_snd : IsRoot τ β
  isRoot_add : IsRoot τ (α + β)
  iform_snd : iform β β = iform α α
  two_iform : 2 * iform α β = -iform α α

@[expose] def a2Roots (α β : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {α, -α, β, -β, α + β, -(α + β)}

theorem a2Roots_isRoot {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    ∀ γ ∈ a2Roots α β, IsRoot τ γ := by
  intro γ hγ
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.isRoot_fst
  · exact IsRoot.neg h.isRoot_fst
  · exact h.isRoot_snd
  · exact IsRoot.neg h.isRoot_snd
  · exact h.isRoot_add
  · exact IsRoot.neg h.isRoot_add

@[expose] def PairsStrOrth (p q : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)) : Prop :=
  ∀ γ ∈ a2Roots p.1 p.2, ∀ δ ∈ a2Roots q.1 q.2, StrOrth γ δ

@[expose] def pairRefl (p : (Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)) : WeylGroup τ :=
  rootReflection p.1 * rootReflection p.2

@[expose] def conjChar (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (t : WeylGroup τ) :
    Multiplicative (Fin τ.rank → ℤ) →* M where
  toFun x := χ (Multiplicative.ofAdd (t⁻¹ • Multiplicative.toAdd x))
  map_one' := by rw [toAdd_one, smul_zero, ofAdd_zero, map_one]
  map_mul' x y := by rw [toAdd_mul, smul_add, ofAdd_add, map_mul]

theorem isCharConj_conjChar (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (t : WeylGroup τ) :
    IsCharConj χ (conjChar χ t) t := fun _ => rfl


theorem iform_neg_fst (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left, neg_one_mul]

theorem iform_neg_snd (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right, neg_one_mul]

theorem eq_one_of_mem_kernelWeylGroup_of_smul_eq {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {w : WeylGroup τ} (hw : w ∈ kernelWeylGroup χ) {h : Fin τ.rank → ℤ} (hwh : w • h = h)
    (hreg : ∀ α ∈ kernelRoots χ, iform α h ≠ 0) : w = 1 := by
  obtain ⟨c, hc, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  obtain ⟨u, y, hy, hx⟩ := exists_weylAct_mem_dominantCone (ofLattice h)
  have hy' : ofLattice (u⁻¹ • h) = y := by
    rw [← weylAct_ofLattice, hx, ← weylAct_mul_apply, inv_mul_cancel, map_one]
    rfl
  have hC := isCharConj_conjChar χ u⁻¹
  have hw' : u⁻¹ * w * u⁻¹⁻¹ ∈ kernelWeylGroup (conjChar χ u⁻¹) := by
    rw [kernelWeylGroup_eq_map hC]
    exact ⟨w, hw, rfl⟩
  have hfix : (u⁻¹ * w * u⁻¹⁻¹) • (u⁻¹ • h) = u⁻¹ • h := by
    rw [mul_smul, mul_smul, inv_smul_smul, hwh]
  have key : ∀ α ∈ kernelRoots (conjChar χ u⁻¹), 0 < height α → 0 < iform α (u⁻¹ • h) := by
    intro α hα hpos
    have h1 : iform α (u⁻¹ • h) ≠ 0 := by
      have := hreg (u⁻¹⁻¹ • α) ((kernelRoots_iff_of_isCharConj hC).1 hα)
      rwa [← iform_smul u⁻¹, smul_inv_smul] at this
    have h2 := IsRoot.inner_nonneg_of_mem_dominantCone hα.1 hpos hy
    rw [← hy', hinner] at h2
    have h3 : (0 : ℝ) ≤ iform α (u⁻¹ • h) := nonneg_of_mul_nonneg_right h2 hc
    exact lt_of_le_of_ne (by exact_mod_cast h3) (Ne.symm h1)
  have hpres : ∀ α ∈ posRoots (kernelRoots (conjChar χ u⁻¹)),
      (u⁻¹ * w * u⁻¹⁻¹) • α ∈ posRoots (kernelRoots (conjChar χ u⁻¹)) := by
    rintro α ⟨hα, hpos⟩
    have hwα := smul_mem_kernelRoots (kernelWeylGroup_le hw') hα
    refine ⟨hwα, ?_⟩
    have e : iform ((u⁻¹ * w * u⁻¹⁻¹) • α) (u⁻¹ • h) = iform α (u⁻¹ • h) := by
      conv_lhs => rw [← hfix]
      exact iform_smul _ α _
    rcases IsRoot.height_pos_or_neg hwα.1 with hp | hn
    · exact hp
    · exfalso
      have h1 := IsRoot.inner_nonpos_of_mem_dominantCone hwα.1 hn hy
      rw [← hy', hinner, e] at h1
      have h2 : (0 : ℝ) < iform α (u⁻¹ • h) := by exact_mod_cast key α hα hpos
      nlinarith
  have h1 := eq_one_of_mem_kernelWeylGroup hw' hpres
  calc w = u * (u⁻¹ * w * u⁻¹⁻¹) * u⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_smul_eq_forall_iform_ne_zero (w : WeylGroup τ) (S : Finset (Fin τ.rank → ℤ))
    (hS : ∀ α ∈ S, ∃ v, w • v = v ∧ iform α v ≠ 0) :
    ∃ h, w • h = h ∧ ∀ α ∈ S, iform α h ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, smul_zero w, fun α hα => absurd hα (Finset.notMem_empty α)⟩
  | insert a S ha ih =>
    obtain ⟨h, hwh, hh⟩ := ih fun α hα => hS α (Finset.mem_insert_of_mem hα)
    obtain ⟨v, hwv, hav⟩ := hS a (Finset.mem_insert_self a S)
    let bad : (Fin τ.rank → ℤ) → ℤ := fun β => -iform β h / iform β v
    obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset ((insert a S).image bad)
    refine ⟨h + N • v, by rw [smul_add, smul_comm, hwh, hwv], fun β hβ h0 => ?_⟩
    rw [iform_add_right, iform_smul_right] at h0
    by_cases hβv : iform β v = 0
    · rw [hβv, mul_zero, add_zero] at h0
      rcases Finset.mem_insert.1 hβ with rfl | hβS
      · exact hav hβv
      · exact hh β hβS h0
    · apply hN
      refine Finset.mem_image.2 ⟨β, hβ, ?_⟩
      have e : -iform β h = N * iform β v := by linarith
      simp only [bad]
      rw [e, Int.mul_ediv_cancel _ hβv]

theorem exists_kernelRoot_perp {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ}
    (hw : w ∈ kernelWeylGroup χ) (hne : w ≠ 1) :
    ∃ α ∈ kernelRoots χ, ∀ v, w • v = v → iform α v = 0 := by
  classical
  by_contra hno
  push Not at hno
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  obtain ⟨h, hwh, hh⟩ := exists_smul_eq_forall_iform_ne_zero w hfin.toFinset
    fun α hα => hno α (hfin.mem_toFinset.1 hα)
  exact hne (eq_one_of_mem_kernelWeylGroup_of_smul_eq hw hwh
    fun α hα => hh α (hfin.mem_toFinset.2 hα))

theorem smul_smul_smul_of_pow_three {w : WeylGroup τ} (h3 : w ^ 3 = 1) (v : Fin τ.rank → ℤ) :
    w • w • w • v = v := by
  rw [← mul_smul, ← mul_smul, ← pow_three', h3, one_smul]

theorem add_smul_add_smul_eq_zero {w : WeylGroup τ} (h3 : w ^ 3 = 1) {α : Fin τ.rank → ℤ}
    (hα : ∀ v, w • v = v → iform α v = 0) : α + w • α + w • w • α = 0 := by
  set s := α + w • α + w • w • α with hs
  have hws : w • s = s := by
    rw [hs, smul_add, smul_add, smul_smul_smul_of_pow_three h3]
    abel
  have h1 : iform (w • α) s = iform α s := by
    conv_lhs => rw [← hws]
    exact iform_smul w α s
  have h2 : iform (w • w • α) s = iform α s := by
    conv_lhs => rw [← hws, ← hws]
    rw [iform_smul, iform_smul]
  have hss : iform s s = 0 := by
    conv_lhs => arg 1; rw [hs]
    rw [iform_add_left, iform_add_left, h1, h2, hα s hws]
    ring
  by_contra hne
  exact (iform_self_pos hne).ne' hss

theorem IsA2Pair.corootPair_snd_fst {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    corootPair β α = -1 := by
  have hp := iform_self_pos_of_isRoot h.isRoot_fst
  rw [corootPair, iform_comm, h.two_iform, h.iform_snd]
  rw [Int.neg_ediv_of_dvd ⟨1, (mul_one _).symm⟩, Int.ediv_self hp.ne']

theorem IsA2Pair.corootPair_fst_snd {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    corootPair α β = -1 := by
  have hp := iform_self_pos_of_isRoot h.isRoot_fst
  rw [corootPair, h.two_iform, Int.neg_ediv_of_dvd ⟨1, (mul_one _).symm⟩, Int.ediv_self hp.ne']

theorem IsA2Pair.rootReflection_snd_smul_fst {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    rootReflection β • α = α + β := by
  rw [rootReflection_smul h.isRoot_snd, h.corootPair_snd_fst, neg_one_smul, sub_neg_eq_add]

theorem IsA2Pair.rootReflection_fst_smul_snd {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    rootReflection α • β = α + β := by
  rw [rootReflection_smul h.isRoot_fst, h.corootPair_fst_snd, neg_one_smul, sub_neg_eq_add,
    add_comm]

theorem IsA2Pair.rootReflection_fst_snd_fst {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    rootReflection α * rootReflection β * rootReflection α = rootReflection (α + β) := by
  rw [← h.rootReflection_fst_smul_snd, rootReflection_smul_root _ h.isRoot_snd,
    rootReflection_inv h.isRoot_fst]

theorem IsA2Pair.rootReflection_snd_fst_snd {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    rootReflection β * rootReflection α * rootReflection β = rootReflection (α + β) := by
  rw [← h.rootReflection_snd_smul_fst, rootReflection_smul_root _ h.isRoot_fst,
    rootReflection_inv h.isRoot_snd]

theorem IsA2Pair.pairRefl_pow_three {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    pairRefl (α, β) ^ 3 = 1 := by
  have e : pairRefl (α, β) ^ 3 =
      (rootReflection α * rootReflection β * rootReflection α) *
        (rootReflection β * rootReflection α * rootReflection β) := by
    simp only [pairRefl, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, h.rootReflection_fst_snd_fst, h.rootReflection_snd_fst_snd,
    rootReflection_mul_self h.isRoot_add]

theorem isA2Pair_of_perp {w : WeylGroup τ} (h3 : w ^ 3 = 1) {α : Fin τ.rank → ℤ}
    (hαr : IsRoot τ α) (hα : ∀ v, w • v = v → iform α v = 0) : IsA2Pair α (w • α) := by
  have hsum := add_smul_add_smul_eq_zero h3 hα
  have hab : α + w • α = -(w • w • α) := eq_neg_of_add_eq_zero_left hsum
  have hn1 : iform (w • α) (w • α) = iform α α := iform_smul w α α
  have hn2 : iform (w • w • α) (w • w • α) = iform α α := by rw [iform_smul, iform_smul]
  have hn3 : iform (α + w • α) (α + w • α) = iform α α := by
    rw [hab]
    simp only [iform, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
    exact hn2
  refine ⟨hαr, IsRoot.smul hαr w, ?_, hn1, ?_⟩
  · rw [hab]
    exact IsRoot.neg (IsRoot.smul (IsRoot.smul hαr w) w)
  · rw [iform_add_left, iform_add_right, iform_add_right, hn1, iform_comm (w • α) α] at hn3
    linarith

theorem strOrth_of_max {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w w' : WeylGroup τ}
    (hfix : ∀ v : Fin τ.rank → ℤ, w • v = v → w' • v = v) {N : ℤ}
    (hmax : ∀ γ ∈ kernelRoots χ, (∀ v, w • v = v → iform γ v = 0) → iform γ γ ≤ N)
    {γ : Fin τ.rank → ℤ} (hγS : γ ∈ kernelRoots χ) (hγp : ∀ v, w • v = v → iform γ v = 0)
    (hγw : w' • γ = γ) (hγN : iform γ γ = N) {δ : Fin τ.rank → ℤ} (hδS : δ ∈ kernelRoots χ)
    (hδp : ∀ v, w' • v = v → iform δ v = 0) : StrOrth γ δ := by
  have h0 : iform γ δ = 0 := by rw [iform_comm]; exact hδp γ hγw
  have hδpos := iform_self_pos_of_isRoot hδS.1
  have hpw : ∀ ε, IsRoot τ ε → χ (Multiplicative.ofAdd ε) = 1 →
      (∀ v, w • v = v → iform ε v = 0) → iform ε ε ≤ N := fun ε hε hχ hp => hmax ε ⟨hε, hχ⟩ hp
  refine ⟨h0, fun hr => ?_, fun hr => ?_⟩
  · have := hpw (γ + δ) hr (by rw [ofAdd_add, map_mul, hγS.2, hδS.2, one_mul]) fun v hv => by
      rw [iform_add_left, hγp v hv, hδp v (hfix v hv), add_zero]
    rw [iform_add_left, iform_add_right, iform_add_right, h0, iform_comm δ γ, h0, hγN] at this
    omega
  · have := hpw (γ - δ) hr (by rw [ofAdd_sub, map_div, hγS.2, hδS.2, div_one]) fun v hv => by
      rw [iform_sub_left, hγp v hv, hδp v (hfix v hv), sub_zero]
    rw [iform_sub_left, iform_sub_right, iform_sub_right, h0, iform_comm δ γ, h0, hγN] at this
    omega

theorem a2Roots_props {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w w' : WeylGroup τ}
    {α β : Fin τ.rank → ℤ} (hA2 : IsA2Pair α β) (hαS : α ∈ kernelRoots χ)
    (hβS : β ∈ kernelRoots χ) (hαp : ∀ v, w • v = v → iform α v = 0)
    (hβp : ∀ v, w • v = v → iform β v = 0) (hfixα : w' • α = α) (hfixβ : w' • β = β) :
    ∀ γ ∈ a2Roots α β, γ ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform γ v = 0) ∧
      w' • γ = γ ∧ iform γ γ = iform α α := by
  have hsumS : α + β ∈ kernelRoots χ :=
    ⟨hA2.isRoot_add, by rw [ofAdd_add, map_mul, hαS.2, hβS.2, one_mul]⟩
  have hsump : ∀ v, w • v = v → iform (α + β) v = 0 := fun v hv => by
    rw [iform_add_left, hαp v hv, hβp v hv, add_zero]
  have hsumw : w' • (α + β) = α + β := by rw [smul_add, hfixα, hfixβ]
  have hsumN : iform (α + β) (α + β) = iform α α := by
    rw [iform_add_left, iform_add_right, iform_add_right, iform_comm β α, hA2.iform_snd]
    linarith [hA2.two_iform]
  have hneg : ∀ γ, γ ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform γ v = 0) ∧ w' • γ = γ ∧
      iform γ γ = iform α α → -γ ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform (-γ) v = 0) ∧
      w' • (-γ) = -γ ∧ iform (-γ) (-γ) = iform α α := by
    rintro γ ⟨hγS, hγp, hγw, hγN⟩
    refine ⟨⟨IsRoot.neg hγS.1, chi_neg hγS.2⟩, fun v hv => by rw [iform_neg_fst, hγp v hv,
      neg_zero], by rw [smul_neg, hγw], by rw [iform_neg_fst, iform_neg_snd, neg_neg, hγN]⟩
  have hα : α ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform α v = 0) ∧ w' • α = α ∧
      iform α α = iform α α := ⟨hαS, hαp, hfixα, rfl⟩
  have hβ : β ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform β v = 0) ∧ w' • β = β ∧
      iform β β = iform α α := ⟨hβS, hβp, hfixβ, hA2.iform_snd⟩
  have hs : α + β ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform (α + β) v = 0) ∧
      w' • (α + β) = α + β ∧ iform (α + β) (α + β) = iform α α := ⟨hsumS, hsump, hsumw, hsumN⟩
  intro γ hγ
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hneg _ hα
  · exact hβ
  · exact hneg _ hβ
  · exact hs
  · exact hneg _ hs

theorem exists_a2Blocks_aux {χ : Multiplicative (Fin τ.rank → ℤ) →* M} :
    ∀ (n : ℕ) (w : WeylGroup τ), w ∈ kernelWeylGroup χ → w ^ 3 = 1 →
      {γ | IsRoot τ γ ∧ w • γ ≠ γ}.ncard = n →
      ∃ B : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)),
        (∀ p ∈ B, IsA2Pair p.1 p.2 ∧ ∀ γ ∈ a2Roots p.1 p.2, γ ∈ kernelRoots χ ∧
          ∀ v, w • v = v → iform γ v = 0) ∧
        B.Pairwise PairsStrOrth ∧ w = (B.map pairRefl).prod := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw h3 hn
  by_cases hw1 : w = 1
  · subst hw1
    exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
  set T := {α | α ∈ kernelRoots χ ∧ ∀ v, w • v = v → iform α v = 0} with hT
  have hTfin : T.Finite := (finite_setOf_isRoot τ).subset fun α h => h.1.1
  obtain ⟨α₀, hα₀, hα₀p⟩ := exists_kernelRoot_perp hw hw1
  obtain ⟨α, hαT, hαmax⟩ := Finset.exists_max_image hTfin.toFinset (fun α => iform α α)
    ⟨α₀, hTfin.mem_toFinset.2 ⟨hα₀, hα₀p⟩⟩
  obtain ⟨hαS, hαp⟩ := hTfin.mem_toFinset.1 hαT
  have hmax : ∀ γ ∈ kernelRoots χ, (∀ v, w • v = v → iform γ v = 0) →
      iform γ γ ≤ iform α α := fun γ hγ hγp => hαmax γ (hTfin.mem_toFinset.2 ⟨hγ, hγp⟩)
  set β := w • α with hβ
  have hA2 : IsA2Pair α β := isA2Pair_of_perp h3 hαS.1 hαp
  have hwχ : w ∈ charStabilizer χ := kernelWeylGroup_le hw
  have hβS : β ∈ kernelRoots χ := smul_mem_kernelRoots hwχ hαS
  have hβp : ∀ v, w • v = v → iform β v = 0 := fun v hv => by
    calc iform β v = iform (w • α) (w • v) := by rw [hv]
      _ = 0 := by rw [iform_smul]; exact hαp v hv
  have hwβ : w • β = -(α + β) :=
    eq_neg_of_add_eq_zero_right (add_smul_add_smul_eq_zero h3 hαp)
  set c := pairRefl (α, β) with hc
  have hcS : c ∈ kernelWeylGroup χ :=
    mul_mem (rootReflection_mem_kernelWeylGroup hαS) (rootReflection_mem_kernelWeylGroup hβS)
  have hconj : w * c * w⁻¹ = c := by
    have h1 : w * rootReflection α * w⁻¹ = rootReflection β :=
      (rootReflection_smul_root w hαS.1).symm
    have h2 : w * rootReflection β * w⁻¹ = rootReflection (α + β) := by
      rw [← rootReflection_smul_root w hA2.isRoot_snd, hwβ, rootReflection_neg hA2.isRoot_add]
    calc w * c * w⁻¹ = (w * rootReflection α * w⁻¹) * (w * rootReflection β * w⁻¹) := by
          rw [hc, pairRefl]
          group
      _ = rootReflection β * (rootReflection β * rootReflection α * rootReflection β) := by
          rw [h1, h2, hA2.rootReflection_snd_fst_snd]
      _ = c := by
          rw [← mul_assoc, ← mul_assoc, rootReflection_mul_self hA2.isRoot_snd, one_mul, hc,
            pairRefl]
  have hcomm : Commute w c := by
    calc w * c = (w * c * w⁻¹) * w := by group
      _ = c * w := by rw [hconj]
  set w' := w * c⁻¹ with hw'
  have hw'S : w' ∈ kernelWeylGroup χ := mul_mem hw (inv_mem hcS)
  have hw'3 : w' ^ 3 = 1 := by
    rw [hw', (hcomm.inv_right).mul_pow, h3, inv_pow, hA2.pairRefl_pow_three, inv_one, one_mul]
  have hcinv : c⁻¹ = rootReflection β * rootReflection α := by
    rw [hc, pairRefl, mul_inv_rev, rootReflection_inv hA2.isRoot_snd,
      rootReflection_inv hA2.isRoot_fst]
  have hfixα : w' • α = α := by
    rw [hw', mul_smul, hcinv, mul_smul, rootReflection_smul_self hA2.isRoot_fst, smul_neg,
      hA2.rootReflection_snd_smul_fst, smul_neg, smul_add, ← hβ, hwβ]
    abel
  have hfixβ : w' • β = β := by
    have e : rootReflection β • (α + β) = α := by
      rw [smul_add, hA2.rootReflection_snd_smul_fst, rootReflection_smul_self hA2.isRoot_snd]
      abel
    rw [hw', mul_smul, hcinv, mul_smul, hA2.rootReflection_fst_smul_snd, e]
  have hfix : ∀ v : Fin τ.rank → ℤ, w • v = v → w' • v = v := fun v hv => by
    rw [hw', mul_smul, hcinv, mul_smul,
      rootReflection_smul_of_iform_eq_zero hA2.isRoot_fst (hαp v hv),
      rootReflection_smul_of_iform_eq_zero hA2.isRoot_snd (hβp v hv), hv]
  have hsub : {γ | IsRoot τ γ ∧ w' • γ ≠ γ} ⊂ {γ | IsRoot τ γ ∧ w • γ ≠ γ} := by
    refine ⟨fun γ ⟨hγ, hne⟩ => ⟨hγ, fun h => hne (hfix γ h)⟩, fun h => ?_⟩
    have hαβ : β ≠ α := by
      intro e
      have h2 := hA2.two_iform
      rw [e] at h2
      have := iform_self_pos_of_isRoot hαS.1
      omega
    exact (h ⟨hαS.1, hαβ⟩).2 hfixα
  have hlt : {γ | IsRoot τ γ ∧ w' • γ ≠ γ}.ncard < n := by
    rw [← hn]
    exact Set.ncard_lt_ncard hsub ((finite_setOf_isRoot τ).subset fun γ h => h.1)
  obtain ⟨B', hB', hpair', hprod'⟩ := ih _ hlt w' hw'S hw'3 rfl
  have hsix : ∀ γ ∈ a2Roots α β, γ ∈ kernelRoots χ ∧ (∀ v, w • v = v → iform γ v = 0) ∧
      w' • γ = γ ∧ iform γ γ = iform α α :=
    a2Roots_props hA2 hαS hβS hαp hβp hfixα hfixβ
  refine ⟨(α, β) :: B', fun p hp => ?_, List.Pairwise.cons (fun q hq => ?_) hpair', ?_⟩
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hA2, fun γ hγ => ⟨(hsix γ hγ).1, (hsix γ hγ).2.1⟩⟩
    · obtain ⟨h1, h2⟩ := hB' p hp
      exact ⟨h1, fun γ hγ => ⟨(h2 γ hγ).1, fun v hv => (h2 γ hγ).2 v (hfix v hv)⟩⟩
  · obtain ⟨-, h2⟩ := hB' q hq
    intro γ hγ δ hδ
    obtain ⟨hγS, hγp, hγw, hγN⟩ := hsix γ hγ
    exact strOrth_of_max hfix hmax hγS hγp hγw hγN (h2 δ hδ).1 (h2 δ hδ).2
  · rw [List.map_cons, List.prod_cons, ← hprod', ← hc, hw', ← mul_assoc, ← hcomm.eq,
      mul_inv_cancel_right]

theorem exists_a2Blocks {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ}
    (hw : w ∈ kernelWeylGroup χ) (h3 : w ^ 3 = 1) :
    ∃ B : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)),
      (∀ p ∈ B, IsA2Pair p.1 p.2 ∧ a2Roots p.1 p.2 ⊆ kernelRoots χ) ∧
      B.Pairwise PairsStrOrth ∧ w = (B.map pairRefl).prod := by
  obtain ⟨B, hB, hP, hprod⟩ := exists_a2Blocks_aux _ w hw h3 rfl
  exact ⟨B, fun p hp => ⟨(hB p hp).1, fun γ hγ => ((hB p hp).2 γ hγ).1⟩, hP, hprod⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
