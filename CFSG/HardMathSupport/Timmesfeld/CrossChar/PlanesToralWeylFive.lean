module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralChain

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*} [CommGroup M]


theorem rootReflection_smul_SL (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (x : Fin τ.rank → ℤ) : rootReflection β • x = x - iform β x • β := by
  rw [rootReflection_smul hβ, corootPair, hSL β hβ, Int.mul_ediv_cancel_left _ two_ne_zero]

theorem iform_le_one_SL (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) :
    -1 ≤ iform γ δ ∧ iform γ δ ≤ 1 := by
  have h1 := iform_self_pos (sub_ne_zero.2 hne)
  have h2 := iform_self_pos (fun h : γ + δ = 0 => hne' (eq_neg_of_add_eq_zero_left h))
  rw [iform_sub_left, iform_sub_right, iform_sub_right, hSL γ hγ, hSL δ hδ, iform_comm δ γ] at h1
  rw [iform_add_left, iform_add_right, iform_add_right, hSL γ hγ, hSL δ hδ, iform_comm δ γ] at h2
  constructor <;> omega

theorem strOrth_of_iform_eq_zero_SL (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h0 : iform γ δ = 0) :
    StrOrth γ δ := by
  refine ⟨h0, fun hr => ?_, fun hr => ?_⟩
  · have := hSL _ hr
    rw [iform_add_left, iform_add_right, iform_add_right, hSL γ hγ, hSL δ hδ, h0,
      iform_comm δ γ, h0] at this
    omega
  · have := hSL _ hr
    rw [iform_sub_left, iform_sub_right, iform_sub_right, hSL γ hγ, hSL δ hδ, h0,
      iform_comm δ γ, h0] at this
    omega

@[expose] def OrbitZero5 (w : WeylGroup τ) : Prop :=
  ∀ γ : Fin τ.rank → ℤ, (∀ v, w • v = v → iform γ v = 0) →
    γ + w • γ + w • w • γ + w • w • w • γ + w • w • w • w • γ = 0

theorem orbitZero5_of_pow {w : WeylGroup τ} (h5 : w ^ 5 = 1) : OrbitZero5 w := by
  intro γ hγ
  set s := γ + w • γ + w • w • γ + w • w • w • γ + w • w • w • w • γ with hs
  have hw5 : w • w • w • w • w • γ = γ := by
    have h55 : w * w * w * w * w = w ^ 5 := by simp only [pow_succ, pow_zero, one_mul]
    rw [← mul_smul, ← mul_smul, ← mul_smul, ← mul_smul, h55, h5, one_smul]
  have hws : w • s = s := by
    rw [hs, smul_add, smul_add, smul_add, smul_add, hw5]
    abel
  have hsplit : ∀ t, iform s t = iform γ t + iform (w • γ) t + iform (w • w • γ) t +
      iform (w • w • w • γ) t + iform (w • w • w • w • γ) t := fun t => by
    rw [hs, iform_add_left, iform_add_left, iform_add_left, iform_add_left]
  have hinv : ∀ (x : Fin τ.rank → ℤ), iform (w • x) s = iform x s := fun x => by
    conv_lhs => rw [← hws]
    exact iform_smul w x s
  have hss := hsplit s
  rw [hinv, hinv, hinv, hinv, hinv, hinv, hinv, hinv, hinv, hinv, hγ s hws] at hss
  by_contra hne
  have := iform_self_pos hne
  omega


section Chain

variable (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {β : Fin 4 → Fin τ.rank → ℤ}
include hSL

theorem IsAChain.gram_four (h : IsAChain β) :
    iform (β 0) (β 0) = 2 ∧ iform (β 1) (β 1) = 2 ∧ iform (β 2) (β 2) = 2 ∧
    iform (β 3) (β 3) = 2 ∧ iform (β 0) (β 1) = -1 ∧ iform (β 1) (β 0) = -1 ∧
    iform (β 1) (β 2) = -1 ∧ iform (β 2) (β 1) = -1 ∧ iform (β 2) (β 3) = -1 ∧
    iform (β 3) (β 2) = -1 ∧ iform (β 0) (β 2) = 0 ∧ iform (β 2) (β 0) = 0 ∧
    iform (β 0) (β 3) = 0 ∧ iform (β 3) (β 0) = 0 ∧ iform (β 1) (β 3) = 0 ∧
    iform (β 3) (β 1) = 0 := by
  have f01 := h.adj 0 1 rfl
  have f12 := h.adj 1 2 rfl
  have f23 := h.adj 2 3 rfl
  have f02 := h.orth 0 2 (by decide)
  have f03 := h.orth 0 3 (by decide)
  have f13 := h.orth 1 3 (by decide)
  exact ⟨hSL _ (h.isRoot 0), hSL _ (h.isRoot 1), hSL _ (h.isRoot 2), hSL _ (h.isRoot 3), f01,
    by rw [iform_comm]; exact f01, f12, by rw [iform_comm]; exact f12, f23,
    by rw [iform_comm]; exact f23, f02, by rw [iform_comm]; exact f02, f03,
    by rw [iform_comm]; exact f03, f13, by rw [iform_comm]; exact f13⟩

theorem IsAChain.chainRefl_smul_four (h : IsAChain β) :
    chainRefl β • β 0 = β 1 ∧ chainRefl β • β 1 = β 2 ∧ chainRefl β • β 2 = β 3 ∧
      chainRefl β • β 3 = -(β 0 + β 1 + β 2 + β 3) := by
  have r := fun i => rootReflection_smul_SL hSL (h.isRoot i)
  obtain ⟨g00, g11, g22, g33, g01, g10, g12, g21, g23, g32, g02, g20, g03, g30, g13, g31⟩ :=
    h.gram_four hSL
  have hc : chainRefl β = rootReflection (β 0) * rootReflection (β 1) * rootReflection (β 2) *
      rootReflection (β 3) := by
    simp [chainRefl, List.ofFn_succ, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [hc, mul_smul, r, iform_sub_right, iform_smul_right, g00, g11, g22, g33, g01, g10,
      g12, g21, g23, g32, g02, g20, g03, g30, g13, g31]
    module

end Chain

theorem perp_smul {w : WeylGroup τ} {x : Fin τ.rank → ℤ} (hx : ∀ v, w • v = v → iform x v = 0) :
    ∀ v, w • v = v → iform (w • x) v = 0 := fun v hv => by
  rw [← hv, iform_smul]
  exact hx v hv

theorem abs_iform_le_two_SL (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {x y : Fin τ.rank → ℤ}
    (hx : IsRoot τ x) (hy : IsRoot τ y) : -2 ≤ iform x y ∧ iform x y ≤ 2 := by
  have h1 : 0 ≤ iform (x - y) (x - y) := by
    by_cases h : x - y = 0
    · rw [h]; simp [iform]
    · exact (iform_self_pos h).le
  have h2 : 0 ≤ iform (x + y) (x + y) := by
    by_cases h : x + y = 0
    · rw [h]; simp [iform]
    · exact (iform_self_pos h).le
  rw [iform_sub_left, iform_sub_right, iform_sub_right, hSL x hx, hSL y hy, iform_comm y x] at h1
  rw [iform_add_left, iform_add_right, iform_add_right, hSL x hx, hSL y hy, iform_comm y x] at h2
  constructor <;> omega

section Orbit

variable (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {w : WeylGroup τ} (hP : OrbitZero5 w)
  {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : ∀ v, w • v = v → iform α v = 0)
include hSL hP hα hαp

theorem orbit_gram5 :
    w • w • w • w • α = -(α + w • α + w • w • α + w • w • w • α) ∧
      w • (w • w • w • w • α) = α ∧
      iform (w • α) (w • w • α) = iform α (w • α) ∧
      iform (w • w • α) (w • w • w • α) = iform α (w • α) ∧
      iform (w • α) (w • w • w • α) = iform α (w • w • α) ∧
      iform α (w • w • w • α) = iform α (w • w • α) ∧
      iform α (w • α) + iform α (w • w • α) = -1 := by
  set a1 := w • α with ha1
  set a2 := w • a1 with ha2
  set a3 := w • a2 with ha3
  set a4 := w • a3 with ha4
  have h0 : α + a1 + a2 + a3 + a4 = 0 := hP α hαp
  have h1 : a1 + a2 + a3 + a4 + w • a4 = 0 := hP a1 (perp_smul hαp)
  have e4 : a4 = -(α + a1 + a2 + a3) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  have e5 : w • a4 = α := by
    have : w • a4 = α + (a1 + a2 + a3 + a4 + w • a4) - (α + a1 + a2 + a3 + a4) := by abel
    rw [this, h0, h1]
    abel
  have inv : ∀ x y : Fin τ.rank → ℤ, iform (w • x) (w • y) = iform x y := iform_smul w
  have g12 : iform a1 a2 = iform α a1 := inv _ _
  have g23 : iform a2 a3 = iform α a1 := by rw [inv, inv]
  have g13 : iform a1 a3 = iform α a2 := inv _ _
  have g24 : iform a2 a4 = iform α a2 := by rw [inv, inv]
  have g34 : iform a3 a4 = iform α a1 := by rw [inv, inv, inv]
  have g03 : iform α a3 = iform α a2 := by
    have e : iform α a3 = iform (w • a4) (w • a2) := by rw [e5]
    rw [e, inv, iform_comm, g24]
  have g04 : iform α a4 = iform α a1 := by
    have e : iform α a4 = iform (w • a4) (w • a3) := by rw [e5]
    rw [e, inv, iform_comm, g34]
  refine ⟨e4, e5, g12, g23, g13, g03, ?_⟩
  have hsum : iform α (α + a1 + a2 + a3 + a4) = 0 := by
    rw [h0]
    simp [iform]
  rw [iform_add_right, iform_add_right, iform_add_right, iform_add_right, hSL α hα, g03,
    g04] at hsum
  omega

theorem orbit_bounds5 :
    (-1 ≤ iform α (w • α) ∧ iform α (w • α) ≤ 1) ∧
      (-1 ≤ iform α (w • w • α) ∧ iform α (w • w • α) ≤ 1) := by
  obtain ⟨e4, -, -, -, -, -, hsum⟩ := orbit_gram5 hSL hP hα hαp
  have h2 := hSL α hα
  have hr1 : IsRoot τ (w • α) := IsRoot.smul hα w
  have hr2 : IsRoot τ (w • w • α) := IsRoot.smul hr1 w
  have b1 := abs_iform_le_two_SL hSL hα hr1
  have b2 := abs_iform_le_two_SL hSL hα hr2
  have n1 : w • α ≠ α := fun e => by
    have := hαp α e
    omega
  have n2 : w • w • α ≠ -α := fun e => by
    have e3 : w • w • w • α = -(w • α) := by rw [e, smul_neg]
    have e4' : w • w • w • w • α = α := by rw [e3, smul_neg, e, neg_neg]
    rw [e4', e3, e] at e4
    apply hα.ne_zero
    rw [e4]
    abel
  have n1' : w • α ≠ -α := fun e => by
    have e2 : w • w • α = α := by rw [e, smul_neg, e, neg_neg]
    rw [e2, e, iform_neg_snd, h2] at hsum
    omega
  have n2' : w • w • α ≠ α := fun e => by
    rw [e, h2] at hsum
    omega
  have i1 := iform_le_one_SL hSL hα hr1 (Ne.symm n1) (fun e => n1' (by
    nth_rewrite 2 [e]
    rw [neg_neg]))
  have i2 := iform_le_one_SL hSL hα hr2 (Ne.symm n2') (fun e => n2 (by
    nth_rewrite 2 [e]
    rw [neg_neg]))
  exact ⟨i1, i2⟩

end Orbit

theorem chainRefl_four (β : Fin 4 → Fin τ.rank → ℤ) :
    chainRefl β = rootReflection (β 0) * rootReflection (β 1) * rootReflection (β 2) *
      rootReflection (β 3) := by
  simp [chainRefl, List.ofFn_succ, mul_assoc]

theorem exists_good_root5 (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ} (hw : w ∈ kernelWeylGroup χ)
    (hP : OrbitZero5 w) {α₀ : Fin τ.rank → ℤ} (hα₀ : α₀ ∈ kernelRoots χ)
    (hα₀p : ∀ v, w • v = v → iform α₀ v = 0) :
    ∃ α ∈ kernelRoots χ, (∀ v, w • v = v → iform α v = 0) ∧ iform α (w • α) = -1 := by
  obtain ⟨-, -, g12, g23, -, g03, hsum⟩ := orbit_gram5 hSL hP hα₀.1 hα₀p
  obtain ⟨⟨b1, b1'⟩, ⟨b2, b2'⟩⟩ := orbit_bounds5 hSL hP hα₀.1 hα₀p
  by_cases h1 : iform α₀ (w • α₀) = -1
  · exact ⟨α₀, hα₀, hα₀p, h1⟩
  have hg1 : iform α₀ (w • α₀) = 0 := by omega
  have hg2 : iform α₀ (w • w • α₀) = -1 := by omega
  have hwχ : w ∈ charStabilizer χ := kernelWeylGroup_le hw
  have h2S : w • w • α₀ ∈ kernelRoots χ :=
    smul_mem_kernelRoots hwχ (smul_mem_kernelRoots hwχ hα₀)
  have hr : IsRoot τ (α₀ + w • w • α₀) := by
    refine isRoot_add_of_iform_neg hα₀.1 h2S.1 (fun e => ?_) (by omega)
    have : iform α₀ (w • w • α₀) = iform (-(w • w • α₀)) (w • w • α₀) := by rw [← e]
    rw [this, iform_neg_fst, hSL _ h2S.1] at hg2
    omega
  refine ⟨α₀ + w • w • α₀, ⟨hr, by rw [ofAdd_add, map_mul, hα₀.2, h2S.2, one_mul]⟩,
    fun v hv => by rw [iform_add_left, hα₀p v hv, perp_smul (perp_smul hα₀p) v hv, add_zero],
    ?_⟩
  rw [smul_add, iform_add_left, iform_add_right, iform_add_right, g03,
    iform_comm (w • w • α₀) (w • α₀), g12, g23]
  omega

theorem isAChain_orbit5 (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {w : WeylGroup τ}
    (hP : OrbitZero5 w) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hαp : ∀ v, w • v = v → iform α v = 0) (h1 : iform α (w • α) = -1) :
    IsAChain (![α, w • α, w • w • α, w • w • w • α] : Fin 4 → Fin τ.rank → ℤ) := by
  obtain ⟨-, -, g12, g23, g13, g03, hsum⟩ := orbit_gram5 hSL hP hα hαp
  have h2 : iform α (w • w • α) = 0 := by omega
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact hα
    · exact IsRoot.smul hα w
    · exact IsRoot.smul (IsRoot.smul hα w) w
    · exact IsRoot.smul (IsRoot.smul (IsRoot.smul hα w) w) w
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega

theorem exists_a4Blocks_aux (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} :
    ∀ (n : ℕ) (w : WeylGroup τ), w ∈ kernelWeylGroup χ → OrbitZero5 w →
      {γ | IsRoot τ γ ∧ w • γ ≠ γ}.ncard = n →
      ∃ B : List (Fin 4 → Fin τ.rank → ℤ),
        (∀ β ∈ B, IsAChain β ∧ ∀ x ∈ aChainRoots β, x ∈ kernelRoots χ ∧
          ∀ v, w • v = v → iform x v = 0) ∧
        B.Pairwise ChainsStrOrth ∧ w = (B.map chainRefl).prod := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hP hn
  by_cases hw1 : w = 1
  · subst hw1
    exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
  obtain ⟨α₀, hα₀, hα₀p⟩ := exists_kernelRoot_perp hw hw1
  obtain ⟨α, hαS, hαp, h1⟩ := exists_good_root5 hSL hw hP hα₀ hα₀p
  have hwχ : w ∈ charStabilizer χ := kernelWeylGroup_le hw
  set β : Fin 4 → Fin τ.rank → ℤ := ![α, w • α, w • w • α, w • w • w • α] with hβ
  have hch : IsAChain β := isAChain_orbit5 hSL hP hαS.1 hαp h1
  obtain ⟨e4, e5, -⟩ := orbit_gram5 hSL hP hαS.1 hαp
  have hβS : ∀ k, β k ∈ kernelRoots χ := by
    intro k
    fin_cases k
    · exact hαS
    · exact smul_mem_kernelRoots hwχ hαS
    · exact smul_mem_kernelRoots hwχ (smul_mem_kernelRoots hwχ hαS)
    · exact smul_mem_kernelRoots hwχ (smul_mem_kernelRoots hwχ (smul_mem_kernelRoots hwχ hαS))
  have hβp : ∀ k, ∀ v, w • v = v → iform (β k) v = 0 := by
    intro k
    fin_cases k
    · exact hαp
    · exact perp_smul hαp
    · exact perp_smul (perp_smul hαp)
    · exact perp_smul (perp_smul (perp_smul hαp))
  obtain ⟨c0, c1, c2, c3⟩ := hch.chainRefl_smul_four hSL
  set c := chainRefl β with hc
  have hcS : c ∈ kernelWeylGroup χ := by
    rw [hc, chainRefl_four]
    exact mul_mem (mul_mem (mul_mem (rootReflection_mem_kernelWeylGroup (hβS 0))
      (rootReflection_mem_kernelWeylGroup (hβS 1))) (rootReflection_mem_kernelWeylGroup (hβS 2)))
      (rootReflection_mem_kernelWeylGroup (hβS 3))
  have hcfix : ∀ x, (∀ k, iform (β k) x = 0) → c • x = x := by
    intro x hx
    rw [hc, chainRefl_four, mul_smul, mul_smul, mul_smul,
      rootReflection_smul_of_iform_eq_zero (hch.isRoot 3) (hx 3),
      rootReflection_smul_of_iform_eq_zero (hch.isRoot 2) (hx 2),
      rootReflection_smul_of_iform_eq_zero (hch.isRoot 1) (hx 1),
      rootReflection_smul_of_iform_eq_zero (hch.isRoot 0) (hx 0)]
  have hcinvfix : ∀ x, (∀ k, iform (β k) x = 0) → c⁻¹ • x = x := fun x hx => by
    conv_lhs => rw [← hcfix x hx]
    rw [inv_smul_smul]
  set w' := c⁻¹ * w with hw'def
  have hw'S : w' ∈ kernelWeylGroup χ := mul_mem (inv_mem hcS) hw
  have hw' : ∀ x : Fin τ.rank → ℤ, w' • x = c⁻¹ • w • x := fun x => mul_smul _ _ _
  have c0' : c • α = w • α := c0
  have c1' : c • (w • α) = w • w • α := c1
  have c2' : c • (w • w • α) = w • w • w • α := c2
  have c3' : c • (w • w • w • α) = w • w • w • w • α := by
    rw [e4]
    exact c3
  have hfixβ : ∀ k, w' • β k = β k := by
    intro k
    fin_cases k
    · change w' • α = α
      rw [hw', ← c0', inv_smul_smul]
    · change w' • (w • α) = w • α
      rw [hw', ← c1', inv_smul_smul]
    · change w' • (w • w • α) = w • w • α
      rw [hw', ← c2', inv_smul_smul]
    · change w' • (w • w • w • α) = w • w • w • α
      rw [hw', ← c3', inv_smul_smul]
  have hfix : ∀ v, w • v = v → w' • v = v := fun v hv => by
    rw [hw', hv, hcinvfix v fun k => hβp k v hv]
  have hperp : ∀ x, (∀ k, iform (β k) x = 0) → ∀ k, iform (β k) (w • x) = 0 := by
    intro x hx k
    fin_cases k
    · change iform α (w • x) = 0
      have : iform α (w • x) = iform (w • (w • w • w • w • α)) (w • x) := by rw [e5]
      have h0 : iform α x = 0 := hx 0
      have h1' : iform (w • α) x = 0 := hx 1
      have h2' : iform (w • w • α) x = 0 := hx 2
      have h3' : iform (w • w • w • α) x = 0 := hx 3
      rw [this, iform_smul, e4, iform_neg_fst, iform_add_left, iform_add_left, iform_add_left, h0,
        h1', h2', h3']
      rfl
    · change iform (w • α) (w • x) = 0
      rw [iform_smul]
      exact hx 0
    · change iform (w • w • α) (w • x) = 0
      rw [iform_smul]
      exact hx 1
    · change iform (w • w • w • α) (w • x) = 0
      rw [iform_smul]
      exact hx 2
  have hw'eq : ∀ x, (∀ k, iform (β k) x = 0) → w' • x = w • x := fun x hx => by
    rw [hw', hcinvfix _ (hperp x hx)]
  have hP' : OrbitZero5 w' := by
    intro γ hγ
    have hγβ : ∀ k, iform (β k) γ = 0 := fun k => by
      rw [iform_comm]
      exact hγ _ (hfixβ k)
    have hγw : ∀ v, w • v = v → iform γ v = 0 := fun v hv => hγ v (hfix v hv)
    have x1 := hperp γ hγβ
    have x2 := hperp _ x1
    have x3 := hperp _ x2
    rw [hw'eq γ hγβ, hw'eq _ x1, hw'eq _ x2, hw'eq _ x3]
    exact hP γ hγw
  have hsub : {γ | IsRoot τ γ ∧ w' • γ ≠ γ} ⊂ {γ | IsRoot τ γ ∧ w • γ ≠ γ} := by
    refine ⟨fun γ ⟨hγ, hne⟩ => ⟨hγ, fun h => hne (hfix γ h)⟩, fun h => ?_⟩
    have hmov : w • α ≠ α := fun e => by
      have := hαp α e
      rw [hSL α hαS.1] at this
      omega
    exact (h ⟨hαS.1, hmov⟩).2 (hfixβ 0)
  have hlt : {γ | IsRoot τ γ ∧ w' • γ ≠ γ}.ncard < n := by
    rw [← hn]
    exact Set.ncard_lt_ncard hsub ((finite_setOf_isRoot τ).subset fun γ h => h.1)
  obtain ⟨B', hB', hpair', hprod'⟩ := ih _ hlt w' hw'S hP' rfl
  refine ⟨β :: B', fun γ hγ => ?_, List.Pairwise.cons (fun γ hγ => ?_) hpair', ?_⟩
  · rcases List.mem_cons.1 hγ with rfl | hγ
    · exact ⟨hch, fun x hx => ⟨aChainRoots_subset_kernelRoots hSL hch hβS hx,
        fun v hv => iform_eq_zero_of_mem_aChainRoots hx fun k => hβp k v hv⟩⟩
    · obtain ⟨h1, h2⟩ := hB' γ hγ
      exact ⟨h1, fun x hx => ⟨(h2 x hx).1, fun v hv => (h2 x hx).2 v (hfix v hv)⟩⟩
  · obtain ⟨hγch, hγ2⟩ := hB' γ hγ
    intro x hx y hy
    have hxr := mem_aChainRoots_isRoot hSL hch x hx
    have hyr := mem_aChainRoots_isRoot hSL hγch y hy
    have hx' : w' • x = x := smul_eq_of_mem_aChainRoots hx hfixβ
    refine strOrth_of_iform_eq_zero_SL hSL hxr hyr ?_
    rw [iform_comm]
    exact (hγ2 y hy).2 x hx'
  · rw [List.map_cons, List.prod_cons, ← hprod', hw'def, ← hc, mul_inv_cancel_left]

theorem exists_a4Blocks (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ} (hw : w ∈ kernelWeylGroup χ)
    (h5 : w ^ 5 = 1) :
    ∃ B : List (Fin 4 → Fin τ.rank → ℤ),
      (∀ β ∈ B, IsAChain β ∧ aChainRoots β ⊆ kernelRoots χ) ∧
      B.Pairwise ChainsStrOrth ∧ w = (B.map chainRefl).prod := by
  obtain ⟨B, hB, hP, hprod⟩ := exists_a4Blocks_aux hSL _ w hw (orbitZero5_of_pow h5) rfl
  exact ⟨B, fun β hβ => ⟨(hB β hβ).1, fun x hx => ((hB β hβ).2 x hx).1⟩, hP, hprod⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
