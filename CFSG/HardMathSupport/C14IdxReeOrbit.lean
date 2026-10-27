module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation
public import CFSG.RankThree.PartOne.RF4.Basic

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction

private theorem quadForm_mul_iform_dualRoot
    (x y : Fin ReeTag.F4.tag.rank → ℤ) (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) :
    ReeTag.F4.quadForm x * ReeTag.F4.quadForm y *
        iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot y) = 8 * iform x y := by
  have key : ∀ x ∈ rootFinset ReeTag.F4.tag, ∀ y ∈ rootFinset ReeTag.F4.tag,
      ReeTag.F4.quadForm x * ReeTag.F4.quadForm y *
        iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot y) = 8 * iform x y := by
    decide +kernel
  exact key x (mem_rootFinset.2 hx) y (mem_rootFinset.2 hy)

private theorem root_pair_arith
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) :
    (iform x x = iform y y → x ≠ y → x ≠ -y → iform x y < 0 →
      2 * iform x y = -iform x x) ∧
    (iform x x = 4 → iform y y = 2 → iform x y < 0 → iform x y = -2) := by
  have key : ∀ x ∈ rootFinset ReeTag.F4.tag, ∀ y ∈ rootFinset ReeTag.F4.tag,
      (iform x x = iform y y → x ≠ y → x ≠ -y → iform x y < 0 →
        2 * iform x y = -iform x x) ∧
      (iform x x = 4 → iform y y = 2 → iform x y < 0 → iform x y = -2) := by
    decide +kernel
  exact key x (mem_rootFinset.2 hx) y (mem_rootFinset.2 hy)

private theorem two_iform_eq_neg_self_of_same_length
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) (hq : iform x x = iform y y) (hne : x ≠ y)
    (hne' : x ≠ -y) (hxy : iform x y < 0) : 2 * iform x y = -iform x x :=
  (root_pair_arith hx hy).1 hq hne hne' hxy

private theorem iform_eq_neg_two_of_long_short
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) (hqx : iform x x = 4) (hqy : iform y y = 2)
    (hxy : iform x y < 0) : iform x y = -2 :=
  (root_pair_arith hx hy).2 hqx hqy hxy

private theorem iform_dualRoot_eq_zero_and_neg
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) :
    (iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot y) = 0 ↔ iform x y = 0) ∧
    (iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot y) < 0 ↔ iform x y < 0) := by
  have h := quadForm_mul_iform_dualRoot x y hx hy
  have hxq : 0 < ReeTag.F4.quadForm x := by
    rw [ReeTag.quadForm_eq_iform]; exact iform_self_pos hx.ne_zero
  have hyq : 0 < ReeTag.F4.quadForm y := by
    rw [ReeTag.quadForm_eq_iform]; exact iform_self_pos hy.ne_zero
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h0
    have : 8 * iform x y = 0 := by rw [← h, h0]; ring
    omega
  · intro h0
    have h1 : ReeTag.F4.quadForm x * ReeTag.F4.quadForm y *
        iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot y) = 0 := by rw [h, h0]; ring
    exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hxq.ne' hyq.ne')
  · intro hlt; nlinarith [mul_pos hxq hyq]
  · intro hlt; nlinarith [mul_pos hxq hyq]

private theorem iform_dualRoot_self_mul
    {x : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x) :
    iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot x) * iform x x = 8 := by
  have h := (ReeTag.rootDualityCheck_spec (t := ReeTag.F4) hx).2.2.2.2.1
  rw [ReeTag.quadForm_eq_iform, ReeTag.quadForm_eq_iform] at h
  simpa [ReeTag.prime] using h

private theorem iform_θ_self_ne
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    {x : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x) :
    iform (θ x) (θ x) ≠ iform x x := by
  have hprod := iform_dualRoot_self_mul hx
  have hθx : iform (θ x) (θ x) =
      iform (ReeTag.F4.dualRoot x) (ReeTag.F4.dualRoot x) := by
    rw [hθ x, iform_smul]
  intro heq
  rw [hθx] at heq
  have hsq : iform x x * iform x x = 8 := by rw [heq] at hprod; exact hprod
  rcases iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hx with h | h
  · rw [h] at hsq; norm_num at hsq
  · rw [h] at hsq; norm_num at hsq

private theorem oddDerivNotRootB_of_not_isRoot
    {v : Fin ReeTag.F4.tag.rank → ℤ} (hv : ¬ IsRoot ReeTag.F4.tag v) :
    oddDerivNotRootB ReeTag.F4.tag v = true := by
  have h : RootOps.isRootB ReeTag.F4.tag v = false := by
    cases hb : RootOps.isRootB ReeTag.F4.tag v with
    | false => rfl
    | true => exact absurd (RootOps.isRootB_iff.1 hb) hv
  simp [oddDerivNotRootB, h]

private theorem iform_θθ_eq_zero_and_neg
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) :
    (iform (θ x) (θ y) = 0 ↔ iform x y = 0) ∧
    (iform (θ x) (θ y) < 0 ↔ iform x y < 0) := by
  rw [hθ x, hθ y, iform_smul]
  exact iform_dualRoot_eq_zero_and_neg hx hy

private theorem iform_θθ_eq_zero_iff
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) :
    iform (θ x) (θ y) = 0 ↔ iform x y = 0 :=
  (iform_θθ_eq_zero_and_neg hθ hx hy).1

private theorem iform_θθ_neg_iff
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    {x y : Fin ReeTag.F4.tag.rank → ℤ} (hx : IsRoot ReeTag.F4.tag x)
    (hy : IsRoot ReeTag.F4.tag y) :
    iform (θ x) (θ y) < 0 ↔ iform x y < 0 :=
  (iform_θθ_eq_zero_and_neg hθ hx hy).2

theorem orthogonal_or_b2Pair_or_a2Cycle_ree
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M}
    {w : WeylGroup ReeTag.F4.tag} {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    (hΔ : Set.MapsTo θ (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)))
    {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ simpleRoots (kernelRoots χ)) {n : ℕ} (hn : 0 < n)
    (hnα : θ^[n] α = α) (hmin : ∀ m, 0 < m → m < n → θ^[m] α ≠ α) :
    (∀ i < n, ∀ j < n, i ≠ j → iform (θ^[i] α) (θ^[j] α) = 0) ∨
      (n = 2 ∧ iform α (θ α) ≠ 0) ∨
      (n = 4 ∧ OddDerivPair ReeTag.F4.tag α (θ^[2] α) ∧
        ∀ γ ∈ ({α, θ^[2] α} : Set (Fin ReeTag.F4.tag.rank → ℤ)),
          ∀ δ ∈ ({θ α, θ^[3] α} : Set (Fin ReeTag.F4.tag.rank → ℤ)), iform γ δ = 0) := by
  classical
  let β : ℕ → (Fin ReeTag.F4.tag.rank → ℤ) := fun i => θ^[i] α
  have hβ0 : β 0 = α := rfl
  have hβ_succ : ∀ i, β (i + 1) = θ (β i) := by
    intro i
    change θ^[i + 1] α = θ (θ^[i] α)
    rw [Function.iterate_succ_apply']
  have hmem : ∀ i, β i ∈ simpleRoots (kernelRoots χ) := by
    intro i
    induction i with
    | zero => simpa [hβ0] using hα
    | succ i ih => rw [hβ_succ i]; exact hΔ ih
  have hroot : ∀ i, IsRoot ReeTag.F4.tag (β i) := by
    intro i
    induction i with
    | zero => simpa [hβ0] using simpleRoots_isRoot hα
    | succ i ih =>
        rw [hβ_succ i, hθ (β i)]
        exact IsRoot.smul (ReeTag.isRoot_dualRoot ih) w
  have hdistinct : ∀ i j, i < n → j < n → i < j → β i ≠ β j := by
    intro i j hi hj hij hEq
    have hjle : j ≤ n := le_of_lt hj
    have h1 : θ^[n - j] (β j) = α := by
      change θ^[n - j] (θ^[j] α) = α
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjle, hnα]
    have h2 : θ^[n - j] (β i) = α := by
      rw [hEq, h1]
    have h3 : θ^[n - j + i] α = α := by
      calc θ^[n - j + i] α = θ^[n - j] (θ^[i] α) :=
            Function.iterate_add_apply θ (n - j) i α
        _ = θ^[n - j] (β i) := rfl
        _ = α := h2
    exact hmin (n - j + i) (by omega) (by omega) h3
  have hne_β : ∀ i j, i < n → j < n → i ≠ j → β i ≠ β j := by
    intro i j hi hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hdistinct i j hi hj hlt
    · exact fun h => hdistinct j i hj hi hgt h.symm
  have hinj : Function.Injective (fun i : Fin n => β i.val) := by
    intro i j hij
    by_contra hne
    exact absurd hij (hne_β i.val j.val i.isLt j.isLt (fun hv => hne (Fin.ext hv)))
  have hLI : LinearIndependent ℚ (fun i : Fin n => fun j => (β i.val j : ℚ)) :=
    linearIndependent_simpleRoots_kernelRoots (χ := χ) hinj (fun i => hmem i.val)
  have hnle : n ≤ 4 := by
    have h := hLI.fintype_card_le_finrank (R := ℚ)
    simpa [Module.finrank_fintype_fun_eq_card, show ReeTag.F4.tag.rank = 4 from rfl] using h
  let q : ℕ → ℤ := fun i => iform (β i) (β i)
  have hq_rec : ∀ i, q (i + 1) * q i = 8 := by
    intro i
    have hprod := iform_dualRoot_self_mul (hroot i)
    have hθeq : q (i + 1) =
        iform (ReeTag.F4.dualRoot (β i)) (ReeTag.F4.dualRoot (β i)) := by
      dsimp only [q]
      rw [hβ_succ i, hθ (β i), iform_smul]
    rw [hθeq]
    exact hprod
  have hq_ne : ∀ i, q (i + 1) ≠ q i := by
    intro i
    have h := iform_θ_self_ne hθ (hroot i)
    dsimp only [q]
    rw [← hβ_succ i] at h
    exact h
  have hq_shift : ∀ i, q (i + 2) = q i := by
    intro i
    have h1 := hq_rec i
    have h2 := hq_rec (i + 1)
    have h2' : q (i + 2) * q (i + 1) = 8 := by
      simpa [Nat.add_assoc] using h2
    have h1' : q i * q (i + 1) = 8 := by rw [mul_comm]; exact h1
    have hne : q (i + 1) ≠ 0 := (iform_self_pos (hroot (i + 1)).ne_zero).ne'
    have : q (i + 2) * q (i + 1) = q i * q (i + 1) := by rw [h2', h1']
    exact mul_right_cancel₀ hne this
  have heven : ∀ k, q (2 * k) = q 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have e : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [e, hq_shift (2 * k), ih]
  have hodd : ∀ k, q (2 * k + 1) = q 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
        rw [e, hq_shift (2 * k + 1), ih]
  have hq0ne : q 0 ≠ q 1 := (hq_ne 0).symm
  have hn_even : Even n := by
    rcases Nat.even_or_odd n with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := h
      have hqn : q n = q 0 := by
        change iform (θ^[n] α) (θ^[n] α) = iform α α
        rw [hnα]
      have hq1 : q n = q 1 := by rw [hk, hodd k]
      exact hq0ne (hqn.symm.trans hq1)
  have hn24 : n = 2 ∨ n = 4 := by
    obtain ⟨k, hk⟩ := hn_even
    omega
  rcases hn24 with hn2 | hn4
  · subst hn2
    by_cases h0 : iform α (θ α) = 0
    · left
      intro i hi j hj hij
      interval_cases i <;> interval_cases j <;>
        first
          | exact (hij rfl).elim
          | simpa [Function.iterate_zero, Function.iterate_one] using h0
          | (rw [Function.iterate_one, Function.iterate_zero, iform_comm]; exact h0)
    · right
      left
      exact ⟨rfl, h0⟩
  · subst hn4
    have h4 : θ^[4] α = α := hnα
    have hθ3 : θ (β 3) = α := by
      rw [← hβ_succ 3]
      simpa [β] using h4
    have h13ne : β 1 ≠ β 3 := hne_β 1 3 (by norm_num) (by norm_num) (by norm_num)
    have h01ne : β 0 ≠ β 1 := hne_β 0 1 (by norm_num) (by norm_num) (by norm_num)
    have h02ne : β 0 ≠ β 2 := hne_β 0 2 (by norm_num) (by norm_num) (by norm_num)
    have h01np : iform (β 0) (β 1) ≤ 0 :=
      iform_nonpos_of_mem_simpleRoots_kernelRoots (hmem 0) (hmem 1) h01ne
    have h02np : iform (β 0) (β 2) ≤ 0 :=
      iform_nonpos_of_mem_simpleRoots_kernelRoots (hmem 0) (hmem 2) h02ne
    have h13np : iform (β 1) (β 3) ≤ 0 :=
      iform_nonpos_of_mem_simpleRoots_kernelRoots (hmem 1) (hmem 3) h13ne
    have hlen02 : iform (β 2) (β 2) = iform (β 0) (β 0) := hq_shift 0
    have hlen13 : iform (β 3) (β 3) = iform (β 1) (β 1) := hq_shift 1
    have h0cases : iform (β 0) (β 0) = 2 ∨ iform (β 0) (β 0) = 4 :=
      iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 (hroot 0)
    have h1cases : iform (β 1) (β 1) = 2 ∨ iform (β 1) (β 1) = 4 :=
      iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 (hroot 1)
    by_cases hab0 : iform (β 0) (β 1) = 0
    · have hbc0 : iform (β 1) (β 2) = 0 := by
        have h := (iform_θθ_eq_zero_iff hθ (hroot 0) (hroot 1)).2 hab0
        rwa [← hβ_succ 0, ← hβ_succ 1] at h
      have hcd0 : iform (β 2) (β 3) = 0 := by
        have h := (iform_θθ_eq_zero_iff hθ (hroot 1) (hroot 2)).2 hbc0
        rwa [← hβ_succ 1, ← hβ_succ 2] at h
      have hda0 : iform (β 3) (β 0) = 0 := by
        have h := (iform_θθ_eq_zero_iff hθ (hroot 2) (hroot 3)).2 hcd0
        rw [← hβ_succ 2, hθ3] at h
        exact h
      by_cases hac0 : iform (β 0) (β 2) = 0
      · left
        have hbd0 : iform (β 1) (β 3) = 0 := by
          have h := (iform_θθ_eq_zero_iff hθ (hroot 0) (hroot 2)).2 hac0
          rwa [← hβ_succ 0, ← hβ_succ 2] at h
        have h10 : iform (β 1) (β 0) = 0 := by rw [iform_comm]; exact hab0
        have h21 : iform (β 2) (β 1) = 0 := by rw [iform_comm]; exact hbc0
        have h32 : iform (β 3) (β 2) = 0 := by rw [iform_comm]; exact hcd0
        have h03 : iform (β 0) (β 3) = 0 := by rw [iform_comm]; exact hda0
        have h20 : iform (β 2) (β 0) = 0 := by rw [iform_comm]; exact hac0
        have h31 : iform (β 3) (β 1) = 0 := by rw [iform_comm]; exact hbd0
        intro i hi j hj hij
        interval_cases i <;> interval_cases j <;>
          first
            | exact (hij rfl).elim
            | exact hab0 | exact h10 | exact hbc0 | exact h21
            | exact hcd0 | exact h32 | exact hda0 | exact h03
            | exact hac0 | exact h20 | exact hbd0 | exact h31
      · right
        right
        have h02neg : iform (β 0) (β 2) < 0 := lt_of_le_of_ne h02np hac0
        have h02neg' : β 0 ≠ -β 2 := by
          intro h
          have hh := congrArg height h
          rw [height_neg] at hh
          have h0p := simpleRoots_height_pos (hmem 0)
          have h2p := simpleRoots_height_pos (hmem 2)
          omega
        have htwos : 2 * iform (β 0) (β 2) = -iform (β 0) (β 0) :=
          two_iform_eq_neg_self_of_same_length (hroot 0) (hroot 2) hlen02.symm
            h02ne h02neg' h02neg
        have hsum : IsRoot ReeTag.F4.tag (β 0 + β 2) :=
          isRoot_add_of_iform_neg (hroot 0) (hroot 2) h02neg' h02neg
        have hnot_sub : ¬ IsRoot ReeTag.F4.tag (β 0 - β 2) := by
          intro hr
          have hself := iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hr
          have hval : iform (β 0 - β 2) (β 0 - β 2) = 3 * iform (β 0) (β 0) := by
            rw [iform_sub_left, iform_sub_right, iform_sub_right]
            have h20 : iform (β 2) (β 0) = iform (β 0) (β 2) := iform_comm _ _
            nlinarith [htwos, h20]
          rcases hself with hs | hs <;> rcases h0cases with hL | hL <;> omega
        have hnot_2a : ¬ IsRoot ReeTag.F4.tag (2 • β 0 + β 2) := by
          intro hr
          have hself := iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hr
          have hval : iform (2 • β 0 + β 2) (2 • β 0 + β 2) =
              3 * iform (β 0) (β 0) := by
            rw [two_nsmul]
            simp only [iform_add_left, iform_add_right]
            have h20 : iform (β 2) (β 0) = iform (β 0) (β 2) := iform_comm _ _
            nlinarith [htwos, h20, hlen02]
          rcases hself with hs | hs <;> rcases h0cases with hL | hL <;> omega
        have hnot_a2c : ¬ IsRoot ReeTag.F4.tag (β 0 + 2 • β 2) := by
          intro hr
          have hself := iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hr
          have hval : iform (β 0 + 2 • β 2) (β 0 + 2 • β 2) =
              3 * iform (β 0) (β 0) := by
            rw [two_nsmul]
            simp only [iform_add_left, iform_add_right]
            have h20 : iform (β 2) (β 0) = iform (β 0) (β 2) := iform_comm _ _
            nlinarith [htwos, h20, hlen02]
          rcases hself with hs | hs <;> rcases h0cases with hL | hL <;> omega
        have hstring : oddDerivStringB ReeTag.F4.tag (β 0) (β 2) = true := by
          rw [oddDerivStringB]
          simp only [oddDerivNotRootB_of_not_isRoot hnot_sub,
            oddDerivNotRootB_of_not_isRoot hnot_2a,
            oddDerivNotRootB_of_not_isRoot hnot_a2c, Bool.and_self]
        have hpair : OddDerivPair ReeTag.F4.tag (β 0) (β 2) :=
          oddDerivPair_of_oddDerivStringB (hroot 0) (hroot 2) h02ne h02neg' hsum hstring
        refine ⟨rfl, ?_, ?_⟩
        · simpa [β] using hpair
        · intro γ hγ δ hδ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ hδ
          rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
          · exact hab0
          · simpa [β] using (by rw [iform_comm]; exact hda0)
          · simpa [β] using (by rw [iform_comm]; exact hbc0)
          · simpa [β] using hcd0
    · exfalso
      have hab_neg : iform (β 0) (β 1) < 0 := lt_of_le_of_ne h01np hab0
      have hbc_neg : iform (β 1) (β 2) < 0 := by
        have h := (iform_θθ_neg_iff hθ (hroot 0) (hroot 1)).2 hab_neg
        rwa [← hβ_succ 0, ← hβ_succ 1] at h
      have hcd_neg : iform (β 2) (β 3) < 0 := by
        have h := (iform_θθ_neg_iff hθ (hroot 1) (hroot 2)).2 hbc_neg
        rwa [← hβ_succ 1, ← hβ_succ 2] at h
      have hda_neg : iform (β 3) (β 0) < 0 := by
        have h := (iform_θθ_neg_iff hθ (hroot 2) (hroot 3)).2 hcd_neg
        rw [← hβ_succ 2, hθ3] at h
        exact h
      by_cases hlong : iform (β 0) (β 0) = 4
      · have hb2 : iform (β 1) (β 1) = 2 := by
          rcases h1cases with h2 | h4
          · exact h2
          · exfalso
            exact (hq_ne 0) (by dsimp only [q]; rw [h4, hlong])
        have hc4 : iform (β 2) (β 2) = 4 := by rw [hlen02, hlong]
        have hd2 : iform (β 3) (β 3) = 2 := by rw [hlen13, hb2]
        have h_ab2 : iform (β 0) (β 1) = -2 :=
          iform_eq_neg_two_of_long_short (hroot 0) (hroot 1) hlong hb2 hab_neg
        have h_ba2 : iform (β 1) (β 0) = -2 := by rw [iform_comm]; exact h_ab2
        have h_bc2 : iform (β 1) (β 2) = -2 := by
          rw [iform_comm]
          exact iform_eq_neg_two_of_long_short (hroot 2) (hroot 1) hc4 hb2
            (by rw [iform_comm]; exact hbc_neg)
        have h_cb2 : iform (β 2) (β 1) = -2 := by rw [iform_comm]; exact h_bc2
        have h_cd2 : iform (β 2) (β 3) = -2 :=
          iform_eq_neg_two_of_long_short (hroot 2) (hroot 3) hc4 hd2 hcd_neg
        have h_dc2 : iform (β 3) (β 2) = -2 := by rw [iform_comm]; exact h_cd2
        have h_da2 : iform (β 3) (β 0) = -2 := by
          rw [iform_comm]
          exact iform_eq_neg_two_of_long_short (hroot 0) (hroot 3) hlong hd2
            (by rw [iform_comm]; exact hda_neg)
        have h_ad2 : iform (β 0) (β 3) = -2 := by rw [iform_comm]; exact h_da2
        let v : Fin ReeTag.F4.tag.rank → ℤ :=
          β 0 + β 2 + (2 : ℤ) • β 1 + (2 : ℤ) • β 3
        have hv_formula : iform v v =
            -8 + 2 * iform (β 0) (β 2) + 8 * iform (β 1) (β 3) := by
          simp only [v, iform_add_left, iform_add_right, iform_smul_left, iform_smul_right,
            hlong, hc4, hb2, hd2, h_ab2, h_ba2, h_bc2, h_cb2, h_cd2, h_dc2, h_da2, h_ad2,
            iform_comm (β 2) (β 0), iform_comm (β 3) (β 1)]
          ring_nf
        have hv_nonpos : iform v v ≤ 0 := by
          rw [hv_formula]
          nlinarith [h02np, h13np]
        have hv_ne : v ≠ 0 := by
          intro hv0
          have h0p := simpleRoots_height_pos (hmem 0)
          have h1p := simpleRoots_height_pos (hmem 1)
          have h2p := simpleRoots_height_pos (hmem 2)
          have h3p := simpleRoots_height_pos (hmem 3)
          have hpos : 0 < height v := by
            simp only [v, height_add, height_zsmul]
            linarith
          rw [hv0] at hpos
          simp [height] at hpos
        exact absurd (iform_self_pos hv_ne) (not_lt.mpr hv_nonpos)
      · have hq02 : iform (β 0) (β 0) = 2 := by
          rcases h0cases with h2 | h4
          · exact h2
          · exact (hlong h4).elim
        have hb4 : iform (β 1) (β 1) = 4 := by
          rcases h1cases with h2 | h4
          · exfalso
            exact (hq_ne 0) (by dsimp only [q]; rw [h2, hq02])
          · exact h4
        have hc2 : iform (β 2) (β 2) = 2 := by rw [hlen02]; exact hq02
        have hd4 : iform (β 3) (β 3) = 4 := by rw [hlen13, hb4]
        have h_ab2 : iform (β 0) (β 1) = -2 := by
          rw [iform_comm]
          exact iform_eq_neg_two_of_long_short (hroot 1) (hroot 0) hb4 hq02
            (by rw [iform_comm]; exact hab_neg)
        have h_ba2 : iform (β 1) (β 0) = -2 := by rw [iform_comm]; exact h_ab2
        have h_bc2 : iform (β 1) (β 2) = -2 :=
          iform_eq_neg_two_of_long_short (hroot 1) (hroot 2) hb4 hc2 hbc_neg
        have h_cb2 : iform (β 2) (β 1) = -2 := by rw [iform_comm]; exact h_bc2
        have h_cd2 : iform (β 2) (β 3) = -2 := by
          rw [iform_comm]
          exact iform_eq_neg_two_of_long_short (hroot 3) (hroot 2) hd4 hc2
            (by rw [iform_comm]; exact hcd_neg)
        have h_dc2 : iform (β 3) (β 2) = -2 := by rw [iform_comm]; exact h_cd2
        have h_da2 : iform (β 3) (β 0) = -2 :=
          iform_eq_neg_two_of_long_short (hroot 3) (hroot 0) hd4 hq02 hda_neg
        have h_ad2 : iform (β 0) (β 3) = -2 := by rw [iform_comm]; exact h_da2
        let v : Fin ReeTag.F4.tag.rank → ℤ :=
          (2 : ℤ) • β 0 + (2 : ℤ) • β 2 + β 1 + β 3
        have hv_formula : iform v v =
            -8 + 8 * iform (β 0) (β 2) + 2 * iform (β 1) (β 3) := by
          simp only [v, iform_add_left, iform_add_right, iform_smul_left, iform_smul_right,
            hq02, hc2, hb4, hd4, h_ab2, h_ba2, h_bc2, h_cb2, h_cd2, h_dc2, h_da2, h_ad2,
            iform_comm (β 2) (β 0), iform_comm (β 3) (β 1)]
          ring_nf
        have hv_nonpos : iform v v ≤ 0 := by
          rw [hv_formula]
          nlinarith [h02np, h13np]
        have hv_ne : v ≠ 0 := by
          intro hv0
          have h0p := simpleRoots_height_pos (hmem 0)
          have h1p := simpleRoots_height_pos (hmem 1)
          have h2p := simpleRoots_height_pos (hmem 2)
          have h3p := simpleRoots_height_pos (hmem 3)
          have hpos : 0 < height v := by
            simp only [v, height_add, height_zsmul]
            linarith
          rw [hv0] at hpos
          simp [height] at hpos
        exact absurd (iform_self_pos hv_ne) (not_lt.mpr hv_nonpos)

end CFSG.HardMathSupport.C14Idx
