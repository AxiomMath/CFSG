module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrrCoord

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace CoreIrr

variable {K : Type} [Field K]

private theorem exists_coeff {σ : K ≃+* K} (hθ : ∃ θ, σ θ ≠ θ) {α : K} (hα : α ≠ 0) (β : K) :
    (∃ c, c * α + σ c * β ≠ 0) ∧ (∃ c, c * β + σ c * α ≠ 0) := by
  obtain ⟨θ, hθ⟩ := hθ
  refine ⟨?_, ?_⟩
  · by_contra h
    have h' : ∀ c, c * α + σ c * β = 0 := fun c => by_contra fun h1 => h ⟨c, h1⟩
    have h1 := h' 1
    have h2 := h' θ
    rw [map_one] at h1
    have h3 : (θ - σ θ) * α = 0 := by linear_combination h2 - σ θ * h1
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hθ (sub_eq_zero.1 h4).symm
    · exact hα h4
  · by_contra h
    have h' : ∀ c, c * β + σ c * α = 0 := fun c => by_contra fun h1 => h ⟨c, h1⟩
    have h1 := h' 1
    have h2 := h' θ
    rw [map_one] at h1
    have h3 : (σ θ - θ) * α = 0 := by linear_combination h2 - θ * h1
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hθ (sub_eq_zero.1 h4)
    · exact hα h4

private theorem pair_raise {σ : K ≃+* K} (hθ : ∃ θ, σ θ ≠ θ) (i₀ i₁ : Fin TwistTag.E6.tag.rank)
    (n : Rv K) (m : ℤ) (hn : VanishLE (m - 1) n) {γ₀ γ₁ : Dr} (hγ₀ : ht γ₀ = m)
    (hne : n γ₀ ≠ 0) (hj : γ₁.1 = γ₀.1 + Pi.single i₀ 1 ∨ γ₁.1 = γ₀.1 + Pi.single i₁ 1) :
    ∃ c : K, VanishLE m (xop K i₀ c (xop K i₁ (σ c) n) - n) ∧
      xop K i₀ c (xop K i₁ (σ c) n) - n ≠ 0 := by
  have hE0 : VanishLE m (eop K i₀ n) := (hn.eop i₀).mono (by omega)
  have hE1 : VanishLE m (eop K i₁ n) := (hn.eop i₁).mono (by omega)
  have hE01 : VanishLE (m - 1 + 1 + 1) (eop K i₀ (eop K i₁ n)) := (hn.eop i₁).eop i₀
  have hsupp : ∀ c : K, VanishLE m (xop K i₀ c (xop K i₁ (σ c) n) - n) := fun c => by
    rw [xop_comp_sub]
    exact ((hE0.smul c).add (hE1.smul _)).add ((hE01.mono (by omega)).smul _)
  have hht : ht γ₁ = m + 1 := by
    rcases hj with h | h
    · rw [ht_of_add i₀ h, hγ₀]
    · rw [ht_of_add i₁ h, hγ₀]
  have hz : eop K i₀ (eop K i₁ n) γ₁ = 0 := hE01 γ₁ (by omega)
  have hcoord : ∀ c : K, (xop K i₀ c (xop K i₁ (σ c) n) - n) γ₁ =
      c * eop K i₀ n γ₁ + σ c * eop K i₁ n γ₁ := fun c => by
    rw [xop_comp_sub]
    simp [hz]
  rcases hj with h | h
  · have h0 : eop K i₀ n γ₁ = n γ₀ := eop_apply_of_eq i₀ n (by rw [h]; abel)
    obtain ⟨c, hc⟩ := (exists_coeff hθ hne (eop K i₁ n γ₁)).1
    refine ⟨c, hsupp c, fun h' => hc ?_⟩
    have h1 := congrFun h' γ₁
    rw [hcoord c, h0] at h1
    simpa using h1
  · have h0 : eop K i₁ n γ₁ = n γ₀ := eop_apply_of_eq i₁ n (by rw [h]; abel)
    obtain ⟨c, hc⟩ := (exists_coeff hθ hne (eop K i₀ n γ₁)).2
    refine ⟨c, hsupp c, fun h' => hc ?_⟩
    have h1 := congrFun h' γ₁
    rw [hcoord c, h0] at h1
    simpa using h1

private theorem single_raise (i : Fin TwistTag.E6.tag.rank) (n : Rv K) (m : ℤ)
    (hn : VanishLE (m - 1) n) {γ₀ γ₁ : Dr} (hne : n γ₀ ≠ 0)
    (hj : γ₁.1 = γ₀.1 + Pi.single i 1) :
    VanishLE m (xop K i 1 n - n) ∧ xop K i 1 n - n ≠ 0 := by
  have hsub : xop K i 1 n - n = eop K i n := by simp [xop_apply]
  rw [hsub]
  refine ⟨(hn.eop i).mono (by omega), fun h => hne ?_⟩
  have h1 := congrFun h γ₁
  rw [eop_apply_of_eq i n (γ' := γ₀) (by rw [hj]; abel)] at h1
  exact h1

private theorem xorb_zero (σ : K ≃+* K) (c : K) (v : Rv K) :
    xorb K σ 0 c v = xop K 0 c (xop K 5 (σ c) v) := rfl

private theorem xorb_one (σ : K ≃+* K) (c : K) (v : Rv K) :
    xorb K σ 1 c v = xop K 2 c (xop K 4 (σ c) v) := rfl

private theorem xorb_two (σ : K ≃+* K) (c : K) (v : Rv K) : xorb K σ 2 c v = xop K 3 c v := rfl

private theorem raise_mem {σ : K ≃+* K} (hθ : ∃ θ, σ θ ≠ θ) {N : AddSubgroup (Rv K)}
    (hX : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, xorb K σ a c v ∈ N)
    {n : Rv K} (hnN : n ∈ N) {m : ℤ} (hm : VanishLE (m - 1) n) {γ₀ : Dr} (hγ₀ : ht γ₀ = m)
    (hne : n γ₀ ≠ 0) (htop : γ₀ ≠ topD) :
    ∃ n' ∈ N, VanishLE m n' ∧ n' ≠ 0 := by
  rcases exists_up γ₀ htop with hjm | hjm | hjm | hjm | hjm
  · obtain ⟨c, hc, hc0⟩ := pair_raise hθ 0 5 n m hm hγ₀ hne
      (γ₁ := ⟨_, hjm⟩) (Or.inl rfl)
    exact ⟨_, sub_mem (hX 0 (by decide) c (fun h => absurd h (by decide)) n hnN) hnN, by
      rw [xorb_zero]; exact hc, by rw [xorb_zero]; exact hc0⟩
  · obtain ⟨c, hc, hc0⟩ := pair_raise hθ 2 4 n m hm hγ₀ hne
      (γ₁ := ⟨_, hjm⟩) (Or.inl rfl)
    exact ⟨_, sub_mem (hX 1 (by decide) c (fun h => absurd h (by decide)) n hnN) hnN, by
      rw [xorb_one]; exact hc, by rw [xorb_one]; exact hc0⟩
  · obtain ⟨hc, hc0⟩ := single_raise 3 n m hm hne (γ₁ := ⟨_, hjm⟩) rfl
    exact ⟨_, sub_mem (hX 2 (by decide) 1 (fun _ => map_one σ) n hnN) hnN, by
      rw [xorb_two]; exact hc, by rw [xorb_two]; exact hc0⟩
  · obtain ⟨c, hc, hc0⟩ := pair_raise hθ 2 4 n m hm hγ₀ hne
      (γ₁ := ⟨_, hjm⟩) (Or.inr rfl)
    exact ⟨_, sub_mem (hX 1 (by decide) c (fun h => absurd h (by decide)) n hnN) hnN, by
      rw [xorb_one]; exact hc, by rw [xorb_one]; exact hc0⟩
  · obtain ⟨c, hc, hc0⟩ := pair_raise hθ 0 5 n m hm hγ₀ hne
      (γ₁ := ⟨_, hjm⟩) (Or.inr rfl)
    exact ⟨_, sub_mem (hX 0 (by decide) c (fun h => absurd h (by decide)) n hnN) hnN, by
      rw [xorb_zero]; exact hc, by rw [xorb_zero]; exact hc0⟩

private theorem exists_top_aux {σ : K ≃+* K} (hθ : ∃ θ, σ θ ≠ θ) {N : AddSubgroup (Rv K)}
    (hX : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, xorb K σ a c v ∈ N) :
    ∀ (k : ℕ) (m : ℤ), m + k = 11 → ∀ n ∈ N, VanishLE (m - 1) n → n ≠ 0 →
      ∃ n' ∈ N, n' ≠ 0 ∧ ∀ γ, γ ≠ topD → n' γ = 0 := by
  intro k
  induction k with
  | zero =>
    intro m hm n hnN hv hne
    exact absurd (funext fun γ => hv γ (by have := ht_le γ; omega)) hne
  | succ k ih =>
    intro m hm n hnN hv hne
    by_cases hvm : VanishLE m n
    · exact ih (m + 1) (by omega) n hnN (by simpa using hvm) hne
    · obtain ⟨γ₀, hγ₀, hn0⟩ : ∃ γ : Dr, ht γ ≤ m ∧ n γ ≠ 0 := by
        by_contra h
        exact hvm fun γ hγ => by_contra fun h1 => h ⟨γ, hγ, h1⟩
      have hγ₀m : ht γ₀ = m := by
        by_contra h
        exact hn0 (hv γ₀ (by omega))
      by_cases htop : γ₀ = topD
      · refine ⟨n, hnN, hne, fun γ hγ => hv γ ?_⟩
        have h1 := ht_lt hγ
        have h10 : m = 10 := by rw [← hγ₀m, htop, ht_top]
        omega
      · obtain ⟨n', hn'N, hn'v, hn'0⟩ := raise_mem hθ hX hnN hv hγ₀m hn0 htop
        exact ih (m + 1) (by omega) n' hn'N (by simpa using hn'v) hn'0

theorem exists_top {σ : K ≃+* K} (hθ : ∃ θ, σ θ ≠ θ) {N : AddSubgroup (Rv K)}
    (hX : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, xorb K σ a c v ∈ N) (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ γ, γ ≠ topD → n γ = 0 := by
  obtain ⟨n, hnN, hne⟩ : ∃ n ∈ N, n ≠ 0 := by
    by_contra h
    exact hN ((AddSubgroup.eq_bot_iff_forall N).2 fun n hn => by_contra fun h1 => h ⟨n, hn, h1⟩)
  exact exists_top_aux hθ hX 10 1 (by norm_num) n hnN
    (fun γ hγ => absurd hγ (by have := ht_pos γ; omega)) hne

end CoreIrr

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
