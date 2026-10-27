module

public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
set_option linter.unusedSectionVars false

section Pairs

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem mem_perp_of_orth {P P' : HypPair Q} (h : P.Orth P') : P'.e ∈ P.perp ∧ P'.f ∈ P.perp :=
  ⟨HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩, HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩⟩

theorem orth_of_mem_perp {P P' : HypPair Q} (he : P'.e ∈ P.perp) (hf : P'.f ∈ P.perp) :
    P.Orth P' :=
  ⟨(HypPair.mem_perp.mp he).1, (HypPair.mem_perp.mp hf).1, (HypPair.mem_perp.mp he).2,
    (HypPair.mem_perp.mp hf).2⟩

theorem fam_perp (hQ : (polarBilin Q).Nondegenerate) (p : ℕ → HypPair Q) (n : ℕ)
    (ho : ∀ a b, a < n → b < n → a ≠ b → (p a).Orth (p b)) :
    ∃ C : Submodule K V, (∀ x, x ∈ C ↔ ∀ a < n, x ∈ (p a).perp) ∧ PolarNondegOn Q C ∧
      Module.finrank K C + 2 * n = Module.finrank K V := by
  induction n with
  | zero => exact ⟨⊤, by simp, polarNondegOn_top hQ, by simp⟩
  | succ n ih =>
    obtain ⟨C, hC, hnd, hdim⟩ := ih fun a b ha hb hab => ho a b (by omega) (by omega) hab
    have hmem : ∀ a < n, (p n).e ∈ (p a).perp ∧ (p n).f ∈ (p a).perp := fun a ha =>
      mem_perp_of_orth (ho a n (by omega) (by omega) (by omega))
    have he : (p n).e ∈ C := (hC _).mpr fun a ha => (hmem a ha).1
    have hf : (p n).f ∈ C := (hC _).mpr fun a ha => (hmem a ha).2
    refine ⟨C ⊓ (p n).perp, fun x => ?_, hnd.inf_perp (p n) he hf, ?_⟩
    · rw [Submodule.mem_inf, hC]
      constructor
      · rintro ⟨h1, h2⟩ a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with h | h
        · exact h1 a h
        · exact h ▸ h2
      · intro h
        exact ⟨fun a ha => h a (by omega), h n (by omega)⟩
    · have := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ (p n) he hf
      omega

theorem exists_pair_perp_fam (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (p : ℕ → HypPair Q) (n : ℕ) (ho : ∀ a b, a < n → b < n → a ≠ b → (p a).Orth (p b))
    (hd : 2 * n + 3 ≤ Module.finrank K V) : ∃ q : HypPair Q, ∀ a < n, (p a).Orth q := by
  obtain ⟨C, hC, hnd, hdim⟩ := fam_perp hQ p n ho
  obtain ⟨q, hqe, hqf⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hnd (by omega)
  exact ⟨q, fun a ha => orth_of_mem_perp ((hC _).mp hqe a ha) ((hC _).mp hqf a ha)⟩

theorem exists_two_pairs_perp (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (p : ℕ → HypPair Q) (n : ℕ) (ho : ∀ a b, a < n → b < n → a ≠ b → (p a).Orth (p b))
    (hd : 2 * n + 3 ≤ Module.finrank K V) :
    ∃ (q₁ q₂ : HypPair Q) (c : V), (∀ a < n, (p a).Orth q₁ ∧ (p a).Orth q₂) ∧
      q₂.e = q₁.e ∧ q₂.f = q₁.f + c - Q c • q₁.e ∧ Q c ≠ 0 ∧ polar Q q₁.e c = 0 ∧
      polar Q q₁.f c = 0 := by
  obtain ⟨q₁, hq₁⟩ := exists_pair_perp_fam hodd hQ p n ho (by omega)
  let p' : ℕ → HypPair Q := fun a => if a < n then p a else q₁
  have ho' : ∀ a b, a < n + 1 → b < n + 1 → a ≠ b → (p' a).Orth (p' b) := by
    intro a b ha hb hab
    by_cases h1 : a < n <;> by_cases h2 : b < n
    · simp only [p', h1, h2, ite_true]
      exact ho a b h1 h2 hab
    · have : b = n := by omega
      simp only [p', h1, h2, ite_true, ite_false]
      exact hq₁ a h1
    · have : a = n := by omega
      simp only [p', h1, h2, ite_true, ite_false]
      exact (hq₁ b h2).symm
    · omega
  obtain ⟨C, hC, hnd, hdim⟩ := fam_perp hQ p' (n + 1) ho'
  have hpos : 0 < Module.finrank K C := by omega
  have hCbot : C ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨c₀, hc₀C, hc₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCbot
  obtain ⟨y, hyC, hy⟩ := hnd.exists_polar_ne_zero hc₀C hc₀
  have hex : ∃ c ∈ C, Q c ≠ 0 := by
    by_cases h1 : Q c₀ = 0
    · by_cases h2 : Q y = 0
      · refine ⟨c₀ + y, C.add_mem hc₀C hyC, ?_⟩
        rw [QuadraticMap.map_add Q, h1, h2, zero_add, zero_add]
        exact hy
      · exact ⟨y, hyC, h2⟩
    · exact ⟨c₀, hc₀C, h1⟩
  obtain ⟨c, hcC, hQc⟩ := hex
  have hcperp : ∀ a < n + 1, c ∈ (p' a).perp := fun a ha => (hC c).mp hcC a ha
  have hc1 : c ∈ q₁.perp := by
    have := hcperp n (by omega)
    simpa [p'] using this
  have hcp : ∀ a < n, c ∈ (p a).perp := fun a ha => by
    have := hcperp a (by omega)
    simpa [p', ha] using this
  have hce : polar Q q₁.e c = 0 := (HypPair.mem_perp.mp hc1).1
  have hcf : polar Q q₁.f c = 0 := (HypPair.mem_perp.mp hc1).2
  have hQe : Q q₁.e = 0 := q₁.Q_e
  have h1 : polar Q q₁.e (q₁.f + c) = 1 := by
    rw [polar_add_right, q₁.polar_ef, hce, add_zero]
  let q₂ : HypPair Q := HypPair.ofPolarEqOne hQe h1
  have hq₂f : q₂.f = q₁.f + c - Q c • q₁.e := by
    show q₁.f + c - Q (q₁.f + c) • q₁.e = _
    rw [QuadraticMap.map_add Q, q₁.Q_f, zero_add]
    simp [hcf]
  refine ⟨q₁, q₂, c, fun a ha => ⟨hq₁ a ha, ?_⟩, rfl, hq₂f, hQc, hce, hcf⟩
  refine orth_of_mem_perp ?_ ?_
  · have h := (hq₁ a ha)
    exact (mem_perp_of_orth h).1
  · rw [hq₂f]
    refine HypPair.mem_perp.mpr ⟨?_, ?_⟩
    · have h := mem_perp_of_orth (hq₁ a ha)
      have h' := HypPair.mem_perp.mp h.2
      have h'' := HypPair.mem_perp.mp h.1
      have h3 := HypPair.mem_perp.mp (hcp a ha)
      rw [polar_sub_right, polar_add_right, polar_smul_right_eq, h'.1, h3.1, h''.1]
      ring
    · have h := mem_perp_of_orth (hq₁ a ha)
      have h' := HypPair.mem_perp.mp h.2
      have h'' := HypPair.mem_perp.mp h.1
      have h3 := HypPair.mem_perp.mp (hcp a ha)
      rw [polar_sub_right, polar_add_right, polar_smul_right_eq, h'.2, h3.2, h''.2]
      ring

end Pairs

end CFSG.ClassicalInvolution.RouteD.TWE.B6
