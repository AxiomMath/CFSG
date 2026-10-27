module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharLev

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open

theorem rankThreeCent_of_witness_img {p : ℕ} [hp : Fact p.Prime] {G S : Type} [Group G] [Finite G]
    [Group S] [Finite S] (π : G →* S) {U A B : Subgroup G} (hU : IsPGroup p U)
    (hidx : ¬ p ∣ (U.map π).index) (hAU : A ≤ U) (hBA : B ≤ A) (hA : IsElemAbelian p A)
    (hcomm : ∀ u ∈ U, ∀ a ∈ A, u * a * u⁻¹ * a⁻¹ ∈ B)
    (hcard : Nat.card B * p ^ 2 ≤ Nat.card A)
    (hbig : p ^ 3 ≤ Nat.card A ∨
      ((∀ u ∈ U, ∀ a ∈ A, u * a = a * u) ∧ 3 ≤ pRank p (⊤ : Subgroup S)))
    (hinj : ∀ u ∈ U, π u = 1 → u = 1) : RankThreeCent p S := by
  intro y hy
  set P : Sylow p S := (hU.map π).toSylow hidx with hP
  have hPc : (P : Subgroup S) = U.map π := by
    rw [hP, IsPGroup.toSylow_coe]
  have hcA : Nat.card (A.map π) = Nat.card A :=
    card_map_eq_of_injOn_subgroup π (fun u hu => hinj u (hAU hu))
  have hcB : Nat.card (B.map π) = Nat.card B :=
    card_map_eq_of_injOn_subgroup π (fun u hu => hinj u (hAU (hBA hu)))
  refine KD291Lvl.three_le_pRank_of_witness P (A := A.map π) (B := B.map π) ?_
    (CFSG.SectionRank.isElemAbelian_map hA π) (Subgroup.map_mono hBA) ?_ ?_ ?_ hy
  · rw [hPc]
    exact Subgroup.map_mono hAU
  · rw [hPc]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨u * a * u⁻¹ * a⁻¹, hcomm u hu a ha, by simp⟩
  · rw [hcA, hcB]
    exact hcard
  · rcases hbig with h | ⟨hc, h3⟩
    · exact Or.inl (by rwa [hcA])
    · refine Or.inr ⟨?_, h3⟩
      rw [hPc]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul, hc u hu a ha]

section Corner

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {G : Type} [Group G]
  [Finite G] {ρ : G →* Matrix ι ι K} {pos : ι → ℕ}

theorem rankThreeCent_of_corner_img {p : ℕ} [hp : Fact p.Prime] [CharP K p] [Nonempty ι]
    {S : Type} [Group S] [Finite S] (hρ : Function.Injective ρ) {k : ℕ} (hk : 1 ≤ k)
    (hD : ∀ a b : ι, pos b < pos a + 2 * k) (π : G →* S)
    (hπinj : ∀ u ∈ Lev ρ pos 1 le_rfl, π u = 1 → u = 1)
    (hidx : ¬ p ∣ ((Lev ρ pos 1 le_rfl).map π).index) {g₁ g₂ b₀ : G}
    (h₁ : g₁ ∈ Lev ρ pos k hk) (h₂ : g₂ ∈ Lev ρ pos k hk)
    (hb₀ : b₀ ∈ Lev ρ pos (k + 1) (by omega)) (hb₀1 : b₀ ≠ 1)
    {a₁ b₁ a₂ b₂ : ι} (hb₁ : pos b₁ = pos a₁ + k) (hb₂ : pos b₂ = pos a₂ + k)
    (e11 : (ρ g₁ - 1) a₁ b₁ = 1) (e12 : (ρ g₁ - 1) a₂ b₂ = 0) (e21 : (ρ g₂ - 1) a₁ b₁ = 0)
    (e22 : (ρ g₂ - 1) a₂ b₂ = 1) : RankThreeCent p S := by
  have hk1 : 1 ≤ k + 1 := by omega
  have hU : IsPGroup p (Lev ρ pos 1 le_rfl) := isPGroup_Lev hρ (D := 2 * k) hD
  have hA : IsElemAbelian p (Lev ρ pos k hk) :=
    ⟨⟨⟨fun x y => Subtype.ext (Lev_comm hρ hD x.2 y.2)⟩⟩, fun g hg => Lev_pow_eq_one hρ hD hg⟩
  have hBA : Lev ρ pos (k + 1) hk1 ≤ Lev ρ pos k hk := Lev_mono (Nat.le_succ k)
  have hcard : Nat.card (Lev ρ pos (k + 1) hk1) * p ^ 2 ≤ Nat.card (Lev ρ pos k hk) :=
    card_mul_le_of_independent hA hBA h₁ h₂ fun i j hmem =>
      independent_of_entries hD h₁ h₂ hb₁ hb₂ e11 e12 e21 e22 i j hmem
  have hb₀p : orderOf b₀ = p :=
    orderOf_eq_prime (Lev_pow_eq_one hρ hD (hBA hb₀)) hb₀1
  have hBp : p ≤ Nat.card (Lev ρ pos (k + 1) hk1) := by
    have := Subgroup.card_le_of_le (zpowers_le.mpr hb₀)
    rwa [Nat.card_zpowers, hb₀p] at this
  refine rankThreeCent_of_witness_img π hU hidx (Lev_mono hk) hBA hA
    (fun u hu a ha => commutator_mem_Lev hu ha) hcard (Or.inl ?_) hπinj
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ Nat.card (Lev ρ pos (k + 1) hk1) * p ^ 2 := Nat.mul_le_mul_right _ hBp
    _ ≤ _ := hcard

end Corner

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
