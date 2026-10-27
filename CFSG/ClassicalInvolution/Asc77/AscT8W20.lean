module

public import CFSG.ClassicalInvolution.Asc77.AscT8W19
public import CFSG.ClassicalInvolution.Asc77.AscT8W18
public import CFSG.ClassicalInvolution.Asc77.AscT8W10
public import CFSG.ClassicalInvolution.Asc77.AscT8W14

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section TagSp

variable {p f : ℕ} [Fact p.Prime]

theorem e4_gen_sp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {e : ℕ} (M : Ih8Model p f Φ .PSp 2 e)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X)
    (σ : MulAut X) (hσ2 : σ * σ = 1) (hσA : ∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A)
    (hσnt : ¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) :
    Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
      {g | σ (x' * g * x'⁻¹) = g}) = ⊤ := by
  have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSp = .PSL ∧ (2 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSp 2 p e Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSp 2 p e Fact.out trivial M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    T8V.e4_pair_of_model hp2 hq hΦ M hG2 hD4 hnpsl hSperf hnt htrans hA hB hxA hxB hcen
  have hA0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR
  have hB0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR'
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := M.four_le_natCard_galoisField hD4 hq
  have hRl := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R).mp (M.cls_sub hR)
  have hRl' := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R').mp (M.cls_sub hR')
  subst hAR hBR hy hy'
  exfalso
  have hσ2' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : MulAut X => τ z) hσ2
    simpa using this
  have hσR : ∀ r ∈ R, σ (M.ψ r) = M.ψ r := by
    intro r hr
    have h := hσA (M.ψ r) (Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hσnt' : ∃ r ∈ R', σ (M.ψ r) ≠ M.ψ r := by
    by_contra hcon
    push Not at hcon
    apply hσnt
    rintro k ⟨r, hr, rfl⟩
    rw [hB0, Subgroup.mem_bot, mul_inv_eq_one]
    exact hcon r hr
  have hc : y' * y⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField p e)) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, k, hRg, hR'g⟩ := ModelFacts.Orth15.OuterSp4.twin_std_sp h2 hRl hRl' hP.ne hP.hy
    hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hc
  set ψ₀ : StatedSp 2 (GaloisField p e) →* X := M.ψ.comp (MulAut.conj g).toMonoidHom with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : ψ₀.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p e)) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField p e)) := hP.ker hx
    have h2' := (Subgroup.center (StatedSp 2 (GaloisField p e))).normal_of_characteristic.conj_mem
      (g * x * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  have h0 : ∀ r ∈ (SymplecticPairs.longBlock (GaloisField p e) 2 k).range,
      σ (ψ₀ r) = ψ₀ r := by
    intro r hr
    apply hσR
    rw [hRg]
    exact ⟨r, hr, rfl⟩
  have hnt₀ : ∃ r ∈ (SymplecticPairs.longBlock (GaloisField p e) 2 (Fin.rev k)).range,
      σ (ψ₀ r) ≠ ψ₀ r := by
    obtain ⟨r', hr', hne⟩ := hσnt'
    rw [hR'g] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    exact ⟨r, hr, hne⟩
  exact sp4_no_sigma h2 h4 ψ₀ hψ₀s hker₀ hP.perf k σ hσ2' h0 hnt₀

end TagSp

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem e4SecGen : E4SecGen p f := by
  intro hp2 hq n hn X _ _ hlt Φ hΦ hO hgen hnt hdisc A hA B hB x x' hxA hxB hcen σ hσ2 _ hσA _
    hσnt
  rcases T8V.e4_tag hp2 hq hn hlt hΦ hO hgen hnt hdisc hA hB with ⟨e, ⟨M⟩⟩ | ⟨hq3, e, ⟨M⟩⟩ |
    ⟨hq1, e, ⟨M⟩⟩
  · exact e4_gen_sp hp2 hq hΦ M hnt (M.exists_conj_of_fund (by decide) (by decide)) hA hB hxA
      hxB hcen σ hσ2 hσA hσnt
  · exact e4_gen_sl4 hp2 hq hΦ M hnt (M.exists_conj_of_fund (by decide) (by decide)) hA hB hxA
      hxB hcen σ hσ2 hσA hσnt
  · exact e4_gen_su4 hp2 hq hΦ M hnt (M.exists_conj_of_fund (by decide) (by decide)) hA hB hxA
      hxB hcen σ hσ2 hσA hσnt

theorem c27_8E4 : C27_8E4 p f := c27_8E4_of_e4SecGen e4SecGen

end Final

end CFSG.ClassicalInvolution.Asc77.T8W
