module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreEps
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem exc3core_kind_facts {τ : Tag} {L : Type} [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    (twistKind ρ χ i = .exc →
      (compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
        (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24)) ∧
    (twistKind ρ χ i = .twoD → 4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1)) ∧
    (twistKind ρ χ i = .suN → 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1)) := by
  unfold twistKind
  split_ifs with h1 h2 h3 h4
  · simp
  · refine ⟨fun _ => ?_, by simp, by simp⟩
    rcases h2 with h | ⟨h, h', -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, h'⟩
  · exact ⟨by simp, fun _ => h3, by simp⟩
  · exact ⟨by simp, by simp, fun _ => h4⟩
  · simp

theorem exc3core_kind_inner_of_size {τ : Tag} {L : Type} [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (h : (componentRoots χ i).ncard = 2 ∨ (componentRoots χ i).ncard = 18 ∨
      (componentRoots χ i).ncard = 126) :
    twistKind ρ χ i = .inner := by
  obtain ⟨he, ht, hs⟩ := exc3core_kind_facts ρ χ i
  generalize compRank (componentRoots χ i) = r at he ht hs
  generalize (componentRoots χ i).ncard = N at he ht hs h
  cases hk : twistKind ρ χ i
  · rfl
  · exfalso
    obtain ⟨h2, h3⟩ := hs hk
    have hr : r ≤ 11 := by
      by_contra hr
      push Not at hr
      rcases h with h | h | h <;> nlinarith
    interval_cases r <;> omega
  · exfalso
    obtain ⟨h2, h3⟩ := ht hk
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h3
    have hr : s ≤ 10 := by
      by_contra hr
      push Not at hr
      rcases h with h | h | h <;> nlinarith
    interval_cases s <;> omega
  · exfalso
    rcases he hk with ⟨-, h3⟩ | ⟨-, h3⟩ <;> omega

theorem exc3core_not_inner_of_wobs {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (SL : LangSetup τ L 5) {a : Fin τ.rank → Lˣ} {e : ℕ} (hq : SL.D.q = 2 ^ e)
    (h3 : 3 ∣ 2 ^ e + 1) (hT : rootDiagUnit τ a ∈ SL.D.torus) (hap : ∀ m, a m ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hobs : exc3core_WObs τ (rootCharHom a) (componentRoots (rootCharHom a) i))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i').ncard = (componentRoots (rootCharHom a) i).ncard → i' = i) :
    ¬ twistInner (componentRoots (rootCharHom a) i)
      ((SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength SL.ρ
        (componentRoots (rootCharHom a) i)]) := by
  intro hin
  rw [(exc3core_orbit_one SL hq h3 hT hap i huniq).2, Function.iterate_one] at hin
  obtain ⟨γ, hγ, -, hall⟩ := hobs
  obtain ⟨γ', hγ', hχ, hpair⟩ := exc3core_weight_match
    (SL.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (rootCharHom a)
    (fun γ hγ => (SL.frob.isRoot_iff γ).2 hγ) (fun γ δ => SL.frob.iform_eq γ δ)
    (fun γ hγ => exc3core_rho_inv SL hq h3 hT hap hγ) (fun x hx => hx.1) hin hγ
  obtain ⟨β, hβ, hβne⟩ := hall γ' hγ' hχ
  exact hβne (hpair β hβ)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
