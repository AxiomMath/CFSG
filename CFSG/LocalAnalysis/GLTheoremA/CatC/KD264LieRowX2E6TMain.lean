module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TSetup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Lang.E6Descent

section Main

theorem x2e6TorusComponentP_selA : X2E6TorusComponentP SelA := by
  intro K _ _ hK σ hσ Ω _ _ _ _ Fr hFr g hg hgn ζ hζ hζ' G hSel hRG
  classical
  obtain ⟨hG9, u, huG, hu1, hA⟩ := hSel
  obtain ⟨v, hvG, -, hGuv⟩ := exists_closure_pair hG9 huG hu1
  obtain ⟨C, hCroots, hCconn, hCrank, hCorth⟩ := hRG
  have hCu : ∀ α ∈ C, ∑ i, ((α i : ℤ) : ZMod 3) * Multiplicative.toAdd u i = 0 :=
    fun α hα => hCorth α hα _ ⟨u, huG, rfl⟩
  have hCv : ∀ α ∈ C, ∑ i, ((α i : ℤ) : ZMod 3) * Multiplicative.toAdd v i = 0 :=
    fun α hα => hCorth α hα _ ⟨v, hvG, rfl⟩
  obtain ⟨S, hSD⟩ := exists_modelSetup hK σ hσ Fr hFr hg hgn
  have hq2 : S.D.q = 2 := by rw [hSD]; rfl
  have hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ := fun γ hγ =>
    rho_eq_neg (by norm_num) Fr hFr hg hgn hSD hγ
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_isAlgClosure K 2 (by rw [hSD]; exact hK)
  set a : E6Idx → Ωˣ := thetaTuple ζ (Multiplicative.toAdd u) with ha
  set b : E6Idx → Ωˣ := thetaTuple ζ (Multiplicative.toAdd v) with hb
  have haT : rootDiagUnit Tag.E6 a ∈ S.D.torus := by
    rw [hSD]; exact psi6_mem_torus Fr hFr hg hgn hζ u
  have hker : ∀ γ, γ ∈ kernelRoots (rootCharHom a) ↔ γ ∈ PhiU (Multiplicative.toAdd u) :=
    mem_kernelRoots_iff_phiU hζ hζ' (Multiplicative.toAdd u)
  have hCne : C.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have h0 : rootRankQ (∅ : Set (Fin 6 → ℤ)) = 0 := by
      unfold rootRankQ
      simp
    omega
  obtain ⟨α₀, hα₀⟩ := hCne
  have hCk : ∀ x ∈ C, x ∈ kernelRoots (rootCharHom a) := fun x hx =>
    (hker x).2 ⟨hCroots hx, hCu x hx⟩
  set i : KernelComponent (rootCharHom a) := (⟦⟨α₀, hCk α₀ hα₀⟩⟧ : KernelComponent (rootCharHom a))
    with hi
  have hCΨ : C ⊆ componentRoots (rootCharHom a) i := by
    intro x hx
    refine (mem_componentRoots_iff (rootCharHom a) ⟨α₀, hCk α₀ hα₀⟩ x).2 ⟨hCk x hx, ?_⟩
    have hr := hCconn α₀ hα₀ x hx
    refine (Relation.ReflTransGen.mono (r := fun p q => p ∈ C ∧ q ∈ C ∧ cartanForm p q ≠ 0)
      (p := KerAdj (rootCharHom a)) (fun p q hpq => ⟨hCk p hpq.1, hCk q hpq.2.1, ?_⟩)) _ _ hr
    exact fun h => hpq.2.2 ((iform_eq_cartanForm _ _).symm.trans h)
  have hPhi : IsPhiComponent (Multiplicative.toAdd u) (componentRoots (rootCharHom a) i) :=
    isPhiComponent_componentRoots (rootCharHom a) (Multiplicative.toAdd u) hker i
  have hrk : 3 ≤ compRank (componentRoots (rootCharHom a) i) := by
    have hle : Module.finrank ℚ (Submodule.span ℚ
        ((fun γ (j : E6Idx) => ((γ j : ℤ) : ℚ)) '' C)) ≤
        Module.finrank ℚ (Submodule.span ℚ
          ((fun γ (j : E6Idx) => ((γ j : ℤ) : ℚ)) '' componentRoots (rootCharHom a) i)) :=
      Submodule.finrank_mono (Submodule.span_mono (Set.image_mono hCΨ))
    exact hCrank.trans hle
  have hn := hA _ hPhi hrk
  have hp3L : ((3 : ℕ) : Ω) ≠ 0 := by
    have h2 : ((2 : ℕ) : Ω) = 0 := by
      haveI := charP_two_of_card (K := K) (Ω := Ω) hK
      exact CharP.cast_eq_zero Ω 2
    have h3 : ((3 : ℕ) : Ω) = 1 := by
      push_cast at h2 ⊢
      linear_combination h2
    rw [h3]
    exact one_ne_zero
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := Psi6_pow_three hζ u
  obtain ⟨ν, ψ, σf, hν3, hψ, hnorm, hΨ⟩ := exists_frame_of_typeA_E6_T_of_prime S (p := 3)
    Nat.prime_three hp3L hTp i (by omega) hn
  have hr6 : compRank (componentRoots (rootCharHom a) i) ≤ 6 := by
    have h1 : Module.finrank ℚ (Submodule.span ℚ
        ((fun γ (j : E6Idx) => ((γ j : ℤ) : ℚ)) '' componentRoots (rootCharHom a) i)) ≤
        Module.finrank ℚ (E6Idx → ℚ) := Submodule.finrank_le _
    have h2 : Module.finrank ℚ (E6Idx → ℚ) = 6 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      rfl
    exact h1.trans h2.le
  have hcard0 := ncard_frameRoots hψ (κ := 1) one_ne_zero hnorm
  have hcard : compRank (componentRoots (rootCharHom a) i) *
      (compRank (componentRoots (rootCharHom a) i) + 1) = ν * (ν - 1) :=
    hn.symm.trans (hΨ ▸ hcard0)
  have hν : ν = compRank (componentRoots (rootCharHom a) i) + 1 := by
    set r := compRank (componentRoots (rootCharHom a) i) with hr
    obtain ⟨m, rfl⟩ : ∃ m, ν = m + 1 := ⟨ν - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hcard
    rcases lt_trichotomy m r with h | h | h
    · exfalso; nlinarith
    · omega
    · exfalso; nlinarith
  have hCσ : ∀ γ ∈ C, ∃ i j, i ≠ j ∧ γ = σf i j := fun γ hγ => by
    have : γ ∈ frameRoots σf := hΨ ▸ hCΨ hγ
    exact this
  have hCb : ∀ γ ∈ C, rootChar b γ = 1 := fun γ hγ =>
    (rootChar_theta_eq_one_iff hζ hζ' (Multiplicative.toAdd v) γ).2 (hCv γ hγ)
  have hconn : ∀ x ∈ C, ∀ y ∈ C,
      Relation.ReflTransGen (fun p q => p ∈ C ∧ q ∈ C ∧ iform (τ := Tag.E6) p q ≠ 0) x y := by
    intro x hx y hy
    refine (Relation.ReflTransGen.mono (r := fun p q => p ∈ C ∧ q ∈ C ∧ cartanForm p q ≠ 0)
      (p := fun p q => p ∈ C ∧ q ∈ C ∧ iform (τ := Tag.E6) p q ≠ 0)
      (fun p q hpq => ⟨hpq.1, hpq.2.1, ?_⟩)) _ _ (hCconn x hx y hy)
    exact fun h => hpq.2.2 ((iform_eq_cartanForm _ _).symm.trans h)
  obtain ⟨k₀, hk₀⟩ := exists_class_of_connected hψ hnorm b hCσ hCb hconn hα₀
  set X : Finset (Fin ν) := Finset.univ.filter (fun k => rootChar b (σf k k₀) = 1) with hXdef
  have hX : ∀ k, k ∈ X ↔ rootChar b (σf k k₀) = 1 := fun k => by simp [hXdef]
  have hk₀X : k₀ ∈ X := by
    rw [hX, sigma_self hψ, rootChar_zero]
  have hCX : ∀ γ ∈ C, ∃ i j, i ∈ X ∧ j ∈ X ∧ γ = σf i j := by
    intro γ hγ
    obtain ⟨i', j', -, hγij, hi', hj'⟩ := hk₀ γ hγ
    exact ⟨i', j', (hX i').2 hi', (hX j').2 hj', hγij⟩
  have h4 : 4 ≤ X.card := by
    have h1 := finrank_span_class_le hψ X hk₀X hCX
    have h2 : 3 ≤ Module.finrank ℚ (Submodule.span ℚ
        ((fun γ : Fin Tag.E6.rank → ℤ => fun j => ((γ j : ℤ) : ℚ)) '' C)) := hCrank
    omega
  have h2X : ν < 2 * X.card := by omega
  have hω3 : ((ζ : Ωˣ) : Ω) ^ 3 = 1 := by
    have := congrArg Units.val hζ
    simpa using this
  have hω1 : ((ζ : Ωˣ) : Ω) ≠ 1 := by
    intro h
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ'
    omega
  obtain ⟨J₀, hJ₀sub, hJ₀q, hJ₀3⟩ := block_component S hq2 hAlg hρ haT i hν3 hψ hΨ hω3 hω1 k₀ X
    hX h4 h2X
  have hΓ : S.Γ = (modelDatum Fr hFr hg hgn).Γ := by
    unfold LangSetup.Γ
    rw [hSD]
  have hJ : IsSubnormal J₀ ((modelDatum Fr hFr hg hgn).Γ ⊓
      Subgroup.centralizer ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3))))) := by
    rw [centralizer_psi6_eq_inf hζ hGuv, ← inf_assoc, ← hΓ]
    exact hJ₀sub
  exact exists_component_of_lang hK σ hσ Fr hFr hg hgn hζ G J₀ hJ hJ₀q hJ₀3

theorem x2e6TorusGoodP_selA : X2E6TorusGoodP SelA :=
  x2e6TorusGoodP_of_componentP SelA x2e6TorusComponentP_selA

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
