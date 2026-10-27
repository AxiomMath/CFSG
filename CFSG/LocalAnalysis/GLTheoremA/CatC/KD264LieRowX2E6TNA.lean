module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.E6

section Main

@[expose] def dot6 (x : Fin 6 → ZMod 3) (γ : Fin 6 → ℤ) : ZMod 3 :=
  ∑ i, ((γ i : ℤ) : ZMod 3) * x i

theorem dot6_eq_zero_of_mem_closure {γ : Fin 6 → ℤ}
    {u v : Multiplicative (Fin 6 → ZMod 3)}
    (hu : dot6 (Multiplicative.toAdd u) γ = 0) (hv : dot6 (Multiplicative.toAdd v) γ = 0)
    {g : Multiplicative (Fin 6 → ZMod 3)} (hg : g ∈ Subgroup.closure ({u, v} : Set _)) :
    dot6 (Multiplicative.toAdd g) γ = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hu
    · rw [Set.mem_singleton_iff.1 hx]; exact hv
  | one =>
    simp [dot6]
  | mul x y _ _ hx hy =>
    have : dot6 (Multiplicative.toAdd (x * y)) γ =
        dot6 (Multiplicative.toAdd x) γ + dot6 (Multiplicative.toAdd y) γ := by
      simp only [dot6, toAdd_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [this, hx, hy, add_zero]
  | inv x _ hx =>
    have : dot6 (Multiplicative.toAdd x⁻¹) γ = -dot6 (Multiplicative.toAdd x) γ := by
      simp only [dot6, toAdd_inv, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [this, hx, neg_zero]

theorem x2e6TorusComponentP_selNA : X2E6TorusComponentP SelNA := by
  intro K _ _ hK σ hσ Ω _ _ _ _ Fr hFr g hg hgn ζ hζ hζ' G hSel _hRG
  classical
  obtain ⟨hG9, hNA⟩ := hSel
  have hN' : ∀ x ∈ G, x ≠ 1 → ¬ PhiTypeA (Multiplicative.toAdd x) :=
    fun x hx hx1 hP => hNA ⟨hG9, x, hx, hx1, hP⟩
  obtain ⟨u, huG, hu1⟩ : ∃ u ∈ G, u ≠ 1 := by
    by_contra hno
    push Not at hno
    have : G = ⊥ := (Subgroup.eq_bot_iff_forall G).2 hno
    rw [this, Subgroup.card_bot] at hG9
    omega
  obtain ⟨v, hvG, hvz, hGuv⟩ := exists_closure_pair hG9 huG hu1
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ one_mem _)
  have huv1 : u * v ≠ 1 := fun h => hvz (by
    have : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (Subgroup.mem_zpowers u))
  have huv1' : u * v⁻¹ ≠ 1 := fun h => hvz (by
    have : u = v := mul_inv_eq_one.1 h
    rw [← this]
    exact Subgroup.mem_zpowers u)
  have hu0 : Multiplicative.toAdd u ≠ 0 := fun h => hu1 (toAdd_eq_zero.1 h)
  have hv0 : Multiplicative.toAdd v ≠ 0 := fun h => hv1 (toAdd_eq_zero.1 h)
  have huv0 : Multiplicative.toAdd u + Multiplicative.toAdd v ≠ 0 := fun h =>
    huv1 (toAdd_eq_zero.1 (by rw [toAdd_mul]; exact h))
  have huv0' : Multiplicative.toAdd u - Multiplicative.toAdd v ≠ 0 := fun h =>
    huv1' (toAdd_eq_zero.1 (by rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]; exact h))
  have hNuv : ¬ PhiTypeA (Multiplicative.toAdd u + Multiplicative.toAdd v) := by
    have := hN' (u * v) (G.mul_mem huG hvG) huv1
    rwa [toAdd_mul] at this
  have hNuv' : ¬ PhiTypeA (Multiplicative.toAdd u - Multiplicative.toAdd v) := by
    have := hN' (u * v⁻¹) (G.mul_mem huG (G.inv_mem hvG)) huv1'
    rwa [toAdd_mul, toAdd_inv, ← sub_eq_add_neg] at this
  have hp3L : ((3 : ℕ) : Ω) ≠ 0 := by
    have h2 : ((2 : ℕ) : Ω) = 0 := by
      haveI := charP_two_of_card (K := K) (Ω := Ω) hK
      exact CharP.cast_eq_zero Ω 2
    have h3 : ((3 : ℕ) : Ω) = 1 := by
      push_cast at h2 ⊢
      linear_combination h2
    rw [h3]
    exact one_ne_zero
  obtain ⟨x, hxmem, hx24, hxsub⟩ := exists_d4_element hζ hζ' hp3L hu0 hv0 huv0 huv0' (hN' u huG hu1)
    (hN' v hvG hv1) hNuv hNuv'
  obtain ⟨a, haG, ha1, hax⟩ : ∃ a ∈ G, a ≠ 1 ∧ Multiplicative.toAdd a = x := by
    rcases hxmem with h | h | h | h
    · exact ⟨u, huG, hu1, h.symm⟩
    · exact ⟨v, hvG, hv1, h.symm⟩
    · exact ⟨u * v, G.mul_mem huG hvG, huv1, by rw [toAdd_mul]; exact h.symm⟩
    · exact ⟨u * v⁻¹, G.mul_mem huG (G.inv_mem hvG), huv1', by
        rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]; exact h.symm⟩
  subst hax
  obtain ⟨b, hbG, -, hGab⟩ := exists_closure_pair hG9 haG ha1
  obtain ⟨S, hSD⟩ := exists_modelSetup hK σ hσ Fr hFr hg hgn
  have hq2 : S.D.q = 2 := by rw [hSD]; rfl
  have hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ := fun γ hγ =>
    rho_eq_neg (by norm_num) Fr hFr hg hgn hSD hγ
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_isAlgClosure K 2 (by rw [hSD]; exact hK)
  have hFr' : ∀ c, Fr c = c ^ S.D.q := by rw [hSD]; exact hFr
  have hΦ : S.D.Φ = twistHom TwistTag.E6 Ω Fr := by rw [hSD]; rfl
  have haT : rootDiagUnit Tag.E6 (thetaTuple ζ (Multiplicative.toAdd a)) ∈ S.D.torus := by
    rw [hSD]; exact psi6_mem_torus Fr hFr hg hgn hζ a
  have hall : (kernelRoots (rootCharHom (thetaTuple ζ (Multiplicative.toAdd a)))).ncard = 24 :=
    (ncard_kernel_eq_phiSet hζ hζ' _).trans hx24
  have hab : kernelRoots (rootCharHom (thetaTuple ζ (Multiplicative.toAdd a))) ⊆
      kernelRoots (rootCharHom (thetaTuple ζ (Multiplicative.toAdd b))) := by
    intro γ hγ
    have hγa : γ ∈ phiSet (Multiplicative.toAdd a) :=
      (mem_kernel_iff_mem_phiSet hζ hζ' _ γ).1 hγ
    obtain ⟨hγu, hγv⟩ := hxsub γ hγa
    have hr := (mem_phiSet_iff.1 hγu).1
    have hbc : dot6 (Multiplicative.toAdd b) γ = 0 :=
      dot6_eq_zero_of_mem_closure (mem_phiSet_iff.1 hγu).2 (mem_phiSet_iff.1 hγv).2
        (hGuv ▸ hbG)
    exact (mem_kernel_iff_mem_phiSet hζ hζ' _ γ).2 (mem_phiSet_iff.2 ⟨hr, hbc⟩)
  obtain ⟨J₀, hJ₀sub, hJ₀q, hJ₀3⟩ := d4_component S hFr' hΦ hq2 hAlg hρ hp3L haT
    (thetaTuple_pow_three hζ _) hall hab
  have hΓ : S.Γ = (modelDatum Fr hFr hg hgn).Γ := by
    unfold LangSetup.Γ
    rw [hSD]
  have hJ : IsSubnormal J₀ ((modelDatum Fr hFr hg hgn).Γ ⊓
      Subgroup.centralizer ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3))))) := by
    rw [centralizer_psi6_eq_inf hζ hGab, ← inf_assoc, ← hΓ]
    exact hJ₀sub
  exact exists_component_of_lang hK σ hσ Fr hFr hg hgn hζ G J₀ hJ hJ₀q hJ₀3

theorem x2e6TorusGoodP_selNA : X2E6TorusGoodP SelNA :=
  x2e6TorusGoodP_of_componentP SelNA x2e6TorusComponentP_selNA

theorem x2e6TorusGood9_holds : X2E6TorusGood9 :=
  x2e6TorusGood9_of_split x2e6TorusGoodP_selA x2e6TorusGoodP_selNA

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
