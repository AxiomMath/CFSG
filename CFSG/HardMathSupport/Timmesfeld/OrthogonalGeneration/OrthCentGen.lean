module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthGlue
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.CountingFpf
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.AutOrthInner
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.PiGenOrthReduction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.Open (IsElemAbelian)

theorem inner_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {p : ℕ}
    (h : ∀ σ : MulAut G, σ ^ p = 1 → ∃ y : G, σ = MulAut.conj y) :
    ∀ τ : MulAut H, τ ^ p = 1 → ∃ y : H, τ = MulAut.conj y := by
  intro τ hτ
  have hσ : (MulAut.congr e).symm τ ^ p = 1 := by
    rw [← map_pow, hτ, map_one]
  obtain ⟨y, hy⟩ := h _ hσ
  refine ⟨e y, ?_⟩
  ext x
  have := congrArg (fun f : MulAut G => (e.symm x |> f |> e)) hy
  simpa [MulAut.congr_symm_apply, MulAut.conj_apply] using this


section Cases

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

@[expose] noncomputable def statedOmegaPlusEquiv {m : ℕ} (hm : 3 ≤ m) :
    ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) ≃*
      ↥(elementaryGroup (quadPlus m (ZMod 2))) :=
  (Subgroup.equivMapOfInjective _ (toLinEquiv (Fin m ⊕ Fin m) (ZMod 2)).toMonoidHom
    (toLinEquiv (Fin m ⊕ Fin m) (ZMod 2)).injective).trans
    (MulEquiv.subgroupCongr (statedOmega_quadPlus_eq_map_elementaryGroup hm))

@[expose] noncomputable def statedOmegaMinusEquiv {m : ℕ} (hm : 2 ≤ m) :
    ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) ≃*
      ↥(elementaryGroup (quadMinus m (ZMod 2) 1 1)) :=
  (Subgroup.equivMapOfInjective _
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)).toMonoidHom
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)).injective).trans
    (MulEquiv.subgroupCongr (statedOmega_quadMinus_eq_map_elementaryGroup hm))

theorem le_centGenI_of_plus (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) {K : Subgroup X}
    (hK : commutator ↥K = ⊤) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    {A : Subgroup X} (hAel : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set X))
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))))
    (hfpf : HasFixedPointFreeOrder true n p)
    (hAut : ∀ σ : MulAut ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))), σ ^ p = 1 →
      ∃ y, σ = MulAut.conj y) :
    K ≤ GL83.CompFam.centGenI p A K := by
  have hm : 3 ≤ n + 1 := by omega
  have hstd : IsPlusSpace (quadPlus (n + 1) (ZMod 2)) (n + 1) := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  refine le_centGenI_of_orthGeometry hp hp2 hK hZ hAel hAK
    (Q := quadPlus (n + 1) (ZMod 2)) (nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2))
    (φ.trans (statedOmegaPlusEquiv hm)) (inner_of_mulEquiv (statedOmegaPlusEquiv hm) hAut) ?_ ?_
  · intro z hz
    have := eq_one_of_commute_elementaryGroup_of_isPlusSpace hm hstd
      (elementaryGroup_le_orthogonalGroup _ z.2)
      (fun x hx => congrArg Subtype.val (hz ⟨x, hx⟩))
    exact Subtype.ext this
  · intro E hE hexp
    exact exists_fixed_hypPair_of_hasFpf (nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)) hp hp2
      (by omega) hfpf hstd hE hexp

theorem le_centGenI_of_minus (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) {K : Subgroup X}
    (hK : commutator ↥K = ⊤) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    {A : Subgroup X} (hAel : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set X))
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))
    (hfpf : HasFixedPointFreeOrder false n p)
    (hAut : ∀ σ : MulAut ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)), σ ^ p = 1 →
      ∃ y, σ = MulAut.conj y) :
    K ≤ GL83.CompFam.centGenI p A K := by
  have hm : 2 ≤ n + 1 := by omega
  have hm3 : 3 ≤ n + 1 := by omega
  have hstd : IsMinusSpace (quadMinus (n + 1) (ZMod 2) 1 1) (n + 1) :=
    ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  have hnd : (polarBilin (quadMinus (n + 1) (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  refine le_centGenI_of_orthGeometry hp hp2 hK hZ hAel hAK
    (Q := quadMinus (n + 1) (ZMod 2) 1 1) hnd
    (φ.trans (statedOmegaMinusEquiv hm)) (inner_of_mulEquiv (statedOmegaMinusEquiv hm) hAut) ?_ ?_
  · intro z hz
    have := eq_one_of_commute_elementaryGroup_of_isMinusSpace hm3 hstd
      (elementaryGroup_le_orthogonalGroup _ z.2)
      (fun x hx => congrArg Subtype.val (hz ⟨x, hx⟩))
    exact Subtype.ext this
  · intro E hE hexp
    exact exists_fixed_hypPair_of_hasFpf hnd hp hp2 (by omega) hfpf hstd hE hexp

end Cases

@[expose] def AutU42Five : Prop :=
  ∀ σ : MulAut ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)), σ ^ 5 = 1 →
    ∃ y, σ = MulAut.conj y

theorem orthCentGen_of_residuals (hU : AutU42Five)
    (h8 : Nonempty (↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) ≃* ↥(alternatingGroup (Fin 8)))) :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.OrthCentGen := by
  intro X _ _ p hp hp2 K hK hPi hO hnA A hA hAK
  have hKperf : commutator ↥K = ⊤ := hK.2.2.1
  have hZ : Odd (Nat.card (Subgroup.center ↥K)) :=
    odd_card_center_of_primeCore_eq_bot hp2 hp hPi.2.1
  obtain ⟨n, ε, hn1, hΩ, hfpf⟩ := hO
  have hdvd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn1 hfpf
  have hAel : IsElemAbelian p A := hA
  rcases ε with _ | _
  ·
    obtain ⟨φ⟩ : Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (n + 1) (ZMod 2) 1 1))) := hΩ
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      ·
        simp only [typeSign, Bool.false_eq_true, ite_false] at hdvd
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hdvd)
        subst hp3
        exact absurd (Or.inl ⟨1, ⟨φ.trans statedOmega_quadMinus_two_mulEquiv_alt5⟩⟩) hnA
      ·
        simp only [typeSign, Bool.false_eq_true, ite_false] at hdvd
        have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hdvd)
        subst hp5
        exact le_centGenI_of_minus hp hp2 (n := 2) le_rfl hKperf hZ hAel hAK φ hfpf
          (fun σ hσ => hU σ hσ)
    · exact le_centGenI_of_minus hp hp2 (n := n) (by omega) hKperf hZ hAel hAK φ hfpf
        (statedOmega_quadMinus_aut_odd_inner (n + 1) p (by omega) hp hp2)
  ·
    obtain ⟨φ⟩ : Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2)))) := hΩ
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · simp only [typeSign, ite_true] at hdvd
        have : p ∣ 1 := by simpa using hdvd
        exact absurd (Nat.dvd_one.1 this) hp.ne_one
      · simp only [typeSign, ite_true] at hdvd
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hdvd)
        subst hp3
        exact absurd (Or.inl ⟨2, ⟨φ.trans h8.some⟩⟩) hnA
    · refine le_centGenI_of_plus hp hp2 (n := n) (by omega) hKperf hZ hAel hAK φ hfpf
        (statedOmega_quadPlus_aut_odd_inner (n + 1) p (by omega) hp hp2 ?_)
      rintro ⟨rfl, hn4⟩
      have hn3 : n = 3 := by omega
      subst hn3
      simp only [typeSign, ite_true] at hdvd
      omega

theorem orthCentGen_of_autU42Five (hU : AutU42Five) :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.OrthCentGen :=
  orthCentGen_of_residuals hU ⟨statedOmega_quadPlus_three_mulEquiv_alt8⟩

theorem inputPiGenOrth_of_autU42Five (hU : AutU42Five) : InputPiGenOrth :=
  CFSG.HardMathSupport.Timmesfeld.Coordinator.inputPiGenOrth_of_orthCentGen
    (orthCentGen_of_autU42Five hU)

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
