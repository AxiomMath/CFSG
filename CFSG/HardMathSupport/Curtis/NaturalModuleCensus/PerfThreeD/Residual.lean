module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Reduction
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.ModelPlus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.TwoElements
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.FlagStabPlusLink
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.Residual
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Curtis.Coordinator CFSG.LieType.Universal.Spin
open Module QuadraticMap Matrix CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

theorem fixPerfThreeResidualD :
    ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParab L J →
      (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
      ∀ l : ↥L, l ^ 3 ∈ Subgroup.center ↥L → (∀ g : ↥L, g * l = l * g → g ∈ J.subgroupOf L) →
        IsLieOf IdxD8 (↥L ⧸ Subgroup.center ↥L) →
        ¬ PerfThreeCent (QuotientGroup.mk' (Subgroup.center ↥L) l) → False := by
  intro Y _ _ L J hpar hperf l hl3 hlfix hX hno
  set ψ := QuotientGroup.mk' (Subgroup.center ↥L) with hψ
  have hsurj : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hker : ψ.ker ≤ Subgroup.center ↥L := (QuotientGroup.ker_mk' _).le
  have hoddker : Odd (Nat.card ψ.ker) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact hpar.odd
  obtain ⟨⟨d, hv⟩, hd, ⟨e0⟩⟩ := hX
  cases d
  case D r q =>
    obtain ⟨hr4, hp2, hcard⟩ : r = 4 ∧ q.p = 2 ∧ q.card = 2 := hd
    subst hr4
    have hexp : q.exponent = 1 := by
      have hpos := q.exponent_pos
      by_contra hne
      have h2 : 2 ≤ q.exponent := by omega
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      rw [TauCeti.PrimePower.card_def, hp2] at hcard
      omega
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp2 e0
    rw [hp2, hexp] at hmodel
    obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_stated_of_model_pomegaPlus hmodel
    obtain ⟨T0, hT0, hNT0, hneT0⟩ := exists_sylow_normalizer_subgroupOf_of_compParab hpar
    obtain ⟨⟨T, hNT, -⟩, -⟩ := exists_sylow_normalizer_map_of_central_quotient ψ hsurj hker
      hoddker ⟨T0, hT0, hNT0, hneT0⟩ (coprime_card_of_perf_subgroupOf hperf)
    have hJtop : (J.subgroupOf L).map ψ ≠ ⊤ := by
      intro h
      have hkJ : ψ.ker ≤ J.subgroupOf L :=
        hker.trans ((Subgroup.center_le_normalizer ((T0 : Subgroup ↥L) : Set ↥L)).trans hNT0)
      have h1 : J.subgroupOf L = ⊤ := by
        rw [← Subgroup.comap_map_eq_self hkJ, h, Subgroup.comap_top]
      apply hpar.ne_top
      refine le_antisymm hpar.parab.1 fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ J.subgroupOf L := h1 ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    obtain ⟨W, hW0, hWts, hWst⟩ := exists_stab_of_overgroup_plus (n := 4) (by norm_num) e T
      ((J.subgroupOf L).map ψ) hNT hJtop
    have hchar : CharP K 2 := inferInstance
    let ε := e.trans (statedProjEquivDerivedQuadPlus 4 (by norm_num) K)
    have hdim : finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    have hmax := exists_totallySingular_quadPlus 4 K
    have hv3 : (ψ l) ^ 3 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hl3
    have ha3 : (ε (ψ l)) ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
    have h3K : ((3 : ℕ) : K) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff K 2]
      norm_num
    have hnd := nondegenerate_polarBilin_quadPlus 4 K
    have hx : OddOrderIsometry (quadPlus 4 K) 3
        ((ε (ψ l) : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
      ⟨Subgroup.commutator_le_self _ (ε (ψ l)).2, by
        rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one], h3K, fun v hv => hnd.1 v hv⟩
    have hfix : finrank K (fixedSpace
        ((ε (ψ l) : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 4 ∨
        finrank K (fixedSpace
        ((ε (ψ l) : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 2 := by
      by_contra hnot
      apply hno
      refine PerfThreeCent.of_mulEquiv ε ?_
      exact perfThreeCent_orthDerived hnd (ε (ψ l)) ha3 fun hx' =>
        perfectThreeIn_isometryCentralizer_card_two hK hx' hdim hmax (le_refl 4)
          fun h => hnot h.2
    have hstab : ∀ y ∈ (J.subgroupOf L).map ψ, ∀ w ∈ W,
        ((ε y : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) w ∈ W := by
      intro y hy w hw
      obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e y)
      have h1 := hWst y hy A hA w hw
      have h2 := statedProjEquivDerivedQuadPlus_mk 4 (by norm_num) K A w
      rw [hA] at h2
      have h3 : ((ε y : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) w =
          ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ w := h2
      rw [h3]
      exact h1
    have hlJ : l ∈ J.subgroupOf L := hlfix l rfl
    have hWx : ∀ w ∈ W, ((ε (ψ l) : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) w ∈ W :=
      fun w hw => hstab _ ⟨l, hlJ, rfl⟩ w hw
    obtain ⟨g, hgC, hgΩ, ⟨k, hgk⟩, w, hwW, hgw⟩ := exists_twoPower_centralizer_moving hK hx
      (by omega) hmax hfix W hW0
      (fun w hw => (congrFun (coe_quadPlus 4 K) w).trans (hWts w hw)) hWx
    set ybar : ↥L ⧸ Subgroup.center ↥L := ε.symm ⟨g, hgΩ⟩ with hybar
    obtain ⟨g₀, hg₀⟩ := hsurj ybar
    have hcomm : ybar * ψ l = ψ l * ybar := by
      apply ε.injective
      rw [map_mul, map_mul, hybar, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      have := (mem_isometryCentralizer.1 hgC).2
      refine LinearEquiv.ext fun v => ?_
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact this v
    have hc : ⁅g₀, l⁆ ∈ Subgroup.center ↥L := by
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, hg₀, commutatorElement_eq_one_iff_commute]
      exact hcomm
    have hk : (ψ g₀) ^ (2 ^ k) = 1 := by
      rw [hg₀, hybar]
      apply ε.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hgk]
      rfl
    have hmem := mk_mem_map_of_commutator_central (J := J.subgroupOf L) hpar.odd hlfix hc hk
    rw [← hψ, hg₀] at hmem
    have := hstab ybar hmem w hwW
    rw [hybar, MulEquiv.apply_symm_apply] at this
    exact hgw this
  all_goals exact hd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
