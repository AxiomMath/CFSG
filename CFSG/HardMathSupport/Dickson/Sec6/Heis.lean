module

public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.Field
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Wrapper

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

namespace Heis

theorem heisP {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64)
    {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hb : ∃ b ∈ A, b ∉ linearAutGroup 3 K) (hL : ¬ LiftsCommute A) : GenP A := by
  classical
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; norm_num
  obtain ⟨b, hbA, hbD⟩ := hb
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbD (h ▸ (linearAutGroup 3 K).one_mem)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf b = 3 ^ 1 := by rw [pow_one]; exact orderOf_eq_prime hb3 hb1
  set Fr := l3FrameLinear h3 with hFr
  have hbE : ∃ d ∈ Fr.D, ∃ c : K ≃+* K, b = d * Fr.fld c := Fr.three_mem b 1 hord
  obtain ⟨h, hh, c, hc3, hbh⟩ := Fr.lang b hb3 hbE hbD
  obtain ⟨H, hH⟩ := mem_linearAutGroup_iff.1 hh
  set τ : MulAut (projectiveSL 3 K) := h⁻¹ with hτ
  set A' : Subgroup (MulAut (projectiveSL 3 K)) := A.map (MulAut.conj τ).toMonoidHom with hA'
  have hf' : fieldAut 3 K c ∈ A' := by
    refine ⟨b, hbA, ?_⟩
    show τ * b * τ⁻¹ = fieldAut 3 K c
    rw [hbh, hτ]
    show h⁻¹ * (h * fieldAut 3 K c * h⁻¹) * h⁻¹⁻¹ = fieldAut 3 K c
    group
  have hkey : ∀ x : GL (Fin 3) K, conjAut 3 K x ∈ A → conjAut 3 K (H⁻¹ * x * H) ∈ A' := by
    intro x hx
    refine ⟨conjAut 3 K x, hx, ?_⟩
    show τ * conjAut 3 K x * τ⁻¹ = _
    rw [hτ, inv_inv, ← hH, map_mul, map_mul, map_inv]
  have hL' : ¬ LiftsCommute A' := by
    intro hL'
    apply hL
    intro g g' hg hg'
    have h1 := hL' _ _ (hkey g hg) (hkey g' hg')
    have h2 : H⁻¹ * (g * g') * H = H⁻¹ * (g' * g) * H := by
      calc H⁻¹ * (g * g') * H = (H⁻¹ * g * H) * (H⁻¹ * g' * H) := by group
        _ = (H⁻¹ * g' * H) * (H⁻¹ * g * H) := h1
        _ = H⁻¹ * (g' * g) * H := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hel' : IsElemAbelian 3 A' := isElemAbelian_map _ hAel
  have hcard' : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj τ).injective, hA27]
  haveI := charP_two_of_card hK
  exact GenP_of_conj τ A (heis_gen_of_field hK hc3 hel' hcard' hf' hL')

end Heis

theorem l364Rank3Heis_holds : L364Rank3Heis := by
  intro Y _ _ hY hcore K _ _ hK ε A hA h27 hα hL
  set Φ : MulAut Y →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
  have hinjΦ : Function.Injective Φ := phi_injective hY ε
  have hAel' : IsElemAbelian 3 (A.map Φ) := isElemAbelian_map Φ hA
  have hcard' : Nat.card (A.map Φ) = 27 := by
    rw [Subgroup.card_map_of_injective hinjΦ, h27]
  have hb : ∃ b ∈ A.map Φ, b ∉ linearAutGroup 3 K := by
    obtain ⟨α, hαA, hα1, hαn⟩ := hα
    refine ⟨Φ α, ⟨α, hαA, rfl⟩, fun hD => hαn (Or.inl ?_)⟩
    exact isInnDiagPSL3_of_model ε hD
  have hGen := Heis.heisP hK hAel' hcard' hb hL
  have hGen' : GenP (A.map (centerDescend Y)) := by
    refine GenP_of_equiv ε _ ?_
    rw [Subgroup.map_map]
    exact hGen
  have hcen : IsPGroup 3 (Subgroup.center Y) :=
    CFSG.LocalAnalysis.GLTheoremB.isPGroup_center Nat.prime_three hcore
  have hinj : Function.Injective (centerDescend Y) := by
    intro a b hab
    apply hinjΦ
    show MulAut.congr ε (centerDescend Y a) = MulAut.congr ε (centerDescend Y b)
    rw [hab]
  have hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := hY.1
  exact gen_Y_of_GenP_quot hperf hcen hinj A hGen'

end CFSG.HardMathSupport.Dickson.Sec6
