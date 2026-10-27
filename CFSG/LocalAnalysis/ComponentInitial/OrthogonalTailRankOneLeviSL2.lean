module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviRange
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviKer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviComm

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped Pointwise commutatorElement

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

theorem nonempty_bar2_hinf_tailRankOneParabolic_equiv [Finite K] [FiniteDimensional K A]
    {i : Fin r} (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nonempty (Bar2 (Hinf (tailRankOneParabolic qA a₀ i)) ≃* SpecialLinearGroup (Fin 2) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two (by omega) hK
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple (K := K) hK4
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4
  have hT : CFSG.pCore 2 (SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (CFSG.pCore 2 (SpecialLinearGroup (Fin 2) K)) with hbot | htop
    · exact hbot
    · exfalso
      have h1 : IsPGroup 2 (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)) :=
        htop ▸ CFSG.pCore_isPGroup (p := 2) (G := SpecialLinearGroup (Fin 2) K)
      have hpg : IsPGroup 2 (SpecialLinearGroup (Fin 2) K) :=
        h1.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent (SpecialLinearGroup (Fin 2) K) :=
        IsPGroup.isNilpotent (p := 2) (G := SpecialLinearGroup (Fin 2) K) hpg
      exact Group.IsPerfect.not_isSolvable (G := SpecialLinearGroup (Fin 2) K) inferInstance
  exact KTabD.nonempty_bar2_hinf_equiv_of_leviHom_of_equiv
    (P := tailRankOneParabolic qA a₀ i)
    (β := tailRankOneLeviHom hi hani ha₀)
    (hker := isPGroup_ker_tailRankOneLeviHom hi hani ha₀)
    (S := (tailLeviSL2Embed K A r i).range)
    (hSR := fun x hx => by
      obtain ⟨M, rfl⟩ := hx
      exact tailLeviSL2Embed_mem_range hi hani ha₀ M)
    (hcomm := commutator_range_tailRankOneLeviHom_le hi hani ha₀ hcomm)
    (T := SpecialLinearGroup (Fin 2) K)
    (eS := (MonoidHom.ofInjective (tailLeviSL2Embed_injective i)).symm)
    (hperf := inferInstance)
    (hT := hT)

theorem tailRankOneSL2Surjection_holds [Finite K] [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    TailRankOneSL2Surjection (qA := qA) hani ha₀ i := by
  obtain ⟨e⟩ := nonempty_bar2_hinf_tailRankOneParabolic_equiv hi hani ha₀ hcomm hn hK
  let H := CFSG.pCore 2 ↥(Hinf (tailRankOneParabolic qA a₀ i))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' H), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective H)
  · have hker : (e.toMonoidHom.comp (QuotientGroup.mk' H)).ker = H := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    rw [hker]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥(Hinf (tailRankOneParabolic qA a₀ i)))

theorem isL2_tailRankOneParabolic [Finite K] [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsL2 (Bar2 (Hinf (tailRankOneParabolic qA a₀ i))) n :=
  isL2_rankOneParabolic_tail_of_sl2Surjection hani ha₀ hi hn hK
    (tailRankOneSL2Surjection_holds hi hani ha₀ hcomm hn hK)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
