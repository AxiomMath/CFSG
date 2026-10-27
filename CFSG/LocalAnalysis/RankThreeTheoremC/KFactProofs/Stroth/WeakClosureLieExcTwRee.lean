module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwReeClass
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
public import CFSG.Quasithin.EmptyFaithful.R3c18F
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Quasithin.R3c18
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.LargeReeOrder
open scoped commutatorElement

section Gamma

variable
  {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem wcOn_reeGamma_three : WCOn 3 (ReeTag.F4.reeGamma K a) := by
  classical
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2
  haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have h0 : ∀ c : ZMod 2, ι (c ^ 2 ^ 0) = (ι c) ^ 2 ^ a := by
    intro c
    rcases h2 c with rfl | rfl <;> simp [pow_ne_zero]
  have h1 : ∀ c : ZMod 2, ι (c ^ 2 ^ (0 + 1)) = (ι c) ^ 2 ^ (a + 1) := by
    intro c
    rcases h2 c with rfl | rfl <;> simp [pow_ne_zero]
  obtain ⟨x, y, h, -, -, hcomm, -, -, hcard, -, -, -⟩ :=
    CFSG.SectionRank.Tits_sylow3_cubic_witness (K := ZMod 2) (by simp)
  let φ : ↥(commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0)) →* ↥(ReeTag.F4.reeGamma K a) :=
    (reeGammaMap h0 h1).comp ((CFSG.Quasithin.A318P.reeFixedEquivGamma 0).toMonoidHom.comp
      (commutator ↥(reeFixed ReeTag.F4 (ZMod 2) 0)).subtype)
  have hφ : Function.Injective φ :=
    (reeGammaMap_injective h0 h1).comp
      ((CFSG.Quasithin.A318P.reeFixedEquivGamma 0).injective.comp Subtype.val_injective)
  refine WCOn.of_hom_noncomm (x := x) (y := y) φ (IsPGroup.of_card hcard) ?_
    (Subgroup.subset_closure (Set.mem_insert x {y}))
    (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))) ?_
  · intro g _ hg
    exact hφ (hg.trans (map_one φ).symm)
  · intro hxy
    exact hcomm (commutatorElement_eq_one_iff_mul_comm.2 hxy)

theorem wcOn_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    WCOn p (ReeTag.F4.reeGamma K a) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  by_cases hp3 : p = 3
  · subst hp3
    exact wcOn_reeGamma_three
  have hp5 : 5 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd (Fact.out : Nat.Prime 4) (by norm_num)
    omega
  by_cases hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a)
  · obtain ⟨-, hfac⟩ := large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK
    rcases hfac p Fact.out (by omega) hdvd with h | h | h | h | h
    · obtain ⟨P, hP⟩ := ree_sylow_phi1 hK Fact.out hp5 h
      exact WCOn.of_normalizerMovesLines P fun _ _ => hP
    · obtain ⟨P, hP⟩ := ree_sylow_phi2 hK Fact.out hp5 h
      exact WCOn.of_normalizerMovesLines P fun _ _ => hP
    · obtain ⟨P, hP⟩ := ree_sylow_phi4 hK Fact.out hp5 h
      exact WCOn.of_normalizerMovesLines P fun _ _ => hP
    · exact WCOn.of_pRank_top_le_one (by
        rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact pRank_le_one_ree_phi6 hK Fact.out hp5 h)
    · exact WCOn.of_pRank_top_le_one (by
        rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact pRank_le_one_ree_phi12 hK Fact.out hp5 h)
  · apply WCOn.of_factorization_le_one
    rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
    exact Nat.zero_le 1

end Gamma

theorem crossReeTits_twistedF4 :
    CrossReeTits .twistedF4 := by
  intro X _ _ ℓ f p _ hadm hp2 hpℓ hmodel
  obtain ⟨-, -, -, rfl, -, -⟩ := hadm
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KEXC.exists_gamma_of_model hmodel
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  exact WCOn.of_mulEquiv e (wcOn_reeGamma hK' hp2)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
