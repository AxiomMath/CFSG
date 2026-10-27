module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.Main
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem nonempty_statedSp_mulEquiv_zmod_two {K : Type} [Field K] [Finite K] (r : ℕ)
    (hK : Nat.card K = 2) : Nonempty (StatedSp r K ≃* StatedSp r (ZMod 2)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two h
  exact ⟨(MulEquiv.ofBijective (CFSG.ClassicalInvolution.Q3.Q3Z.spMap (n := r) e.toRingHom)
    ⟨CFSG.ClassicalInvolution.Q3.Q3Z.spMap_injective _,
      CFSG.ClassicalInvolution.Q3.Q3Z.spMap_surjective e⟩).symm⟩

theorem fixThreeVoid_b_residual (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixThreeVoid (IsLieOf IdxBResidual) := by
  intro Y _ _ L J u h hX
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  have hq : CFSG.Open.IsQuasisimple ↥L := h.parab.comp.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
    have hPB : IdxB d := by
      cases d with
      | B r q => exact hPd.1
      | _ => exact hPd.elim
    obtain ⟨hd, hA, h2A⟩ := ToralCensus.rest_index (P := IdxB) (Or.inl rfl) hPB
    exact ToralCensus.card_center_eq_one_of_index hGA ⟨d, hv⟩ hd hA h2A e h.parab.odd
  obtain ⟨u', hbar⟩ := exists_fixBarFull_of_fixThreeHyp h hZ
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hPd.1
    have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by rcases hPd.2 with ⟨-, h⟩ | ⟨-, h | h⟩ <;> omega) e
        rwa [hq2] at hm
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hmodel
    have hcardK : Nat.card K = q.card := by
      rw [hcard, TauCeti.PrimePower.card_def, hq2]
    have hf1 : 1 ≤ q.exponent := q.exponent_pos
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
        hcard
    have hr0 : 1 ≤ r := by rcases hPd.2 with ⟨-, h⟩ | ⟨-, h | h⟩ <;> omega
    have : NeZero r := ⟨by omega⟩
    have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := r) (K := K) hf1 hcard).1
    let π : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
    have hfin : Finite (StatedSp r K) := by
      have : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv _ e'.toEquiv
      exact Finite.of_equiv _ π.toEquiv.symm
    let ee : (↥L ⧸ Subgroup.center ↥L) ≃* StatedSp r K := e'.trans π.symm
    have hb := hbar.map_mulEquiv ee
    rcases hPd.2 with ⟨h4, hr2⟩ | ⟨h2, h34⟩
    · subst hr2
      have : CharP K 2 := inferInstance
      exact false_of_fixBarFull_sp_four (by rw [hcardK]; exact h4) hb
    · obtain ⟨ψ⟩ := nonempty_statedSp_mulEquiv_zmod_two (K := K) r (by rw [hcardK]; exact h2)
      have hb' := hb.map_mulEquiv ψ
      rcases h34 with rfl | rfl
      · exact false_of_fixBarFull_sp_six hb'
      · exact false_of_fixBarFull_sp_eight hb'
  | _ => exact hPd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
