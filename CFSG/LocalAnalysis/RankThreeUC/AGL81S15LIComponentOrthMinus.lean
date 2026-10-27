module

public import CFSG.ClassicalGroups.Orthogonal.OddCentralizerSylow
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.QuasithinUnique
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply coe_quadMinus)

theorem odd_centralizer_centralizes_of_component_orth_minus_of_card_ge_five
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L))
    (hQcard : 5 ≤ Q.card) : ∀ l : L, x * l = l * x := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField d)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype F := Fintype.ofFinite F
  let D := (TauCeti.CFSGIndex.lie d).Group
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hdchar : d.characteristic = 2 := by
    change TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.twistedD m Q) = 2
    rw [TauCeti.LieTypeIndex.characteristic_twistedD, hQ]
  have hdfexp : d.fieldExponent = Q.exponent := by
    change TauCeti.LieTypeIndex.fieldExponent (TauCeti.LieTypeIndex.twistedD m Q) = Q.exponent
    rw [TauCeti.LieTypeIndex.fieldExponent_twistedD]
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    change Nat.card ↥d.fixedField = 2 ^ Q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hdchar, hdfexp]
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := Q.exponent)
      (by simpa [Nat.card_eq_fintype_card] using hFcardpow)
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      m Q hv
  let E := StatedProj (StatedOmega (StatedQuadMinus m F b c))
  let q : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let ψ : L →* E := eD.toMonoidHom.comp (e.toMonoidHom.comp q)
  have hψ : Function.Surjective ψ :=
    eD.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : e (q y) = 1 := eD.injective (by simpa [ψ] using hy)
    have h2 : q y = 1 := e.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff y).mp h2
  have hUindex : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hUmax.2.2
  let W : Sylow 2 L := hU2.toSylow hUindex
  have hWcoe : (W : Subgroup L) = U := IsPGroup.toSylow_coe hU2 hUindex
  let U' : Sylow 2 E := W.mapSurjective (f := ψ) hψ
  have hU'coe : (U' : Subgroup E) = U.map ψ := by
    change (W : Subgroup L).map ψ = U.map ψ
    rw [hWcoe]
  let x' : E := ψ x
  have hx'odd : Odd (orderOf x') :=
    hxodd.of_dvd_nat (orderOf_map_dvd ψ x)
  have hx'central : x' ∈ Subgroup.centralizer ((U' : Subgroup E) : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hU'coe] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hcomm : u * x = x * u :=
      (Subgroup.mem_centralizer_iff.mp hxc) u hu
    show ψ u * ψ x = ψ x * ψ u
    rw [← map_mul, hcomm, map_mul]
  have hbot : (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus m F b c)) = ⊥ := by
    have hv0 : quadMinus m F b c
        (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1) ≠ 0 := by
      rw [quadMinus_apply]
      simp
    exact CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus m F b c) (Q₀ := StatedQuadMinus m F b c)
      (coe_quadMinus m F b c) ⟨_, hv0⟩
  let eΩ : E ≃* StatedOmega (StatedQuadMinus m F b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  have hZ : Subgroup.center (StatedOmega (StatedQuadMinus m F b c)) = ⊥ :=
    CFSG.StandardType.center_statedOmega_quadMinus_eq_bot (K := F) (n := m) hm hirr
  have hcenter : Subgroup.center E = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eΩ z ∈ Subgroup.center (StatedOmega (StatedQuadMinus m F b c)) := by
      rw [← Subgroup.map_center_eq eΩ]
      exact Subgroup.mem_map_of_mem eΩ.toMonoidHom hz
    rw [hZ] at hz'
    rw [Subgroup.mem_bot] at hz' ⊢
    exact eΩ.injective (by rw [hz', map_one])
  have hx'center : x' ∈ Subgroup.center E :=
    odd_centralizer_sylow_le_center_orth_minus hm b c hirr U' hx'odd hx'central
  have hx'one : x' = 1 := by
    have h := hx'center
    rw [hcenter] at h
    exact Subgroup.mem_bot.mp h
  have hxker : x ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    show ψ x = 1
    exact hx'one
  have hxmem : x ∈ Subgroup.center L := hker hxker
  intro l
  exact (Subgroup.mem_center_iff.mp hxmem l).symm

end CFSG.LocalAnalysis.RankThreeUC.S15

end
