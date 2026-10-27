module

public import CFSG.ClassicalGroups.Orthogonal.OddCentralizerSylow
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.QuasithinUnique
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply coe_quadMinus)

theorem odd_centralizer_centralizes_of_component_orth_card_four
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2) (hQ4 : Q.card = 4)
    (hv : (TauCeti.LieTypeIndex.D m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L)) :
    ∀ l : L, x * l = l * x := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.D m Q, hv⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField d)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype F := Fintype.ofFinite F
  let D := (TauCeti.CFSGIndex.lie d).Group
  let E := StatedProj (StatedOmega (StatedQuadPlus m F))
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hdchar : d.characteristic = 2 := by
    change TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.D m Q) = 2
    rw [TauCeti.LieTypeIndex.characteristic_D, hQ]
  have hdfexp : d.fieldExponent = Q.exponent := by
    change TauCeti.LieTypeIndex.fieldExponent (TauCeti.LieTypeIndex.D m Q) = Q.exponent
    rw [TauCeti.LieTypeIndex.fieldExponent_D]
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    change Nat.card ↥d.fixedField = 2 ^ Q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hdchar, hdfexp]
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := Q.exponent)
      (by simpa [Nat.card_eq_fintype_card] using hFcardpow)
  have hf : 2 ≤ Q.exponent := by
    have h : 2 ^ Q.exponent = 2 ^ 2 := by
      rw [← hQcardpow, hQ4]
      norm_num
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    omega
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : 3 ≤ m := by omega
  have eD : D ≃* E :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid m Q hv
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
  have hbot : (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
      (StatedOmega (StatedQuadPlus m F)) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (K := F) (by omega)
  let eΩ : E ≃* StatedOmega (StatedQuadPlus m F) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  have hclose : Function.Injective ψ := by
    have hψ' : Function.Surjective (eΩ.toMonoidHom.comp ψ) := eΩ.surjective.comp hψ
    have hker' : (eΩ.toMonoidHom.comp ψ).ker ≤ Subgroup.center L := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      exact eΩ.injective (by simpa using hy)
    have hker'' : ((CFSG.StandardType.rPlusEquivStatedOmega F m).symm.toMonoidHom.comp
        (eΩ.toMonoidHom.comp ψ)).ker ≤ Subgroup.center L := by
      intro y hy
      apply hker'
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (CFSG.StandardType.rPlusEquivStatedOmega F m).symm.injective (by simpa using hy)
    have h := CFSG.StandardType.rPlus_injective_of_cover (K := F) hFcardpow hf hm3 L
      ((CFSG.StandardType.rPlusEquivStatedOmega F m).symm.toMonoidHom.comp
        (eΩ.toMonoidHom.comp ψ))
      ((CFSG.StandardType.rPlusEquivStatedOmega F m).symm.surjective.comp hψ')
      hker'' hL.1
    intro a b hab
    exact h (congrArg
      (fun z => (CFSG.StandardType.rPlusEquivStatedOmega F m).symm (eΩ z)) hab)
  have hqinj : Function.Injective q := by
    intro a b hab
    exact hclose (by simp [ψ, hab])
  let eL : L ≃* E :=
    (MulEquiv.ofBijective q ⟨hqinj, QuotientGroup.mk'_surjective _⟩).trans (e.trans eD)
  have hUindex : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hUmax.2.2
  let W : Sylow 2 L := hU2.toSylow hUindex
  have hWcoe : (W : Subgroup L) = U := IsPGroup.toSylow_coe hU2 hUindex
  let U' : Sylow 2 E :=
    W.comapOfInjective eL.symm eL.symm.injective (fun w _ => ⟨eL w, by simp⟩)
  have hU'coe : (U' : Subgroup E) = U.comap eL.symm.toMonoidHom := by
    change (W : Subgroup L).comap eL.symm.toMonoidHom = U.comap eL.symm.toMonoidHom
    rw [hWcoe]
  let x' : E := eL x
  have hx'odd : Odd (orderOf x') := by
    show Odd (orderOf (eL x))
    rw [MulEquiv.orderOf_eq eL x]
    exact hxodd
  have hx'central : x' ∈ Subgroup.centralizer ((U' : Subgroup E) : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyU : eL.symm y ∈ U := by
      rw [hU'coe] at hy
      exact hy
    have hcomm : eL.symm y * x = x * eL.symm y :=
      (Subgroup.mem_centralizer_iff.mp hxc) (eL.symm y) hyU
    calc y * x' = eL (eL.symm y) * eL x := by rw [eL.apply_symm_apply]
      _ = eL (eL.symm y * x) := by rw [map_mul]
      _ = eL (x * eL.symm y) := by rw [hcomm]
      _ = eL x * eL (eL.symm y) := by rw [map_mul]
      _ = x' * y := by rw [eL.apply_symm_apply]
  have hZ : Subgroup.center (StatedOmega (StatedQuadPlus m F)) = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus hm3]
    refine CFSG.StandardType.TableBOrth.scalars_subgroupOf_omega_eq_bot
      (Q := StatedQuadPlus m F)
      (v₀ := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) (fun z v => ?_) ?_
    · rw [← CFSG.LieType.Universal.Spin.coe_quadPlus, QuadraticMap.map_smul, smul_eq_mul, sq]
    · rw [← CFSG.LieType.Universal.Spin.coe_quadPlus,
        CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp [Pi.single_apply]
  have hcenter : Subgroup.center E = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eΩ z ∈ Subgroup.center (StatedOmega (StatedQuadPlus m F)) := by
      rw [← Subgroup.map_center_eq eΩ]
      exact Subgroup.mem_map_of_mem eΩ.toMonoidHom hz
    rw [hZ] at hz'
    rw [Subgroup.mem_bot] at hz' ⊢
    exact eΩ.injective (by rw [hz', map_one])
  have hx'center : x' ∈ Subgroup.center E :=
    odd_centralizer_sylow_le_center_orth_plus hm U' hx'odd hx'central
  rw [hcenter] at hx'center
  have hx'one : x' = 1 := Subgroup.mem_bot.mp hx'center
  have hxone : x = 1 := by
    have := congrArg eL.symm hx'one
    simpa [x'] using this
  intro l
  rw [hxone]
  simp

theorem odd_centralizer_centralizes_of_component_orth_minus_card_four
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2) (hQ4 : Q.card = 4)
    (hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L)) :
    ∀ l : L, x * l = l * x := by
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
