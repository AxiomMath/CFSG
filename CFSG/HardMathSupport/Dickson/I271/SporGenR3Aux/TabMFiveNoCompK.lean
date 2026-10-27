module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterFiveBCover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralNoComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.KGroupCarrier
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveNoComp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.Generated
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus
  _root_.Timmesfeld.PcFive _root_.Timmesfeld.PcReg

section Classes

variable {G : Type} [Group G]

@[expose] def FiveBOrInv (z x : G) : Prop :=
  InvertedByTwoA x ∨ ∃ j : ℕ, Nat.Coprime j 5 ∧ IsConj x (z ^ j)

theorem fiveBOrInv_conj {z x : G} (h : FiveBOrInv z x) (c : G) : FiveBOrInv z (c * x * c⁻¹) := by
  rcases h with h | ⟨j, hj, hx⟩
  · exact Or.inl (invertedByTwoA_conj h c)
  · exact Or.inr ⟨j, hj, (isConj_iff.2 ⟨c, rfl⟩).symm.trans hx⟩

theorem fiveBOrInv_pow {z x : G} (hx : x ^ 5 = 1) {k : ℕ} (hk : Nat.Coprime k 5)
    (h : FiveBOrInv z x) : FiveBOrInv z (x ^ k) := by
  rcases h with h | ⟨j, hj, hc⟩
  · exact Or.inl ((invertedByTwoA_pow Nat.prime_five hx hk).1 h)
  · obtain ⟨c, hc⟩ := isConj_iff.1 hc
    refine Or.inr ⟨j * k, Nat.Coprime.mul_left hj hk, isConj_iff.2 ⟨c, ?_⟩⟩
    rw [← conj_pow, hc, ← pow_mul]

end Classes

@[expose] noncomputable def fiveGenG (i : Fin 9) : Gmat := gw fiveGens[i.val]!

@[expose] noncomputable def xFiveB : Gmat := fiveGenG 8

@[expose] def M5BClass : Prop :=
  ∀ s : Gmat, orderOf s = 5 → ¬ InvertedByTwoA s →
    ∃ j : ℕ, Nat.Coprime j 5 ∧ IsConj s (xFiveB ^ j)

@[expose] def M5BTargets : Prop :=
  ∀ k < repIdx.size, FiveBOrInv xFiveB (prodAsc fiveGenG (digitsOf 5 9 repIdx[k]!))

section Gmat


theorem gmat_five_setup :
    Finite Gmat ∧ Nat.card Gmat = 5 ^ 9 * (monsterOrder / 5 ^ 9) ∧ ¬ 5 ∣ monsterOrder / 5 ^ 9 ∧
    (∀ i : Fin 9, fiveGenG i ^ 5 = prodAsc fiveGenG pw[i.val]!) ∧
    (∀ i j : Fin 9, i < j →
      fiveGenG i * fiveGenG j * (fiveGenG i)⁻¹ = prodAsc fiveGenG cw[i.val * 9 + j.val]!) ∧
    fiveGenG 8 ≠ 1 := by
  have hcard0 : Nat.card Gmat = monsterOrder := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have hg : ∀ r ∈ relSet 5 (pwF 9 pw) (cwF 9 cw), FreeGroup.lift fiveGenG r = 1 := by
    rw [← fivePw_eq, ← fiveCw_eq]
    exact fiveRels_holds
  obtain ⟨hpow, hcomm⟩ := rel_of_relSet fiveGenG hg
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num [monsterOrder]),
    by rw [hcard0]; norm_num [monsterOrder], by norm_num [monsterOrder], hpow, hcomm,
    fiveGen_eight_ne_one⟩

theorem m5bClass_of_targets (h : M5BTargets) : M5BClass := by
  obtain ⟨hfin, hcard, hm, hpow, hcomm, hz⟩ := gmat_five_setup
  have hN : ∀ j < auts.size, ∃ c : Gmat, ∀ (i : ℕ) (hi : i < 9),
      c * fiveGenG ⟨i, hi⟩ * c⁻¹ = prodAsc fiveGenG (digitsOf 5 9 (auts[j]!)[i]!) := by
    intro j hj
    refine ⟨gw fiveNW[j]!, fun i hi => ?_⟩
    have h3 : j < 3 := by
      have : auts.size = 3 := rfl
      omega
    rw [fiveNImg_eq j hj i hi, ← lift_wordF_eq]
    exact fiveNorm_holds j h3 i hi
  have key := MonsterFiveB.fiveCover_of_targets hcard hm fiveGenG hpow hcomm hz hN
    (R := FiveBOrInv xFiveB) (fun x c hx => fiveBOrInv_conj hx c)
    (fun x k hx hk hR => fiveBOrInv_pow hx hk hR) h
  intro s hs hinv
  rcases key s hs with h | h
  · exact absurd h hinv
  · exact h

theorem sylowData_xFiveB :
    ∃ P : Subgroup Gmat, Nat.card P = 5 ^ 9 ∧ orderOf xFiveB = 5 ∧
      (∀ x ∈ P, x * xFiveB = xFiveB * x) ∧
      ∀ c ∈ P, (∀ y ∈ P, c * y = y * c) → c ∈ Subgroup.zpowers xFiveB := by
  obtain ⟨hfin, hcard, hm, hpow, hcomm, hz⟩ := gmat_five_setup
  obtain ⟨P, hPcard, hzo, -, hPcomm, hPZ⟩ :=
    MonsterFiveB.sylowFive_data hcard hm fiveGenG hpow hcomm hz
  exact ⟨P, hPcard, hzo, hPcomm, hPZ⟩

theorem noComp_xFiveB (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    (hG : CFSG.Open.IsKGroup Gmat) (h65 : ∀ g : Gmat, orderOf g ≠ 65)
    (hO : OPrimeCoreTrivialAt 5 Gmat) (J : Subgroup Gmat) :
    ¬ GLAPComponent 5 (Subgroup.centralizer ({xFiveB} : Set Gmat)) J := by
  obtain ⟨hfin, hcard, hm, -⟩ := gmat_five_setup
  obtain ⟨P, hPcard, hzo, hPcomm, hPZ⟩ := sylowData_xFiveB
  set C := Subgroup.centralizer ({xFiveB} : Set Gmat) with hC
  have hPC : P ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hPcomm x hx)
  have hCG : Nat.card C ∣ Nat.card Gmat := Subgroup.card_subgroup_dvd_card C
  have h59 : 5 ^ 9 ∣ Nat.card C := hPcard ▸ Subgroup.card_dvd_of_le hPC
  have hfacG : (Nat.card Gmat).factorization 5 = 9 := by
    have hm0 : monsterOrder / 5 ^ 9 ≠ 0 := by norm_num [monsterOrder]
    rw [hcard, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
      Nat.prime_five.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hm]
    simp
  have hfac : (Nat.card C).factorization 5 = 9 := by
    have hle1 : 9 ≤ (Nat.card C).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 h59
    have hle2 : (Nat.card C).factorization 5 ≤ (Nat.card Gmat).factorization 5 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hCG 5
    omega
  have hP : Nat.card P = 5 ^ (Nat.card C).factorization 5 := by rw [hfac]; exact hPcard
  have hM : Nat.card Gmat ∣ monsterOrder :=
    (CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder : Nat.card Gmat = monsterOrder) ▸ dvd_rfl
  exact FiveCentralNoComp.no_glaPComponent_of_central_sylow hGA hSpM hG hM h65 hzo hPC hP hPZ
    (hO xFiveB hzo) J

theorem centFiveBNoComp_gmat (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    (hG : CFSG.Open.IsKGroup Gmat) (h65 : ∀ g : Gmat, orderOf g ≠ 65)
    (hO : OPrimeCoreTrivialAt 5 Gmat) (hCls : M5BClass) : CentFiveBNoComp Gmat := by
  intro x hx hinv J hJ
  obtain ⟨j, hj, hxj⟩ := hCls x hx hinv
  obtain ⟨c, hc⟩ := isConj_iff.1 hxj
  have h1 := glaPComponent_map_equiv Nat.prime_five (MulAut.conj c) hJ
  rw [map_centralizer_singleton (MulAut.conj c) x] at h1
  have h4 : (MulAut.conj c) x = xFiveB ^ j := by simpa [MulAut.conj_apply] using hc
  rw [h4] at h1
  obtain ⟨P, -, hord, -⟩ := sylowData_xFiveB
  have hx5 : xFiveB ^ 5 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  rw [centralizer_pow_eq_of_coprime Nat.prime_five hx5 hj] at h1
  exact noComp_xFiveB hGA hSpM hG h65 hO _ h1

end Gmat

section Carrier


theorem centFiveBNoComp_M_of_cls (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    (hK : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M))
    (h65 : ∀ g : NativeSporadic.Carrier .M, orderOf g ≠ 65)
    (hO : OPrimeCoreTrivialAt 5 Gmat) (hCls : M5BClass) :
    CentFiveBNoComp (NativeSporadic.Carrier .M) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  haveI : Finite MGriess :=
    (twoA_data_of_existence CFSG.Milestones.cl_lit_monster_existence_griess_conway).1
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv MGriess e.toEquiv
  let eG : NativeSporadic.Carrier .M ≃* Gmat := e.symm.trans φ
  have hKG : CFSG.Open.IsKGroup Gmat := hK.of_surjective eG.toMonoidHom eG.surjective
  have h65G : ∀ g : Gmat, orderOf g ≠ 65 := fun g hg =>
    h65 (eG.symm g) (by rw [MulEquiv.orderOf_eq]; exact hg)
  exact CentFiveBNoComp.of_equiv e.symm (CentFiveBNoComp.of_equiv φ
    (centFiveBNoComp_gmat hGA hSpM hKG h65G hO hCls))

end Carrier

section Consumer


theorem sporPair_M_five_of_cls (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 5) (hChev : ChevStrong 5)
    (hHN : SporStrong .HN 5) (hA : CentFiveA (NativeSporadic.Carrier .M))
    (hGA : GriessAllModelsStatement) (h65 : ∀ g : NativeSporadic.Carrier .M, orderOf g ≠ 65)
    (hO : OPrimeCoreTrivialAt 5 Gmat) (hCls : M5BClass) : SporPair .M 5 := by
  intro X _ _ hX K B hH hN hS hF hO'
  exact sporPair_M_five_of_tabNoComp hOut hSpM hBr hP hChev hHN hA
    (centFiveBNoComp_M_of_cls hGA hSpM (isKGroup_carrier_of_sporType hBr hX hS) h65 hO hCls)
    X hX K B hH hN hS hF hO'

end Consumer

end CFSG.HardMathSupport.Dickson.I271
