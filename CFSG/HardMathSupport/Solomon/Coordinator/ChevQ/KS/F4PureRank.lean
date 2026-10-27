module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4PureStruct
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4PureGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Pure

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

set_option linter.unusedSectionVars false

section Helpers

theorem card_inf_centralizer_eq {K : Type*} [Group K] (A : Subgroup K) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (A : Set K)) = Nat.card ↥(Subgroup.center ↥A) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩
      invFun := fun z => ⟨z.1.1, Subgroup.mem_inf.2 ⟨z.1.2, ?_⟩⟩
      left_inv := fun x => rfl
      right_inv := fun z => rfl }
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2 g.1 g.2)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩
    exact congrArg Subtype.val this

theorem center_eq_zpowers {J : Type*} [Group J] [Finite J] {z : J} (hz : z ∈ Subgroup.center J)
    (hz3 : orderOf z = 3) (hc : Nat.card (Subgroup.center J) ∣ 3) :
    Subgroup.center J = Subgroup.zpowers z := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center J := Subgroup.zpowers_le.2 hz
  have h3 : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [h3]
  exact Nat.le_of_dvd (by norm_num) hc

theorem exists_two_cover_components {K : Type*} [Group K] [Finite K] (C : Subgroup K)
    (h3 : ∀ J₁ J₂ J₃ : Subgroup K, IsComponentOf J₁ C → IsComponentOf J₂ C → IsComponentOf J₃ C →
      J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) :
    ∃ A B : Subgroup K, (A = ⊥ ∨ IsComponentOf A C) ∧ (B = ⊥ ∨ IsComponentOf B C) ∧
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ ∀ J, IsComponentOf J C → J = A ∨ J = B := by
  by_cases h : ∃ A, IsComponentOf A C
  · obtain ⟨A, hA⟩ := h
    by_cases h' : ∃ B, IsComponentOf B C ∧ B ≠ A
    · obtain ⟨B, hB, hBA⟩ := h'
      refine ⟨A, B, Or.inr hA, Or.inr hB, fun a ha b hb =>
        CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hA hB (Ne.symm hBA) ha hb,
        fun J hJ => ?_⟩
      rcases h3 J A B hJ hA hB with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hBA h.symm).elim
    · push Not at h'
      refine ⟨A, ⊥, Or.inr hA, Or.inl rfl, fun a ha b hb => ?_, fun J hJ =>
        Or.inl (h' J hJ)⟩
      rw [Subgroup.mem_bot.1 hb]
      simp
  · push Not at h
    refine ⟨⊥, ⊥, Or.inl rfl, Or.inl rfl, fun a ha b hb => ?_, fun J hJ => (h J hJ).elim⟩
    rw [Subgroup.mem_bot.1 hb]
    simp

end Helpers

section Cat


theorem card_center_dvd_three {J : Type} [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (h : IsLieQuot J KSF4SU3.IsU3EightIndexTwo) : Nat.card (Subgroup.center J) ∣ 3 := by
  obtain ⟨⟨d, hv⟩, ⟨q, hq', rfl⟩, ⟨φ⟩⟩ := h
  obtain ⟨hp2, he3⟩ := hq'
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv φ
  rw [hp2, he3] at hm
  have hm' : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU 3 2 3 := hm
  have hLM := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical hm'
  have h1 := center_dvd_table CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    (F4InnerExAux.isQuasisimple_of_open hq) (MulEquiv.refl (J ⧸ Subgroup.center J)) hLM
  have h2 : (CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 3).1 *
      (CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 3).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 3).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 3).2) = 3 := by decide
  rwa [h2] at h1

theorem not_isLieQuot_B3_and_U3 {J : Type} [Group J] [Finite J]
    (hB : IsLieQuot J KSF4Out.IsB3EightIndex) (hU : IsLieQuot J KSF4SU3.IsU3EightIndexTwo) :
    False := by
  obtain ⟨⟨d₁, hv₁⟩, ⟨q₁, ⟨hp₁, he₁⟩, rfl⟩, ⟨φ₁⟩⟩ := hB
  obtain ⟨⟨d₂, hv₂⟩, ⟨q₂, ⟨hp₂, he₂⟩, rfl⟩, ⟨φ₂⟩⟩ := hU
  have h1 := lieOrderBridge_holds ⟨.B 3 q₁, hv₁⟩ (J ⧸ Subgroup.center J) ⟨φ₁⟩
  have h2 := lieOrderBridge_holds ⟨.twistedA 2 q₂, hv₂⟩ (J ⧸ Subgroup.center J) ⟨φ₂⟩
  have h3 := h1.symm.trans h2
  simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula,
    TauCeti.PrimePower.card_def, hp₁, he₁, hp₂, he₂] at h3
  exact (by decide +kernel : CFSG.Open.orderBC 3 (2 ^ 3) ≠ CFSG.Open.orderTwistedA 2 (2 ^ 3)) h3

end Cat

@[expose] def SUTypeK {K : Type} [Group K] (e : K) : Prop :=
  ¬ ∀ J : Subgroup K, GLAPComponent 3 (Subgroup.centralizer ({e} : Set K)) J →
    IsLieQuot ↥J KSF4Out.IsB3EightIndex

@[expose] def F4EightPureRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsLieQuot K IsF4EightIndex →
    ∀ k : K, orderOf k = 3 →
      ∀ J : Subgroup K, GLAPComponent 3 (Subgroup.centralizer ({k} : Set K)) J →
        IsLieQuot ↥J KSF4SU3.IsU3EightIndexTwo →
        ∀ E : Subgroup K, CFSG.Open.IsElemAbelian 3 E → k ∈ E →
          (∀ e ∈ E, e ≠ 1 → SUTypeK e) → 27 ≤ Nat.card E →
            9 ≤ (Subgroup.centralizer (J : Set K)).relIndex E

section Rank


theorem f4EightPureRank_of_struct (hS : F4EightStruct) : F4EightPureRank := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro K _ _ hq hLie k hk3 J hJ hJU E hEel hkE hpure h27
  refine relIndex_ge_of_inf_le_zpowers E J k hk3 ?_ h27
  intro e he
  obtain ⟨heE, heJ⟩ := Subgroup.mem_inf.1 he
  by_contra hne
  have he1 : e ≠ 1 := fun h => hne (h ▸ Subgroup.one_mem _)
  have he3 : e ^ 3 = 1 := hEel.2 e heE
  have heo : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hSU := hpure e heE he1
  obtain ⟨hS0e, hS1e, hS2e, hS3e⟩ := hS K hq hLie e heo
  obtain ⟨hS0k, -, -, hS3k⟩ := hS K hq hLie k hk3
  have hcompE : ∀ A : Subgroup K, IsComponentOf A (Subgroup.centralizer ({e} : Set K)) →
      IsLieQuot ↥A KSF4SU3.IsU3EightIndexTwo ∧ e ∈ A := by
    rcases hS3e with h | h
    · exact fun A hA => (hSU fun J' hJ' => h J' (hS0e J' hJ')).elim
    · exact h
  have hJc := hS0k J hJ
  have hkJ : k ∈ J := by
    rcases hS3k with h | h
    · exact (not_isLieQuot_B3_and_U3 (h J hJc) hJU).elim
    · exact (h J hJc).2
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJc.2.2
  have hJk : J ≤ Subgroup.centralizer ({k} : Set K) := hJ.1
  have hkc : k ∈ Subgroup.centralizer (J : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJk hj)
  have hkZ : (⟨k, hkJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hkc g.1 g.2)
  have hko : orderOf (⟨k, hkJ⟩ : ↥J) = 3 := by rw [Subgroup.orderOf_mk]; exact hk3
  have hcenJ : Subgroup.center ↥J = Subgroup.zpowers (⟨k, hkJ⟩ : ↥J) :=
    center_eq_zpowers hkZ hko (card_center_dvd_three hJq hJU)
  have hZJ : ∀ z ∈ J, z ∈ Subgroup.centralizer (J : Set K) → z ∈ Subgroup.zpowers k := by
    intro z hz hzc
    have hzZ : (⟨z, hz⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc g.1 g.2)
    rw [hcenJ] at hzZ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hzZ
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    have := congrArg Subtype.val hi
    simpa using this
  set n := Nat.card (↥J ⧸ Subgroup.center ↥J) with hn
  have hn1 : 1 ≤ n := Nat.card_pos
  have hcardZ : Nat.card (Subgroup.center ↥J) = 3 := by
    rw [hcenJ, Nat.card_zpowers, hko]
  have hJcard : Nat.card ↥J = 3 * n := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J), hcardZ, mul_comm]
  obtain ⟨A, B, hAmem, hBmem, hAB, hcover⟩ := exists_two_cover_components
    (Subgroup.centralizer ({e} : Set K)) hS2e
  have hJe : J ≤ Subgroup.centralizer ({e} : Set K) := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 heJ j hj)
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJlayer : J ≤ GLALayer (Subgroup.centralizer ({e} : Set K)) := hS1e J hJe hJperf
  have hJAB : J ≤ A ⊔ B := by
    refine hJlayer.trans ?_
    refine sSup_le fun J' hJ' => ?_
    rcases hcover J' hJ' with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  have hmember : ∀ X : Subgroup K, (X = ⊥ ∨ IsComponentOf X (Subgroup.centralizer ({e} : Set K))) →
      (∀ a ∈ X, a ∈ Subgroup.centralizer (X : Set K) → a ∈ Subgroup.zpowers e) ∧
        Nat.card ↥X ≤ n * Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set K)) := by
    intro X hX
    rcases hX with rfl | hXc
    · refine ⟨fun a ha _ => ?_, ?_⟩
      · rw [Subgroup.mem_bot.1 ha]
        exact Subgroup.one_mem _
      · simp only [Subgroup.card_bot]
        have : Nat.card ↥((⊥ : Subgroup K) ⊓ Subgroup.centralizer ((⊥ : Subgroup K) : Set K)) = 1 := by
          rw [bot_inf_eq, Subgroup.card_bot]
        rw [this]
        omega
    · obtain ⟨hXU, heX⟩ := hcompE X hXc
      have hXq : CFSG.Open.IsQuasisimple ↥X := hXc.2.2
      have hXe : X ≤ Subgroup.centralizer ({e} : Set K) := hXc.1
      have heZ : (⟨e, heX⟩ : ↥X) ∈ Subgroup.center ↥X := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.1 (hXe g.2)
        exact this
      have heo' : orderOf (⟨e, heX⟩ : ↥X) = 3 := by rw [Subgroup.orderOf_mk]; exact heo
      have hcenX : Subgroup.center ↥X = Subgroup.zpowers (⟨e, heX⟩ : ↥X) :=
        center_eq_zpowers heZ heo' (card_center_dvd_three hXq hXU)
      refine ⟨fun a ha hac => ?_, ?_⟩
      · have haZ : (⟨a, ha⟩ : ↥X) ∈ Subgroup.center ↥X := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hac g.1 g.2)
        rw [hcenX] at haZ
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 haZ
        refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
        have := congrArg Subtype.val hi
        simpa using this
      · have hXn : Nat.card (↥X ⧸ Subgroup.center ↥X) = n := by
          obtain ⟨eX⟩ := KSF4SU3.nonempty_equiv_projSU_of_isLieQuot hXU
          obtain ⟨eJ⟩ := KSF4SU3.nonempty_equiv_projSU_of_isLieQuot hJU
          exact Nat.card_congr (eX.trans eJ.symm).toEquiv
        rw [card_inf_centralizer_eq,
          Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X), hXn]
  obtain ⟨hAZ, hAcard⟩ := hmember A hAmem
  obtain ⟨hBZ, hBcard⟩ := hmember B hBmem
  have hke : k ∈ Subgroup.zpowers e :=
    key_center A B J e k n hAB hJAB hJq hkJ hkc hk3 hZJ hJcard hAZ hBZ hAcard hBcard
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hke
  have h3j : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨t, rfl⟩
    have hk1 : k = 1 := by
      rw [← hj, zpow_mul]
      have : e ^ (3 : ℤ) = 1 := by simpa using he3
      rw [this, one_zpow]
    rw [hk1, orderOf_one] at hk3
    omega
  exact hne (Bal209F4Aux.mem_of_zpow_mem he3 he1 h3j (by rw [hj]; exact Subgroup.mem_zpowers k))

end Rank

end KSF4Pure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
