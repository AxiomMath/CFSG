module

public import CFSG.GH74.GLS.C3.Layer1.St1Prop83
public import CFSG.GH74.GLS.TwoThin.DPair
public import CFSG.Walter.AStar.Subnormal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.St1P41L42
public import CFSG.GH74.GLS.C3.Layer1.Th2Dih
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.Walter.J1
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

section PumpupEq

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_eq_bot_of_subnormal {H K : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hH : pPrimeCore 2 ↥H = ⊥) : pPrimeCore 2 ↥K = ⊥ := by
  have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (G := ↥H) hsub
  rw [hH] at h
  have h1 : pPrimeCore 2 ↥(K.subgroupOf H) = ⊥ := by
    have h2 : (pPrimeCore 2 ↥(K.subgroupOf H)).map (K.subgroupOf H).subtype = ⊥ :=
      le_bot_iff.mp h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (K.subgroupOf H).subtype_injective).mp h2
  have h3 := pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hKH)
  rw [h1, Subgroup.map_bot] at h3
  exact h3.symm

omit [Finite G] in
theorem card_kBar_eq_of_eq_bot {K : Subgroup G} (h : pPrimeCore 2 ↥K = ⊥) :
    Nat.card (kBar K) = Nat.card ↥K := by
  have : Nat.card (kBar K) = (pPrimeCore 2 ↥K).index := rfl
  rw [this, h, Subgroup.index_bot]

namespace Th2.P72c

theorem pumpUp_eq_of_pPrimeCore_eq_bot {u z : G} {K J : Subgroup G}
    (hOu : pPrimeCore 2 ↥(centralizer ({u} : Set G)) = ⊥)
    (hOz : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥)
    (hpump : PumpUpLT 2 u K z J) (htriv : IsTrivialPumpupAt u K z) :
    J = K ∧ IsPCompIn 2 (centralizer ({z} : Set G)) J := by
  have hpump' := hpump
  obtain ⟨⟨hxo, -, hKc⟩, ⟨hx'o, -, -⟩, hx'x, hx'K, hK'p⟩ := hpump
  have hKsub : (K.subgroupOf (centralizer ({u} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hKc).2.1
      Subgroup.IsSubnormal.top
  have hOK : pPrimeCore 2 ↥K = ⊥ := pPrimeCore_eq_bot_of_subnormal hKc.1 hKsub hOu
  have hOKG : pPrimeCoreOf 2 K = ⊥ := by
    unfold pPrimeCoreOf
    rw [hOK, Subgroup.map_bot]
  obtain ⟨Λ, hΛX, hΛlay, hΛpc, hΛuniq, hΛW, h2el, hcovΛ⟩ := pumpup_cover hx'o hKc hx'K
  have hKΛ : K ≤ Λ := by
    intro k hk
    obtain ⟨l, hl, o, ho, rfl⟩ := hcovΛ k hk
    rw [hOKG, Subgroup.mem_bot] at ho
    rw [ho, mul_one]
    exact hl
  have hΛK : Λ ≤ K := hΛX.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({z} : Set G) := hΛX.trans inf_le_right
  have hxY : u ∈ centralizer ({z} : Set G) := mem_centralizer_symm hx'x
  set Y' := centralizer ({z} : Set G) with hY'
  have hso : orderOf (⟨u, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛlay hΛE hK'p
  have himg := (hiff _ hK'2).mp hK'J
  have hinj : Function.Injective (barMk ↥Y') := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_barMk]
    exact hOz
  obtain ⟨hJn, ⟨eJK⟩⟩ := htriv J hpump'
  have hsn : (⟨u, hxY⟩ : ↥Y') ∈ normalizer ((J.subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') := by
    rw [Subgroup.mem_normalizer_iff]
    intro j
    have h := (Subgroup.mem_normalizer_iff.mp hJn) (j : G)
    simp only [Subgroup.mem_subgroupOf]
    exact h
  have hvert : conjSub (barMk ↥Y' ⟨u, hxY⟩)⁻¹ L = L ∧
      (Λ.subgroupOf Y').map (barMk ↥Y') ≤ L := by
    rcases hcases with h | ⟨hLs, hAB, hAD⟩
    · exact h
    · exfalso
      set s' := barMk ↥Y' ⟨u, hxY⟩ with hs'
      have hs'sq : s' * s' = 1 := by
        rw [hs', ← map_mul]
        have : (⟨u, hxY⟩ : ↥Y') * ⟨u, hxY⟩ = 1 := by
          apply Subtype.ext
          show u * u = 1
          rw [← pow_two]
          have := pow_orderOf_eq_one u
          rwa [hxo] at this
        rw [this, map_one]
      have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'sq
      set M := (J.subgroupOf Y').map (barMk ↥Y') with hM
      have hMinv : ∀ m ∈ M, s' * m * s'⁻¹ ∈ M := by
        rintro _ ⟨j, hj, rfl⟩
        have hj' : (⟨u, hxY⟩ : ↥Y') * j * (⟨u, hxY⟩ : ↥Y')⁻¹ ∈ J.subgroupOf Y' := by
          have := (Subgroup.mem_normalizer_iff.mp hsn) j
          exact this.mp hj
        exact ⟨_, hj', by simp [hs', map_mul]⟩
      have hMc : conjSub s'⁻¹ M = M := by
        ext x
        rw [mem_conjSub_iff', inv_inv]
        constructor
        · intro hx
          have := hMinv _ hx
          have e : s' * (s' * x * s'⁻¹) * s'⁻¹ = x := by
            rw [hs'inv]
            calc s' * (s' * x * s') * s' = (s' * s') * x * (s' * s') := by group
              _ = x := by rw [hs'sq]; simp
          rwa [e] at this
        · intro hx
          exact hMinv x hx
      rcases himg with h | h
      · apply hLs
        rw [← h]
        exact hMc
      · apply hLs
        have e : s'⁻¹⁻¹ = s'⁻¹ := by rw [inv_inv, hs'inv]
        have h2 : conjSub s'⁻¹ (conjSub s'⁻¹ L) = L :=
          calc conjSub s'⁻¹ (conjSub s'⁻¹ L) = conjSub s'⁻¹ (conjSub s'⁻¹⁻¹ L) := by rw [e]
            _ = L := conjSub_conjSub_inv s'⁻¹ L
        calc conjSub s'⁻¹ L = M := h.symm
          _ = conjSub s'⁻¹ M := hMc.symm
          _ = conjSub s'⁻¹ (conjSub s'⁻¹ L) := by rw [← h]
          _ = L := h2
  obtain ⟨hvL, hvΛ⟩ := hvert
  have himgL : (J.subgroupOf Y').map (barMk ↥Y') = L := by
    rcases himg with h | h
    · exact h
    · rw [h, hvL]
  have hΛJ : Λ ≤ J := by
    intro a ha
    have hmem : barMk ↥Y' ⟨a, hΛY ha⟩ ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
      ⟨⟨a, hΛY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hmemL := hvΛ hmem
    rw [← himgL] at hmemL
    obtain ⟨j, hj, hjπ⟩ := hmemL
    have hj' : j = ⟨a, hΛY ha⟩ := hinj hjπ
    have := Subgroup.mem_subgroupOf.mp hj
    rw [hj'] at this
    exact this
  have hKJ : K ≤ J := hKΛ.trans hΛJ
  have hJsub : (J.subgroupOf Y').IsSubnormal :=
    Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top
  have hJY : J ≤ Y' := hK'p.1.trans (pumpUp_le_centralizer K z)
  have hOJ : pPrimeCore 2 ↥J = ⊥ := pPrimeCore_eq_bot_of_subnormal hJY hJsub hOz
  have hcard : Nat.card ↥J = Nat.card ↥K := by
    rw [← card_kBar_eq_of_eq_bot hOJ, ← card_kBar_eq_of_eq_bot hOK]
    exact Nat.card_congr eJK.toEquiv
  exact ⟨(Subgroup.eq_of_le_of_card_ge hKJ hcard.le).symm, isPCompIn_two_iff.mpr ⟨hJY, hK'2⟩⟩

end Th2.P72c

theorem b_st1_pumpup_eq : B_st1_pumpup_eq := by
  intro G _ _ _ T5 u z K J hu hz hK hzC hpump htriv
  exact (Th2.P72c.pumpUp_eq_of_pPrimeCore_eq_bot (T5 u hu) (T5 z hz) hpump htriv).1


end PumpupEq

end CFSG.GH74.GLS
