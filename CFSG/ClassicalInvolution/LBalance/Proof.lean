module

public import CFSG.ClassicalInvolution.LBalance
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools
public import CFSG.ClassicalInvolution.LBalance.Proof.Correspondence
public import CFSG.ClassicalInvolution.LBalance.Proof.Central
public import CFSG.ClassicalInvolution.LBalance.Proof.Reductions
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ClassicalInvolution.LBalanceProof

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.LocalCores
  CFSG.GroupTheory Subgroup
open scoped commutatorElement

section

variable {X : Type} [Group X] [Finite X]

theorem balanced_of_pPrimeCore_eq_bot_of_center_eq_bot (hG : GlaubermanSylowFixingSolvable)
    (IH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X → LBalanceAt Y)
    (hO : pPrimeCore 2 X = ⊥) (hZ : center X = ⊥) : LBalanceAt X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hA
  by_cases hX1 : (⊤ : Subgroup X) = ⊥
  · intro K _
    exact (le_top.trans hX1.le).trans bot_le
  obtain ⟨z, hzFA, hz2, P, hP⟩ := exists_involution_centralizing_layer_sylow hO hX1 A hA
  intro K hK
  have hFnil := (CFSG.LocalCores.fitting_nilpotent (G := X))
  have hFn : (fittingSubgroup X).Normal := hFnil.2.1
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have hEn : (layer X).Normal := inferInstance
  have hFs : (generalizedFitting X).Normal := by
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  have hKperf : Group.IsPerfect K := isPerfect_of_isPComponent hK
  have hK2 : TwoComponents.IsTwoComponent K := (CatalogueBAlternating.pComponent_two_iff K).1 hK
  have hYn : ((generalizedFitting X).subgroupOf (centralizer (A : Set X))).Normal :=
    Subgroup.normal_subgroupOf
  have hsub : Open.IsSubnormal ((generalizedFitting X).subgroupOf (centralizer (A : Set X))) ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal hYn.isSubnormal
  have hpl : pLayer X 2 = layer X := pLayer_eq_layer_of_pPrimeCore_eq_bot hO
  rw [hpl]
  rcases TwoComponentSubnormal.contains_or_normalizes_core K
    ((generalizedFitting X).subgroupOf (centralizer (A : Set X))) hK2 hsub with h1 | ⟨h2, h3⟩
  · have hKF : K.map (centralizer (A : Set X)).subtype ≤ generalizedFitting X := by
      rintro _ ⟨k, hk, rfl⟩
      exact h1 hk
    have : Group.IsPerfect (K.map (centralizer (A : Set X)).subtype) :=
      Group.IsPerfect.map (centralizer (A : Set X)).subtype
    exact le_layer_of_perfect_of_le_generalizedFitting _ hKF
  · have hzF : z ∈ generalizedFitting X := hzFA.1
    have hzC : z ∈ centralizer (A : Set X) := hzFA.2
    let zC : centralizer (A : Set X) := ⟨z, hzC⟩
    have hzC2 : orderOf zC = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hz2
    have hzY : zC ∈ (generalizedFitting X).subgroupOf (centralizer (A : Set X)) := hzF
    have hKz : ⁅K, zpowers zC⁆ ≤ pPrimeCore 2 (centralizer (A : Set X)) := by
      have hz' : zpowers zC ≤ (generalizedFitting X).subgroupOf (centralizer (A : Set X)) :=
        (Subgroup.zpowers_le).2 hzY
      have h4 : ⁅K, zpowers zC⁆ ≤ (Open.componentClassificationOddCore K).map K.subtype :=
        (Subgroup.commutator_mono le_rfl hz').trans h3
      refine h4.trans ?_
      rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]
      obtain ⟨_, _, hKsn, _, _⟩ := hK
      exact Walter.map_pPrimeCore_le_of_isSubnormal hKsn
    obtain ⟨K1, hK1, hKle⟩ := exists_twoComponent_centralizer K hK zC hzC2 hKz
    let C : Subgroup X := centralizer (A : Set X)
    let C' : Subgroup C := centralizer ({zC} : Set C)
    let D : Subgroup X := C'.map C.subtype
    let K1X : Subgroup X := (K1.map C'.subtype).map C.subtype
    let Hz : Subgroup X := centralizer ({z} : Set X)
    have hDC : D ≤ C := Subgroup.map_subtype_le _
    have hDHz : D ≤ Hz := by
      rintro _ ⟨c, hc, rfl⟩
      have h := mem_centralizer_singleton_iff.1 hc
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h
    have hK1XD : K1X ≤ D := Subgroup.map_mono (Subgroup.map_subtype_le _)
    have hK1amb : Open.lBalanceIsPComponent 2 C' (K1.map C'.subtype) := by
      refine (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance 2 C' (K1.map C'.subtype)
        (Subgroup.map_subtype_le _)).1 ?_
      have e : (K1.map C'.subtype).subgroupOf C' = K1 :=
        Subgroup.comap_map_eq_self_of_injective C'.subtype_injective K1
      rw [e]
      exact hK1
    have hK1X : Open.lBalanceIsPComponent 2 D K1X := by
      refine (ComponentClassification.LBalance.pComponent_nested_iff 2 D C K1X hDC hK1XD).1 ?_
      have e1 : D.subgroupOf C = C' :=
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective C'
      have e2 : K1X.subgroupOf C = K1.map C'.subtype :=
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
      rw [e1, e2]
      exact hK1amb
    have hK1Xz : Open.lBalanceIsPComponent 2 (D.subgroupOf Hz) (K1X.subgroupOf Hz) :=
      (ComponentClassification.LBalance.pComponent_nested_iff 2 D Hz K1X hDHz hK1XD).2 hK1X
    have hAHz : A ≤ Hz := by
      intro a ha
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hzC a ha
    have hDeq : D.subgroupOf Hz = centralizer ((A.subgroupOf Hz : Subgroup Hz) : Set Hz) := by
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, hcx⟩ := hx
        rw [mem_centralizer_iff]
        intro h hh
        apply Subtype.ext
        have := mem_centralizer_iff.1 c.2 (h : X) hh
        change (h : X) * (x : X) = (x : X) * (h : X)
        have hcx' : (c : X) = (x : X) := hcx
        rw [← hcx']
        exact this
      · intro hx
        have hxC : (x : X) ∈ C := by
          rw [mem_centralizer_iff]
          intro a ha
          have := mem_centralizer_iff.1 hx ⟨a, hAHz ha⟩ ha
          exact congrArg Subtype.val this
        refine ⟨⟨x, hxC⟩, ?_, rfl⟩
        show (⟨x, hxC⟩ : C) ∈ centralizer ({zC} : Set C)
        rw [mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact mem_centralizer_singleton_iff.1 x.2
    rw [hDeq] at hK1Xz
    have hle : K1X.subgroupOf Hz ≤
        centralizer ((A.subgroupOf Hz : Subgroup Hz) : Set Hz) := by
      rw [← hDeq]
      intro x hx
      exact hK1XD hx
    have hK1Xz' : IsPComponent 2 ((K1X.subgroupOf Hz).subgroupOf
        (centralizer ((A.subgroupOf Hz : Subgroup Hz) : Set Hz))) :=
      (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance 2 _ _ hle).2 hK1Xz
    have hHzne : Hz ≠ ⊤ := by
      intro h
      have hzc : z ∈ center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ Hz := h ▸ Subgroup.mem_top g
        exact mem_centralizer_singleton_iff.1 hg
      rw [hZ, Subgroup.mem_bot] at hzc
      rw [hzc] at hz2
      simp at hz2
    have hcard : Nat.card Hz < Nat.card X := by
      have h1 := Subgroup.card_mul_index Hz
      have h2 : Hz.index ≠ 1 := fun h => hHzne (Subgroup.index_eq_one.1 h)
      have h3 : 0 < Hz.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h4 : 0 < Nat.card Hz := Nat.card_pos
      have h5 : 2 ≤ Hz.index := by omega
      nlinarith
    have hAp : IsPGroup 2 (A.subgroupOf Hz) :=
      hA.comap_of_injective Hz.subtype Hz.subtype_injective
    have hIH := IH Hz hcard (A.subgroupOf Hz) hAp _ hK1Xz'
    rw [Subgroup.map_subgroupOf_eq_of_le hle] at hIH
    have hBC : ∀ K' : Subgroup Hz, IsPComponent 2 K' → K'.map Hz.subtype ≤ layer X :=
      fun K' hK' => twoComponent_centralizer_le_layer hG hO z hz2 P Hz rfl hP K' hK'
    have hLayerHz : (pLayer Hz 2).map Hz.subtype ≤ layer X := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun L hL => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact hBC L hL
    have hK1Xle : K1X ≤ layer X := by
      have h1 : (K1X.subgroupOf Hz).map Hz.subtype ≤ (pLayer Hz 2).map Hz.subtype :=
        Subgroup.map_mono hIH
      rw [Subgroup.map_subgroupOf_eq_of_le (hK1XD.trans hDHz)] at h1
      exact h1.trans hLayerHz
    have hOC : Group.IsSolvable ((pPrimeCore 2 C).map C.subtype) := by
      have hodd : Odd (Nat.card (pPrimeCore 2 C)) := by
        have := ComponentClassification.OddCore.odd_card C
        rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
      have : Group.IsSolvable (pPrimeCore 2 C) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      exact isSolvable_map_of_isSolvable C.subtype _
    have hKX : K.map C.subtype ≤ layer X ⊔ (pPrimeCore 2 C).map C.subtype := by
      have h1 := Subgroup.map_mono (f := C.subtype) hKle
      rw [Subgroup.map_sup] at h1
      exact h1.trans (sup_le_sup_right hK1Xle _)
    have : Group.IsPerfect (K.map C.subtype) := Group.IsPerfect.map C.subtype
    exact perfect_le_of_le_sup_solvable (K.map C.subtype) (layer X) ((pPrimeCore 2 C).map C.subtype) hKX
end

theorem balanced_all (hG : GlaubermanSylowFixingSolvable) : ∀ (X : Type) [Group X] [Finite X], LBalanceAt X := by
  have key : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → LBalanceAt X := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X _ _ hn
      have IH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X → LBalanceAt Y :=
        fun Y _ _ hY => ih (Nat.card Y) (hn ▸ hY) Y rfl
      by_cases hO : pPrimeCore 2 X = ⊥
      · by_cases hZ : center X = ⊥
        · exact balanced_of_pPrimeCore_eq_bot_of_center_eq_bot hG IH hO hZ
        · exact balanced_of_center_ne_bot IH hO hZ
      · exact balanced_of_pPrimeCore_ne_bot IH hO
  intro X _ _
  exact key _ X rfl
theorem l2PrimeBalance_of_balanced (h : ∀ (X : Type) [Group X] [Finite X], LBalanceAt X) :
    CFSG.ClassicalInvolution.L2PrimeBalance := by
  intro X _ _ A hA
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact h X A hA K hK
end CFSG.ClassicalInvolution.LBalanceProof

namespace CFSG.ClassicalInvolution

theorem l2PrimeBalance_of_glauberman (hG : GlaubermanSylowFixingSolvable) : L2PrimeBalance :=
  LBalanceProof.l2PrimeBalance_of_balanced (LBalanceProof.balanced_all hG)

end CFSG.ClassicalInvolution
