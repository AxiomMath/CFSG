module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeModule
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeOffender
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.Quasithin.Background.C2PushQuot
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace CFSG.AGLEmbedding

namespace AscTenThree

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

omit [Finite G] in
theorem pCoreOf_barM_normalizer_le (hyp : Asc81bHyp X S) :
    pCoreOf 2 (barM X (X ⊓ Subgroup.normalizer (S : Set G))) ≤ barM X S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := X ⊓ Subgroup.normalizer (S : Set G) with hK
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hmk
  set Pb := pCoreOf 2 (barM X K) with hPb
  set P : Subgroup G := ((Pb.comap mk).map X.subtype) ⊓ K with hP
  have hPK : P ≤ K := inf_le_right
  have hPb2 : IsPGroup 2 Pb := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hQ2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  have hP2 : IsPGroup 2 P := by
    rintro ⟨x, ⟨⟨y, hy, hyx⟩, hxK⟩⟩
    obtain ⟨a, ha⟩ := hPb2 ⟨mk y, hy⟩
    have hya : y ^ 2 ^ a ∈ CFSG.pCore 2 ↥X := by
      have h1 : mk (y ^ 2 ^ a) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val ha
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := hQ2 ⟨_, hya⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (y ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have : x = (y : G) := hyx.symm
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [this, pow_add, pow_mul]
    have := congrArg Subtype.val hb'
    simpa using this
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ n ∈ K, ∀ p ∈ P, n * p * n⁻¹ ∈ P := by
      intro n hn p hp
      obtain ⟨⟨y, hy, hyp⟩, hpK⟩ := hp
      have hnX : n ∈ X := hn.1
      have hnb : mk ⟨n, hnX⟩ ∈ barM X K := ⟨⟨n, hnX⟩, hn, rfl⟩
      have hnN' := Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (barM X K) hnb)
      refine ⟨⟨⟨n, hnX⟩ * y * ⟨n, hnX⟩⁻¹, ?_, ?_⟩, K.mul_mem (K.mul_mem hn hpK) (K.inv_mem hn)⟩
      · show mk (⟨n, hnX⟩ * y * ⟨n, hnX⟩⁻¹) ∈ Pb
        rw [map_mul, map_mul, map_inv]
        exact (hnN' (mk y)).mp hy
      · have hyp' : (y : G) = p := hyp
        simp [hyp']
    intro p
    constructor
    · exact key n hn p
    · intro hp
      have := key n⁻¹ (K.inv_mem hn) _ hp
      rwa [show n⁻¹ * (n * p * n⁻¹) * n⁻¹⁻¹ = p by group] at this
  have hPS : P ≤ S := by
    have h := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPK hKP hP2
    rwa [← hyp.twoRadical.2.2] at h
  intro u hu
  obtain ⟨m, hmK, rfl⟩ : ∃ m : ↥X, (m : G) ∈ K ∧ mk m = u := by
    obtain ⟨m, hm, hmu⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _) hu
    exact ⟨m, hm, hmu⟩
  exact ⟨m, Subgroup.mem_subgroupOf.mpr (hPS ⟨⟨m, hu, rfl⟩, hmK⟩), rfl⟩

theorem isSylowTwoOf_inf_of_normalizer_le_normalizer (hyp : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L)
    (hSL : ¬ barM X S ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)))
    (hNR : X ⊓ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (S : Set G)) :
    IsSylowTwoOf (S ⊓ L) L := by
  set R := S ⊓ Subgroup.normalizer (L : Set G) with hR
  have hSX : S ≤ X := hyp.twoRadical.1
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hR2 : IsPGroup 2 R := hyp.twoRadical.isPGroup.to_le inf_le_left
  have hcomp : CFSG.IsComponent (barM X L) := (CFSG.isComponent_iff_open _).mpr hL.component
  set Kb := barM X (X ⊓ Subgroup.normalizer (S : Set G)) with hKb
  have hHN : Kb ≤ Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    barM_le_normalizer_barM inf_le_right
  have hB := CFSG.Quasithin.C2Push.commutator_inf_le_of_not_le_normalizer hHN hcomp hSL
  have hA := CFSG.Quasithin.C2Push.pCoreOf_inf_le_pCoreOf_of_isComponent Kb hcomp
  have hSKb : barM X S ≤ Kb := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hSX (Subgroup.mem_subgroupOf.mp hx),
      Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hx)⟩, rfl⟩
  have hRsyl : IsSylowTwoOf R (L ⊔ R) := by
    refine isSylowTwoOf_of_forall_normalizer_le le_sup_right hR2 ?_
    intro U hU hU2 hRU hUN u hu
    have hu' : u ∈ ((R ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact hU hu
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRL] at hu'
    obtain ⟨r, hr, ℓ, hℓ, rfl⟩ := hu'
    have hℓU : ℓ ∈ U := by
      have := U.mul_mem (U.inv_mem (hRU hr)) hu
      simpa using this
    have hℓX : ℓ ∈ X := hL.le hℓ
    have hℓN : ℓ ∈ Subgroup.normalizer (S : Set G) := hNR ⟨hℓX, hUN hℓU⟩
    have hℓS : ℓ ∈ S := by
      set lb := QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨ℓ, hℓX⟩ with hlb
      set Ub := barM X (Subgroup.zpowers ℓ) with hUb
      have hzU : Subgroup.zpowers ℓ ≤ U := (Subgroup.zpowers_le).mpr hℓU
      have hUb2 : IsPGroup 2 Ub := AscEightFour.barM_isPGroup (hU2.to_le hzU)
      set P := barM X S ⊓ barM X L with hP
      have hP2 : IsPGroup 2 P :=
        (AscEightFour.barM_isPGroup hyp.twoRadical.isPGroup).to_le inf_le_left
      have hzS : Subgroup.zpowers ℓ ≤ Subgroup.normalizer (S : Set G) :=
        (Subgroup.zpowers_le).mpr hℓN
      have hzL : Subgroup.zpowers ℓ ≤ Subgroup.normalizer (L : Set G) :=
        (Subgroup.zpowers_le).mpr (Subgroup.le_normalizer hℓ)
      have hUbN : Ub ≤ Subgroup.normalizer (P : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := fun z hz =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨barM_le_normalizer_barM hzS hz, barM_le_normalizer_barM hzL hz⟩
      have hU'2 : IsPGroup 2 (P ⊔ Ub : Subgroup _) :=
        IsPGroup.to_sup_of_normal_left' hP2 hUb2 hUbN
      set N := barM X L ⊓ Kb with hN
      have hUbN' : Ub ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (x : G) ∈ Subgroup.zpowers ℓ := Subgroup.mem_subgroupOf.mp hx
        refine ⟨⟨x, Subgroup.mem_subgroupOf.mpr ((Subgroup.zpowers_le).mpr hℓ hx'), rfl⟩,
          ⟨x, Subgroup.mem_subgroupOf.mpr ((Subgroup.zpowers_le).mpr
            (Subgroup.mem_inf.mpr ⟨hℓX, hℓN⟩) hx'), rfl⟩⟩
      have hPN : P ≤ N := fun x hx => ⟨hx.2, hSKb hx.1⟩
      have hU'N : P ⊔ Ub ≤ N := sup_le hPN hUbN'
      have hNU' : N ≤ Subgroup.normalizer ((P ⊔ Ub : Subgroup _) :
          Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
        refine CFSG.Quasithin.C2Push.le_normalizer_of_forall_conj_mem ?_
        intro n hn p hp
        have h1 : ⁅n, p⁆ ∈ P ⊔ Ub := Subgroup.mem_sup_left (hB
          (Subgroup.commutator_mem_commutator (show n ∈ barM X L ⊓ Kb from hn) (hU'N hp)))
        have h2 : ⁅n, p⁆ * p ∈ P ⊔ Ub := (P ⊔ Ub).mul_mem h1 hp
        have e : ⁅n, p⁆ * p = n * p * n⁻¹ := by simp only [commutatorElement_def]; group
        rwa [e] at h2
      have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hU'N hNU' hU'2
      have hlbU : lb ∈ P ⊔ Ub :=
        Subgroup.mem_sup_right ⟨⟨ℓ, hℓX⟩, Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_zpowers ℓ), rfl⟩
      have hlbS : lb ∈ barM X S := pCoreOf_barM_normalizer_le hyp (hA (hle hlbU))
      obtain ⟨s, hs, hsl⟩ := hlbS
      have hq : s⁻¹ * ⟨ℓ, hℓX⟩ ∈ CFSG.pCore 2 ↥X := by
        rw [← QuotientGroup.eq]
        exact hsl
      have hqQ : ((s⁻¹ * ⟨ℓ, hℓX⟩ : ↥X) : G) ∈ pCoreOf 2 X := ⟨_, hq, rfl⟩
      have hqS : ((s⁻¹ * ⟨ℓ, hℓX⟩ : ↥X) : G) ∈ S := hyp.twoCore_le hqQ
      have : ℓ = (s : G) * ((s⁻¹ * ⟨ℓ, hℓX⟩ : ↥X) : G) := by simp
      rw [this]
      exact S.mul_mem (Subgroup.mem_subgroupOf.mp hs) hqS
    exact R.mul_mem hr ⟨hℓS, Subgroup.le_normalizer hℓ⟩
  have h := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hRsyl le_sup_left
    (sup_le Subgroup.le_normalizer hRL)
  have heq : R ⊓ L = S ⊓ L := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) ?_
    rintro x ⟨hxS, hxL⟩
    exact ⟨⟨hxS, Subgroup.le_normalizer hxL⟩, hxL⟩
  rwa [heq] at h

theorem tenThree_of_hyp (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    IsSylowTwoOf (S ⊓ L) L ∨ S ≤ Subgroup.normalizer (L : Set G) := by
  have hSX : S ≤ X := hyp.twoRadical.1
  by_cases hLV : L ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G)
  · exact Or.inr (hL.le_normalizer (barM_le_normalizer_of_le_centralizer_V hyp hL.le hLV) hSX)
  by_cases hSL : barM X S ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X))
  · exact Or.inr (hL.le_normalizer hSL hSX)
  left
  set R := S ⊓ Subgroup.normalizer (L : Set G) with hR
  have hJR : thompsonJ S ≤ R := GammaExtra.thompsonJ_le fun A hA =>
    le_inf hA.1 (hL.le_normalizer (barM_le_normalizer_of_isMaxElemAbelian hyp hL hLV hA)
      (hA.1.trans hSX))
  have hJeq : thompsonJ R = thompsonJ S := GammaExtra.thompsonJ_eq_of_le hJR inf_le_left
  have hNR : X ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ R hx.2
    rw [hJeq] at h1
    have hJS : thompsonJ S ≤ S := C1GN.thompsonJ_le S
    have hJ1 : thompsonJ S ≠ ⊥ :=
      Setup.thompsonJ_ne_bot hyp.twoRadical.isPGroup hyp.twoRadical.2.1
    have h3 : X ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ cgsIn X S :=
      le_iSup_of_le (thompsonJ S) (le_iSup_of_le hJS (le_iSup_of_le hJ1
        (le_iSup_of_le (Setup.characteristic_thompsonJ S) le_rfl)))
    have h2 : x ∈ cgsIn X S := h3 ⟨hx.1, h1⟩
    rw [hyp.cgs] at h2
    exact h2.2
  exact isSylowTwoOf_inf_of_normalizer_le_normalizer hyp hL hSL hNR

end AscTenThree

theorem asc81bTenThree :
    ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Open.IsKGroup ↥X → Asc81bHyp X S →
      IsTwoPrimeComponent X L → IsSylowTwoOf (S ⊓ L) L ∨ S ≤ Subgroup.normalizer (L : Set G) :=
  fun _ _ _ _ _ _ _ hyp hL => AscTenThree.tenThree_of_hyp hyp hL

end CFSG.AGLEmbedding
