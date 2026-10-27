module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TypeIISupportingMaximumExcludesPair
import CFSG.FeitThompson.Local.TypePFixedCoreNormalizer
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape
import CFSG.FeitThompson.Local.AbelianFrobeniusKernelInKernel
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson
open CFSG.FeitThompson (conjSubgroup conjSubgroup_eq hallCoreIn
  hallCoreIn_eq hallCoreIn_le)
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd hallCoreOf
  centralizerIn IsFixedPointFreeOn)

universe u

namespace TypeIISupport

variable {G : Type*} [Group G]

theorem sup_eq_of_coe_mul_coe_eq {L A B : Subgroup G} (hA : A ≤ L) (hB : B ≤ L)
    (h : (A : Set G) * (B : Set G) = (L : Set G)) : A ⊔ B = L := by
  refine le_antisymm (sup_le hA hB) fun x hx => ?_
  rw [← SetLike.mem_coe, ← h] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact mul_mem (le_sup_left (a := A) (b := B) ha) (le_sup_right (a := A) (b := B) hb)

theorem isInternalSemidirectProduct_of_coe_mul_coe_eq {L A B : Subgroup G}
    (hAnorm : (A.subgroupOf L).Normal)
    (hmul : (A : Set G) * (B : Set G) = (L : Set G)) (hdisj : A ⊓ B = ⊥) :
    FreeCore.IsInternalSemidirectProduct L A B where
  sup_eq := sup_eq_of_coe_mul_coe_eq (left_le_of_coe_mul_coe_eq hmul)
    (right_le_of_coe_mul_coe_eq hmul) hmul
  le_normalizer := by
    have := hAnorm
    exact Subgroup.le_normalizer_of_normal_subgroupOf (left_le_of_coe_mul_coe_eq hmul)
  disjoint := disjoint_iff.2 hdisj

theorem disjoint_subgroupOf {A B L : Subgroup G} (h : A ⊓ B = ⊥) :
    Disjoint (A.subgroupOf L) (B.subgroupOf L) := by
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  rw [Subgroup.mem_subgroupOf] at hx hx'
  exact Subtype.ext (Subgroup.disjoint_def.1 (disjoint_iff.2 h) hx hx')

theorem hallCoreIn_ne_bot_of_bot_lt {L : Subgroup G} (h : ⊥ < hallCore ↥L) :
    hallCoreIn L ≠ ⊥ := by
  rw [hallCoreIn_eq]
  intro hc
  exact h.ne ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hc).symm

theorem natCard_hallCore_eq_natCard_hallCoreIn (L : Subgroup G) :
    Nat.card ↥(hallCore ↥L) = Nat.card ↥(hallCoreIn L) := by
  rw [hallCoreIn_eq, Subgroup.card_map_of_injective L.subtype_injective]

theorem conjSubgroup_eq_conj_smul (Y : Subgroup G) (y : G) :
    conjSubgroup Y y = MulAut.conj y⁻¹ • Y := by
  rw [conjSubgroup_eq, conj_smul_eq_map_conj]

theorem le_hallCore_of_frobenius {L H E U B : Subgroup G} [Finite G] [Group.IsSolvable ↥L]
    (hHL : H ≤ L) (hUL : U ≤ L) (hBL : B ≤ L)
    (hHnorm : (H.subgroupOf L).Normal) [IsMulCommutative ↥U]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hHall : (Nat.card ↥H).Coprime (H.relIndex L))
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    (hHne : H ≠ ⊥) (hUne : U ≠ ⊥) (hBne : B ≠ ⊥)
    (hBU : B ≤ normalizer (U : Set G)) (hUB : U ⊓ B = ⊥)
    (hCU : ∀ b ∈ B, b ≠ 1 → U ⊓ centralizer ({b} : Set G) = ⊥)
    (hcop : (Nat.card ↥H).Coprime (Nat.card ↥B)) :
    U ≤ H := by
  have _i : (H.subgroupOf L).Normal := hHnorm
  have _j : IsMulCommutative ↥(U.subgroupOf L) := isMulCommutative_subgroupOf_of_le hUL ‹_›
  have hidx : (H.subgroupOf L).index = H.relIndex L := rfl
  refine le_of_subgroupOf_le_subgroupOf hUL
    (le_of_isMulCommutative_of_coprime_natCard (E := E.subgroupOf L) (B := B.subgroupOf L)
      (isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [hidx, natCard_subgroupOf_of_le' hHL]; exact hHall
  · exact free_subgroupOf hHL hfree
  · exact subgroupOf_ne_bot hHL hHne
  · exact subgroupOf_ne_bot hUL hUne
  · exact subgroupOf_ne_bot hBL hBne
  · exact le_normalizer_subgroupOf hBU
  · exact disjoint_subgroupOf hUB
  · exact free_subgroupOf hUL hCU
  · rw [natCard_subgroupOf_of_le' hHL, natCard_subgroupOf_of_le' hBL]; exact hcop

end TypeIISupport

open TypeIISupport

theorem FBG_type_II_supporting_maximal_configuration
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FPF_type_I_frobenius.{u})
    (h₄ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FBG_type_II_supporting_maximal_configuration.{u} := by
  intro G _ _ hG M T U V W₁ W₂ hM hT hMT hcM hcT hII hcyc hMT' hcover L hL hNU
    P Q H hP hQ hH p q hp hq
  have hsimple := hG.isSimpleGroup
  have hG' : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG'' : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsolvL : Group.IsSolvable ↥L := hG.isSolvable_of_ne_top L hL.1
  obtain ⟨-, hneT, hIL⟩ := FBG_type_II_supporting_maximum_excludes_pair.{u} h₂ G hG
    M T U V W₁ W₂ hM hT hMT hcM hcT hII hcyc hMT' hcover L hL hNU P Q H hP hQ hH p q hp hq
  obtain ⟨-, hpp, hqp, -, -, hpq, hUne, hUcomm, -, hsdU, -, hffpU, -, -, -, -, -, -, -, -, -, -,
    -, -⟩ := h₂ G hG' M U W₁ W₂ hM hcM p q hp hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmodT, hQcard, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G hG' T V W₂ W₁ hT hcT q p hq hp
  obtain ⟨E, hEL, hEne, hsdL, hffpL⟩ := h₃ G hG' L hL hIL
  have hHL : H ≤ L := hH ▸ hallCoreIn_le L
  have hHne : H ≠ ⊥ := hH ▸ hallCoreIn_ne_bot_of_bot_lt hIL.bot_lt_hallCore
  have hHnorm : (H.subgroupOf L).Normal := hH ▸ normal_subgroupOf_hallCoreOf L
  have hsdL' : FreeCore.IsInternalSemidirectProduct L H E := hH ▸ hsdL
  have hfreeL : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥ := fun e he he1 =>
    hH ▸ inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hffpL he he1
  have hHall : (Nat.card ↥H).Coprime (H.relIndex L) :=
    hH ▸ coprime_natCard_relIndex_hallCoreIn L
  have hHnil : Group.IsNilpotent ↥H := hH ▸ isNilpotent_hallCoreIn L
  have hQcard' : Nat.card ↥Q = q ^ p := hQ ▸ hQcard
  have hqT : q ∈ sigmaPrimes T := by
    refine mem_sigmaPrimes_of_dvd_natCard_hallCore hT hqp ?_
    rw [natCard_hallCore_eq_natCard_hallCoreIn, ← hQ, hQcard']
    exact dvd_pow_self q hpp.pos.ne'
  have hTL : ∀ g : G, T ≠ CFSG.FeitThompson.Prep09.conjSub g L := by
    intro g hg
    have hg' : T = conjSubgroup L g := hg
    exact hneT g⁻¹ (by rw [hg', conjSubgroup_conjSubgroup_inv])
  have hsep := h₄ G hG'' L T hL hT hTL
  have hqL : q ∉ sigmaPrimes L := by
    intro hc
    rw [Set.eq_empty_iff_forall_notMem] at hsep
    exact hsep q ⟨hc, hqT⟩
  have hHq : (Nat.card ↥H).Coprime q := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 fun hdvd => hqL ?_)
    refine mem_sigmaPrimes_of_dvd_natCard_hallCore hL hqp ?_
    rw [natCard_hallCore_eq_natCard_hallCoreIn, ← hH]
    exact hdvd
  have hUL : U ≤ L := Subgroup.le_normalizer.trans hNU
  have hW₁U : W₁ ≤ normalizer (U : Set G) := hsdU.right_le.trans hsdU.le_normalizer
  have hW₁L : W₁ ≤ L := hW₁U.trans hNU
  have hUH : U ≤ H :=
    le_hallCore_of_frobenius hHL hUL hW₁L hHnorm hsdL'.coe_eq_mul.symm hsdL'.inf_eq_bot hHall
      hfreeL hHne hUne hcM.ne_bot_W₁ hW₁U hsdU.inf_eq_bot
      (fun w hw hw1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hffpU hw hw1)
      (hq ▸ hHq)
  refine ⟨hIL, ⟨E, hEne, hsdL', hfreeL⟩, hUH, ?_⟩
  obtain ⟨hnormW₁, hcentW₁, hsdQW₂⟩ := FBG_type_p_fixed_core_normalizer.{u} h₁ h₂ G hG T V W₂ W₁
    hT hcT
  have hQdef : hallCoreIn T = Q := hQ.symm
  have hsdQ : FreeCore.IsInternalSemidirectProduct (Q ⊔ W₂) Q W₂ := hQdef ▸ hsdQW₂
  have hNmul : (Q : Set G) * (W₂ : Set G) = ((normalizer (W₁ : Set G) : Subgroup G) : Set G) := by
    rw [hnormW₁, hcentW₁, hQdef]
  have hNeq : normalizer (W₁ : Set G) = Q ⊔ W₂ := by
    refine SetLike.coe_injective ?_
    rw [← hNmul, hsdQ.coe_eq_mul]
  have hQnorm : (Q.subgroupOf (normalizer (W₁ : Set G))).Normal := by
    rw [hNeq]; exact hsdQ.normal_subgroupOf
  obtain ⟨V₀, _, _, -, ⟨e⟩⟩ := hmodT
  have hQea : IsElementaryAbelian q Q :=
    hQdef ▸ isElementaryAbelian_of_mulEquiv_multiplicative e
  have hW₁Q : W₁ ≤ Q := hQdef ▸ hcT.le_hallCore_W₂
  rcases supporting_frobenius_complement_shape (G := G) (p := p) (q := q) hpp hqp hpq
      hQea hp.symm (odd_natCard_subgroup hG.odd_natCard L) hHne hEne hHL hEL hHnorm
      hsdL'.coe_eq_mul.symm hsdL'.inf_eq_bot hHnil hHall hfreeL (le_inf hW₁L hW₁Q) hq.symm hHq
      hNmul hsdQ.inf_eq_bot hQnorm with
    ⟨hmul, hdisj⟩ | ⟨y, hy, hmul, hdisj⟩
  · exact Or.inl (isInternalSemidirectProduct_of_coe_mul_coe_eq hHnorm hmul hdisj)
  · refine Or.inr ⟨y, hy, ?_⟩
    rw [conjSubgroup_eq_conj_smul]
    exact isInternalSemidirectProduct_of_coe_mul_coe_eq hHnorm hmul hdisj

end

end CFSG.FeitThompson.Proofs
