module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Exc

open Subgroup CFSG CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.GH74.GLS.IVK.GHInv
  CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

instance instNormalI₁ (S : Shape Y F₁ F₂) : S.I₁.Normal := normal_I₁ S

instance instNormalI₂ (S : Shape Y F₁ F₂) : S.I₂.Normal := normal_I₂ S

theorem isSolvable_quot_of_solvable_I₂ (S : Shape Y F₁ F₂) (h₂ : Group.IsSolvable ↥S.I₂) :
    Group.IsSolvable (Y ⧸ S.I₁) := by
  set π := QuotientGroup.mk' S.I₁ with hπ
  set P : Subgroup (Y ⧸ S.I₁) := S.I₂.map π with hP
  have hPn : P.Normal := (instNormalI₂ S).map π (QuotientGroup.mk'_surjective _)
  have hPs : Group.IsSolvable ↥P :=
    Group.isSolvable_of_surjective (f := π.subgroupMap S.I₂) (π.subgroupMap_surjective S.I₂)
  have hJn : (S.I₁ ⊔ S.I₂).Normal := inferInstance
  have hcomm : ∀ a b : (Y ⧸ S.I₁) ⧸ P, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective b'
    have hmem : ⁅y₁, y₂⁆ ∈ S.I₁ ⊔ S.I₂ :=
      commutator_mem_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) (t := S.t) S.gen y₁ y₂
    have hmem' : π ⁅y₁, y₂⁆ ∈ P := by
      rw [Subgroup.mem_sup_of_normal_left] at hmem
      obtain ⟨j, hj, k, hk, hjk⟩ := hmem
      have hj1 : π j = 1 := (QuotientGroup.eq_one_iff j).2 hj
      rw [← hjk, map_mul, hj1, one_mul]
      exact ⟨k, hk, rfl⟩
    have h1 : (QuotientGroup.mk' P) (π ⁅y₁, y₂⁆) = 1 := (QuotientGroup.eq_one_iff _).2 hmem'
    rw [map_commutatorElement, map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hq : Group.IsSolvable ((Y ⧸ S.I₁) ⧸ P) := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_ker_le_range P.subtype (QuotientGroup.mk' P)
    (by rw [QuotientGroup.ker_mk']; intro x hx; exact ⟨⟨x, hx⟩, rfl⟩)

theorem isSolvable_of_solvable_factors (S : Shape Y F₁ F₂) (h₁ : Group.IsSolvable ↥S.I₁)
    (h₂ : Group.IsSolvable ↥S.I₂) : Group.IsSolvable Y := by
  have := isSolvable_quot_of_solvable_I₂ S h₂
  exact Group.isSolvable_of_ker_le_range S.I₁.subtype (QuotientGroup.mk' S.I₁)
    (by rw [QuotientGroup.ker_mk']; intro x hx; exact ⟨⟨x, hx⟩, rfl⟩)

theorem not_comm_of_perfect {A : Subgroup Y} [Group.IsPerfect ↥A] [Nontrivial ↥A] :
    ¬ ∀ b ∈ A, ∀ b' ∈ A, b * b' = b' * b := fun hab =>
  Group.IsPerfect.not_isSolvable ↥A
    (Group.isSolvable_of_comm fun u v => Subtype.ext (hab u u.2 v v.2))

variable [Finite Y]

theorem pComponent_eq_I₁_of_solvable_I₂ (S : Shape Y F₁ F₂) (hq₁ : CFSG.IsQuasisimple ↥S.I₁)
    (h₂ : Group.IsSolvable ↥S.I₂) {A : Subgroup Y} (hA : CFSG.IsPComponent 2 A) : A = S.I₁ := by
  have hn₁ := normal_I₁ S
  have := isSolvable_quot_of_solvable_I₂ S h₂
  have hperf : Group.IsPerfect ↥A := CatalogueBAlternating.pComponent_perfect hA
  have hnt : Nontrivial ↥A := CatalogueBAlternating.pComponent_nontrivial hA
  have hle : A ≤ S.I₁ := CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient S.I₁ A
  have hI : CFSG.IsComponent S.I₁ := ⟨hq₁, hn₁.isSubnormal⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hI hA.choose_spec.2.1 with h | h
  · exact le_antisymm hle h
  · exfalso
    apply not_comm_of_perfect (A := A)
    intro b hb b' hb'
    have h3 : ⁅b', b⁆ ∈ ⁅S.I₁, A⁆ := Subgroup.commutator_mem_commutator (hle hb') hb
    rw [h, Subgroup.mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm

theorem commute_pPrimeCore {I : Subgroup Y} (hI : I.Normal) (hbot : pPrimeCore 2 ↥I = ⊥)
    {n a : Y} (hn : n ∈ pPrimeCore 2 Y) (ha : a ∈ I) : n * a = a * n := by
  have hN : (pPrimeCore 2 Y).Normal := inferInstance
  have hsub : (pPrimeCore 2 Y).subgroupOf I = ⊥ := by
    refine (pPrimeCore_eq_bot_iff.1 hbot) _ inferInstance ?_
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ I.subtype_injective)
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := Y))
  have hc : ⁅n, a⁆ ∈ pPrimeCore 2 Y ⊓ I := by
    refine ⟨?_, ?_⟩
    · have h1 : a * n⁻¹ * a⁻¹ ∈ pPrimeCore 2 Y := hN.conj_mem _ (inv_mem hn) a
      have h2 : n * (a * n⁻¹ * a⁻¹) ∈ pPrimeCore 2 Y := mul_mem hn h1
      convert h2 using 1
      simp [commutatorElement_def, mul_assoc]
    · have h1 : n * a * n⁻¹ ∈ I := hI.conj_mem a ha n
      have h2 : n * a * n⁻¹ * a⁻¹ ∈ I := mul_mem h1 (inv_mem ha)
      convert h2 using 1
  have h3 : (⟨⁅n, a⁆, hc.2⟩ : ↥I) ∈ (pPrimeCore 2 Y).subgroupOf I := hc.1
  rw [hsub, Subgroup.mem_bot] at h3
  have h4 : ⁅n, a⁆ = 1 := congrArg Subtype.val h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h4

theorem pComponent_eq_I (S : Shape Y F₁ F₂) (hq₁ : CFSG.IsQuasisimple ↥S.I₁)
    (hq₂ : CFSG.IsQuasisimple ↥S.I₂) (hb₁ : pPrimeCore 2 ↥S.I₁ = ⊥)
    (hb₂ : pPrimeCore 2 ↥S.I₂ = ⊥) {A : Subgroup Y} (hA : CFSG.IsPComponent 2 A) :
    A = S.I₁ ∨ A = S.I₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn₁ := instNormalI₁ S
  have hn₂ := instNormalI₂ S
  have hperf : Group.IsPerfect ↥A := CatalogueBAlternating.pComponent_perfect hA
  have hnt : Nontrivial ↥A := CatalogueBAlternating.pComponent_nontrivial hA
  have hsub : A.IsSubnormal := hA.choose_spec.2.1
  have hAN : A ≤ S.I₁ ⊔ S.I₂ :=
    le_of_perfect_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) (t := S.t) S.gen
      (Subgroup.isPerfect_iff.mp hperf)
  have hcomm : ∀ n ∈ pPrimeCore 2 Y, ∀ a ∈ S.I₁ ⊔ S.I₂, n * a = a * n := by
    intro n hn
    have hle : S.I₁ ⊔ S.I₂ ≤ Subgroup.centralizer ({n} : Set Y) :=
      sup_le
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (commute_pPrimeCore hn₁ hb₁ hn ha).symm)
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (commute_pPrimeCore hn₂ hb₂ hn ha).symm)
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ha)).symm
  have hcen : pPrimeCore 2 ↥A ≤ Subgroup.center ↥A := by
    intro u hu
    have hu' : ((u : ↥A) : Y) ∈ A ⊓ pPrimeCore 2 Y := by
      rw [← UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub]
      exact ⟨u, hu, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hcomm _ hu'.2 _ (hAN g.2)).symm
  have hAq : CFSG.IsQuasisimple ↥A :=
    ((CatalogueBPrimeJoin.p_component_core_centrality_criterion hA).1).2 hcen
  have hAc : CFSG.IsComponent A := ⟨hAq, hsub⟩
  have D : ∀ I : Subgroup Y, I.Normal → CFSG.IsQuasisimple ↥I → A = I ∨ ⁅A, I⁆ = ⊥ := by
    intro I hI hq
    have hIc : CFSG.IsComponent I := ⟨hq, hI.isSubnormal⟩
    have hIperf : Group.IsPerfect ↥I := hq.1
    have hInt : Nontrivial ↥I := CFSG.LocalCores.isQuasisimple_nontrivial hq
    rcases CFSG.LocalCores.component_subnormal_subgroup hIc hsub with h1 | h1 <;>
    rcases CFSG.LocalCores.component_normal_subgroup hAc hI with h2 | h2
    · exact Or.inl (le_antisymm h2 h1)
    · exfalso
      apply not_comm_of_perfect (A := I)
      intro b hb b' hb'
      have h3 : ⁅b', b⁆ ∈ ⁅A, I⁆ := Subgroup.commutator_mem_commutator (h1 hb') hb
      rw [h2, Subgroup.mem_bot] at h3
      exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    · exfalso
      apply not_comm_of_perfect (A := A)
      intro b hb b' hb'
      have h3 : ⁅b', b⁆ ∈ ⁅I, A⁆ := Subgroup.commutator_mem_commutator (h2 hb') hb
      rw [h1, Subgroup.mem_bot] at h3
      exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    · exact Or.inr h2
  rcases D S.I₁ hn₁ hq₁ with h1 | h1
  · exact Or.inl h1
  rcases D S.I₂ hn₂ hq₂ with h2 | h2
  · exact Or.inr h2
  exfalso
  apply not_comm_of_perfect (A := A)
  intro b hb b' hb'
  have hc : S.I₁ ⊔ S.I₂ ≤ Subgroup.centralizer ({b} : Set Y) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · have h3 : ⁅b, a⁆ ∈ ⁅A, S.I₁⁆ := Subgroup.commutator_mem_commutator hb ha
      rw [h1, Subgroup.mem_bot] at h3
      exact Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    · have h3 : ⁅b, a⁆ ∈ ⁅A, S.I₂⁆ := Subgroup.commutator_mem_commutator hb ha
      rw [h2, Subgroup.mem_bot] at h3
      exact Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hc (hAN hb'))).symm

omit [Finite Y] in
theorem pPrimeCore_eq_bot_of_equiv_sl2 {I : Subgroup Y} {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : ↥I ≃* SL(2, F)) :
    pPrimeCore 2 ↥I = ⊥ := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have h := CFSG.pPrimeCore_map_iso 2 e
  rw [CatFactsSp4.pPrimeCore_SL2 h2 h4] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Exc
