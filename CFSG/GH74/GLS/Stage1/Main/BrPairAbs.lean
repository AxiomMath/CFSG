module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.RankThree.Transfer.Yoshida
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
open scoped commutatorElement

section Abstract

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem isSubnormal_of_comm_normal {A B : Subgroup Γ} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hN : (A ⊔ B).Normal) : A.IsSubnormal := by
  have hAN : (A.subgroupOf (A ⊔ B)).Normal := by
    constructor
    intro n hn g
    obtain ⟨g, hg⟩ := g
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hg
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : a * b * (n : Γ) * (a * b)⁻¹ = a * n * a⁻¹ := by
      have hbn : b * (n : Γ) = (n : Γ) * b := (hcomm n hn b hb).symm
      calc a * b * (n : Γ) * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * n * a⁻¹ := by rw [hbn]; group
    show a * b * (n : Γ) * (a * b)⁻¹ ∈ A
    rw [e]
    exact A.mul_mem (A.mul_mem ha hn) (A.inv_mem ha)
  exact Subgroup.IsSubnormal.trans le_sup_left hAN.isSubnormal hN.isSubnormal

theorem comps_of_pair {A₁ A₂ : Subgroup Γ} (hQ₁ : IsQuasisimple ↥A₁) (hQ₂ : IsQuasisimple ↥A₂)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hN : (A₁ ⊔ A₂).Normal)
    (hC : ∀ γ : Γ, (∀ a ∈ A₁ ⊔ A₂, a * γ = γ * a) → γ ∈ A₁ ⊔ A₂) :
    {K : Subgroup Γ | IsComponent K} = {A₁, A₂} := by
  have hc₁ : IsComponent A₁ := ⟨hQ₁, isSubnormal_of_comm_normal hcomm hN⟩
  have hcomm' : ∀ b ∈ A₂, ∀ a ∈ A₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hN' : (A₂ ⊔ A₁).Normal := by rw [sup_comm]; exact hN
  have hc₂ : IsComponent A₂ := ⟨hQ₂, isSubnormal_of_comm_normal hcomm' hN'⟩
  ext K
  constructor
  · intro hK
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    have h1 : ⁅K, A₁⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hc₁).resolve_left hne.1
    have h2 : ⁅K, A₂⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hc₂).resolve_left hne.2
    have hKC : K ≤ A₁ ⊔ A₂ := by
      intro k hk
      apply hC
      intro a ha
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm ha
      have e1 : a₁ * k = k * a₁ := by
        have : ⁅k, a₁⁆ = 1 := by
          have hmem : ⁅k, a₁⁆ ∈ ⁅K, A₁⁆ := Subgroup.commutator_mem_commutator hk ha₁
          rw [h1] at hmem; simpa using hmem
        have := commutatorElement_eq_one_iff_mul_comm.1 this
        exact this.symm
      have e2 : a₂ * k = k * a₂ := by
        have : ⁅k, a₂⁆ = 1 := by
          have hmem : ⁅k, a₂⁆ ∈ ⁅K, A₂⁆ := Subgroup.commutator_mem_commutator hk ha₂
          rw [h2] at hmem; simpa using hmem
        have := commutatorElement_eq_one_iff_mul_comm.1 this
        exact this.symm
      calc a₁ * a₂ * k = a₁ * (a₂ * k) := by group
        _ = a₁ * (k * a₂) := by rw [e2]
        _ = (a₁ * k) * a₂ := by group
        _ = (k * a₁) * a₂ := by rw [e1]
        _ = k * (a₁ * a₂) := by group
    rcases eq_or_eq_of_isComponent_le_sup hK hc₁ hc₂ hKC with h | h
    · exact hne.1 h
    · exact hne.2 h
  · rintro (rfl | rfl)
    · exact hc₁
    · exact hc₂


theorem perfect_le_oResidual {Y : Type*} [Group Y] [Finite Y] (K : Subgroup Y) (hK : Group.IsPerfect K) :
    K ≤ oResidual 2 Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (oResidual 2 Y).Normal := oResidual_normal 2 Y
  have hQ : IsPGroup 2 (Y ⧸ oResidual 2 Y) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le (oResidual 2 Y) le_rfl
  let q : ↥K →* Y ⧸ oResidual 2 Y := (QuotientGroup.mk' (oResidual 2 Y)).comp K.subtype
  have hperf : Group.IsPerfect q.range := by
    have := hK
    exact Group.IsPerfect.ofSurjective (G := ↥K) (G' := ↥q.range) (f := q.rangeRestrict)
      q.rangeRestrict_surjective
  have hbot : q.range = ⊥ := by
    by_contra hne
    have : Nontrivial q.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hperf
    exact Group.IsPerfect.not_isNilpotent q.range ((hQ.to_subgroup q.range).isNilpotent)
  intro x hx
  have h1 : q ⟨x, hx⟩ = 1 := by
    have : q ⟨x, hx⟩ ∈ q.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem odd_index_oPrimeResidual' (Y : Type*) [Group Y] [Finite Y] :
    Odd (oPrimeResidual 2 Y).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hP : (P : Subgroup Y) ≤ oPrimeResidual 2 Y := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : (oPrimeResidual 2 Y).index ∣ (P : Subgroup Y).index := Subgroup.index_dvd_of_le hP
  have hnd : ¬ 2 ∣ (P : Subgroup Y).index := P.not_dvd_index
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 => hnd (h2.trans hdvd)))

theorem perfect_le_oPrimeResidual' {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : Group.IsPerfect K) : K ≤ oPrimeResidual 2 Y := by
  have : (oPrimeResidual 2 Y).Normal := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 Y
  have hodd : Odd (Nat.card (Y ⧸ oPrimeResidual 2 Y)) := odd_index_oPrimeResidual' Y
  have hsolv : Group.IsSolvable (Y ⧸ oPrimeResidual 2 Y) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have himg : K.map (QuotientGroup.mk' (oPrimeResidual 2 Y)) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Y))) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hK
    have : Group.IsPerfect ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Y))) :=
      Group.IsPerfect.map (QuotientGroup.mk' (oPrimeResidual 2 Y))
    exact Group.IsPerfect.not_isSolvable ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Y))) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg

theorem perfect_le_oPrimePResidual' {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : Group.IsPerfect K) : K ≤ oPrimePResidual 2 Y := by
  have hKY : K ≤ oPrimeResidual 2 Y := perfect_le_oPrimeResidual' hK
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf (oPrimeResidual 2 Y)) := by
    have e : ↥(K.subgroupOf (oPrimeResidual 2 Y)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKY
    exact Group.IsPerfect.ofSurjective (G := ↥K) (G' := ↥(K.subgroupOf (oPrimeResidual 2 Y)))
      (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 : K.subgroupOf (oPrimeResidual 2 Y) ≤ oResidual 2 ↥(oPrimeResidual 2 Y) :=
    perfect_le_oResidual _ hK'perf
  calc K = (K.subgroupOf (oPrimeResidual 2 Y)).map (oPrimeResidual 2 Y).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hKY).symm
    _ ≤ (oResidual 2 ↥(oPrimeResidual 2 Y)).map (oPrimeResidual 2 Y).subtype :=
        Subgroup.map_mono h1

end Abstract

section Abstract2

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem oResidual_sup_eq {Y : Type*} [Group Y] [Finite Y] {N T : Subgroup Y} (hN : N.Normal)
    (hperf : N ≤ oResidual 2 Y) (hT : IsPGroup 2 ↥T) (hY : N ⊔ T = ⊤) : oResidual 2 Y = N := by
  apply le_antisymm
  · have hQ : IsPGroup 2 (Y ⧸ N) := by
      have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp T.subtype) := by
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        have hy : y ∈ ((N ⊔ T : Subgroup Y) : Set Y) := by rw [hY]; trivial
        have := hN
        rw [Subgroup.normal_mul N T] at hy
        obtain ⟨n, hn, t, ht, rfl⟩ := hy
        refine ⟨⟨t, ht⟩, ?_⟩
        show QuotientGroup.mk t = QuotientGroup.mk (n * t)
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
      exact hT.of_surjective _ hsurj
    exact oResidual_le_of_isPGroup_quotient hQ
  · exact hperf

theorem oPrimePResidual_eq_pair {A₁ A₂ T : Subgroup Γ} (hP₁ : Group.IsPerfect ↥A₁)
    (hP₂ : Group.IsPerfect ↥A₂) (hN : (A₁ ⊔ A₂).Normal) (hT : IsPGroup 2 ↥T)
    (hY : oPrimeResidual 2 Γ = A₁ ⊔ A₂ ⊔ T) : oPrimePResidual 2 Γ = A₁ ⊔ A₂ := by
  have hN_le : A₁ ⊔ A₂ ≤ oPrimeResidual 2 Γ := by rw [hY]; exact le_sup_left
  have hT_le : T ≤ oPrimeResidual 2 Γ := by rw [hY]; exact le_sup_right
  have hA₁ : A₁ ≤ oPrimeResidual 2 Γ := le_sup_left.trans hN_le
  have hA₂ : A₂ ≤ oPrimeResidual 2 Γ := le_sup_right.trans hN_le
  have hperf : ∀ {A : Subgroup Γ} (hA : A ≤ oPrimeResidual 2 Γ), Group.IsPerfect ↥A →
      A.subgroupOf (oPrimeResidual 2 Γ) ≤ oResidual 2 ↥(oPrimeResidual 2 Γ) := by
    intro A hA hAp
    apply perfect_le_oResidual
    have e := Subgroup.subgroupOfEquivOfLe hA
    exact Group.IsPerfect.ofSurjective (G := ↥A) (G' := ↥(A.subgroupOf (oPrimeResidual 2 Γ)))
      (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 : (A₁ ⊔ A₂).subgroupOf (oPrimeResidual 2 Γ) ≤ oResidual 2 ↥(oPrimeResidual 2 Γ) := by
    rw [Subgroup.subgroupOf_sup hA₁ hA₂]
    exact sup_le (hperf hA₁ hP₁) (hperf hA₂ hP₂)
  have h2 : (A₁ ⊔ A₂).subgroupOf (oPrimeResidual 2 Γ) ⊔ T.subgroupOf (oPrimeResidual 2 Γ) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hN_le hT_le, ← hY]
    exact Subgroup.subgroupOf_self (oPrimeResidual 2 Γ)
  have hTp : IsPGroup 2 ↥(T.subgroupOf (oPrimeResidual 2 Γ)) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hT_le).symm
  have hNY : ((A₁ ⊔ A₂).subgroupOf (oPrimeResidual 2 Γ)).Normal := hN.subgroupOf _
  have := oResidual_sup_eq hNY h1 hTp h2
  unfold oPrimePResidual
  rw [this]
  exact Subgroup.map_subgroupOf_eq_of_le hN_le

theorem perfect_le_of_le_sup_pgroup {N T P : Subgroup Γ} (hN : N.Normal) (hT : IsPGroup 2 ↥T)
    (hP : Group.IsPerfect ↥P) (hPNT : P ≤ N ⊔ T) : P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : P.map (QuotientGroup.mk' N) ≤ T.map (QuotientGroup.mk' N) := by
    calc P.map (QuotientGroup.mk' N) ≤ (N ⊔ T).map (QuotientGroup.mk' N) := Subgroup.map_mono hPNT
      _ = N.map (QuotientGroup.mk' N) ⊔ T.map (QuotientGroup.mk' N) := Subgroup.map_sup _ _ _
      _ = T.map (QuotientGroup.mk' N) := by rw [QuotientGroup.map_mk'_self, bot_sup_eq]
  have hpT : IsPGroup 2 ↥(T.map (QuotientGroup.mk' N)) := hT.map (QuotientGroup.mk' N)
  have himg : P.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(P.map (QuotientGroup.mk' N)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hP
    have : Group.IsPerfect ↥(P.map (QuotientGroup.mk' N)) := Group.IsPerfect.map (QuotientGroup.mk' N)
    exact Group.IsPerfect.not_isNilpotent ↥(P.map (QuotientGroup.mk' N)) ((hpT.to_le hle).isNilpotent)
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg

omit [Finite Γ] in
theorem isComponent_map_subtype_of_le_normal {W N : Subgroup Γ} (hN : N.Normal) (hNW : N ≤ W)
    {H : Subgroup ↥W} (hH : IsComponent H) (hHN : H.map W.subtype ≤ N) :
    IsComponent (H.map W.subtype) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (H.equivMapOfInjective W.subtype W.subtype_injective) hH.1, ?_⟩
  have h1 : (H.subgroupOf (N.subgroupOf W)).IsSubnormal := hH.2.subgroupOf
  let e : ↥(N.subgroupOf W) ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNW
  have h2 : ((H.subgroupOf (N.subgroupOf W)).map e.toMonoidHom).IsSubnormal :=
    h1.map (f := e.toMonoidHom) e.surjective
  have h3 : (H.subgroupOf (N.subgroupOf W)).map e.toMonoidHom = (H.map W.subtype).subgroupOf N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(y : ↥W), hy, rfl⟩
    · intro hx
      obtain ⟨w, hw, hwx⟩ := hx
      have hwN : w ∈ N.subgroupOf W := by
        show (w : Γ) ∈ N
        rw [show (w : Γ) = (x : Γ) from hwx]
        exact x.2
      exact ⟨⟨w, hwN⟩, hw, Subtype.ext hwx⟩
  rw [h3] at h2
  exact Subgroup.IsSubnormal.trans hHN h2 hN.isSubnormal

end Abstract2

end CFSG.GH74.GLS.Stage1.Main
