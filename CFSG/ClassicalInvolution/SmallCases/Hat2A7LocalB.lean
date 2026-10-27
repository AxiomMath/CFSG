module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Reduction

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ComponentClassification
open scoped commutatorElement

section Closure

variable {F : Type} [Group F]

theorem normalClosureIn2A7_subgroupOf_normal {C S : Subgroup F} (hS : S ≤ C) :
    ((normalClosureIn2A7 C S).subgroupOf C).Normal := by
  have key : ∀ k ∈ C, (normalClosureIn2A7 C S).map (MulAut.conj k).toMonoidHom ≤
      normalClosureIn2A7 C S := by
    intro k hk
    unfold normalClosureIn2A7
    rw [Subgroup.map_iSup]
    refine iSup_le fun c => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hc => ?_
    rw [map_map_conj]
    exact le_iSup₂_of_le (k * c) (C.mul_mem hk hc) le_rfl
  rw [Subgroup.normal_subgroupOf_iff (normalClosureIn2A7_le hS)]
  intro h k hh hk
  exact key k hk ⟨h, hh, rfl⟩

end Closure

section Ordinary

variable {F : Type} [Group F]

@[expose] def A7TwoComponentOrdinary (F : Type) [Group F] : Prop :=
  ∀ x : F, orderOf x = 2 → ∀ (N : Subgroup F) (w : F),
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) N w →
    ∀ M : Subgroup ↥(Subgroup.centralizer ({x} : Set F)), TwoComponents.IsTwoComponent M →
      N.subgroupOf (Subgroup.centralizer ({x} : Set F)) ≤ M → IsComponentOf M ⊤

theorem A7TwoComponentOrdinary.of_localB [Finite F] (h : LocalB.LocalBProperty F) :
    A7TwoComponentOrdinary F :=
  fun x hx _ _ _ M hM _ => LocalB.ordinary_at_involution h x hx M hM

end Ordinary

section Centralize

variable {F : Type} [Group F] [Finite F]

theorem IsClassical2A7.commute_oddCore_of_component {C N : Subgroup F} {w : F}
    (hN : IsClassical2A7 C N w)
    (hB : ∀ M : Subgroup ↥C, TwoComponents.IsTwoComponent M → N.subgroupOf C ≤ M →
      IsComponentOf M ⊤)
    (d n : ↥C) (hd : d ∈ componentClassificationOddCore ↥C) (hn : (n : F) ∈ N) :
    n * d = d * n := by
  have hNC : N ≤ C := hN.le
  have hcl := hN.subgroupOf hNC le_rfl
  have hz2 : orderOf (⟨w, hNC hN.mem⟩ : ↥C) = 2 := hcl.orderOf_eq_two
  have hzL : (⟨w, hNC hN.mem⟩ : ↥C) ∈ N.subgroupOf C := hcl.mem
  have hperf : commutator (N.subgroupOf C) = ⊤ := hcl.perfect.commutator_eq_top
  have hsub : IsSubnormal (N.subgroupOf C)
      (Subgroup.centralizer ({(⟨w, hNC hN.mem⟩ : ↥C)} : Set ↥C)) := by
    have h1 := hcl.subnormal
    rwa [top_inf_eq] at h1
  have hq : CFSG.Open.IsQuasisimple
      ((N.subgroupOf C) ⧸ componentClassificationOddCore (N.subgroupOf C)) := hcl.witness.1
  obtain ⟨K, ⟨hK, hNK⟩, -⟩ :=
    existsUnique_isTwoComponent_of_l2PrimeBalance l2PrimeBalance hz2 hzL hperf hsub hq
  have hcomp : IsComponentOf K ⊤ := hB K hK hNK
  have hsolv : Group.IsSolvable ↥(componentClassificationOddCore ↥C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (OddCore.odd_card _)
  have hOsub : IsSubnormal (componentClassificationOddCore ↥C) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hcomm := LocalComponents.commutes_with_solvable_subnormal K _ hcomp hOsub
  have hnK : n ∈ K := hNK (Subgroup.mem_subgroupOf.mpr hn)
  have hmem := Subgroup.commutator_mem_commutator hnK hd
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem oddCore_normalClosure_le {C S : Subgroup F} (hS : S ≤ C)
    (e : ↥(normalClosureIn2A7 C S))
    (he : e ∈ componentClassificationOddCore ↥(normalClosureIn2A7 C S)) :
    ∃ h : (e : F) ∈ C, (⟨(e : F), h⟩ : ↥C) ∈ componentClassificationOddCore ↥C := by
  have hsub : IsSubnormal (normalClosureIn2A7 C S) C :=
    isSubnormal_of_normal_subgroupOf (normalClosureIn2A7_le hS)
      (normalClosureIn2A7_subgroupOf_normal hS)
  exact (OddCore.subnormal_mem_iff hsub (e : F) e.2).mp he

theorem oddCore_normalClosure_le_center {C L M : Subgroup F} {u v : F}
    (hL : IsClassical2A7 C L u) (hM : IsClassical2A7 C M v)
    (h : ∀ (N : Subgroup F) (w : F), IsClassical2A7 C N w →
      ∀ (d n : ↥C), d ∈ componentClassificationOddCore ↥C → (n : F) ∈ N → n * d = d * n) :
    classicalInvolutionOddCore ↥(normalClosureIn2A7 C (L ⊔ M)) ≤
      Subgroup.center ↥(normalClosureIn2A7 C (L ⊔ M)) := by
  have hLM : L ⊔ M ≤ C := sup_le hL.le hM.le
  intro e he
  obtain ⟨heC, heO⟩ := oddCore_normalClosure_le hLM e he
  have hgen : normalClosureIn2A7 C (L ⊔ M) ≤ Subgroup.centralizer ({(e : F)} : Set F) := by
    refine normalClosureIn2A7_le_of fun c hc => ?_
    rw [Subgroup.map_sup]
    have key : ∀ {N : Subgroup F} {w : F}, IsClassical2A7 C N w →
        N.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer ({(e : F)} : Set F) := by
      intro N w hN n hn
      have h1 := hN.conj c
      rw [map_conj_eq_of_mem hc] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := h _ _ h1 ⟨(e : F), heC⟩ ⟨n, h1.le hn⟩ heO hn
      exact congrArg Subtype.val this
    exact sup_le (key hL) (key hM)
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hgen y.2))

end Centralize

section LocalP1

variable {F : Type} [Group F] [Finite F]

theorem localOddCentral2A7_of_ordinary (hB : A7TwoComponentOrdinary F) :
    LocalOddCentral2A7 F := by
  intro x hx _ L M u v hL hM
  exact oddCore_normalClosure_le_center hL hM fun N w hN d n hd hn =>
    IsClassical2A7.commute_oddCore_of_component hN (hB x hx N w hN) d n hd hn

end LocalP1

@[expose] def A7BStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassical2A7 ⊤ K z → CITBelow2A7 (Nat.card G) →
      A7TwoComponentOrdinary G

theorem localOddCentralStep2A7_of_B (h : A7BStep) : LocalOddCentralStep2A7 :=
  fun G _ _ _ hnab K z hK hB => localOddCentral2A7_of_ordinary (h G hnab K z hK hB)

theorem cit2A7_of_B (h : GoldschmidtMilestone) (TW : TwinExclusion) (BS : A7BStep) : CIT2A7 :=
  cit2A7_of_remaining_inputs h TW (localOddCentralStep2A7_of_B BS)

end CFSG.ClassicalInvolution.Hat2A7
