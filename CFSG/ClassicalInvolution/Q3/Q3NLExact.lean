module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyLink
public import CFSG.ClassicalInvolution.Q3.Induction

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups

section Core

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z c : G}

@[expose] def exactCore3 (c : G) (K : Subgroup G) : Subgroup G :=
  K ⊓ Subgroup.centralizer ({c} : Set G)

theorem exactCore3_le_left (c : G) (K : Subgroup G) : exactCore3 c K ≤ K := inf_le_left

theorem exactCore3_le_centralizer (c : G) (K : Subgroup G) :
    exactCore3 c K ≤ Subgroup.centralizer ({c} : Set G) := inf_le_right

theorem axisResidual_exactCore3 (hK : IsClassicalMember3 K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) :
    AxisResidual K (Subgroup.zpowers c) (exactCore3 c K) z := by
  have hcen := isCentralInvolution_of_isClassicalMember3 hK
  have h := axisResidual_centralizer hK.mem hcen.sq (fun x hx => (hcen.central x hx).symm)
    hK.subnormal hc2 (Subgroup.zpowers_le.mpr hcK)
  simpa only [exactCore3, centralizer_zpowers_eq_singleton'] using h

end Core

section SectionMember

variable {G : Type} [Group G] {z : G}

structure IsSectionMember3 (Y K : Subgroup G) (z : G) : Prop where
  le : K ≤ Y
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ K
  subnormal : IsSubnormal K (Subgroup.centralizer ({z} : Set G) ⊓ Y)
  nonempty_equiv : Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, ZMod 3))

namespace IsSectionMember3

variable {Y K : Subgroup G}

theorem restrict (h : IsSectionMember3 Y K z) {H : Subgroup G} (hHY : H ≤ Y) (hKH : K ≤ H) :
    IsSectionMember3 H K z :=
  { h with
    le := hKH
    subnormal := by
      have h1 := isSubnormal_inf h.subnormal H
      rwa [inf_eq_left.mpr hKH, inf_assoc, inf_eq_right.mpr hHY] at h1 }

theorem toIn (h : IsSectionMember3 Y K z) : IsClassicalMember3In Y K z := by
  have hzY : z ∈ Y := h.le h.mem
  have e : K.subgroupOf Y ≃* K := Subgroup.subgroupOfEquivOfLe h.le
  refine ⟨hzY, ?_, Subgroup.mem_subgroupOf.mpr h.mem, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact h.orderOf_eq_two
  · have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y =
        Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h.subnormal Y
  · obtain ⟨e'⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore (K.subgroupOf Y)).map e.toMonoidHom =
        classicalInvolutionOddCore K :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).trans e'⟩

end IsSectionMember3

theorem isSectionMember3_of_axisResidual {J A I : Subgroup G} (hJ : IsClassicalMember3 J z)
    (h : AxisResidual J A I z) : IsSectionMember3 (Subgroup.centralizer (A : Set G)) I z where
  le := h.le_inf.trans inf_le_right
  orderOf_eq_two := hJ.orderOf_eq_two
  mem := h.mem
  subnormal := h.subnormal
  nonempty_equiv := by
    obtain ⟨e'⟩ := hJ.nonempty_equiv
    obtain ⟨φ⟩ := h.nonempty_equiv
    exact ⟨φ.trans e'⟩

end SectionMember

section CoreProperties

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z c : G}
  (hK : IsClassicalMember3 K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
  (hcK : c ∈ trivialOnQuot K)
include hK hc2 hcK

theorem exactCore3_cover : ∀ x ∈ K, ∃ i ∈ exactCore3 c K, ∃ n ∈ oddCoreIn K, x = i * n :=
  (axisResidual_exactCore3 hK hc2 hcK).cover

theorem mem_exactCore3 : z ∈ exactCore3 c K :=
  (axisResidual_exactCore3 hK hc2 hcK).mem

theorem mul_comm_of_mem_trivialOnQuot : c * z = z * c :=
  (Subgroup.mem_centralizer_singleton_iff.mp (exactCore3_le_centralizer c K
    (mem_exactCore3 hK hc2 hcK))).symm

theorem oddCoreIn_exactCore3 : oddCoreIn (exactCore3 c K) = exactCore3 c K ⊓ oddCoreIn K :=
  (axisResidual_exactCore3 hK hc2 hcK).oddCoreIn_eq

theorem nonempty_equiv_exactCore3 :
    Nonempty (↥(exactCore3 c K) ⧸ classicalInvolutionOddCore ↥(exactCore3 c K) ≃*
      ↥K ⧸ classicalInvolutionOddCore ↥K) :=
  (axisResidual_exactCore3 hK hc2 hcK).nonempty_equiv

theorem isSectionMember3_exactCore3 :
    IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) (exactCore3 c K) z := by
  have h := isSectionMember3_of_axisResidual hK (axisResidual_exactCore3 hK hc2 hcK)
  simpa only [centralizer_zpowers_eq_singleton'] using h

theorem isClassicalMember3In_exactCore3 {Y : Subgroup G} (hY : exactCore3 c K ≤ Y)
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) :
    IsClassicalMember3In Y (exactCore3 c K) z :=
  ((isSectionMember3_exactCore3 hK hc2 hcK).restrict hYc hY).toIn

theorem mem_trivialOnQuot_exactCore3 {b : G} (hb : b ∈ trivialOnQuot K)
    (hbc : b ∈ Subgroup.centralizer ({c} : Set G)) : b ∈ trivialOnQuot (exactCore3 c K) := by
  refine ⟨mem_normalizer_inf hb.1 (Subgroup.le_normalizer hbc), fun x hx => ?_⟩
  rw [oddCoreIn_exactCore3 hK hc2 hcK]
  have hxK : x ∈ K := exactCore3_le_left c K hx
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c K hx
  refine ⟨⟨?_, ?_⟩, hb.2 x hxK⟩
  · have h1 : ⁅b, x⁆ = b * x * b⁻¹ * x⁻¹ := rfl
    rw [h1]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hb.1 x).mp hxK) (K.inv_mem hxK)
  · have h1 : ⁅b, x⁆ = b * x * b⁻¹ * x⁻¹ := rfl
    rw [h1]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hbc hxc)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hbc))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hxc)

end CoreProperties

section Action

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z c : G}

theorem exactCore3_conjSub (g c : G) (K : Subgroup G) :
    exactCore3 (g * c * g⁻¹) (conjSub g K) = conjSub g (exactCore3 c K) := by
  unfold exactCore3
  have h2 : conjSub g (K ⊓ Subgroup.centralizer ({c} : Set G)) =
      conjSub g K ⊓ conjSub g (Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.map_inf_eq _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [conjSub_centralizer_singleton] at h2
  exact h2.symm

omit [Finite G] in
theorem exactCore3_eq_self (hKc : K ≤ Subgroup.centralizer ({c} : Set G)) :
    exactCore3 c K = K :=
  inf_eq_left.mpr hKc

theorem le_trivialOnQuot_exactCore3 (hK : IsClassicalMember3 K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) {B : Subgroup G}
    (hBc : B ≤ Subgroup.centralizer ({c} : Set G)) (hB : B ≤ trivialOnQuot K) :
    B ≤ trivialOnQuot (exactCore3 c K) := fun _ hb =>
  mem_trivialOnQuot_exactCore3 hK hc2 hcK (hB hb) (hBc hb)

theorem mem_trivialOnQuot_exactCore3_self (c : G) (K : Subgroup G) :
    c ∈ trivialOnQuot (exactCore3 c K) :=
  mem_trivialOnQuot_of_centralizes fun _ hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (exactCore3_le_centralizer c K hx)).symm

end Action

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {K K' : Subgroup G}

@[expose] def tqMembers3 (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  {K | K ∈ Ω ∧ c ∈ trivialOnQuot K}

@[expose] def exactFamily3 (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  {K' | ∃ K ∈ tqMembers3 Ω c, K' = exactCore3 c K}

theorem mem_tqMembers3_iff : K ∈ tqMembers3 Ω c ↔ K ∈ Ω ∧ c ∈ trivialOnQuot K := Iff.rfl

theorem mem_exactFamily3_iff :
    K' ∈ exactFamily3 Ω c ↔ ∃ K ∈ tqMembers3 Ω c, K' = exactCore3 c K := Iff.rfl

theorem exactCore3_mem_exactFamily3 (hK : K ∈ tqMembers3 Ω c) :
    exactCore3 c K ∈ exactFamily3 Ω c :=
  ⟨K, hK, rfl⟩

theorem le_centralizer_of_mem_exactFamily3 (hK' : K' ∈ exactFamily3 Ω c) :
    K' ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨K, -, rfl⟩ := hK'
  exact exactCore3_le_centralizer c K

theorem mem_tqMembers3_of_le_centralizer (hK : K ∈ Ω)
    (hKc : K ≤ Subgroup.centralizer ({c} : Set G)) : K ∈ tqMembers3 Ω c :=
  ⟨hK, mem_trivialOnQuot_of_centralizes fun _ hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKc hx)).symm⟩

theorem mem_exactFamily3_of_le_centralizer (hK : K ∈ Ω)
    (hKc : K ≤ Subgroup.centralizer ({c} : Set G)) : K ∈ exactFamily3 Ω c :=
  ⟨K, mem_tqMembers3_of_le_centralizer hK hKc, (exactCore3_eq_self hKc).symm⟩

theorem conjSub_mem_tqMembers3 (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) (hK : K ∈ tqMembers3 Ω c) :
    conjSub n K ∈ tqMembers3 Ω c := by
  refine ⟨hΩ n K hK.1, ?_⟩
  have h := trivialOnQuot_conjSub hK.2 n
  rwa [conj_eq_of_mem_centralizer_singleton hn] at h

theorem conjSub_mem_exactFamily3 (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) (hK' : K' ∈ exactFamily3 Ω c) :
    conjSub n K' ∈ exactFamily3 Ω c := by
  obtain ⟨K, hK, rfl⟩ := hK'
  refine ⟨conjSub n K, conjSub_mem_tqMembers3 hΩ hn hK, ?_⟩
  have h := exactCore3_conjSub n c K
  rw [conj_eq_of_mem_centralizer_singleton hn] at h
  exact h.symm

end Family

section SecData

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

structure SecData3 (a : G) (Φ : Set (Subgroup G)) : Prop where
  nonempty : Φ.Nonempty
  le : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G)
  conj : ∀ n ∈ Subgroup.centralizer ({a} : Set G), ∀ K ∈ Φ, conjSub n K ∈ Φ
  member : ∀ K ∈ Φ, ∃ z, IsSectionMember3 (Subgroup.centralizer ({a} : Set G)) K z

theorem inClass3_of_isClassicalMember3In {H : Subgroup G} {𝒮 : Set (Subgroup G)}
    (hne : 𝒮.Nonempty) (hle : ∀ L ∈ 𝒮, L ≤ H) (hconj : ∀ n ∈ H, ∀ L ∈ 𝒮, conjSub n L ∈ 𝒮)
    (hgen : (⨆ L ∈ 𝒮, L) = H) (hcl : ∀ L ∈ 𝒮, ∃ z, IsClassicalMember3In H L z) :
    InClass3 (restrictFamily 𝒮 H) where
  nonempty := by
    obtain ⟨L, hL⟩ := hne
    exact ⟨L.subgroupOf H, L, hL, hle L hL, rfl⟩
  conjInvariant := by
    rintro n _ ⟨L, hL, hLH, rfl⟩
    exact ⟨conjSub (n : G) L, hconj n n.2 L hL, hle _ (hconj n n.2 L hL),
      conjSub_subgroupOf _ n L⟩
  generated := by
    have key := iSup_subgroupOf_self (G := G) (fun i : 𝒮 => (i : Subgroup G))
    have hsup : (⨆ i : 𝒮, (i : Subgroup G)) = H := by
      rw [← hgen, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup H) (_ : L' ∈ restrictFamily 𝒮 H) => L')
      ((i : Subgroup G).subgroupOf H) ⟨i, i.2, hle i i.2, rfl⟩
  classical := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    obtain ⟨z, hz, hcl'⟩ := hcl L hL
    exact ⟨⟨z, hz⟩, hcl'⟩

namespace SecData3

variable (h : SecData3 a Φ)
include h

theorem centralizingMembers_eq : centralizingMembers Φ {a} = Φ := by
  ext K
  exact ⟨fun hK => hK.1, fun hK => ⟨hK, h.le K hK⟩⟩

theorem inClass3 :
    InClass3 (restrictFamily (centralizingMembers Φ {a}) (centralizingLayer Φ {a})) := by
  refine inClass3_of_isClassicalMember3In (H := centralizingLayer Φ {a})
    (𝒮 := centralizingMembers Φ {a}) ?_ (fun L hL => le_centralizingLayer hL) ?_ rfl ?_
  · obtain ⟨K, hK⟩ := h.nonempty
    exact ⟨K, ⟨hK, h.le K hK⟩⟩
  · intro n hn L hL
    have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Φ {a} hn
    exact ⟨h.conj n hnC L hL.1, h.le _ (h.conj n hnC L hL.1)⟩
  · intro L hL
    obtain ⟨z, hz⟩ := h.member L hL.1
    exact ⟨z, (hz.restrict (centralizingLayer_le_centralizer Φ {a})
      (le_centralizingLayer hL)).toIn⟩

end SecData3

end SecData

section Pair


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {K : Subgroup G}

theorem secData3_exactFamily (hΩ : InClass3 Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) : SecData3 c (exactFamily3 Ω c) := by
  refine ⟨?_, fun K' hK' => le_centralizer_of_mem_exactFamily3 hK',
    fun n hn K' hK' => conjSub_mem_exactFamily3 hΩ.conjInvariant hn hK', ?_⟩
  · obtain ⟨K, hK⟩ := hne
    exact ⟨exactCore3 c K, exactCore3_mem_exactFamily3 hK⟩
  · rintro K' ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical K hK.1
    exact ⟨z, isSectionMember3_exactCore3 hz hc2 hK.2⟩

abbrev exactLayer3 (Ω : Set (Subgroup G)) (c : G) : Subgroup G :=
  centralizingLayer (exactFamily3 Ω c) {c}

abbrev exactPair3 (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup ↥(exactLayer3 Ω c)) :=
  restrictFamily (centralizingMembers (exactFamily3 Ω c) {c}) (exactLayer3 Ω c)

theorem exactFamily3_eq_empty_of_not_nonempty (hne : ¬ (tqMembers3 Ω c).Nonempty) :
    exactFamily3 Ω c = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨K, hK, _⟩ => hne ⟨K, hK⟩

theorem centralizingMembers_exactFamily3 (Ω : Set (Subgroup G)) (c : G) :
    centralizingMembers (exactFamily3 Ω c) {c} = exactFamily3 Ω c := by
  ext K'
  exact ⟨fun h => h.1, fun h => ⟨h, le_centralizer_of_mem_exactFamily3 h⟩⟩

theorem exactLayer3_le_centralizer (Ω : Set (Subgroup G)) (c : G) :
    exactLayer3 Ω c ≤ Subgroup.centralizer ({c} : Set G) :=
  centralizingLayer_le_centralizer _ _

theorem exactCore3_le_exactLayer3 (hK : K ∈ tqMembers3 Ω c) :
    exactCore3 c K ≤ exactLayer3 Ω c :=
  le_centralizingLayer ⟨exactCore3_mem_exactFamily3 hK, exactCore3_le_centralizer c K⟩

theorem inClass3_exactPair3 (hΩ : InClass3 Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) : InClass3 (exactPair3 Ω c) :=
  (secData3_exactFamily hΩ hc2 hne).inClass3

theorem exactLayer3_eq_bot_of_not_nonempty (hne : ¬ (tqMembers3 Ω c).Nonempty) :
    exactLayer3 Ω c = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun K' hK' => ?_)
  obtain ⟨K, hK, -⟩ := hK'.1
  exact (hne ⟨K, hK⟩).elim

theorem lieSystemMod3_exactPair3 (hΩ : InClass3 Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hBelow : CIT3Below (Nat.card G)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) :
    LieSystemMod3 (exactPair3 Ω c) := by
  by_cases hne : (tqMembers3 Ω c).Nonempty
  · exact hBelow _ (card_centralizingLayer_lt _ hnc) _ (inClass3_exactPair3 hΩ hc2 hne)
  · have hbot := exactLayer3_eq_bot_of_not_nonempty hne
    have hfam := exactFamily3_eq_empty_of_not_nonempty hne
    have hrf : exactPair3 Ω c = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun K' ⟨L, hL, _⟩ => ?_
      rw [centralizingMembers_exactFamily3, hfam] at hL
      exact hL
    have hsub : Subsingleton ↥(exactLayer3 Ω c) := by rw [hbot]; infer_instance
    have hq : Subsingleton (↥(exactLayer3 Ω c) ⧸ classicalInvolutionOddCore ↥(exactLayer3 Ω c)) :=
      inferInstance
    exact LieSystem3.of_empty (by rw [hrf]; simp [oddQuotientFamily])

theorem exactLocalLieSystems3_of_cit3Below (hΩ : InClass3 Ω)
    (hBelow : CIT3Below (Nat.card G)) :
    ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) → ¬ ({c} : Set G) ⊆ Subgroup.center G →
      LieSystemMod3 (exactPair3 Ω c) :=
  fun _ hc2 hnc => lieSystemMod3_exactPair3 hΩ hc2 hBelow hnc

end Pair

section Compare

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem centralizingMembers_subset_tqMembers3 :
    centralizingMembers Ω {c} ⊆ tqMembers3 Ω c :=
  fun _ hK => mem_tqMembers3_of_le_centralizer hK.1 hK.2

theorem centralizingMembers_subset_exactFamily3 :
    centralizingMembers Ω {c} ⊆ exactFamily3 Ω c :=
  fun _ hK => mem_exactFamily3_of_le_centralizer hK.1 hK.2

theorem centralizingLayer_le_exactLayer3 : centralizingLayer Ω {c} ≤ exactLayer3 Ω c :=
  iSup₂_le fun _ hK => le_centralizingLayer
    (⟨centralizingMembers_subset_exactFamily3 hK, hK.2⟩ :
      _ ∈ centralizingMembers (exactFamily3 Ω c) {c})

theorem tqMembers3_eq_centralizingMembers_of_exact (hex : ExactMembers3 Ω) :
    tqMembers3 Ω c = centralizingMembers Ω {c} := by
  ext K
  refine ⟨fun hK => ⟨hK.1, fun x hx => ?_⟩, fun hK => mem_tqMembers3_of_le_centralizer hK.1 hK.2⟩
  have hO : oddCoreIn K = ⊥ := by
    show Subgroup.map _ (classicalInvolutionOddCore ↥K) = ⊥
    rw [hex K hK.1, Subgroup.map_bot]
  have h := hK.2.2 x hx
  rw [hO, Subgroup.mem_bot] at h
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp h).symm

theorem exactFamily3_eq_centralizingMembers_of_exact (hex : ExactMembers3 Ω) :
    exactFamily3 Ω c = centralizingMembers Ω {c} := by
  ext K'
  refine ⟨?_, fun hK => centralizingMembers_subset_exactFamily3 hK⟩
  rintro ⟨K, hK, rfl⟩
  have hK' : K ∈ centralizingMembers Ω {c} := by
    rwa [← tqMembers3_eq_centralizingMembers_of_exact hex]
  rw [exactCore3_eq_self hK'.2]
  exact hK'

theorem exactLayer3_eq_centralizingLayer_of_exact (hex : ExactMembers3 Ω) :
    exactLayer3 Ω c = centralizingLayer Ω {c} := by
  have hfam : centralizingMembers (exactFamily3 Ω c) {c} = centralizingMembers Ω {c} := by
    rw [exactFamily3_eq_centralizingMembers_of_exact hex]
    ext K
    exact ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩
  unfold exactLayer3 centralizingLayer
  rw [hfam]

end Compare

end CFSG.ClassicalInvolution.Q3.Q3NL
