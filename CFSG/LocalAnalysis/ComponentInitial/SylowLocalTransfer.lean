module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {D : Type*} [Group D]

theorem not_le_of_isQuasisimple_of_isSolvable {K R : Subgroup D}
    (hK : CFSG.Assembly.IsQuasisimple K) (hR : Group.IsSolvable R) : ¬ K ≤ R := by
  intro hKR
  have hKn := (AssemblyBPredicates.isQuasisimple_iff_native K).1 hK
  have : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hKR)
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKn
  have : Group.IsPerfect K := hKn.1
  exact Group.IsPerfect.not_isSolvable (G := K) ‹_›

theorem not_isComponentOf_of_selfCentralizing [Finite D] {C R K : Subgroup D} (hRC : R ≤ C)
    (hRn : (R.subgroupOf C).Normal) (hR2 : IsPGroup 2 R) (hcen : C ⊓ centralizer (R : Set D) ≤ R)
    (hK : CFSG.Assembly.IsComponentOf K C) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable R := by
    have := hR2.isNilpotent
    infer_instance
  have hKn := (isComponentOf_iff_isComponent_subgroupOf hK.1).1 hK
  rcases component_normal_subgroup hKn hRn with h | h
  · refine not_le_of_isQuasisimple_of_isSolvable hK.2.2 hsolv fun k hk => ?_
    exact Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_subgroupOf.2 hk :
      (⟨k, hK.1 hk⟩ : C) ∈ K.subgroupOf C))
  · have h' := congrArg (Subgroup.map C.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK.1,
      Subgroup.map_subgroupOf_eq_of_le hRC, Subgroup.map_bot] at h'
    exact not_le_of_isQuasisimple_of_isSolvable hK.2.2 hsolv
      ((le_inf hK.1 (commutator_eq_bot_iff_le_centralizer.1 h')).trans hcen)

theorem sylow_containing_subgroup_local_normal_two_transfer [Finite D] {S : Subgroup D}
    (hS : ∃ P : Sylow 2 D, (P : Subgroup D) ≤ S) {t : D} (ht : orderOf t = 2)
    (hH : CFSG.IsCharacteristicP 2 (centralizer ({t} : Set D))) :
    ∃ s : D, (∃ g : D, s = g⁻¹ * t * g) ∧ s ∈ S ∧
      (∃ R : Subgroup D, R ≤ S ⊓ centralizer ({s} : Set D) ∧
        (R.subgroupOf (S ⊓ centralizer ({s} : Set D))).Normal ∧ IsPGroup 2 R ∧
        S ⊓ centralizer ({s} : Set D) ⊓ centralizer (R : Set D) ≤ R) ∧
      (∀ K : Subgroup D, ¬ CFSG.Assembly.IsComponentOf K (S ⊓ centralizer ({s} : Set D))) ∧
      ordProj[2] (Nat.card ↥(S ⊓ centralizer ({s} : Set D))) =
        ordProj[2] (Nat.card (centralizer ({t} : Set D))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀S⟩ := hS
  set H := centralizer ({t} : Set D) with hHdef
  set O := (CFSG.pCore 2 H).map H.subtype with hOdef
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hO2 : IsPGroup 2 O := (CFSG.pCore_isPGroup).map _
  have hOn : H ≤ normalizer (O : Set D) := by
    have hn : (O.subgroupOf H).Normal := by
      rw [hOdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact CFSG.pCore_normal
    exact (normal_subgroupOf_iff_le_normalizer hOH).1 hn
  have hcenO : H ⊓ centralizer (O : Set D) ≤ O := by
    intro x hx
    obtain ⟨hxH, hxc⟩ := mem_inf.1 hx
    have hmem : (⟨x, hxH⟩ : H) ∈ centralizer (CFSG.pCore 2 H : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.1 hxc (y : D) ⟨y, hy, rfl⟩)
    exact ⟨⟨x, hxH⟩, hH hmem, rfl⟩
  have htH : t ∈ H := mem_centralizer_iff.2 fun w hw => by rw [Set.mem_singleton_iff.1 hw]
  have htO : t ∈ O := by
    have hcen : (⟨t, htH⟩ : H) ∈ center H :=
      mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 y.2 t rfl).symm
    have hn : (zpowers (⟨t, htH⟩ : H)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxc : x ∈ center H := (zpowers_le.2 hcen) hx
      rw [mem_center_iff.1 hxc g, mul_inv_cancel_right]
      exact hx
    have h2 : IsPGroup 2 (zpowers (⟨t, htH⟩ : H)) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
    exact ⟨⟨t, htH⟩, le_pCore hn h2 (mem_zpowers _), rfl⟩
  obtain ⟨P₁⟩ : Nonempty (Sylow 2 H) := inferInstance
  set P := (P₁ : Subgroup H).map H.subtype with hPdef
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hOP : O ≤ P := Subgroup.map_mono (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup P₁)
  obtain ⟨T, hPT⟩ := (P₁.isPGroup'.map H.subtype).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq D T P₀
  have hcT : conjSub c (T : Subgroup D) ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    apply hP₀S
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (T : Subgroup D) hx
  set s := c * t * c⁻¹ with hsdef
  have hHs : conjSub c H = centralizer ({s} : Set D) := map_conj_centralizer_singleton c t
  set C := S ⊓ centralizer ({s} : Set D) with hCdef
  set R := conjSub c O with hRdef
  have hPC : conjSub c P ≤ C :=
    le_inf ((map_mono hPT).trans hcT) (hHs ▸ map_mono hPH)
  have hCH : C ≤ conjSub c H := hHs ▸ inf_le_right
  have hRC : R ≤ C := (map_mono hOP).trans hPC
  have hRn : (R.subgroupOf C).Normal := by
    refine normal_subgroupOf_of_le_normalizer (hCH.trans ?_)
    have := map_mono (f := (MulAut.conj c).toMonoidHom) hOn
    rwa [map_equiv_normalizer_eq] at this
  have hR2 : IsPGroup 2 R := hO2.map _
  have hcenR : C ⊓ centralizer (R : Set D) ≤ R := by
    calc C ⊓ centralizer (R : Set D) ≤ conjSub c H ⊓ centralizer (R : Set D) :=
          inf_le_inf_right _ hCH
      _ = conjSub c (H ⊓ centralizer (O : Set D)) := by
          rw [hRdef, ← conjSub_centralizer]
          exact (Subgroup.map_inf _ _ _ (MulAut.conj c).injective).symm
      _ ≤ R := map_mono hcenO
  refine ⟨s, ⟨c⁻¹, by rw [hsdef, inv_inv]⟩, hcT ⟨t, hPT (hOP htO), rfl⟩,
    ⟨R, hRC, hRn, hR2, hcenR⟩,
    fun K hK => not_isComponentOf_of_selfCentralizing hRC hRn hR2 hcenR hK, ?_⟩
  have hHcard : Nat.card (conjSub c H) = Nat.card H := card_conjSub c H
  have hPcard : Nat.card (conjSub c P) = ordProj[2] (Nat.card H) := by
    rw [card_conjSub, hPdef, Subgroup.card_map_of_injective H.subtype_injective,
      Sylow.card_eq_multiplicity]
  have hCpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hHpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  apply Nat.dvd_antisymm
  · have h1 : Nat.card C ∣ Nat.card H := hHcard ▸ Subgroup.card_dvd_of_le hCH
    exact Nat.ordProj_dvd_ordProj_of_dvd hHpos h1 2
  · have h1 : Nat.card (conjSub c P) ∣ Nat.card C := Subgroup.card_dvd_of_le hPC
    rw [hPcard] at h1
    exact (Nat.prime_two.pow_dvd_iff_dvd_ordProj hCpos).1 h1

end CFSG.LocalAnalysis.ComponentInitial
