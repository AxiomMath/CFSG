module

public import CFSG.LargeExtraspecial.S4SevenAMain
public import CFSG.LargeExtraspecial.S4FiveMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem dtEqConj_of_transitive (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v) : DtEqConj S g t :=
  dtEqConj_of_forall_mem_orbitOf H ht fun _ hth => htr _ (bV_ne_zero H hth)

theorem dtEqConj_of_linCase (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) : DtEqConj S g t :=
  dtEqConj_of_forall_mem_orbitOf H ht fun _ hth =>
    (mem_orbitOf_RmodN_iff H.conj_mem ht).mpr (hL.mem_orbit _ (bV_ne_zero H hth))

theorem dtEqConj_of_omegaCase (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hΩ : OmegaCase H C ht ht1 hVQ) : DtEqConj S g t :=
  dtEqConj_of_forall_mem_orbitOf H ht fun _ hth =>
    bV_mem_orbitOf H C ht ht1 hVQ hNo hΩ.not_transitive hth

theorem dtEqConj_of_pgl25Case (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hP : PGL25Case H C ht ht1 hVQ) : DtEqConj S g t :=
  dtEqConj_of_transitive H ht hP.transitive

theorem naturalPair_of_linCase {t : S.O} {ht : t ∈ S.Lbar g} (hL : LinCase S g ht) :
    NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) :=
  Or.inl ⟨hL.two_le_finrank, hL.eq_top, hL.LmodN_eq⟩

theorem naturalPair_of_spCase (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hSp : SpCase H C ht ht1 hVQ) : NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) :=
  Or.inr (Or.inl ⟨four_le_finrank_Vt H C ht ht1 hVQ hNo, beta H C ht ht1 hVQ,
    beta_isAlt H C ht ht1 hVQ, beta_nondegenerate H C ht ht1 hVQ, hSp.eq_sp, hSp.LmodN_eq⟩)

theorem naturalPair_of_a6Case (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hA : A6Case H C ht ht1 hVQ) : NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hle := LmodN_le_spPointRadical H C ht ht1 hVQ
  have hlt : LmodN S g t < spPointRadical (beta H C ht ht1 hVQ) (aV ht) :=
    lt_of_le_of_ne hle fun h => hA.tau_not_mem (h ▸ spTransvection_mem_U _ _)
  have hcard : Nat.card (spPointRadical (beta H C ht ht1 hVQ) (aV ht)) =
      2 * Nat.card (LmodN S g t) := by
    have h1 := card_spPointRadical_le_two_mul H C ht ht1 hVQ
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
    have h2 := Subgroup.card_lt_of_lt hlt
    have hpos : 0 < Nat.card (LmodN S g t) := Nat.card_pos
    rw [hk] at h1 h2 ⊢
    have hk1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      have : Nat.card (LmodN S g t) * k ≤ Nat.card (LmodN S g t) * 1 :=
        Nat.mul_le_mul_left _ hk1
      omega
    have hk2 : k ≤ 2 := by
      have : Nat.card (LmodN S g t) * k ≤ Nat.card (LmodN S g t) * 2 := by linarith
      exact Nat.le_of_mul_le_mul_left this hpos
    have : k = 2 := by omega
    rw [this, mul_comm]
  exact Or.inr (Or.inr (Or.inl ⟨hA.finrank_eq, beta H C ht ht1 hVQ, beta_isAlt H C ht ht1 hVQ,
    beta_nondegenerate H C ht ht1 hVQ, hA.eq_commutator, hle, hcard, hA.tau_not_mem,
    hA.no_typeA⟩))

theorem naturalPair_of_omegaCase (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hΩ : OmegaCase H C ht ht1 hVQ) : NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) := by
  obtain ⟨Q, hQ, -, hX, hE, hsing⟩ := hΩ.exists_form
  refine Or.inr (Or.inr (Or.inr ⟨four_le_finrank_Vt H C ht ht1 hVQ hNo, Q, hQ, ?_, hX, hE⟩))
  exact (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩

theorem N0bar_eq_iSup_Dset (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hD : DtEqConj S g t) : N0bar S g t = ⨆ X ∈ Dset S g t, X ⊓ Nbar S g t := by
  apply le_antisymm
  · exact iSup₂_le fun k hk => le_iSup₂_of_le (S.Lbar ((k : G) * g))
      (Lbar_mul_mem_Dset (mem_Lbar_mul_of_mem_Rbar H ht hk)) le_rfl
  · refine iSup₂_le fun X hX => ?_
    obtain ⟨h, rfl, hth⟩ := hX
    obtain ⟨k, hk, hhk⟩ := hD h hth
    rw [hhk]
    exact Lbar_mul_inf_Nbar_le_N0bar hk

theorem normal_N0bar_subgroupOf_Nbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} :
    ((N0bar S g t).subgroupOf (Nbar S g t)).Normal :=
  ⟨fun x hx n => by
    rw [mem_subgroupOf] at hx ⊢
    exact conj_mem_N0bar haQ (Nbar_le_Rbar n.2) hx⟩

theorem isSolvable_Nbar_of_index (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (h3 : ((N0bar S g t).subgroupOf (Nbar S g t)).index = 3) : Group.IsSolvable (Nbar S g t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := normal_N0bar_subgroupOf_Nbar (t := t) H.conj_mem
  have hp : IsPGroup 2 ((N0bar S g t).subgroupOf (Nbar S g t)) :=
    (isPGroup_N0bar H ht).comap_of_injective _ (Nbar S g t).subtype_injective
  have : Group.IsNilpotent ((N0bar S g t).subgroupOf (Nbar S g t)) := hp.isNilpotent
  have hc : IsCyclic (↥(Nbar S g t) ⧸ (N0bar S g t).subgroupOf (Nbar S g t)) :=
    isCyclic_of_prime_card (p := 3) (by rw [← Subgroup.index, h3])
  have : Group.IsSolvable (↥(Nbar S g t) ⧸ (N0bar S g t).subgroupOf (Nbar S g t)) :=
    Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  exact Group.isSolvable_of_subgroup_quotient ((N0bar S g t).subgroupOf (Nbar S g t))

theorem timmesfeld_4_7_a (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g)
    (hP : ∀ hVQ : ¬ V S g t ≤ S.Qa g, ¬ PGL25Case H C ht ht1 hVQ) :
    (IsPGroup 2 (Nbar S g t) ∧ Nbar S g t = N0bar S g t ∧
      Nbar S g t = ⨆ X ∈ Dset S g t, X ⊓ Nbar S g t) ∨
    (A6Pair (RmodN S g t) (LmodN S g t) (aV ht) ∧
      ((N0bar S g t).subgroupOf (Nbar S g t)).index = 3 ∧ Group.IsSolvable (Nbar S g t)) := by
  have key : ∀ hD : DtEqConj S g t, NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) →
      (IsPGroup 2 (Nbar S g t) ∧ Nbar S g t = N0bar S g t ∧
        Nbar S g t = ⨆ X ∈ Dset S g t, X ⊓ Nbar S g t) ∨
      (A6Pair (RmodN S g t) (LmodN S g t) (aV ht) ∧
        ((N0bar S g t).subgroupOf (Nbar S g t)).index = 3 ∧ Group.IsSolvable (Nbar S g t)) := by
    intro hD hpair
    rcases Nbar_eq_N0bar_or hCE H C ht hD hpair with h | ⟨hA, h3⟩
    · refine Or.inl ⟨h ▸ isPGroup_N0bar H ht, h, ?_⟩
      rw [← N0bar_eq_iSup_Dset H ht hD, h]
    · exact Or.inr ⟨hA, h3, isSolvable_Nbar_of_index H ht h3⟩
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hSp | hA | hΩ | hPG⟩
  · exact absurd hR' hR
  · exact key (dtEqConj_of_linCase H hL) (naturalPair_of_linCase hL)
  · exact key (dtEqConj_of_transitive H ht hSp.transitive)
      (naturalPair_of_spCase H hNo C hSp)
  · exact key (dtEqConj_of_transitive H ht hA.transitive) (naturalPair_of_a6Case H C hA)
  · exact key (dtEqConj_of_omegaCase H hNo C hΩ) (naturalPair_of_omegaCase H hNo C hΩ)
  · exact absurd hPG (hP hVQ)

end CFSG.LargeExtraspecial.S4
