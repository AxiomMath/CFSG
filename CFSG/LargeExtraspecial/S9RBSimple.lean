module

public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S4SevenCases
public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem nonempty_RmodN_equiv_a6 (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hA6 : A6Case H C ht ht1 hVQ) :
    Nonempty (RmodN S g t ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := S45Q.nonempty_isometryGroup_equiv_perm (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) hA6.finrank_eq
  set Sp := TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) with hSp
  have h1 : RmodN S g t = (commutator Sp).map Sp.subtype := by
    rw [hA6.eq_commutator, ← hSp, Subgroup.map_subtype_commutator]
  have h2 : (commutator Sp).map (e : Sp →* Perm (Fin 6)) = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      ← commutator_def, alternatingGroup.commutator_perm_eq (by simp)]
  exact ⟨(MulEquiv.subgroupCongr h1).trans
    (((Subgroup.equivMapOfInjective _ _ Sp.subtype_injective).symm.trans
      (Subgroup.equivMapOfInjective _ _ e.injective)).trans (MulEquiv.subgroupCongr h2))⟩

theorem mem_of_index_lt_a6 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hA6 : A6Case H C ht ht1 hVQ) {K : Subgroup (Rbar S g t)} (hKn : K.Normal)
    (hN0 : ∀ x : Rbar S g t, (x : S.O) ∈ N0bar S g t → x ∈ K) (hK : K.index < 360)
    {x : Rbar S g t} (hx : x * x = 1) : x ∈ K := by
  have haQ := H.conj_mem
  set f := (resV haQ t).rangeRestrict with hf
  have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  obtain ⟨e⟩ := nonempty_RmodN_equiv_a6 H C ht ht1 hVQ hA6
  have e' : (resV haQ t).range ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr (range_resV haQ t)).trans e
  have hsimp : IsSimpleGroup (resV haQ t).range := by
    have := S45Q.isSimpleGroup_alternatingGroup_six
    exact e'.isSimpleGroup
  have hcard : Nat.card (resV haQ t).range = 360 := by
    rw [Nat.card_congr e'.toEquiv, S45Q.card_alternatingGroup_six]
  have hker : f.ker = (Nbar S g t).subgroupOf (Rbar S g t) := by
    ext y
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, mem_subgroupOf]
    exact resV_eq_one_iff haQ y
  have := hKn
  have hKm : (K.map f).Normal := hKn.map f hfs
  have hdvd3 : K.index ∣ 3 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map f) with h | h
    · exfalso
      have hle : K ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp h
      have h1 : f.ker.index ∣ K.index := Subgroup.index_dvd_of_le hle
      have h2 : f.ker.index = 360 := by
        rw [MonoidHom.ker_rangeRestrict, Subgroup.index_ker]
        exact hcard
      have h3 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h1
      omega
    · have hcod : Codisjoint K f.ker :=
        Subgroup.map_eq_range_iff.mp (h.trans (MonoidHom.range_eq_top_of_surjective _ hfs).symm)
      have hsup : f.ker ⊔ K = ⊤ := by rw [sup_comm]; exact codisjoint_iff.mp hcod
      have hidx : K.index = K.relIndex f.ker := by
        rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right]
      have hN0K : (N0bar S g t).subgroupOf (Rbar S g t) ≤ K := fun y hy =>
        hN0 y (mem_subgroupOf.mp hy)
      have h1 := Subgroup.relIndex_dvd_of_le_left (L := f.ker) hN0K
      rw [hker, Subgroup.relIndex_subgroupOf (Nbar_le_Rbar (S := S) (g := g) (t := t))] at h1
      rw [hidx, hker]
      rcases Nbar_eq_N0bar_or hCE H C ht (dtEqConj_of_transitive H ht hA6.transitive)
        (naturalPair_of_a6Case H C hA6) with h0 | ⟨-, h3⟩
      · rw [← h0, Subgroup.relIndex_self] at h1
        exact (Nat.dvd_one.mp h1) ▸ one_dvd 3
      · have h3' : (N0bar S g t).relIndex (Nbar S g t) = 3 := h3
        rw [h3'] at h1
        exact h1
  have hq2 : orderOf (x : Rbar S g t ⧸ K) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two, ← QuotientGroup.mk_mul, hx, QuotientGroup.mk_one]
  have hq3 : orderOf (x : Rbar S g t ⧸ K) ∣ 3 :=
    (_root_.orderOf_dvd_natCard _).trans hdvd3
  have hq1 : orderOf (x : Rbar S g t ⧸ K) = 1 :=
    Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hq2 hq3)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hq1
  exact hq1

end CFSG.LargeExtraspecial.S9.RB
