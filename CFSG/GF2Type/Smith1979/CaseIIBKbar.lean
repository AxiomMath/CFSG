module

public import CFSG.GF2Type.Smith1979.CaseIIBHyp
public import CFSG.GF2Type.Smith1979.CaseIICTransfer
public import CFSG.GF2Type.Smith1979.CaseIIA0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def LbarL (S : Setting G) (g : G) :
    Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (S.Lbar g).map S.O.subtype

theorem mem_LbarL {s : S.Qt ≃ₗ[ZMod 2] S.Qt} :
    s ∈ LbarL S g ↔ ∃ s' ∈ S.Lbar g, (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) = s :=
  Iff.rfl

theorem coe_mem_LbarL {s : S.O} (hs : s ∈ S.Lbar g) : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ LbarL S g :=
  ⟨s, hs, rfl⟩

theorem ctx_Lbar (H : Hyp4 S g) (C : Cons311 S g) (hw : S.width = 6) :
    PhaseB.Ctx S.q (S.cl (g * S.z * g⁻¹)) (S.clSub (S.QG ⊓ S.Qa g)) (LbarL S g) where
  nondeg := S.q_nondegenerate
  finrank_V := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  a_ne := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  a_mem := cl_mem_clSub_self H.conj_mem
  finrank_E := by
    have h := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
    omega
  q_E := fun e he => S.q_eq_zero_of_mem_clSub_QG_inf_Qa H.conj_ne he
  perp_E := fun x hx => by
    rw [← orthogonal_clSub_eq H.conj_mem H.conj_ne C.card_QG_inf_Qa]
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun e he => ?_
    rw [polarBilin_apply_apply, polar_comm]
    exact hx e he
  card_L := by
    have h1 : Nat.card (LbarL S g) = Nat.card (S.Lbar g) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (S.Lbar g) S.O.subtype
        S.O.subtype_injective).toEquiv).symm
    rw [h1, C.card_Lbar, hw]
    norm_num
  q_apply := by
    rintro s ⟨s', -, rfl⟩ x
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup s'.2 x
  mul_self := by
    rintro s ⟨s', hs', rfl⟩
    exact congrArg Subtype.val (mul_self_of_mem_Lbar S H.conj_mem hs')
  apply_a := by
    rintro s ⟨s', hs', rfl⟩
    have h : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact (mem_fixSub S).mp h s' hs'
  comm := by
    rintro s ⟨s', hs', rfl⟩ t ⟨t', ht', rfl⟩
    exact congrArg Subtype.val (Lbar_comm S H.conj_mem hs' ht')
  sub_E := by
    rintro s ⟨s', hs', rfl⟩ e he
    exact Lbar_apply_sub_mem_span' H.conj_mem he hs'
  sub_A := by
    rintro s ⟨s', hs', rfl⟩ x hx
    obtain ⟨x', hx'Q, rfl⟩ := S.exists_cl x
    have hcomm : (g * S.z * g⁻¹) * x' = x' * (g * S.z * g⁻¹) :=
      (S.polar_cl_eq_zero_iff H.conj_mem hx'Q).mp hx
    exact C.comm_le x' ⟨hx'Q, mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hcomm⟩ s' hs'
  faithful := by
    rintro s ⟨s', hs', rfl⟩ h
    rw [C.faithful s' hs' h]
    rfl

theorem exists_Kbar_of_rank_six (H : Hyp4 S g) (C : Cons311 S g) (hw : S.width = 6) {t : S.O}
    (ht : t ∈ S.Lbar g)
    (h6 : finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 6) :
    ∃ Kb : Subgroup S.O, Kb ≤ S.Lbar g ∧
      (∀ s ∈ S.Lbar g, s ∈ Kb ↔
        finrank (ZMod 2) (commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≠ 6) ∧
      (∀ n ∈ NLbar S g, ∀ k ∈ Kb, n * k * n⁻¹ ∈ Kb) ∧ t ∉ Kb ∧
      ∀ l ∈ S.Lbar g, l ∈ Kb ∨ t * l ∈ Kb := by
  obtain ⟨K, hKL, hK, htK, hLK⟩ :=
    (ctx_Lbar H C hw).exists_Kbar (coe_mem_LbarL ht) h6
  have hchar : ∀ s ∈ S.Lbar g, s ∈ K.comap S.O.subtype ↔
      finrank (ZMod 2) (commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≠ 6 := fun s hs =>
    hK _ (coe_mem_LbarL hs)
  have hle : K.comap S.O.subtype ≤ S.Lbar g := by
    intro k hk
    obtain ⟨k', hk', hkk'⟩ := mem_LbarL.mp (hKL hk)
    rwa [← Subtype.ext hkk']
  refine ⟨K.comap S.O.subtype, hle, hchar, ?_, ?_, ?_⟩
  · intro n hn k hk
    have hkL : k ∈ S.Lbar g := hle hk
    have hnk : n * k * n⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hn.2 k).mp hkL
    rw [hchar _ hnk]
    have := (hchar k hkL).mp hk
    have e : ((n * k * n⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        (n : S.Qt ≃ₗ[ZMod 2] S.Qt) * (k : S.Qt ≃ₗ[ZMod 2] S.Qt) *
          (n : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := rfl
    rwa [e, finrank_commSpace_conj]
  · exact htK
  · intro l hl
    exact hLK _ (coe_mem_LbarL hl)

theorem not_mem_commutator_Mbar_of_rank_six (H : Hyp4 S g) (C : Cons311 S g)
    (hw : S.width = 6) {t : S.O} (ht : t ∈ S.Lbar g)
    (h6 : finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 6) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype := by
  obtain ⟨Kb, -, -, hKN, htK, hLK⟩ := exists_Kbar_of_rank_six H C hw ht h6
  exact not_mem_commutator_Mbar_II H C ht Kb hKN htK hLK

namespace Data

theorem not_mem_commutator_Mbar {t : S.O} (D : Data S g t) :
    t ∉ (_root_.commutator S.Mbar).map S.Mbar.subtype :=
  not_mem_commutator_Mbar_of_rank_six D.H D.C D.hw D.ht D.finrank_commSpace

end Data

end Case2

end CFSG.GF2Type.Smith1979
