module

public import CFSG.LargeExtraspecial.AS35HCoprime
public import CFSG.LargeExtraspecial.S14C12SmQ
public import CFSG.LargeExtraspecial.S14SMEDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup CFSG.Open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G]

abbrev cent2 (t u : G) : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G)

theorem mem_cent2 {t u x : G} : x ∈ cent2 t u ↔ Commute x t ∧ Commute x u := by
  rw [mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1.eq, h.2.eq⟩⟩

theorem z_mem_cent2 (S : Setting G) {t u : G} (htM : t ∈ S.M) (huM : u ∈ S.M) :
    S.z ∈ cent2 t u :=
  mem_cent2.mpr ⟨(S.z_comm htM).symm, (S.z_comm huM).symm⟩

variable [Finite G]

theorem mul_not_mem_QG (S : Setting G) {t u : G} (h3 : orderOf (t * u) = 3) :
    t * u ∉ S.QG := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one (S.pow_four_eq_one h)
  rw [h3] at hd
  norm_num at hd

theorem fixQt_eq_of_smithE34a (h34a : SmithE34a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t : G}
    (ht : IsConj S.z t) (htM : t ∈ S.M) (htQ : t ∉ S.QG) :
    S.fixQt t = S.clSub (S.QG ⊓ centralizer ({t} : Set G)) := by
  by_contra hne
  obtain ⟨y, -, hy⟩ := S.lemma_3_2_1 htM hne
  exact h34a G S hw hU t ht htM htQ (ht.trans (isConj_iff.mpr ⟨y, hy⟩))

theorem rhoL_rhoL (S : Setting G) {t : G} (htM : t ∈ S.M) (ht2 : t * t = 1) (w : S.Qt) :
    S.rhoL htM (S.rhoL htM w) = w := by
  have h := congrArg (fun f : S.Qt ≃ₗ[ZMod 2] S.Qt => f w) (S.ρ_mul_self htM (by rw [sq, ht2]))
  exact h

theorem cqx_eq_cent2 (h25 : SmithE25) (h34a : SmithE34a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t u : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (huQ : u ∉ S.QG) (h3 : orderOf (t * u) = 3) :
    S.QG ⊓ centralizer ({t * u} : Set G) = S.QG ⊓ cent2 t u := by
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  · obtain ⟨hqQ, hqθ⟩ := mem_inf.mp hq
    have hqθ' : q * (t * u) = t * u * q := mem_centralizer_singleton_iff.mp hqθ
    have htt : t * t = 1 := SmithQ.mul_self_eq_one_of_isConj S ht
    set v := S.cl q with hv
    have h1 : S.rhoL htM (S.rhoL huM v) = v := by
      rw [hv, S.rhoL_cl huM hqQ, S.rhoL_cl htM (S.conj_mem_QG huM hqQ)]
      congr 1
      calc t * (u * q * u⁻¹) * t⁻¹ = (q * (t * u)) * (t * u)⁻¹ := by rw [hqθ']; group
        _ = q := by group
    have h2 : S.rhoL htM v = S.rhoL huM v := by
      conv_lhs => rw [← h1]
      exact rhoL_rhoL S htM htt _
    obtain ⟨-, h3p⟩ := h25 G S hw hU t u ht hu htM huM htQ huQ (mul_not_mem_QG S h3)
    have hbot := h3p (by rw [← h3, pow_orderOf_eq_one]; exact S.QG.one_mem)
    have hmem : S.rhoL htM v - v ∈ S.commQt t ⊓ S.commQt u := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [S.commQt_of_mem htM]
        exact mem_commSpace.mpr ⟨v, rfl⟩
      · rw [S.commQt_of_mem huM, h2]
        exact mem_commSpace.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    have hmem' : S.rhoL huM v = v := h2 ▸ hmem
    have hfixt : S.cl q ∈ S.fixQt t := by
      rw [S.cl_mem_fixQt_iff htM hqQ, ← S.rhoL_cl htM hqQ]
      exact hmem
    have hfixu : S.cl q ∈ S.fixQt u := by
      rw [S.cl_mem_fixQt_iff huM hqQ, ← S.rhoL_cl huM hqQ]
      exact hmem'
    have hct := S.commute_of_cl_mem_fixQt htM
      (fixQt_eq_of_smithE34a h34a S hw hU ht htM htQ) hqQ hfixt
    have hcu := S.commute_of_cl_mem_fixQt huM
      (fixQt_eq_of_smithE34a h34a S hw hU hu huM huQ) hqQ hfixu
    exact mem_inf.mpr ⟨hqQ, mem_cent2.mpr ⟨hct.symm, hcu.symm⟩⟩
  · obtain ⟨hqQ, hqc⟩ := mem_inf.mp hq
    obtain ⟨hqt, hqu⟩ := mem_cent2.mp hqc
    exact mem_inf.mpr ⟨hqQ, mem_centralizer_singleton_iff.mpr (hqt.mul_right hqu).eq⟩

theorem isExtraspecialPGroup_cent2 (h25 : SmithE25) (h34a : SmithE34a) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t u : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (huQ : u ∉ S.QG) (h3 : orderOf (t * u) = 3)
    (hcard : 2 ^ 9 ≤ Nat.card ↥(S.QG ⊓ cent2 t u)) :
    IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) := by
  have hθM : t * u ∈ S.M := S.M.mul_mem htM huM
  have hθ3 : (t * u) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have heq := cqx_eq_cent2 h25 h34a S hw hU ht hu htM huM htQ huQ h3
  have hfix : fixSpace (S.rhoL hθM) ≠ ⊥ := by
    intro hbot
    have hc := S.card_cqx_of_pow_three hθM hθ3
    rw [hbot, finrank_bot, pow_zero, mul_one, heq] at hc
    rw [hc] at hcard
    norm_num at hcard
  exact CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (MulEquiv.subgroupCongr heq)
    (S.isExtraspecialPGroup_cqx hθM hθ3 hfix)

end CFSG.LargeExtraspecial.S14.SMJ
