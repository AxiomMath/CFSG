module

public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem cl_eq_of_Lbar_eq {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hbQ : g' * S.z * g'⁻¹ ∈ S.QG) (hbne : g' * S.z * g'⁻¹ ≠ S.z) (hn : 3 ≤ S.width)
    (hL : S.Lbar g = S.Lbar g') : S.cl (g * S.z * g⁻¹) = S.cl (g' * S.z * g'⁻¹) := by
  by_contra hab
  have haQb := S.s12_not_mem_Qa_of_Lbar_eq haQ hne hbQ hbne hL hab
  have hW := fun w hw => S.s12_cl_eq_zero_of_mem_inf_inf haQ hne hbQ hbne hL hab haQb (w := w) hw
  have hfixb : ∀ t ∈ S.Lbar g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g' * S.z * g'⁻¹)) =
      S.cl (g' * S.z * g'⁻¹) := fun t ht => S.s12_Lbar_apply_cl_a hbQ (hL ▸ ht)
  have hcomm := S.s12_commute_a_of_fixed haQ hne (by omega) hbQ hfixb
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hb0 := S.s12_cl_ne_zero_of_conj hbQ hbne
  have hqa : S.q (S.cl (g * S.z * g⁻¹)) = 0 := (S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)
  have hqb : S.q (S.cl (g' * S.z * g'⁻¹)) = 0 :=
    (S.q_cl_eq_zero_iff hbQ).mpr (S.s12_conj_z_sq g')
  have hpol : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl (g' * S.z * g'⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff haQ hbQ).mpr hcomm.symm
  have hli : LinearIndependent (ZMod 2) ![S.cl (g * S.z * g⁻¹), S.cl (g' * S.z * g'⁻¹)] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨ha0, hb0, hab⟩
  have hfixperp : ∀ t ∈ S.Lbar g, ∀ v, polar S.q (S.cl (g * S.z * g⁻¹)) v = 0 →
      polar S.q (S.cl (g' * S.z * g'⁻¹)) v = 0 → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro t ht v hva hvb
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
    have hxa := (S.polar_cl_eq_zero_iff haQ hxQ).mp hva
    have hxb := (S.polar_cl_eq_zero_iff hbQ hxQ).mp hvb
    exact S.s12_Lbar_fix_of_commute haQ hne hL hW hxQ hxa.symm hxb.symm ht
  have hall : ∀ t ∈ S.Lbar g, t ≠ 1 → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      CFSG.ClassicalGroups.Orthogonal.eichler S.q (S.cl (g * S.z * g⁻¹))
        (S.cl (g' * S.z * g'⁻¹)) := by
    intro t ht ht1
    have ht1' : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun e => ht1 (Subtype.ext e)
    obtain ⟨-, hc, -, -⟩ := timmesfeld_12_2 S.q_nondegenerate t.2 ht1' hli hqa hqb hpol
      (hfixperp t ht)
    rcases eq_one_or_eq_eichler_of_totallySingular S.q_nondegenerate hli hqa hqb hpol t.2
      hc.le (hfixperp t ht) with e | e
    · exact absurd e ht1'
    · exact e
  have hcard := Setting.s12_card_le_two_of_forall_eq (S.Lbar g) fun x hx y hy hx1 hy1 =>
    Subtype.ext ((hall x hx hx1).trans (hall y hy hy1).symm)
  have hge := S.card_Lbar_ge haQ hne
  have h4 : 2 ^ 2 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem Lbar_mul_self {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {e : S.O} (he : e ∈ S.Lbar g) :
    e * e = 1 := by
  have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
  have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) e he
  rw [pow_two] at h2
  exact h2

theorem isPGroup_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) : IsPGroup 2 (S.Lbar g) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, pow_two, Lbar_mul_self haQ x.2]
  rfl

theorem Lbar_comm {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {e e' : S.O} (he : e ∈ S.Lbar g)
    (he' : e' ∈ S.Lbar g) : e * e' = e' * e :=
  congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)

end CFSG.LargeExtraspecial.GLR
